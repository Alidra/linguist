require open tests.OK.Set tests.OK.Prop tests.OK.FOL tests.OK.Eq
  tests.OK.Nat tests.OK.Bool;

(a:Set) inductive 𝕃:TYPE ≔
| □ : 𝕃 a // \Box
| ⸬ : τ a → 𝕃 a → 𝕃 a; // ::

notation ⸬ infix right 20;

// set code for 𝕃

constant symbol list : Set → Set;

rule τ (list $a) ↪ 𝕃 $a;

// is□

symbol is□ [a]: 𝕃 a → 𝔹;

rule is□ □ ↪ true
with is□ (_ ⸬ _) ↪ false;

// non confusion of constructors

opaque symbol ⸬≠□ [a] [x:τ a] [l] : π (x ⸬ l ≠ □) ≔
begin
  assume a x l h; refine ind_eq h (λ l, istrue(is□ l)) ⊤ᵢ
end;

opaque symbol □≠⸬ [a] [x:τ a] [l] : π (□ ≠ x ⸬ l) ≔
begin
  assume a x l h; apply @⸬≠□ a x l; symmetry; apply h
end;

// head

symbol head [a] : τ a → 𝕃 a → τ a;

rule head $x □ ↪ $x
with head _ ($x ⸬ _) ↪ $x;

// tail

symbol behead [a] : 𝕃 a → 𝕃 a;

rule behead □ ↪ □
with behead (_ ⸬ $l) ↪ $l;

// injectivity of constructors

opaque symbol ⸬_inj [a] [x:τ a] [l y m] : π(x ⸬ l = y ⸬ m) → π(x = y ∧ l = m) ≔
begin
  assume a x l y m e; apply ∧ᵢ { refine feq (head x) e } { refine feq behead e }
end;

// boolean equality on lists

symbol eql [a] : (τ a → τ a → 𝔹) → 𝕃 a → 𝕃 a → 𝔹;

rule eql _ □ □ ↪ true
with eql _ (_ ⸬ _) □ ↪ false
with eql _ □ (_ ⸬ _) ↪ false
with eql $beq ($x ⸬ $l) ($y ⸬ $m) ↪ ($beq $x $y) and (eql $beq $l $m);

opaque symbol eql_correct a (beq:τ a → τ a → 𝔹) :
  π(`∀ x, `∀ y, beq x y ⇒ x = y) → π(`∀ l, `∀ m, eql beq l m ⇒ l = m) ≔
begin
  assume a beq beq_correct; induction
  { induction
    { reflexivity }
    { simplify; assume y m i c; refine ⊥ₑ c }
  }
  { assume x l h; induction
    { simplify; assume c; refine ⊥ₑ c; }
    { simplify; assume y m i c;
      apply feq2 (⸬) _ _
      { apply beq_correct; apply @andₑ₁ _ (eql beq l m) c }
      { apply h; refine @andₑ₂ (beq x y) _ c
      } 
    }
  }
end;

opaque symbol eql_complete a (beq : τ a → τ a → 𝔹) :
  π(`∀ x, `∀ y, x = y ⇒ beq x y) → π(`∀ l, `∀ m, l = m ⇒ eql beq l m) ≔
begin
  assume a beq beq_complete; induction
  { assume m i; rewrite left i; apply ⊤ᵢ; }
  { assume x l h; induction
    { assume j; apply ⸬≠□ j; }
    { assume y m i j; simplify;
      have j': π(x = y ∧ l = m) { apply ⸬_inj j };
      apply @istrue_and (beq x y) (eql beq l m); apply ∧ᵢ
      { apply beq_complete x y; apply ∧ₑ₁ j' }
      { apply h m; apply ∧ₑ₂ j' }
    }
  }
end;

// size

symbol size [a] : 𝕃 a → ℕ;

rule size □ ↪ 0
with size (_ ⸬ $l) ↪ size $l +1;

opaque symbol size0nil [a] (l:𝕃 a) : π (size l = 0) → π (l = □) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume e l h i; apply ⊥ₑ; apply s≠0 i; }
end;

symbol nilp [a] l ≔ is0 (@size a l);

opaque symbol size_behead [a] (l:𝕃 a) : π (size (behead l) = size l ∸1) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume e l h; reflexivity; }
end;

// concatenation

symbol ++ [a] : 𝕃 a → 𝕃 a → 𝕃 a; notation ++ infix right 30; // \cdot

assert x y z ⊢ x ++ y ++ z ≡ x ++ (y ++ z);
assert x l m ⊢ x ⸬ l ++ m ≡ x ⸬ (l ++ m);

rule □ ++ $m ↪ $m
with ($x ⸬ $l) ++ $m ↪ $x ⸬ ($l ++ $m);

opaque symbol cat0s [a] (l:𝕃 a) : π (□ ++ l = l) ≔
begin
  reflexivity;
end;

opaque symbol cat1s [a] (x:τ a) l : π ((x ⸬ □) ++ l = (x ⸬ l)) ≔
begin
  reflexivity;
end;

opaque symbol cat_cons [a] (x:τ a) l1 l2 : π ((x ⸬ l1) ++ l2 = x ⸬ (l1 ++ l2)) ≔
begin
  reflexivity;
end;

// nseq

symbol nseq [a] : ℕ → τ a → 𝕃 a;

rule nseq 0 _ ↪ □
with nseq ($n +1) $x ↪ $x ⸬ (nseq $n $x);

// ncons

symbol ncons [a] : ℕ → τ a → 𝕃 a → 𝕃 a;

rule ncons 0 _ $l ↪ $l
with ncons ($n +1) $x $l ↪ $x ⸬ ncons $n $x $l;

opaque symbol size_ncons [a] n (x:τ a) l : π (size (ncons n x l) = n + size l) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume n h x l; simplify; apply feq (+1) (h x l); }
end;

opaque symbol size_nseq [a] n (x:τ a) : π (size (nseq n x) = n) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume n h x; simplify; apply feq (+1) (h x); }
end;

opaque symbol cat_nseq [a] n (x:τ a) l : π (nseq n x ++ l = ncons n x l) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume n h x l; simplify; rewrite h x l; reflexivity; }
end;

opaque symbol nseqD [a] n1 n2 (x:τ a) :
  π (nseq (n1 + n2) x = nseq n1 x ++ nseq n2 x) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume n1 h n2 x; simplify; rewrite h n2; reflexivity; }
end;

opaque symbol cats0 [a] (l:𝕃 a) : π(l ++ □ = l) ≔
begin
  assume a;
  induction
    // case l = □
    { reflexivity; }
    // case l = x ⸬ l'
    { assume x l' h; simplify; rewrite h; reflexivity; }
end;

rule $m ++ □ ↪ $m;

opaque symbol size_cat [a] (l m : 𝕃 a) : π(size (l ++ m) = size l + size m) ≔
begin
  assume a;
  induction
    // case l = □
    { reflexivity; }
    // case l = x⸬l'
    { assume x l' h m; simplify; rewrite h; reflexivity; }
end;

rule size ($l ++ $m) ↪ size $l + size $m;

opaque symbol catA  [a] (l m n : 𝕃 a) : π((l ++ m) ++ n = l ++ (m ++ n)) ≔
begin
  assume a;
  induction
    // case l = □
    { reflexivity; }
    // case l = x⸬l'
    { assume x l' h m n; simplify; rewrite h; reflexivity; }
end;

rule ($l ++ $m) ++ $n ↪ $l ++ ($m ++ $n);

opaque symbol cat_nilp [a] (l1 l2 : 𝕃 a) :
  π (nilp (l1 ++ l2) = (nilp l1 and nilp l2)) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume e l h l2; simplify; reflexivity; }
end;

// list reversal

symbol rev [a] : 𝕃 a → 𝕃 a;

rule rev □ ↪ □
with rev ($x ⸬ $l) ↪ rev $l ++ ($x ⸬ □);

opaque symbol rev_concat [a] (l m : 𝕃 a) : π(rev (l ++ m) = rev m ++ rev l) ≔
begin
  assume a;
  induction
    // case l = □
    { simplify; reflexivity; }
    // case l = ⸬
    { assume x l h m; simplify; rewrite h; reflexivity; }
end;

rule rev ($l ++ $m) ↪ rev $m ++ rev $l;

opaque symbol rev_idem [a] (l :𝕃 a) : π(rev (rev l) = l) ≔
begin
  assume a; induction
  { reflexivity }
  { assume x l h; simplify; rewrite h; reflexivity }
end;

opaque symbol size_rev [a] (l : 𝕃 a) : π(size (rev l) = size l) ≔
begin
  assume a;
  induction
    // case l = □
    { simplify; reflexivity; }
    // case l = ⸬
    { assume x l h; simplify; rewrite h; reflexivity; }
end;

// rcons

symbol rcons [a] : 𝕃 a → τ a → 𝕃 a;

rule rcons □ $x ↪ $x ⸬ □
with rcons ($e ⸬ $l) $x ↪ $e ⸬ (rcons $l $x);

opaque symbol cats1 [a] (l:𝕃 a) (z:τ a) : π (l ++ (z ⸬ □) = rcons l z) ≔
begin
  assume a; induction
  { reflexivity; }
  { assume e l h z; simplify; rewrite h z; reflexivity; }
end;

opaque symbol rcons_cons [a] (x:τ a) (s:𝕃 a) (z:τ a) :
  π (rcons (x ⸬ s) z = x ⸬ rcons s z) ≔
begin
  reflexivity;
end;

// Arr

symbol Arr : ℕ → Set → Set → TYPE;

rule Arr 0 _ $b ↪ τ $b
with Arr ($n +1) $a $b ↪ τ $a → Arr $n $a $b;

// seqn

symbol seqn_acc [a] n : 𝕃 a → Arr n a (list a);

rule seqn_acc 0 $l ↪ rev $l
with seqn_acc ($n +1) $l $x ↪ seqn_acc $n ($x ⸬ $l);

symbol seqn [a] n ≔ @seqn_acc a n □;

assert a (x y : τ a) ⊢ seqn 2 x y ≡ x ⸬ y ⸬ □;

// iota

symbol iota : ℕ → ℕ → 𝕃 nat;
rule iota _ 0 ↪ □
with iota $n ($k +1) ↪ $n ⸬ iota ($n +1) $k;

assert ⊢ iota 1 2 ≡ 1 ⸬ 2 ⸬ □;

// indexes

symbol indexes [a] : 𝕃 a → 𝕃 nat;

rule indexes $l ↪ iota 0 (size $l);

assert x ⊢ indexes (x ⸬ x ⸬ x  ⸬ x ⸬ □) ≡ 0 ⸬ 1 ⸬ 2 ⸬ 3 ⸬ □;

// last

symbol last [a] : τ a → 𝕃 a → τ a;

rule last $x □ ↪ $x
with last _ ($e ⸬ $l) ↪ last $e $l;

assert ⊢ last 4 (3 ⸬ 2 ⸬ 1 ⸬ □) ≡ 1;
assert ⊢ last 4 □ ≡ 4;

// belast

symbol belast [a] : τ a → 𝕃 a → 𝕃 a;

rule belast _ □ ↪ □
with belast $x ($e ⸬ $l) ↪ $x ⸬ belast $e $l;

assert ⊢ belast 4 (3 ⸬ 2 ⸬ 1 ⸬ □) ≡ 4 ⸬ 3 ⸬ 2 ⸬ □;

// nth

symbol nth [a] : τ a → 𝕃 a → ℕ → τ a;

rule nth $x □ _ ↪ $x
with nth _ ($e ⸬ _) 0 ↪ $e
with nth $x (_ ⸬ $l) ($n +1) ↪ nth $x $l $n;

assert ⊢ nth 4 (3 ⸬ 2 ⸬ 1 ⸬ □) 0 ≡ 3;
assert ⊢ nth 4 (3 ⸬ 2 ⸬ 1 ⸬ □) 2 ≡ 1;
assert ⊢ nth 4 (3 ⸬ 2 ⸬ 1 ⸬ □) 3 ≡ 4;
assert ⊢ nth 4 (3 ⸬ 2 ⸬ 1 ⸬ □) 42 ≡ 4;

// set_nth

symbol set_nth [a] : τ a → 𝕃 a → ℕ → τ a → 𝕃 a;

rule set_nth _ □ 0 $y ↪ $y ⸬ □
with set_nth _ (_ ⸬ $l) 0 $y ↪ $y ⸬ $l
with set_nth $x □ ($i +1) $y ↪ $x ⸬ set_nth $x □ $i $y
with set_nth $x ($e ⸬ $l) ($i +1) $y ↪ $e ⸬ set_nth $x $l $i $y;

assert ⊢ set_nth 42 (3 ⸬ 2 ⸬ 1 ⸬ □) 1 6 ≡ 3 ⸬ 6 ⸬ 1 ⸬ □;
assert ⊢ set_nth 42 (3 ⸬ 2 ⸬ 1 ⸬ □) 2 6 ≡ 3 ⸬ 2 ⸬ 6 ⸬ □;
assert ⊢ set_nth 42 (3 ⸬ 2 ⸬ 1 ⸬ □) 5 6 ≡ 3 ⸬ 2 ⸬ 1 ⸬ 42 ⸬ 42 ⸬ 6 ⸬ □;

// incr_nth

symbol incr_nth : 𝕃 nat → τ nat → 𝕃 nat;

rule incr_nth □ 0 ↪ 1 ⸬ □
with incr_nth □ ($i +1) ↪ 0 ⸬ incr_nth □ $i
with incr_nth ($n ⸬ $l) 0 ↪ $n +1 ⸬ $l
with incr_nth ($n ⸬ $l) ($i +1) ↪ $n ⸬ incr_nth $l $i;

assert ⊢ incr_nth (3 ⸬ 2 ⸬ 1 ⸬ □) 1 ≡ 3 ⸬ 3 ⸬ 1 ⸬ □;
assert ⊢ incr_nth (3 ⸬ 2 ⸬ 1 ⸬ □) 2 ≡ 3 ⸬ 2 ⸬ 2 ⸬ □;
assert ⊢ incr_nth (3 ⸬ 2 ⸬ 1 ⸬ □) 5 ≡ 3 ⸬ 2 ⸬ 1 ⸬ 0 ⸬ 0 ⸬ 1 ⸬ □;

// zip 

symbol zip [a b] : 𝕃 a → 𝕃 b → 𝕃 (a × b);

rule zip □ □ ↪ □
with zip □ _ ↪ □
with zip _ □ ↪ □
with zip ($x ⸬ $l) ($y ⸬ $m) ↪ $x & $y ⸬ zip $l $m;

symbol unzip1 [a b] : 𝕃 (a × b) → 𝕃 a;

rule unzip1 □  ↪ □
with unzip1 ($x & _ ⸬ $l) ↪ $x ⸬ unzip1 $l;

symbol unzip2 [a b] : 𝕃 (a × b) → 𝕃 b;

rule unzip2 □ ↪ □
with unzip2 (_ & $y ⸬ $l) ↪ $y ⸬ unzip2 $l;

assert ⊢ unzip1 ((3 & 5) ⸬ (6 & 4) ⸬ (7 & 2) ⸬ (8 & 1) ⸬ □) ≡ 3 ⸬ 6 ⸬ 7 ⸬ 8 ⸬ □;
assert ⊢ unzip2 ((3 & 5) ⸬ (6 & 4) ⸬ (7 & 2) ⸬ (8 & 1) ⸬ □) ≡ 5 ⸬ 4 ⸬ 2 ⸬ 1 ⸬ □;

symbol all2 [a b] : (τ a → τ b → 𝔹) → 𝕃 a → 𝕃 b → 𝔹;

rule all2 _ □ □ ↪ true
with all2 $p ($x ⸬ $l) ($y ⸬ $m) ↪ ($p $x $y) and (all2 $p $l $m);

opaque symbol unzip1_zip [a b] (la:𝕃 a) (lb:𝕃 b) :
  π (size la ≤ size lb) → π (unzip1 (zip la lb) = la) ≔
begin
  assume a b; induction
  { reflexivity; }
  { assume ea la h; induction
    { assume i; apply ⊥ₑ i; }
    { assume eb lb i j; apply feq (λ l, ea ⸬ l) (h lb j); }
  }
end;

opaque symbol unzip2_zip [a b] (la:𝕃 a) (lb:𝕃 b) :
  π (size lb ≤ size la) → π (unzip2 (zip la lb) = lb) ≔
begin
  assume a b; induction
  { assume lb h;
     have t:π (size lb = 0) { apply ≤0 (size lb) h; };
     symmetry; apply size0nil lb t; }
  { assume ea la h; induction
    { reflexivity; }
    { assume eb lb i j; apply feq (λ l, eb ⸬ l) (h lb j); }
  }
end;

opaque symbol size1_zip [a b] (la:𝕃 a) (lb:𝕃 b) :
  π (size la ≤ size lb) → π (size (zip la lb) = size la) ≔
begin
  assume a b; induction
  { reflexivity; }
  { assume ea la h; induction
    { assume i; apply ⊥ₑ i; }
    { assume eb lb i j; apply feq (+1) (h lb j); }
  }
end;

opaque symbol size2_zip [a b] (la:𝕃 a) (lb:𝕃 b) :
  π (size lb ≤ size la) → π (size (zip la lb) = size lb) ≔
begin
  assume a b; induction
  { assume lb h; symmetry; apply ≤0 (size lb) h; }
  { assume ea la h; induction
    { reflexivity; }
    { assume eb lb i j; apply feq (+1) (h lb j); }
  }
end;

opaque symbol size_zip [a b] (la:𝕃 a) (lb:𝕃 b) :
  π (size (zip la lb) = min (size la) (size lb)) ≔
begin
  assume a b; induction
  { reflexivity }
  { assume ea la h; induction
    { reflexivity; }
    { assume eb lb i; simplify; apply feq (+1) (h lb); }
  }
end;

// double induction

opaque symbol seq_ind2 [a b] (p:𝕃 a → 𝕃 b → Prop) :
  π (p □ □) →
  (Π la lb ea eb, π(size la = size lb) → π(p la lb) → π(p (ea ⸬ la) (eb ⸬ lb)))
  → Π la lb, π(size la = size lb) → π(p la lb) ≔
begin
  assume a b p p0 pH; induction
  { induction
    { assume h; apply p0; }
    { assume eb lb h1 h2; apply ⊥ₑ; apply s≠0 [size lb]; symmetry; apply h2 }
  }
  { assume ea la h; induction
    { assume i; apply ⊥ₑ (s≠0 i); }
    { assume eb lb i j;
      have t:π (size la = size lb) { apply +1_inj j; };
      apply pH la lb ea eb t (h lb t); }
  }
end;

opaque symbol zip_cat [a b] (la sa:𝕃 a) (lb sb:𝕃 b) :
  π (size la = size lb) → π (zip (la ++ sa) (lb ++ sb) = zip la lb ++ zip sa sb) ≔
begin
  assume a b la sa lb sb h;
  apply @seq_ind2 a b (λ l1 l2, (zip (l1 ++ sa) (l2 ++ sb) = zip l1 l2 ++ zip sa sb)) _ _ la lb h {
    reflexivity;
  } {
    assume l1 l2 e1 e2 h1 h2; simplify; apply feq (λ l, e1 & e2 ⸬ l) h2; 
  };
end;

opaque symbol nth_zip [a b] (x:τ a) (y:τ b) la lb i: π(size la = size lb) →
  π(nth (x & y) (zip la lb) i = nth x la i & nth y lb i) ≔
begin
  assume a b x y; induction
  { assume lb i h;
    have t: π (lb = □) { apply size0nil lb; symmetry; apply h; };
    rewrite t; reflexivity; }
  { assume ea la h; induction
    { assume i j; apply ⊥ₑ (s≠0 j); }
    { assume eb lb k; induction
      { assume m; reflexivity; }
      { assume i m n; refine h lb i _; apply +1_inj n; }
    }
  }
end;

opaque symbol rev_zip [a b] (la:𝕃 a) (lb:𝕃 b) :
  π (size la = size lb) → π (rev (zip la lb) = zip (rev la) (rev lb)) ≔
begin
  assume a b la lb h;
  apply seq_ind2 (λ l1 l2, rev (zip l1 l2) = zip (rev l1) (rev l2)) _ _ la lb h {
    reflexivity;
  } {
    assume l1 l2 e1 e2 i j; simplify;
    have i': π(size(rev l1) = size(rev l2))
      { rewrite @size_rev; rewrite @size_rev; apply i}; 
    rewrite zip_cat (rev l1) (e1 ⸬ □) (rev l2) (e2 ⸬ □) i';
    rewrite left j; reflexivity;
  };
end;
