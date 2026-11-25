/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Advantage
public import Mathlib.Algebra.Group.TypeTags.Basic
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
# Bilinear groups: interface, toy model, BDH and SXDH games

A bilinear-group interface over explicit exponent isomorphisms
(`BilinearGroupData`): the groups are cyclic of order `q` with a pairing whose
exponents multiply in `ZMod q`. Bimultiplicativity, the power law and trivial
kernels are derived, not assumed.

`BilinearGroupData` packages algebraic witness data: the exponent isomorphisms
`exp1`, `exp2` and `expT` expose decoders through their `symm` fields, so every
instance is insecure against unrestricted function/`PMF` adversaries that decode
exponents with `exp.symm`. The games below measure only adversaries that do not
decode; a real hardness assumption needs an admissibility model excluding
decoding adversaries.

The toy exponent model (`toyModel`) elaborates the interface with all groups
equal to `Multiplicative (ZMod q)`, serving as an elaboration witness.

Security games use the framework advantage vocabulary (`winProb`, `advantage`):
the bilinear Diffie-Hellman game (`bdhGame`, `bdhAdvantage`) and the two
Diffie-Hellman games behind the pointwise advantage-bound predicate
(`sxdhAdvBound`), which bounds fixed distinguishers only and is not the SXDH
hardness assumption. A decoding adversary wins the BDH game with probability
one (`toy_bdhAdvantage_eq_one`), exhibiting the insecurity above.
-/

@[expose] public section

namespace Cslib.Crypto.Framework

/-- A bilinear-group interface: cyclic groups of order `q` with named exponent
isomorphisms and a pairing whose exponents multiply in `ZMod q`. -/
structure BilinearGroupData where
  /-- The group order. -/
  q : ℕ
  /-- The order exceeds one, so `(1 : ZMod q) ≠ 0`. -/
  hq : 1 < q
  /-- The first source group. -/
  G1 : Type*
  /-- The second source group. -/
  G2 : Type*
  /-- The target group. -/
  GT : Type*
  [commGroup1 : CommGroup G1]
  [commGroup2 : CommGroup G2]
  [commGroupT : CommGroup GT]
  /-- The exponent isomorphism for `G1`. -/
  exp1 : Multiplicative (ZMod q) ≃* G1
  /-- The exponent isomorphism for `G2`. -/
  exp2 : Multiplicative (ZMod q) ≃* G2
  /-- The exponent isomorphism for `GT`. -/
  expT : Multiplicative (ZMod q) ≃* GT
  /-- The pairing. -/
  e : G1 → G2 → GT
  /-- Compatibility: on exponents, the pairing is multiplication in `ZMod q`. -/
  compat : ∀ a b : ZMod q,
    e (exp1 (Multiplicative.ofAdd a)) (exp2 (Multiplicative.ofAdd b)) =
      expT (Multiplicative.ofAdd (a * b))

attribute [instance] BilinearGroupData.commGroup1 BilinearGroupData.commGroup2
  BilinearGroupData.commGroupT

namespace BilinearGroupData

/-- The order hypothesis as a `Fact` instance. -/
instance fact_one_lt (B : BilinearGroupData) : Fact (1 < B.q) := ⟨B.hq⟩

/-- The order is nonzero. -/
instance neZero (B : BilinearGroupData) : NeZero B.q :=
  ⟨by have h := B.hq; omega⟩

/-- The generator of `G1`: the image of the wrapped residue `1`. -/
def g1 (B : BilinearGroupData) : B.G1 := B.exp1 (Multiplicative.ofAdd 1)

/-- The generator of `G2`. -/
def g2 (B : BilinearGroupData) : B.G2 := B.exp2 (Multiplicative.ofAdd 1)

/-- The generator of `GT`. -/
def gT (B : BilinearGroupData) : B.GT := B.expT (Multiplicative.ofAdd 1)

/-- Since `1 < B.q`, `1 ≠ 0` in `ZMod B.q`. -/
theorem one_ne_zero (B : BilinearGroupData) : (1 : ZMod B.q) ≠ 0 := by
  intro h
  have hq1 : B.q = 1 := ZMod.one_eq_zero_iff.mp h
  have hlt := B.hq
  omega

/-- The target generator is nontrivial. -/
theorem gT_ne_one (B : BilinearGroupData) : B.gT ≠ 1 := by
  intro h
  have h' : B.expT (Multiplicative.ofAdd (1 : ZMod B.q)) = 1 := h
  have h2 : B.expT (Multiplicative.ofAdd (1 : ZMod B.q)) =
      B.expT (Multiplicative.ofAdd (0 : ZMod B.q)) := by
    rw [h', ofAdd_zero, map_one]
  have h3 := B.expT.injective h2
  have h4 : (1 : ZMod B.q) = 0 := by simpa using congrArg Multiplicative.toAdd h3
  exact B.one_ne_zero h4

/-- The pairing of the generators is the target generator. -/
theorem e_g1_g2 (B : BilinearGroupData) : B.e B.g1 B.g2 = B.gT := by
  have h : B.e (B.exp1 (Multiplicative.ofAdd (1 : ZMod B.q)))
      (B.exp2 (Multiplicative.ofAdd (1 : ZMod B.q))) =
      B.expT (Multiplicative.ofAdd (1 : ZMod B.q)) := by
    rw [B.compat, mul_one]
  exact h

/-- Generator pairing nondegeneracy. -/
theorem e_g1_g2_ne_one (B : BilinearGroupData) : B.e B.g1 B.g2 ≠ 1 := by
  rw [B.e_g1_g2]
  exact B.gT_ne_one

/-- The pairing is multiplicative in its first argument. -/
theorem map_mul_left (B : BilinearGroupData) (x₁ x₂ : B.G1) (y : B.G2) :
    B.e (x₁ * x₂) y = B.e x₁ y * B.e x₂ y := by
  obtain ⟨a₁, rfl⟩ := B.exp1.surjective x₁
  obtain ⟨a₂, rfl⟩ := B.exp1.surjective x₂
  obtain ⟨b, rfl⟩ := B.exp2.surjective y
  rw [← ofAdd_toAdd a₁, ← ofAdd_toAdd a₂, ← ofAdd_toAdd b]
  have hmul : B.exp1 (Multiplicative.ofAdd a₁.toAdd) *
      B.exp1 (Multiplicative.ofAdd a₂.toAdd) =
      B.exp1 (Multiplicative.ofAdd a₁.toAdd * Multiplicative.ofAdd a₂.toAdd) :=
    (map_mul _ _ _).symm
  rw [hmul, ← ofAdd_add, B.compat, B.compat, B.compat]
  have hmulT : B.expT (Multiplicative.ofAdd (a₁.toAdd * b.toAdd)) *
      B.expT (Multiplicative.ofAdd (a₂.toAdd * b.toAdd)) =
      B.expT (Multiplicative.ofAdd (a₁.toAdd * b.toAdd) *
        Multiplicative.ofAdd (a₂.toAdd * b.toAdd)) := (map_mul _ _ _).symm
  rw [hmulT, ← ofAdd_add]
  have hring : (a₁.toAdd + a₂.toAdd) * b.toAdd =
      a₁.toAdd * b.toAdd + a₂.toAdd * b.toAdd := add_mul _ _ _
  rw [hring]

/-- The pairing is multiplicative in its second argument. -/
theorem map_mul_right (B : BilinearGroupData) (x : B.G1) (y₁ y₂ : B.G2) :
    B.e x (y₁ * y₂) = B.e x y₁ * B.e x y₂ := by
  obtain ⟨a, rfl⟩ := B.exp1.surjective x
  obtain ⟨b₁, rfl⟩ := B.exp2.surjective y₁
  obtain ⟨b₂, rfl⟩ := B.exp2.surjective y₂
  rw [← ofAdd_toAdd a, ← ofAdd_toAdd b₁, ← ofAdd_toAdd b₂]
  have hmul : B.exp2 (Multiplicative.ofAdd b₁.toAdd) *
      B.exp2 (Multiplicative.ofAdd b₂.toAdd) =
      B.exp2 (Multiplicative.ofAdd b₁.toAdd * Multiplicative.ofAdd b₂.toAdd) :=
    (map_mul _ _ _).symm
  rw [hmul, ← ofAdd_add, B.compat, B.compat, B.compat]
  have hmulT : B.expT (Multiplicative.ofAdd (a.toAdd * b₁.toAdd)) *
      B.expT (Multiplicative.ofAdd (a.toAdd * b₂.toAdd)) =
      B.expT (Multiplicative.ofAdd (a.toAdd * b₁.toAdd) *
        Multiplicative.ofAdd (a.toAdd * b₂.toAdd)) := (map_mul _ _ _).symm
  rw [hmulT, ← ofAdd_add]
  have hring : a.toAdd * (b₁.toAdd + b₂.toAdd) =
      a.toAdd * b₁.toAdd + a.toAdd * b₂.toAdd := mul_add _ _ _
  rw [hring]

/-- The pairing kills the identity on the left. -/
theorem e_one_left (B : BilinearGroupData) (y : B.G2) : B.e 1 y = 1 := by
  obtain ⟨b, rfl⟩ := B.exp2.surjective y
  have h1 : (1 : B.G1) = B.exp1 (Multiplicative.ofAdd (0 : ZMod B.q)) := by
    rw [ofAdd_zero]
    exact (map_one _).symm
  rw [h1, ← ofAdd_toAdd b, B.compat, zero_mul, ofAdd_zero, map_one]

/-- The pairing kills the identity on the right. -/
theorem e_one_right (B : BilinearGroupData) (x : B.G1) : B.e x 1 = 1 := by
  obtain ⟨a, rfl⟩ := B.exp1.surjective x
  have h1 : (1 : B.G2) = B.exp2 (Multiplicative.ofAdd (0 : ZMod B.q)) := by
    rw [ofAdd_zero]
    exact (map_one _).symm
  rw [h1, ← ofAdd_toAdd a, B.compat, mul_zero, ofAdd_zero, map_one]

/-- The left kernel of the pairing is trivial. -/
theorem eq_one_of_forall_e_eq_one_left (B : BilinearGroupData) (x : B.G1)
    (h : ∀ y : B.G2, B.e x y = 1) : x = 1 := by
  obtain ⟨a, rfl⟩ := B.exp1.surjective x
  rw [← ofAdd_toAdd a] at h ⊢
  have h2 := h (B.exp2 (Multiplicative.ofAdd (1 : ZMod B.q)))
  rw [B.compat, mul_one] at h2
  have h3 : B.expT (Multiplicative.ofAdd a.toAdd) =
      B.expT (Multiplicative.ofAdd (0 : ZMod B.q)) := by
    rw [h2, ofAdd_zero, map_one]
  have h4 := B.expT.injective h3
  have h5 : a.toAdd = 0 := by simpa using congrArg Multiplicative.toAdd h4
  rw [h5, ofAdd_zero, map_one]

/-- The right kernel of the pairing is trivial. -/
theorem eq_one_of_forall_e_eq_one_right (B : BilinearGroupData) (y : B.G2)
    (h : ∀ x : B.G1, B.e x y = 1) : y = 1 := by
  obtain ⟨b, rfl⟩ := B.exp2.surjective y
  rw [← ofAdd_toAdd b] at h ⊢
  have h2 := h (B.exp1 (Multiplicative.ofAdd (1 : ZMod B.q)))
  rw [B.compat, one_mul] at h2
  have h3 : B.expT (Multiplicative.ofAdd b.toAdd) =
      B.expT (Multiplicative.ofAdd (0 : ZMod B.q)) := by
    rw [h2, ofAdd_zero, map_one]
  have h4 := B.expT.injective h3
  have h5 : b.toAdd = 0 := by simpa using congrArg Multiplicative.toAdd h4
  rw [h5, ofAdd_zero, map_one]

/-- Power law for the pairing. -/
theorem e_pow (B : BilinearGroupData) (x : B.G1) (y : B.G2) (m n : ℕ) :
    B.e (x ^ m) (y ^ n) = (B.e x y) ^ (m * n) := by
  have hleft : ∀ m : ℕ, ∀ x : B.G1, ∀ y : B.G2, B.e (x ^ m) y = (B.e x y) ^ m := by
    intro m
    induction m with
    | zero => intro x y; rw [pow_zero, e_one_left, pow_zero]
    | succ m ih => intro x y; rw [pow_succ, map_mul_left, ih, pow_succ]
  have hright : ∀ n : ℕ, ∀ z : B.G1, ∀ y : B.G2, B.e z (y ^ n) = (B.e z y) ^ n := by
    intro n
    induction n with
    | zero => intro z y; rw [pow_zero, e_one_right, pow_zero]
    | succ n ih => intro z y; rw [pow_succ, map_mul_right, ih, pow_succ]
  rw [hright, hleft, ← pow_mul]

/-- The toy exponent model: all three groups are `Multiplicative (ZMod q)` with
identity exponent maps and exponent multiplication as the pairing. It serves
as an elaboration witness. -/
def toyModel (q : ℕ) (hq : 1 < q) : BilinearGroupData where
  q := q
  hq := hq
  G1 := Multiplicative (ZMod q)
  G2 := Multiplicative (ZMod q)
  GT := Multiplicative (ZMod q)
  commGroup1 := inferInstance
  commGroup2 := inferInstance
  commGroupT := inferInstance
  exp1 := MulEquiv.refl _
  exp2 := MulEquiv.refl _
  expT := MulEquiv.refl _
  e := fun a b => Multiplicative.ofAdd (a.toAdd * b.toAdd)
  compat := fun _ _ => rfl

open Classical in
/-- The BDH win experiment at fixed exponents: run the randomized adversary and
test whether its output equals `gT ^ (a*b*c)`. -/
noncomputable def bdhWin (B : BilinearGroupData) (A : B.G1 → B.G1 → B.G2 → PMF B.GT)
    (a b c : ZMod B.q) : PMF Bool :=
  (A (B.exp1 (Multiplicative.ofAdd a)) (B.exp1 (Multiplicative.ofAdd b))
    (B.exp2 (Multiplicative.ofAdd c))).map fun w =>
    if w = B.expT (Multiplicative.ofAdd (a * b * c)) then true else false

/-- The BDH game: sample `a`, `b`, `c` uniformly and run the adversary,
sampling its coins via `PMF.bind`. -/
noncomputable def bdhGame (B : BilinearGroupData) (A : B.G1 → B.G1 → B.G2 → PMF B.GT) :
    PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (ZMod B.q)).bind fun a =>
    (Cslib.Probability.PMF.uniformOfFintype (ZMod B.q)).bind fun b =>
      (Cslib.Probability.PMF.uniformOfFintype (ZMod B.q)).bind fun c =>
        B.bdhWin A a b c

/-- The BDH advantage: the winning probability of the BDH game. -/
noncomputable def bdhAdvantage (B : BilinearGroupData)
    (A : B.G1 → B.G1 → B.G2 → PMF B.GT) : ℝ :=
  winProb (B.bdhGame A)

/-- An adversary that always wins induces the constantly-`true` game. -/
theorem bdhGame_eq_pure_true (B : BilinearGroupData) (A : B.G1 → B.G1 → B.G2 → PMF B.GT)
    (h : ∀ a b c, B.bdhWin A a b c = PMF.pure true) :
    B.bdhGame A = PMF.pure true := by
  unfold bdhGame
  simp only [h, PMF.bind_const]

/-- Decoding adversary for BDH: recovers the exponents and outputs the answer
as a `PMF` via `PMF.pure`. In the toy model this reads `Multiplicative.toAdd`;
in any instance the same attack decodes with `exp.symm`, exhibiting the
insecurity of every instance against unrestricted adversaries. -/
noncomputable def toyBdhAdversary (q : ℕ) : Multiplicative (ZMod q) →
    Multiplicative (ZMod q) → Multiplicative (ZMod q) → PMF (Multiplicative (ZMod q)) :=
  fun x y z => PMF.pure (Multiplicative.ofAdd (x.toAdd * y.toAdd * z.toAdd))

/-- The decoding adversary always wins the toy BDH game. -/
theorem toy_bdhWin (q : ℕ) (hq : 1 < q) (a b c : ZMod q) :
    (toyModel q hq).bdhWin (toyBdhAdversary q) a b c = PMF.pure true := by
  have hcond : (toyBdhAdversary q) ((toyModel q hq).exp1 (Multiplicative.ofAdd a))
        ((toyModel q hq).exp1 (Multiplicative.ofAdd b))
        ((toyModel q hq).exp2 (Multiplicative.ofAdd c)) =
        PMF.pure ((toyModel q hq).expT (Multiplicative.ofAdd (a * b * c))) := rfl
  unfold bdhWin
  rw [hcond, PMF.pure_map]
  exact congrArg PMF.pure (ite_eq_left rfl)

/-- In the toy model, the decoding adversary wins the BDH game with probability one,
exhibiting the insecurity of the interface against decoding adversaries. -/
theorem toy_bdhAdvantage_eq_one (q : ℕ) (hq : 1 < q) :
    (toyModel q hq).bdhAdvantage (toyBdhAdversary q) = 1 := by
  have h := bdhGame_eq_pure_true (toyModel q hq) (toyBdhAdversary q) (toy_bdhWin q hq)
  unfold bdhAdvantage
  rw [h]
  simp [winProb_pure]

/-- The DDH game in `G1` against the real distribution, sampling the
randomized distinguisher's coins via `PMF.bind`. -/
noncomputable def ddh1RealGame (B : BilinearGroupData)
    (D : B.G1 → B.G1 → B.G1 → PMF Bool) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (ZMod B.q)).bind fun a =>
    (Cslib.Probability.PMF.uniformOfFintype (ZMod B.q)).bind fun b =>
      D (B.exp1 (Multiplicative.ofAdd a)) (B.exp1 (Multiplicative.ofAdd b))
        (B.exp1 (Multiplicative.ofAdd (a * b)))

/-- The DDH game in `G1` against the random distribution. -/
noncomputable def ddh1RandomGame (B : BilinearGroupData)
    (D : B.G1 → B.G1 → B.G1 → PMF Bool) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (ZMod B.q)).bind fun a =>
    (Cslib.Probability.PMF.uniformOfFintype (ZMod B.q)).bind fun b =>
      (Cslib.Probability.PMF.uniformOfFintype (ZMod B.q)).bind fun c =>
        D (B.exp1 (Multiplicative.ofAdd a)) (B.exp1 (Multiplicative.ofAdd b))
          (B.exp1 (Multiplicative.ofAdd c))

/-- The DDH advantage in `G1`. -/
noncomputable def ddh1Advantage (B : BilinearGroupData)
    (D : B.G1 → B.G1 → B.G1 → PMF Bool) : ℝ :=
  advantage (B.ddh1RealGame D) (B.ddh1RandomGame D)

/-- The DDH game in `G2` against the real distribution, sampling the
randomized distinguisher's coins via `PMF.bind`. -/
noncomputable def ddh2RealGame (B : BilinearGroupData)
    (D : B.G2 → B.G2 → B.G2 → PMF Bool) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (ZMod B.q)).bind fun a =>
    (Cslib.Probability.PMF.uniformOfFintype (ZMod B.q)).bind fun b =>
      D (B.exp2 (Multiplicative.ofAdd a)) (B.exp2 (Multiplicative.ofAdd b))
        (B.exp2 (Multiplicative.ofAdd (a * b)))

/-- The DDH game in `G2` against the random distribution. -/
noncomputable def ddh2RandomGame (B : BilinearGroupData)
    (D : B.G2 → B.G2 → B.G2 → PMF Bool) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (ZMod B.q)).bind fun a =>
    (Cslib.Probability.PMF.uniformOfFintype (ZMod B.q)).bind fun b =>
      (Cslib.Probability.PMF.uniformOfFintype (ZMod B.q)).bind fun c =>
        D (B.exp2 (Multiplicative.ofAdd a)) (B.exp2 (Multiplicative.ofAdd b))
          (B.exp2 (Multiplicative.ofAdd c))

/-- The DDH advantage in `G2`. -/
noncomputable def ddh2Advantage (B : BilinearGroupData)
    (D : B.G2 → B.G2 → B.G2 → PMF Bool) : ℝ :=
  advantage (B.ddh2RealGame D) (B.ddh2RandomGame D)

/-- A pointwise advantage bound for fixed distinguishers in `G1` and `G2`.
This is a fixed-instance advantage bound for the given distinguishers, NOT the
SXDH hardness assumption, which needs admissible adversary classes because
exponent witnesses expose decoders. -/
def sxdhAdvBound (B : BilinearGroupData) (D₁ : B.G1 → B.G1 → B.G1 → PMF Bool)
    (D₂ : B.G2 → B.G2 → B.G2 → PMF Bool) (ε : ℝ) : Prop :=
  B.ddh1Advantage D₁ ≤ ε ∧ B.ddh2Advantage D₂ ≤ ε

end BilinearGroupData

end Cslib.Crypto.Framework
