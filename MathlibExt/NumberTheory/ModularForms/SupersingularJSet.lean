/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_ModularCurve_EichlerMass.lean`,
`Definitions/Def_ModularCurve_GenusNumerics.lean`,
`Definitions/Def_ModularCurve_SupersingularLocus.lean` and
`Definitions/Def_ModularCurve_SupersingularModuli.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import MathlibExt.AlgebraicGeometry.EllipticCurve.Supersingular
public import MathlibExt.NumberTheory.ArithmeticFunction.DedekindPsi
import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.AlgebraicGeometry.EllipticCurve.NormalForms

/-!
# Supersingular `j`-invariants, short Weierstrass models and the Eichler mass

This file defines the supersingular `j`-invariants in characteristic `p` (`ModularCurve.ssJSet`,
through `WeierstrassCurve.Affine.IsSupersingular`) and shows that in characteristic `2` they are
the image of the table `ssSetTwo = {0}` (`ModularCurve.ssJSet_two`). The tables `ssSetThree`,
`ssSetFive`, `ssSetSeven`, `ssSetEleven` and `ssSetThirteen`, and the polynomials `∏ (X - j)` over
them, are numerical data: the supersingular `j`-invariants in characteristics `3`, `5`, `7`, `11`
and `13` as tabulated by Birch and Kuyk. The file also defines the automorphism weights, the short
Weierstrass models with their affine point counts, the Eichler mass and the supersingular count
formula.

Scope: every declaration that reads `ZMod p` as the field with `p` elements takes
`[Fact p.Prime]`. These declarations are defined for the prime fields `ZMod p` only; prime-power
fields `𝔽_q` with `q = p ^ n`, `n > 1`, are out of scope (`ZMod (p ^ n)` is not a field for
`n > 1`). The levels `N` of `nuTwo`, `nuThree`, `eichlerMass` and `ssCountFormula` are arbitrary
natural numbers, with `ZMod N` read as a ring.

## References

* B. J. Birch and W. Kuyk (eds.), *Modular functions of one variable IV*, Lecture Notes in
  Mathematics 476, Springer, 1975, pp. 142–144: the table of supersingular `j`-invariants that
  `ssSetTwo`, ..., `ssSetThirteen` record.
* J. H. Silverman, *The Arithmetic of Elliptic Curves*, 2nd ed., Graduate Texts in Mathematics
  106, Springer, 2009, Theorem III.10.1: the orders of the automorphism groups behind
  `autWeight`.
* J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer, 2021,
  Theorem 25.3.18 (Eichler's mass formula for Eichler orders), Theorem 30.1.5 (Eichler's class
  number formula), and Corollary 42.3.7, paragraph 42.3.8 and Remark 42.3.10 (the Deuring
  correspondence, also with a cyclic subgroup of order prime to `p`): the mass and count formulas
  behind `eichlerMass` and `ssCountFormula`.
-/

@[expose] public section

attribute [local instance] Classical.propDecidable

namespace ModularCurve

/-- The number of roots of `x ^ 2 + 1` in `ZMod N`. -/
public noncomputable def nuTwo (N : ℕ) : ℕ := Nat.card {x : ZMod N // x ^ 2 + 1 = 0}

/-- The number of roots of `x ^ 2 + x + 1` in `ZMod N`. -/
public noncomputable def nuThree (N : ℕ) : ℕ := Nat.card {x : ZMod N // x ^ 2 + x + 1 = 0}

/-- The Eichler mass of level `N` in prime characteristic `p`, defined as `(p - 1) * ψ(N) / 12`,
where `ψ` is the Dedekind psi function `ArithmeticFunction.dedekindPsi`. The hypothesis
`[Fact p.Prime]` makes `ZMod p` the field with `p` elements (`ZMod (p ^ n)` is not a field for
`n > 1`).

Eichler's mass formula with the Deuring correspondence (J. Voight, *Quaternion Algebras*,
Theorem 25.3.18 and Remark 42.3.10) states that, for a level `N ≥ 1` not divisible by `p`, it
equals the sum of `2 / |Aut(E, C)|` over the supersingular points `(E, C)` of `X₀(N)` over an
algebraic closure of `ZMod p`. Here `C` is a cyclic subgroup of `E` of order `N`, and `Aut(E, C)`
is the group of the automorphisms of `E` that map `C` onto itself, not the group `Aut(E)` of all
automorphisms of `E` that `autWeight` uses; the two agree at level `1`. -/
public noncomputable def eichlerMass (N p : ℕ) [Fact p.Prime] : ℚ :=
  ((p : ℚ) - 1) * (ArithmeticFunction.dedekindPsi N : ℚ) / 12

/-- The supersingular count formula of level `N` in prime characteristic `p`, defined as
`eichlerMass N p + (2 - ν₂(p)) * ν₂(N) / 4 + (2 - ν₃(p)) * ν₃(N) / 3`, where `ν₂ = nuTwo` and
`ν₃ = nuThree` count the roots of `x ^ 2 + 1` and of `x ^ 2 + x + 1` in `ZMod N` and in the field
`ZMod p`. The hypothesis `[Fact p.Prime]` makes `ZMod p` the field with `p` elements
(`ZMod (p ^ n)` is not a field for `n > 1`).

For a level `N ≥ 1` not divisible by `p`, Eichler's class number formula (J. Voight, *Quaternion
Algebras*, Theorem 30.1.5) gives this value as the class number of an Eichler order of level `N`
in the quaternion algebra over `ℚ` ramified at `p` and `∞`, which by the Deuring correspondence
(Remark 42.3.10 there) is the number of supersingular points `(E, C)` of `X₀(N)` over an algebraic
closure of `ZMod p`, counted without weights. -/
public noncomputable def ssCountFormula (N p : ℕ) [Fact p.Prime] : ℚ :=
  eichlerMass N p + (2 - (nuTwo p : ℚ)) * (nuTwo N : ℚ) / 4
    + (2 - (nuThree p : ℚ)) * (nuThree N : ℚ) / 3

public theorem eichlerMass_one (p : ℕ) [Fact p.Prime] : eichlerMass 1 p = ((p : ℚ) - 1) / 12 := by
  simp [eichlerMass]

public theorem ssCountFormula_eq (N p : ℕ) [Fact p.Prime] :
    ssCountFormula N p = eichlerMass N p + (2 - (nuTwo p : ℚ)) * (nuTwo N : ℚ) / 4
      + (2 - (nuThree p : ℚ)) * (nuThree N : ℚ) / 3 :=
  rfl

/-- The automorphism weight of `j : ZMod p` in prime characteristic `p`, defined by cases: `12` in
characteristic `2` at `j = 0`, `6` in characteristic `3` at `j = 0`, `3` at `j = 0` and `2` at
`j = 1728` in characteristic greater than `3`, and `1` otherwise. The hypothesis `[Fact p.Prime]`
makes `ZMod p` the field with `p` elements (`ZMod (p ^ n)` is not a field for `n > 1`).

These values are half the order of `Aut(E)`, the group of all automorphisms of an elliptic curve
`E` over an algebraic closure of `ZMod p` with `j`-invariant `j`, that is, the order of
`Aut(E) / {±1}`: `|Aut(E)|` is `24`, `12`, `6`, `4` and `2` in the five cases (J. H. Silverman,
*The Arithmetic of Elliptic Curves*, 2nd ed., Theorem III.10.1). So for `j` in `ZMod p` the
weight `2 / |Aut(E)|` is `1 / autWeight p j`. A supersingular `j` outside `ZMod p` is neither `0`
nor `1728`, so its weight `2 / |Aut(E)|` is `1`. The level-one mass formula
`∑ 1 / |Aut(E)| = (p - 1) / 24` (J. Voight, *Quaternion Algebras*, (42.3.9)) reads
`∑ 2 / |Aut(E)| = eichlerMass 1 p`, the sum running over the supersingular `j` in an algebraic
closure of `ZMod p`. For `p ≤ 13` all of them lie in `ZMod p`, so the sum is that of
`1 / autWeight p j` over them. At a level `N > 1` not divisible by `p`, the weights of
`eichlerMass N p` use the automorphisms `Aut(E, C)` of `E` that preserve a cyclic subgroup `C` of
order `N` instead. -/
public def autWeight (p : ℕ) [Fact p.Prime] (j : ZMod p) : ℕ :=
  if p = 2 then (if j = 0 then 12 else 1)
  else if p = 3 then (if j = 0 then 6 else 1)
  else if j = 0 then 3 else if j = 1728 then 2 else 1

public theorem autWeight_two_zero : autWeight 2 0 = 12 := by simp [autWeight]
public theorem autWeight_three_zero : autWeight 3 0 = 6 := by simp [autWeight]

public theorem autWeight_of_ne {p : ℕ} [Fact p.Prime] (h2 : p ≠ 2) (h3 : p ≠ 3) {j : ZMod p}
    (h0 : j ≠ 0) (h1728 : j ≠ 1728) : autWeight p j = 1 := by
  simp [autWeight, h2, h3, h0, h1728]

-- Only the characteristic-`2` table is proved to enumerate `ssJSet` (`ssJSet_two` below); the
-- other tables, and the polynomials over them, are numerical data from the cited table.

/-- The supersingular `j`-invariants in characteristic `2`, as tabulated by B. J. Birch and
W. Kuyk (eds.), *Modular functions of one variable IV*, Lecture Notes in Mathematics 476,
pp. 142–144: `ssJSet 2` is the image of this set in an algebraic closure of `ZMod 2`
(`ssJSet_two`). -/
public def ssSetTwo : Finset (ZMod 2) := {0}
/-- Numerical data: the supersingular `j`-invariants in characteristic `3` as tabulated by
B. J. Birch and W. Kuyk (eds.), *Modular functions of one variable IV*, Lecture Notes in
Mathematics 476, pp. 142–144, as elements of `ZMod 3` (where `1728 = 0`). -/
public def ssSetThree : Finset (ZMod 3) := {0}
/-- Numerical data: the supersingular `j`-invariants in characteristic `5` as tabulated by
B. J. Birch and W. Kuyk (eds.), *Modular functions of one variable IV*, Lecture Notes in
Mathematics 476, pp. 142–144, as elements of `ZMod 5`. -/
public def ssSetFive : Finset (ZMod 5) := {0}
/-- Numerical data: the supersingular `j`-invariants in characteristic `7` as tabulated by
B. J. Birch and W. Kuyk (eds.), *Modular functions of one variable IV*, Lecture Notes in
Mathematics 476, pp. 142–144, as elements of `ZMod 7`. -/
public def ssSetSeven : Finset (ZMod 7) := {1728}
/-- Numerical data: the supersingular `j`-invariants in characteristic `11` as tabulated by
B. J. Birch and W. Kuyk (eds.), *Modular functions of one variable IV*, Lecture Notes in
Mathematics 476, pp. 142–144, as elements of `ZMod 11`. -/
public def ssSetEleven : Finset (ZMod 11) := {0, 1728}
/-- Numerical data: the supersingular `j`-invariants in characteristic `13` as tabulated by
B. J. Birch and W. Kuyk (eds.), *Modular functions of one variable IV*, Lecture Notes in
Mathematics 476, pp. 142–144, as elements of `ZMod 13`. -/
public def ssSetThirteen : Finset (ZMod 13) := {5}

/-- The product of `X - j` over the supersingular `j`-invariants `ssSetTwo` in
characteristic `2`. -/
public noncomputable def ssPolyTwo : Polynomial (ZMod 2) :=
  ∏ a ∈ ssSetTwo, (Polynomial.X - Polynomial.C a)
/-- Numerical data: the product of `X - j` over the tabulated `j` in `ssSetThree`. -/
public noncomputable def ssPolyThree : Polynomial (ZMod 3) :=
  ∏ a ∈ ssSetThree, (Polynomial.X - Polynomial.C a)
/-- Numerical data: the product of `X - j` over the tabulated `j` in `ssSetFive`. -/
public noncomputable def ssPolyFive : Polynomial (ZMod 5) :=
  ∏ a ∈ ssSetFive, (Polynomial.X - Polynomial.C a)
/-- Numerical data: the product of `X - j` over the tabulated `j` in `ssSetSeven`. -/
public noncomputable def ssPolySeven : Polynomial (ZMod 7) :=
  ∏ a ∈ ssSetSeven, (Polynomial.X - Polynomial.C a)
/-- Numerical data: the product of `X - j` over the tabulated `j` in `ssSetEleven`. -/
public noncomputable def ssPolyEleven : Polynomial (ZMod 11) :=
  ∏ a ∈ ssSetEleven, (Polynomial.X - Polynomial.C a)
/-- Numerical data: the product of `X - j` over the tabulated `j` in `ssSetThirteen`. -/
public noncomputable def ssPolyThirteen : Polynomial (ZMod 13) :=
  ∏ a ∈ ssSetThirteen, (Polynomial.X - Polynomial.C a)

public theorem ssPolyTwo_eq : ssPolyTwo = Polynomial.X - Polynomial.C 0 := by
  simp [ssPolyTwo, ssSetTwo]
public theorem card_ssSetEleven : ssSetEleven.card = 2 := by decide

public theorem ssPolyEleven_monic : ssPolyEleven.Monic := by
  rw [ssPolyEleven]
  exact Polynomial.monic_prod_of_monic _ _ fun a _ => Polynomial.monic_X_sub_C a

/-- The coefficient `A` of the short Weierstrass equation `y ^ 2 = x ^ 3 + A * x + B` of the
model curve `ssModel p j` attached to `j : ZMod p`, with `B = ssModelB p j`. The hypothesis
`[Fact p.Prime]` makes `ZMod p` the field with `p` elements (`ZMod (p ^ n)` is not a field for
`n > 1`). -/
public def ssModelA (p : ℕ) [Fact p.Prime] (j : ZMod p) : ZMod p :=
  if j = 0 then 0 else if j = 1728 then 1 else 3 * j * (1728 - j)

/-- The coefficient `B` of the short Weierstrass equation `y ^ 2 = x ^ 3 + A * x + B` of the
model curve `ssModel p j` attached to `j : ZMod p`, with `A = ssModelA p j`. The hypothesis
`[Fact p.Prime]` makes `ZMod p` the field with `p` elements (`ZMod (p ^ n)` is not a field for
`n > 1`). -/
public def ssModelB (p : ℕ) [Fact p.Prime] (j : ZMod p) : ZMod p :=
  if j = 0 then 1 else if j = 1728 then 0 else 2 * j * (1728 - j) ^ 2

public theorem ssModelA_zero (p : ℕ) [Fact p.Prime] : ssModelA p 0 = 0 := by simp [ssModelA]
public theorem ssModelB_zero (p : ℕ) [Fact p.Prime] : ssModelB p 0 = 1 := by simp [ssModelB]

/-- The short Weierstrass curve `y ^ 2 = x ^ 3 + ssModelA p j * x + ssModelB p j` over the prime
field `ZMod p` attached to `j : ZMod p`. For `p > 3` it is an elliptic curve with `j`-invariant `j`
(`ssModel_j`). It is not a model in characteristic `2` or `3`, where its discriminant vanishes
for every `j`: in characteristic `2` the discriminant of every short Weierstrass equation does,
and in characteristic `3` the coefficient `ssModelA 3 j` is `0`. In every characteristic,
`WeierstrassCurve.ofJ j` is an elliptic curve with `j`-invariant `j`. The hypothesis
`[Fact p.Prime]` makes `ZMod p` the field with `p` elements (`ZMod (p ^ n)` is not a field for
`n > 1`). -/
public def ssModel (p : ℕ) [Fact p.Prime] (j : ZMod p) : WeierstrassCurve (ZMod p) :=
  ⟨0, 0, 0, ssModelA p j, ssModelB p j⟩

private theorem two_ne_zero_and_three_ne_zero (p : ℕ) [Fact (3 < p)] :
    (2 : ZMod p) ≠ 0 ∧ (3 : ZMod p) ≠ 0 := by
  have hp : 3 < p := Fact.out
  have key (n : ℕ) (hn : n ≠ 0) (hnp : n ≤ 3) : (n : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro h
    have := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h
    omega
  exact ⟨by exact_mod_cast key 2 (by norm_num) (by norm_num),
    by exact_mod_cast key 3 (by norm_num) (by norm_num)⟩

public instance (p : ℕ) [Fact p.Prime] [Fact (3 < p)] (j : ZMod p) :
    (ssModel p j).IsElliptic := by
  have : (ssModel p j).IsShortNF := ⟨rfl, rfl, rfl⟩
  obtain ⟨h2, h3⟩ := two_ne_zero_and_three_ne_zero p
  refine ⟨isUnit_iff_ne_zero.mpr ?_⟩
  rw [WeierstrassCurve.Δ_of_isShortNF]
  simp only [ssModel, ssModelA, ssModelB]
  split_ifs with h0 h1728
  · have e : (-16 * (4 * 0 ^ 3 + 27 * 1 ^ 2) : ZMod p) = -(2 ^ 4 * 3 ^ 3) := by ring
    rw [e]
    exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3))
  · have e : (-16 * (4 * 1 ^ 3 + 27 * 0 ^ 2) : ZMod p) = -(2 ^ 6) := by ring
    rw [e]
    exact neg_ne_zero.mpr (pow_ne_zero _ h2)
  · have e : (-16 * (4 * (3 * j * (1728 - j)) ^ 3 + 27 * (2 * j * (1728 - j) ^ 2) ^ 2) : ZMod p) =
        -(2 ^ 12 * 3 ^ 6) * j ^ 2 * (1728 - j) ^ 3 := by ring
    rw [e]
    refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ h0)) (pow_ne_zero _ ?_)
    · exact neg_ne_zero.mpr (mul_ne_zero (pow_ne_zero _ h2) (pow_ne_zero _ h3))
    · exact sub_ne_zero.mpr (Ne.symm h1728)

public theorem ssModel_j (p : ℕ) [Fact p.Prime] [Fact (3 < p)] (j : ZMod p) :
    (ssModel p j).j = j := by
  have : (ssModel p j).IsShortNF := ⟨rfl, rfl, rfl⟩
  obtain ⟨h2, h3⟩ := two_ne_zero_and_three_ne_zero p
  rw [WeierstrassCurve.j_of_isShortNF]
  simp only [ssModel, ssModelA, ssModelB]
  split_ifs with h0 h1728
  · subst h0
    simp
  · subst h1728
    have e : (4 * 1 ^ 3 + 27 * 0 ^ 2 : ZMod p) = 2 ^ 2 := by ring
    rw [e, div_eq_iff (pow_ne_zero _ h2)]
    ring
  · have e : (4 * (3 * j * (1728 - j)) ^ 3 + 27 * (2 * j * (1728 - j) ^ 2) ^ 2 : ZMod p) =
        2 ^ 8 * 3 ^ 6 * j ^ 2 * (1728 - j) ^ 3 := by ring
    rw [e, div_eq_iff (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ h2)
      (pow_ne_zero _ h3)) (pow_ne_zero _ h0)) (pow_ne_zero _ (sub_ne_zero.mpr (Ne.symm h1728))))]
    ring

/-- The number of affine points on `y ^ 2 = x ^ 3 + A * x + B` over the prime field `ZMod p`.
The hypothesis `[Fact p.Prime]` makes `ZMod p` the field with `p` elements (`ZMod (p ^ n)` is not
a field for `n > 1`). -/
public def affinePointCount (p : ℕ) [Fact p.Prime] (A B : ZMod p) : ℕ :=
  (Finset.univ.filter fun P : ZMod p × ZMod p => P.2 ^ 2 = P.1 ^ 3 + A * P.1 + B).card

public theorem affinePointCount_le (p : ℕ) [Fact p.Prime] (A B : ZMod p) :
    affinePointCount p A B ≤ p ^ 2 := by
  refine (Finset.card_filter_le _ _).trans_eq ?_
  simp [pow_two]

/-- The supersingular `j`-invariants in characteristic `p`, for a prime `p`: the `j` in an
algebraic closure of `ZMod p` such that every elliptic curve over that algebraic closure with
`j`-invariant `j` is supersingular in the sense of `WeierstrassCurve.Affine.IsSupersingular`, that
is, has no nonzero geometric point killed by `p`. Every `j` is the `j`-invariant of an elliptic
curve, for example `WeierstrassCurve.ofJ j`, so the condition is not vacuous. -/
public def ssJSet (p : ℕ) [Fact p.Prime] : Set (AlgebraicClosure (ZMod p)) :=
  {j | ∀ (W : WeierstrassCurve (AlgebraicClosure (ZMod p))) [W.IsElliptic], W.j = j →
    W.toAffine.IsSupersingular}

public theorem mem_ssJSet_iff {p : ℕ} [Fact p.Prime] {j : AlgebraicClosure (ZMod p)} :
    j ∈ ssJSet p ↔ ∀ (W : WeierstrassCurve (AlgebraicClosure (ZMod p))) [W.IsElliptic],
      W.j = j → W.toAffine.IsSupersingular :=
  Iff.rfl

section CharacteristicTwo

attribute [local instance] Classical.decEq

open WeierstrassCurve

/-- In characteristic `2`, every elliptic curve with `j = 0` is supersingular: `j = 0` forces
`a₁ = 0`, the discriminant is then `a₃ ^ 4`, and a point equal to its negative would force
`a₃ = 0`. -/
private theorem zero_mem_ssJSet_two : (0 : AlgebraicClosure (ZMod 2)) ∈ ssJSet 2 := by
  refine mem_ssJSet_iff.mpr fun W _ hj P hP => ?_
  have ha₁ : W.a₁ = 0 := W.j_eq_zero_iff_of_char_two.mp hj
  have ha₃ : W.a₃ ≠ 0 := by
    intro h
    have hΔ := W.isUnit_Δ
    rw [W.Δ_of_char_two, ha₁, h] at hΔ
    simp at hΔ
  rcases P with _ | ⟨x, y, hxy⟩
  · rfl
  · exfalso
    rw [two_nsmul] at hP
    by_cases hy : y = W.toAffine.negY x y
    · apply ha₃
      rw [Affine.negY, ha₁] at hy
      linear_combination hy - y * (CharTwo.two_eq_zero : (2 : AlgebraicClosure (ZMod 2)) = 0)
    · rw [Affine.Point.add_self_of_Y_ne hy] at hP
      exact Affine.Point.some_ne_zero _ hP

/-- In characteristic `2`, a nonzero `j` is not supersingular: the curve `WeierstrassCurve.ofJ j`
has the nonzero point `(0, y)` with `y ^ 2 = a₆`, which equals its negative. -/
private theorem eq_zero_of_mem_ssJSet_two {j : AlgebraicClosure (ZMod 2)} (hj : j ∈ ssJSet 2) :
    j = 0 := by
  by_contra h0
  have h1728 : j ≠ 1728 := by
    have : (1728 : AlgebraicClosure (ZMod 2)) = 0 := by
      linear_combination 864 * (CharTwo.two_eq_zero : (2 : AlgebraicClosure (ZMod 2)) = 0)
    rwa [this]
  obtain ⟨y, hy⟩ := IsAlgClosed.exists_pow_nat_eq (-(j - 1728) ^ 5) two_pos
  have hW := ofJ_ne_0_ne_1728 j h0 h1728
  have heq : (ofJ j).toAffine.Equation 0 y := by
    rw [Affine.equation_iff', hW]
    simp [ofJNe0Or1728, hy]
  have hns := Affine.equation_iff_nonsingular.mp heq
  have h2 : 2 • (Affine.Point.some 0 y hns) = 0 := by
    rw [two_nsmul]
    refine Affine.Point.add_self_of_Y_eq ?_
    rw [Affine.negY, hW]
    simp [ofJNe0Or1728, CharTwo.neg_eq]
  exact Affine.Point.some_ne_zero hns (mem_ssJSet_iff.mp hj (ofJ j) (ofJ_j j) _ h2)

/-- **Supersingular `j`-invariants in characteristic two.** In characteristic `2` the supersingular
`j`-invariants are the image of the table `ssSetTwo = {0}`: every elliptic curve with `j = 0` over
an algebraic closure of `ZMod 2` is supersingular, and for `j ≠ 0` the curve
`WeierstrassCurve.ofJ j` is not. -/
public theorem ssJSet_two :
    ssJSet 2 = algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2)) '' ssSetTwo := by
  ext j
  simp only [ssSetTwo, Finset.coe_singleton, Set.image_singleton, map_zero,
    Set.mem_singleton_iff]
  exact ⟨eq_zero_of_mem_ssJSet_two, fun h => h ▸ zero_mem_ssJSet_two⟩

end CharacteristicTwo

end ModularCurve
