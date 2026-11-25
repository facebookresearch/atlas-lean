/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.AlgebraicGeometry.EllipticCurve.ModelsWithJ
import Mathlib.Tactic.NormNum.Prime
import MathlibExt.NumberTheory.ModularForms.SupersingularJSet

namespace ModularCurve

open WeierstrassCurve

private instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
private instance : Fact (3 < 5) := ⟨by norm_num⟩
private instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
private instance : Fact (3 < 7) := ⟨by norm_num⟩
private instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩
private instance : Fact (3 < 11) := ⟨by norm_num⟩
private instance : Fact (Nat.Prime 13) := ⟨by norm_num⟩
private instance : Fact (3 < 13) := ⟨by norm_num⟩

section Locus

attribute [local instance] Classical.decEq

/-- Consumer: on a curve whose `j`-invariant lies in `ssJSet p`, every geometric point killed by a
positive power of `p` is zero. -/
private theorem exactSource {p : ℕ} [Fact p.Prime] {j : AlgebraicClosure (ZMod p)}
    (h : j ∈ ssJSet p) (W : WeierstrassCurve (AlgebraicClosure (ZMod p))) [W.IsElliptic]
    (hW : W.j = j) {r : ℕ} (hr : 0 < r) {P : W.toAffine.Point} (hP : (p ^ r) • P = 0) :
    P = 0 :=
  Affine.IsSupersingular.pow_torsion _ (mem_ssJSet_iff.mp h W hW) hr hP

/-- Membership constrains an actual curve: `WeierstrassCurve.ofJ j` has `j`-invariant `j`. -/
example (p : ℕ) [Fact p.Prime] (j : AlgebraicClosure (ZMod p)) (hj : j ∈ ssJSet p) :
    (ofJ j).toAffine.IsSupersingular :=
  mem_ssJSet_iff.mp hj _ (ofJ_j j)

/-- The set is only defined in prime characteristic: at `p = 1` there is no instance
`Fact (Nat.Prime 1)`. -/
example : True := by
  fail_if_success have := ssJSet 1
  trivial

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

/-- In characteristic `2` the supersingular `j`-invariants are the image of `ssSetTwo`. -/
private theorem ssJSet_two :
    ssJSet 2 = algebraMap (ZMod 2) (AlgebraicClosure (ZMod 2)) '' ssSetTwo := by
  ext j
  simp only [ssSetTwo, Finset.coe_singleton, Set.image_singleton, map_zero,
    Set.mem_singleton_iff]
  exact ⟨eq_zero_of_mem_ssJSet_two, fun h => h ▸ zero_mem_ssJSet_two⟩

end Locus

/-- Consumer with the source's binders, at a prime characteristic `p`. -/
example (N p : ℕ) [Fact p.Prime] :
    eichlerMass N p = ((p : ℚ) - 1) * (ArithmeticFunction.dedekindPsi N : ℚ) / 12 :=
  rfl

example (N p : ℕ) [Fact p.Prime] :
    ssCountFormula N p = eichlerMass N p + (2 - (nuTwo p : ℚ)) * (nuTwo N : ℚ) / 4
      + (2 - (nuThree p : ℚ)) * (nuThree N : ℚ) / 3 :=
  ssCountFormula_eq N p

/-! The prime-power field `𝔽_4` is out of scope: `ZMod 4` is not a field, and the declarations
that read `ZMod p` as the field with `p` elements need `Fact (Nat.Prime p)`. -/

example : True := by
  fail_if_success have := ssCountFormula 1 4
  trivial

example : True := by
  fail_if_success have := eichlerMass 1 4
  trivial

example : True := by
  fail_if_success have := autWeight 4 0
  trivial

example : True := by
  fail_if_success have := ssModel 4 0
  trivial

example : eichlerMass 1 13 = 1 := by norm_num [eichlerMass_one]

/-- The Eichler mass uses `ArithmeticFunction.dedekindPsi`: `ψ(2) = 3`. -/
example : eichlerMass 2 13 = 3 := by
  norm_num [eichlerMass, ArithmeticFunction.dedekindPsi_prime Nat.prime_two]

/-! At level one the count formula gives the number of supersingular `j`-invariants listed by
`ssSetTwo`, ..., `ssSetThirteen`. -/

private theorem nuTwo_one : nuTwo 1 = 1 := by rw [nuTwo, Nat.card_eq_fintype_card]; decide
private theorem nuThree_one : nuThree 1 = 1 := by rw [nuThree, Nat.card_eq_fintype_card]; decide
private theorem nuTwo_two : nuTwo 2 = 1 := by rw [nuTwo, Nat.card_eq_fintype_card]; decide
private theorem nuThree_two : nuThree 2 = 0 := by rw [nuThree, Nat.card_eq_fintype_card]; decide
private theorem nuTwo_three : nuTwo 3 = 0 := by rw [nuTwo, Nat.card_eq_fintype_card]; decide
private theorem nuThree_three : nuThree 3 = 1 := by
  rw [nuThree, Nat.card_eq_fintype_card]; decide
private theorem nuTwo_five : nuTwo 5 = 2 := by rw [nuTwo, Nat.card_eq_fintype_card]; decide
private theorem nuThree_five : nuThree 5 = 0 := by rw [nuThree, Nat.card_eq_fintype_card]; decide
private theorem nuTwo_seven : nuTwo 7 = 0 := by rw [nuTwo, Nat.card_eq_fintype_card]; decide
private theorem nuThree_seven : nuThree 7 = 2 := by
  rw [nuThree, Nat.card_eq_fintype_card]; decide
private theorem nuTwo_eleven : nuTwo 11 = 0 := by rw [nuTwo, Nat.card_eq_fintype_card]; decide
private theorem nuThree_eleven : nuThree 11 = 0 := by
  rw [nuThree, Nat.card_eq_fintype_card]; decide
private theorem nuTwo_thirteen : nuTwo 13 = 2 := by rw [nuTwo, Nat.card_eq_fintype_card]; decide
private theorem nuThree_thirteen : nuThree 13 = 2 := by
  rw [nuThree, Nat.card_eq_fintype_card]; decide

example : ssCountFormula 1 2 = ssSetTwo.card := by
  rw [ssCountFormula_eq, eichlerMass_one, nuTwo_one, nuThree_one, nuTwo_two, nuThree_two]
  norm_num [ssSetTwo]

example : ssCountFormula 1 3 = ssSetThree.card := by
  rw [ssCountFormula_eq, eichlerMass_one, nuTwo_one, nuThree_one, nuTwo_three, nuThree_three]
  norm_num [ssSetThree]

example : ssCountFormula 1 5 = ssSetFive.card := by
  rw [ssCountFormula_eq, eichlerMass_one, nuTwo_one, nuThree_one, nuTwo_five, nuThree_five]
  norm_num [ssSetFive]

example : ssCountFormula 1 7 = ssSetSeven.card := by
  rw [ssCountFormula_eq, eichlerMass_one, nuTwo_one, nuThree_one, nuTwo_seven, nuThree_seven]
  norm_num [ssSetSeven]

example : ssCountFormula 1 11 = ssSetEleven.card := by
  rw [ssCountFormula_eq, eichlerMass_one, nuTwo_one, nuThree_one, nuTwo_eleven, nuThree_eleven,
    card_ssSetEleven]
  norm_num

example : ssCountFormula 1 13 = ssSetThirteen.card := by
  rw [ssCountFormula_eq, eichlerMass_one, nuTwo_one, nuThree_one, nuTwo_thirteen,
    nuThree_thirteen]
  norm_num [ssSetThirteen]

example : autWeight 2 0 = 12 := autWeight_two_zero
example : autWeight 3 0 = 6 := autWeight_three_zero
example : autWeight 5 0 = 3 := by simp [autWeight]
example : autWeight 7 1728 = 2 := by decide
example (j : ZMod 5) (h0 : j ≠ 0) (h : j ≠ 1728) : autWeight 5 j = 1 :=
  autWeight_of_ne (by norm_num) (by norm_num) h0 h

/-! The weights `1 / autWeight q j = 2 / |Aut E|` of the listed supersingular `j` add up to
`eichlerMass 1 q = (q - 1) / 12`, twice the classical mass `∑ 1 / |Aut E| = (q - 1) / 24`. -/

example : ∑ j ∈ ssSetTwo, (1 : ℚ) / autWeight 2 j = eichlerMass 1 2 := by
  norm_num [ssSetTwo, autWeight, eichlerMass_one]

example : ∑ j ∈ ssSetThree, (1 : ℚ) / autWeight 3 j = eichlerMass 1 3 := by
  norm_num [ssSetThree, autWeight, eichlerMass_one]

example : ∑ j ∈ ssSetFive, (1 : ℚ) / autWeight 5 j = eichlerMass 1 5 := by
  norm_num [ssSetFive, autWeight, eichlerMass_one]

example : ∑ j ∈ ssSetSeven, (1 : ℚ) / autWeight 7 j = eichlerMass 1 7 := by
  have h : (1728 : ZMod 7) ≠ 0 := by decide
  norm_num [ssSetSeven, autWeight, eichlerMass_one, h]

example : ∑ j ∈ ssSetEleven, (1 : ℚ) / autWeight 11 j = eichlerMass 1 11 := by
  have h : (1728 : ZMod 11) ≠ 0 := by decide
  rw [ssSetEleven, Finset.sum_insert (by decide), Finset.sum_singleton]
  norm_num [autWeight, eichlerMass_one, h]

example : ∑ j ∈ ssSetThirteen, (1 : ℚ) / autWeight 13 j = eichlerMass 1 13 := by
  have h0 : (5 : ZMod 13) ≠ 0 := by decide
  have h : (5 : ZMod 13) ≠ 1728 := by decide
  norm_num [ssSetThirteen, autWeight, eichlerMass_one, h0, h]

example : ssPolyTwo = Polynomial.X - Polynomial.C 0 := ssPolyTwo_eq
example : ssPolyTwo = Polynomial.X := by rw [ssPolyTwo_eq, map_zero, sub_zero]
example : ssSetEleven.card = 2 := card_ssSetEleven
example : ssPolyEleven.Monic := ssPolyEleven_monic
example : ssModelA 5 0 = 0 := ssModelA_zero 5
example : ssModelB 5 0 = 1 := ssModelB_zero 5

/-! For a prime `q > 3` the models of the listed supersingular `j` are elliptic curves with that
`j`-invariant. -/

example : (ssModel 5 0).j = 0 := ssModel_j 5 0
example : (ssModel 7 1728).j = 1728 := ssModel_j 7 1728
example : (ssModel 11 0).j = 0 := ssModel_j 11 0
example : (ssModel 11 1728).j = 1728 := ssModel_j 11 1728
example : (ssModel 13 5).j = 5 := ssModel_j 13 5

/-- In characteristic `5` the model is an elliptic curve at every `j`. -/
example (j : ZMod 5) : (ssModel 5 j).IsElliptic := inferInstance

/-- A direct computation: the model is nonsingular at every `j` in characteristic `5`. -/
example : ∀ j : ZMod 5, (ssModel 5 j).Δ ≠ 0 := by decide

/-- The model of `j = 5` in characteristic `13` is nonsingular: its discriminant is a unit. -/
example : IsUnit (ssModel 13 5).Δ := (ssModel 13 5).isUnit_Δ

/-- A direct computation of the same discriminant. -/
example : (ssModel 13 5).Δ ≠ 0 := by decide

/-- Every point of the model of `j = 5` in characteristic `13` is nonsingular. -/
example (x y : ZMod 13) (h : (ssModel 13 5).toAffine.Equation x y) :
    (ssModel 13 5).toAffine.Nonsingular x y :=
  Affine.equation_iff_nonsingular.mp h

/-! Boundary: in characteristic `2` and `3` the coefficients give singular curves. -/

example : ∀ j : ZMod 2, (ssModel 2 j).Δ = 0 := by decide
example : ∀ j : ZMod 3, (ssModel 3 j).Δ = 0 := by decide

/-- At `q = 2`, `j = 0` the equation is `y ^ 2 = x ^ 3 + 1`, singular at `(0, 1)`. -/
example : (ssModel 2 0).toAffine.Equation 0 1 ∧ ¬ (ssModel 2 0).toAffine.Nonsingular 0 1 := by
  rw [Affine.nonsingular_iff', Affine.equation_iff']
  decide

/-- At `q = 3`, `j = 0` the equation is `y ^ 2 = x ^ 3 + 1`, singular at `(-1, 0)`. -/
example : (ssModel 3 0).toAffine.Equation (-1) 0 ∧ ¬ (ssModel 3 0).toAffine.Nonsingular (-1) 0 := by
  rw [Affine.nonsingular_iff', Affine.equation_iff']
  decide

/-- There Mathlib's generalized Weierstrass model `WeierstrassCurve.ofJ` is nonsingular. -/
example : (ofJ (0 : ZMod 2)).Δ ≠ 0 := by decide

example : (ofJ (0 : ZMod 3)).Δ ≠ 0 := by decide

example (A B : ZMod 5) : affinePointCount 5 A B ≤ 25 := by
  have h := affinePointCount_le 5 A B
  norm_num at h ⊢
  exact h

/-! A supersingular elliptic curve over `ZMod p`, `p ≥ 5`, has `p + 1` points, so the model at a
listed supersingular `j` has `p` affine points; at an ordinary `j` the count differs. -/

example : affinePointCount 5 (ssModelA 5 0) (ssModelB 5 0) = 5 := by decide
example : affinePointCount 7 (ssModelA 7 1728) (ssModelB 7 1728) = 7 := by decide
example : affinePointCount 11 (ssModelA 11 0) (ssModelB 11 0) = 11 := by decide
example : affinePointCount 11 (ssModelA 11 1728) (ssModelB 11 1728) = 11 := by decide
example : affinePointCount 13 (ssModelA 13 5) (ssModelB 13 5) = 13 := by decide

/-- `j = 1728` is ordinary in characteristic `5`. -/
example : affinePointCount 5 (ssModelA 5 1728) (ssModelB 5 1728) = 3 := by decide

end ModularCurve
