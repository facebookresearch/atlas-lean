/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.MvPolynomial.TranslationSupport

/-!
# Tests of polynomial translation on monomial exponents

The shift `(1, 2)` introduces a missing linear term in a bilinear polynomial. A separate
quadratic has three different nonzero coefficients of the same degree.
-/

open MvPolynomial

private abbrev E := Bool →₀ ℕ
private abbrev P := MvPolynomial Bool ℤ
private noncomputable abbrev x : E := Finsupp.single false 1
private noncomputable abbrev y : E := Finsupp.single true 1
private def a (b : Bool) : ℤ := if b then 2 else 1
private noncomputable abbrev tr : P →ₐ[ℤ] P := aeval (fun b => X b + C (a b))

private theorem expand_xy : tr (X false * X true) =
    (X false * X true + C 2 * X false + X true + C 2 : P) := by
  simp [tr, a]
  ring

private noncomputable def allowed : Set E := {0, x, x + y}

private theorem xy_monomial : (X false * X true : P) = monomial (x + y) 1 := by
  rw [X, X, monomial_mul_monomial, one_mul]

-- The unshifted polynomial belongs to the incomplete class, but its translate does not.
example : ↑(X false * X true : P).support ⊆ allowed ∧
    ¬ ↑(tr (X false * X true)).support ⊆ allowed := by
  classical
  have hy : y ∉ allowed := by
    simp [allowed, x, y, Finsupp.ext_iff, Bool.forall_bool]
  constructor
  · rw [xy_monomial]
    simp [support_monomial, allowed]
  · intro h
    apply hy (h ?_)
    change y ∈ (tr (X false * X true)).support
    rw [mem_support_iff, expand_xy, xy_monomial]
    simp only [AddMonoidAlgebra.coeff_add, Finsupp.add_apply, coeff_C_mul]
    simp [coeff_X, x, y, Finsupp.ext_iff, Bool.forall_bool]

-- A square of the same total degree as `xy` is absent both before and after an arbitrary shift.
example (v : Bool → ℤ) :
    (aeval (fun i => X i + C (v i)) (X false * X true : P)).coeff (Finsupp.single false 2) = 0 := by
  rw [xy_monomial, coeff_aeval_X_add_C_of_totalDegree_le]
  · simp [x, y, Finsupp.ext_iff, Bool.forall_bool]
  · exact (totalDegree_monomial_le _ _).trans
      (show (x + y).degree ≤ (Finsupp.single false 2).degree by simp [x, y])

-- In the complete class of divisors of `xy`, every target fit has a preimage in the class.
example (v : Bool → ℤ) : ∃ p : P, ↑p.support ⊆ Set.Iic (x + y) ∧
    aeval (fun i => X i + C (v i)) p = X false * X true := by
  apply (bijOn_aeval_X_add_C_of_isLowerSet v (IsLowerSet.Iic (x + y))).surjOn
  rw [xy_monomial]
  change ↑(monomial (x + y) (1 : ℤ)).support ⊆ Set.Iic (x + y)
  simp [support_monomial]

private noncomputable def quadratic : P :=
  monomial (Finsupp.single false 2) 1 + monomial (x + y) 3 + monomial (Finsupp.single true 2) (-2)

-- Three numerical coefficients simultaneously, for every integer shift, not just shift zero.
example (v : Bool → ℤ) : let q := aeval (fun i => X i + C (v i)) quadratic
    q.coeff (Finsupp.single false 2) = 1 ∧ q.coeff (x + y) = 3 ∧
    q.coeff (Finsupp.single true 2) = -2 := by
  dsimp only
  have hb : quadratic.totalDegree ≤ 2 := by
    apply (totalDegree_add _ _).trans
    apply max_le
    · apply (totalDegree_add _ _).trans
      apply max_le
      · exact (totalDegree_monomial_le _ _).trans (by simp)
      · exact (totalDegree_monomial_le _ _).trans (show (x + y).degree ≤ 2 by simp [x, y])
    · exact (totalDegree_monomial_le _ _).trans (by simp)
  have keep (d : E) (hd : d.degree = 2) :=
    coeff_aeval_X_add_C_of_totalDegree_le quadratic v d (hd ▸ hb)
  rw [keep _ (by simp), keep _ (by simp [x, y]), keep _ (by simp)]
  simp [quadratic, x, y, Finsupp.ext_iff, Bool.forall_bool]

-- The bound also covers zero coefficients at exponents above the actual degree.
example (a : Bool → ℤ) : (aeval (fun i => X i + C (a i)) (C 5 : P)).coeff x = 0 := by
  rw [coeff_aeval_X_add_C_of_totalDegree_le _ _ _ (by rw [totalDegree_C]; exact Nat.zero_le _)]
  exact coeff_C_of_ne_zero (by simp [x]) _

-- No nonzero-polynomial assumption, even when its top degree is zero.
example (a : Empty → ℕ) : homogeneousComponent 0 (aeval (fun i => X i + C (a i))
    (0 : MvPolynomial Empty ℕ)) = homogeneousComponent 0 (0 : MvPolynomial Empty ℕ) :=
  homogeneousComponent_aeval_X_add_C _ _ (by simp)
