/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicGeometry.TropicalVariety

open MathlibExt.AlgebraicGeometry.TropicalVarietyWanted

namespace MathlibExtTest.AlgebraicGeometry.TropicalVariety

variable {K : Type*} [Field K] (v : AddValuation K (WithTop ℝ))
  (hv : ∃ x : K, x ≠ 0 ∧ v x ≠ 0)

-- A nonzero monomial has empty tropical hypersurface, including in zero variables.
example [IsAlgClosed K] {n : ℕ} (u : Fin n → ℤ) {c : K} (hc : c ≠ 0) :
    closure (valuationsOfZeros v (AddMonoidAlgebra.single u c)) = ∅ := by
  rw [← tropicalHypersurface_eq_closure_valuationsOfZeros v hv _ (by simpa using hc)]
  ext w
  simp [tropicalHypersurface, AddMonoidAlgebra.coeff_single, Finsupp.support_single _ hc]

-- The Laurent binomial X⁻¹ - a has the single torus root a⁻¹, of valuation -v(a).
private noncomputable def binomial (a : Kˣ) : LaurentPoly K 1 :=
  AddMonoidAlgebra.single (fun _ ↦ -1) 1 + AddMonoidAlgebra.single 0 (-(a : K))

private lemma eval_binomial (a : Kˣ) (y : Fin 1 → Kˣ) :
    evalTorus (binomial a) y = ((y 0 : K)⁻¹ - a) := by
  classical
  simp [binomial, evalTorus, AddMonoidAlgebra.coeff_single, Finsupp.sum_add_index,
    sub_eq_add_neg, add_mul, -Finsupp.single_neg, -AddMonoidAlgebra.single_neg]

example [IsAlgClosed K] (a : Kˣ) {r : ℝ} (ha : v (a : K) = r) :
    tropicalHypersurface v (binomial a) = {fun _ ↦ -r} := by
  classical
  have hne : (fun _ : Fin 1 ↦ (-1 : ℤ)) ≠ 0 := by
    intro h
    have := congrFun h 0
    norm_num at this
  have hf : binomial a ≠ 0 := by
    intro h
    have he := congrArg (fun f : LaurentPoly K 1 ↦ f.coeff (fun _ ↦ -1)) h
    simp [binomial, AddMonoidAlgebra.coeff_single, hne.symm] at he
  rw [tropicalHypersurface_eq_closure_valuationsOfZeros v hv _ hf]
  suffices valuationsOfZeros v (binomial a) = {fun _ ↦ -r} by simp [this]
  ext w
  constructor
  · rintro ⟨y, hy, hw⟩
    have hinv : (y 0 : K)⁻¹ = (a : K) := by simpa [eval_binomial, sub_eq_zero] using hy
    have hy0 : (y 0 : K) = (a : K)⁻¹ := inv_eq_iff_eq_inv.mp hinv
    apply funext
    intro i
    rw [Subsingleton.elim i 0]
    exact WithTop.coe_injective ((hw 0).symm.trans (by simp [hy0, ha]))
  · rintro rfl
    exact ⟨fun _ ↦ a⁻¹, by simp [eval_binomial], by simp [ha]⟩

end MathlibExtTest.AlgebraicGeometry.TropicalVariety
