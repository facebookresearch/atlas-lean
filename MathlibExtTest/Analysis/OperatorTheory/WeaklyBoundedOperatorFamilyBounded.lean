/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.OperatorTheory.WeaklyBoundedOperatorFamilyBounded

namespace MathlibExt.Analysis.OperatorTheory.WeaklyBoundedOperatorFamilyBoundedWanted

-- The operator set may be empty.
example : ∃ M : ℝ, ∀ A ∈ (∅ : Set (ℝ →L[ℝ] ℝ)), ‖A‖ ≤ M := by
  apply exists_bound_opNorm_of_forall_inner_bounded ℝ ℝ ℝ
  exact fun _ _ ↦ ⟨0, fun _ hA ↦ hA.elim⟩

-- A norm-unbounded sequence of complex operators has one unbounded matrix coefficient.
example {H K : Type*} [NormedAddCommGroup H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ H] [InnerProductSpace ℂ K] [CompleteSpace H] [CompleteSpace K]
    (T : ℕ → H →L[ℂ] K) (hT : ∀ M : ℝ, ∃ n, M < ‖T n‖) :
    ∃ f : H, ∃ g : K, ∀ C : ℝ, ∃ n, C < ‖inner ℂ (T n f) g‖ := by
  by_contra! h
  obtain ⟨M, hM⟩ := exists_bound_opNorm_of_forall_inner_bounded ℂ H K (Set.range T) (by
    intro f g
    obtain ⟨C, hC⟩ := h f g
    exact ⟨C, Set.forall_mem_range.mpr hC⟩)
  obtain ⟨n, hn⟩ := hT M
  exact hn.not_ge (hM (T n) (Set.mem_range_self n))

end MathlibExt.Analysis.OperatorTheory.WeaklyBoundedOperatorFamilyBoundedWanted
