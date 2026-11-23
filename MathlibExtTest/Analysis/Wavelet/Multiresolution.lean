/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Wavelet.Multiresolution

/-!
# Tests for multiresolution approximations

The axioms exclude the two degenerate sequences: all subspaces trivial (the union is not dense)
and all subspaces equal to `L²(ℝ)` (the intersection is not `{0}`).
-/

open MeasureTheory Set
open MathlibExt.Analysis.Wavelet.Multiresolution

namespace MathlibExtTest.Analysis.Wavelet.Multiresolution

/-- The indicator of `[0, 1]` is a nonzero element of `L²(ℝ)`. -/
theorem exists_ne_zero : ∃ f : Lp ℂ 2 (volume : Measure ℝ), f ≠ 0 := by
  refine ⟨indicatorConstLp 2 (measurableSet_Icc (a := (0 : ℝ)) (b := 1)) (by simp) (1 : ℂ),
    fun h => ?_⟩
  have := congrArg norm h
  rw [norm_indicatorConstLp (by norm_num) (by norm_num)] at this
  simp at this

/-- The constant sequence `L²(ℝ)` is not a multiresolution approximation. -/
example : ¬ IsMultiresolutionApproximation fun _ => ⊤ := by
  rintro ⟨-, -, -, hinter, -⟩
  obtain ⟨f, hf⟩ := exists_ne_zero
  exact hf (hinter f fun _ => Submodule.mem_top)

/-- The constant sequence `{0}` is not a multiresolution approximation. -/
example : ¬ IsMultiresolutionApproximation fun _ => ⊥ := by
  rintro ⟨-, -, hdense, -⟩
  obtain ⟨f, hf⟩ := exists_ne_zero
  have hU : (⋃ _ : ℤ, ((⊥ : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))) :
      Set (Lp ℂ 2 (volume : Measure ℝ)))) = {0} := by
    simp
  rw [hU] at hdense
  have := hdense.closure_eq
  rw [closure_singleton] at this
  exact hf (this ▸ mem_univ f : f ∈ ({0} : Set _))

end MathlibExtTest.Analysis.Wavelet.Multiresolution
