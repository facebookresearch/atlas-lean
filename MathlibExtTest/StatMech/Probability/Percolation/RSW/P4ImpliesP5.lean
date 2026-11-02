/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.RSW.P4ImpliesP5
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.RSW.P4ImpliesP5`

* `rp4_P4` holds for the constant sequence `1` (it does not decay exponentially).
* `rp4_expDecay_of_stretched` for `a n = exp (-n)`.
* `rp4_p4_implies_p5` for `a = 1` and the constant model `ν = lam = 1/2`, with the dichotomy
  discharged by its `P5b` branch.
-/

@[expose] public section

open StatMech StatMech.Lattice StatMech.RSW StatMech.RSW.Box

namespace MathlibExtTest.StatMech.Probability.Percolation.RSW.P4ImpliesP5

/-- The constant sequence `1` does not decay exponentially. -/
theorem one_P4 : P4ImpliesP5.rp4_P4 (fun _ => (1 : ℝ)) := by
  rintro ⟨c, hc, C, hC, h⟩
  have ht : Filter.Tendsto (fun n : ℕ => C * Real.exp (-c * n)) Filter.atTop (nhds 0) := by
    have h1 : Filter.Tendsto (fun n : ℕ => c * (n : ℝ)) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop hc
    have h2 := (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul C
    simpa [Function.comp_def, neg_mul] using h2
  have hle : (1 : ℝ) ≤ 0 := ge_of_tendsto' ht h
  norm_num at hle

theorem exp_neg_submult (m n : ℕ) :
    Real.exp (-((m + n : ℕ) : ℝ)) ≤ Real.exp (-(m : ℝ)) * Real.exp (-(n : ℝ)) := by
  rw [← Real.exp_add]; push_cast; ring_nf; exact le_rfl

example : P4ImpliesP5.rp4_ExpDecay (fun n : ℕ => Real.exp (-(n : ℝ))) :=
  P4ImpliesP5.rp4_expDecay_of_stretched _ (fun _ => (Real.exp_pos _).le)
    (fun n => Real.exp_le_one_iff.mpr (by simp))
    (fun m n hmn => Real.exp_le_exp.mpr (by simpa using hmn))
    exp_neg_submult ⟨1, one_pos, fun n => by simp⟩

/-- The constant set function `1/2`. -/
noncomputable def half : ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ := fun _ _ => 1 / 2

example : P5 half :=
  P4ImpliesP5.rp4_p4_implies_p5 (fun _ => (1 : ℝ)) (ν := fun _ => half)
    (fun _ => zero_le_one) (fun _ => le_rfl) (fun _ _ _ => le_rfl) (fun _ _ => by norm_num)
    one_P4 (Or.inl fun _ _ => ⟨1 / 2, by norm_num, fun _ => le_rfl⟩) (fun _ _ => le_rfl)

end MathlibExtTest.StatMech.Probability.Percolation.RSW.P4ImpliesP5
