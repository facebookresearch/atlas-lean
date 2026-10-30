/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.RSW.BoxCrossingCapstone
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.Percolation.RSW.BoxCrossingCapstone`

* `boxCrossing_uniform_of_p4_inputs` with all hypotheses discharged by the constant model
  `μ = ν = 1/2` and `a = 1` (no exponential decay). As its docstring says, the conclusion is the
  hypothesis `htwo`; the test shows the remaining hypotheses are jointly satisfiable.
-/

@[expose] public section

open StatMech StatMech.Lattice StatMech.RSW StatMech.RSW.Box

namespace MathlibExtTest.StatMech.Probability.Percolation.RSW.BoxCrossingCapstone

/-- The constant set function `1/2`. -/
noncomputable def half : ℕ → Set (ConfigSpace (Sym2 (Site 2))) → ℝ := fun _ _ => 1 / 2

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

example : P5c (fun (_ : Unit) => half) :=
  boxCrossing_uniform_of_p4_inputs () (fun _ => (1 : ℝ)) (ν := fun _ => half)
    (fun _ => zero_le_one) (fun _ => le_rfl) (fun _ _ _ => le_rfl) (fun _ _ => by norm_num)
    one_P4 (Or.inl fun _ _ => ⟨1 / 2, by norm_num, fun _ => le_rfl⟩) (fun _ _ => le_rfl)
    (fun _ => by simp only [half]; norm_num) (fun _ _ => le_rfl)
    (fun _ _ => ⟨1 / 2, by norm_num, fun _ _ => by simp only [half]; norm_num⟩)

end MathlibExtTest.StatMech.Probability.Percolation.RSW.BoxCrossingCapstone
