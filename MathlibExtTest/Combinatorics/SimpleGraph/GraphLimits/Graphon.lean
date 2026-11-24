/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.GraphLimits.Graphon

/-! Sanity tests for graphon homomorphism densities, the graphon cut norm and the cut distance. -/

namespace MathlibExtTest.Combinatorics.SimpleGraph.GraphLimits.Graphon

open MathlibExt.Combinatorics.SimpleGraph.GraphLimits MeasureTheory

/-- The edgeless graph on two vertices has density `1` in every graphon (volume of `[0, 1]²`). -/
example (W : ℝ → ℝ → ℝ) : graphonHomDensity (⊥ : SimpleGraph (Fin 2)) W = 1 := by
  simp [graphonHomDensity, measureReal_def, Real.volume_Icc_pi]

/-- The cut norm of the zero kernel is `0`. -/
example : graphonCutNorm (fun _ _ => 0) = 0 := by
  simp [graphonCutNorm]

/-- The cut norm is nonnegative. -/
example (W : ℝ → ℝ → ℝ) : 0 ≤ graphonCutNorm W :=
  Real.iSup_nonneg fun _ => abs_nonneg _

/-- A graphon is at cut distance `0` from itself (take the identity maps). -/
example (W : ℝ → ℝ → ℝ) : cutDistance W W = 0 := by
  have hnn : ∀ p : UnitIntervalMP × UnitIntervalMP,
      0 ≤ graphonCutNorm fun x y => W (p.1.1 x) (p.1.1 y) - W (p.2.1 x) (p.2.1 y) :=
    fun _ => Real.iSup_nonneg fun _ => abs_nonneg _
  have hid : UnitIntervalMP := ⟨id, MeasurePreserving.id _⟩
  refine le_antisymm ?_ (Real.iInf_nonneg hnn)
  calc cutDistance W W ≤ graphonCutNorm fun x y => W (hid.1 x) (hid.1 y) - W (hid.1 x) (hid.1 y) :=
        ciInf_le ⟨0, fun _ ⟨p, hp⟩ => hp ▸ hnn p⟩ (hid, hid)
    _ = 0 := by simp [graphonCutNorm]

end MathlibExtTest.Combinatorics.SimpleGraph.GraphLimits.Graphon
