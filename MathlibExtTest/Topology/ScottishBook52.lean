/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.ScottishBook52
import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Tactic.NormNum

open Set Filter Topology
open MathlibExt.Topology.ScottishBook52Wanted

namespace MathlibExtTest.Topology.ScottishBook52

private abbrev I := ↥(Ioo (0 : ℝ) 1)

-- Make the Borel structure on the compact-open function space explicit.
example : ¬ @MeasurableSet C(I, ℝ) (borel _) {f | HasDerivativeAtEveryPoint f} :=
  everywhere_differentiable_class_not_borel

-- The zero extension of this constant function jumps at the endpoints.
example : HasDerivativeAtEveryPoint (ContinuousMap.const I (1 : ℝ)) := by
  intro x hx
  apply (differentiableAt_const (𝕜 := ℝ) (x := x) (1 : ℝ)).congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  simp [hy]

-- A corner at an interior point is detected by the same zero-extension definition.
example : ¬ HasDerivativeAtEveryPoint
    (⟨fun x : I ↦ |(x : ℝ) - 1 / 2|, (continuous_subtype_val.sub continuous_const).abs⟩) := by
  intro h
  have hx : (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 := by constructor <;> norm_num
  have hd : DifferentiableAt ℝ (fun y : ℝ ↦ |y - 1 / 2|) (1 / 2) := by
    apply (h _ hx).congr_of_eventuallyEq
    filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
    simp [hy]
  have ht := differentiableAt_id (𝕜 := ℝ) (x := (0 : ℝ)) |>.add_const (1 / 2)
  have hd' : DifferentiableAt ℝ (fun y : ℝ ↦ |y - 1 / 2|) (id (0 : ℝ) + 1 / 2) := by
    simpa using hd
  have hshift := hd'.comp 0 ht
  exact not_differentiableAt_abs_zero (by simpa [Function.comp_def] using hshift)

end MathlibExtTest.Topology.ScottishBook52
