/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Topology.Maps.Proper.Basic
import MathlibExt.Analysis.Complex.NoProperHolomorphicMapUnitDisc

/-!
# A holomorphic map with a pole on the unit circle
-/

open Metric MathlibExt.Analysis.Complex.NoProperHolomorphicMapUnitDiscWanted

-- A pole at one boundary point does not make this map proper on the disc.
example : ¬ IsProperMap (fun z : ball (0 : ℂ) 1 => (1 - (z : ℂ))⁻¹) := by
  intro h
  apply not_exists_differentiableOn_ball_isCompact_preimage
  refine ⟨fun z => (1 - z)⁻¹, (differentiableOn_id.const_sub 1).inv ?_,
    fun _ hK => h.isCompact_preimage hK⟩
  intro z hz hzero
  obtain rfl : (1 : ℂ) = z := sub_eq_zero.mp hzero
  simp at hz
