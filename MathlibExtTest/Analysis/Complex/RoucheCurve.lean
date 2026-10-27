/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Normed.Module.RCLike.Real
import MathlibExt.Analysis.Complex.RoucheCurve

set_option autoImplicit false

open Metric Set

-- On the unit circle, `‖z - (z - 1 / 2)‖ = 1 / 2 < 1 = ‖z‖`, so `z` and `z - 1 / 2` have finitely
-- many zeros inside the circle, and equally many.
example : {z ∈ (range ((↑) : Circle → ℂ)).inside | z - 1 / 2 = 0}.Finite ∧
    ∑ᶠ z ∈ (range ((↑) : Circle → ℂ)).inside, analyticOrderNatAt (fun z : ℂ => z) z =
      ∑ᶠ z ∈ (range ((↑) : Circle → ℂ)).inside, analyticOrderNatAt (fun z : ℂ => z - 1 / 2) z := by
  obtain ⟨-, hg, h⟩ := Complex.rouche (f := fun z => z) (g := fun z => z - 1 / 2) isOpen_univ
    isConnected_univ differentiableOn_id (differentiableOn_id.sub_const _) continuous_subtype_val
    Circle.coe_injective (subset_univ _) (subset_univ _) fun t => by norm_num
  exact ⟨hg, h⟩

-- On the unit disc, `‖z ^ 2 - (z ^ 2 + z / 2)‖ = 1 / 2 < 1 = ‖z ^ 2‖` on the boundary circle, so
-- `z ^ 2` and `z ^ 2 + z / 2` have finitely many zeros in the disc, and equally many.
example : {z ∈ ball (0 : ℂ) 1 | z ^ 2 + z / 2 = 0}.Finite ∧
    ∑ᶠ z ∈ ball (0 : ℂ) 1, analyticOrderNatAt (fun z : ℂ => z ^ 2) z =
      ∑ᶠ z ∈ ball (0 : ℂ) 1, analyticOrderNatAt (fun z : ℂ => z ^ 2 + z / 2) z := by
  obtain ⟨-, hg, h⟩ := Complex.rouche_of_isBounded (U := ball (0 : ℂ) 1)
    (f := fun z => z ^ 2) (g := fun z => z ^ 2 + z / 2) isOpen_ball isBounded_ball
    (fun z _ => by fun_prop) (fun z _ => by fun_prop) fun z hz => by
      rw [frontier_ball 0 one_ne_zero, mem_sphere_zero_iff_norm] at hz
      norm_num [hz]
  exact ⟨hg, h⟩

#print axioms Complex.rouche
#print axioms Complex.rouche_of_isBounded
