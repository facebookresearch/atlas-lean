/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.GroupTheory.QuaternionWordMapRealPartRange
import Mathlib.Tactic.NormNum

/-! # Tests for Mycielski's real-part question -/

namespace MathlibExtTest.GroupTheory.QuaternionWordMapRealPartRange

open MathlibExt.GroupTheory.WordMapTraceRangeKourovka16Problem69Wanted

local notation "ℍ" => Quaternion ℝ

example : ¬ (∀ w : FreeGroup (Fin 2), w ≠ 1 →
    Set.Icc (-5 / 27 : ℝ) 1 ⊆ Set.range fun xy : ℍˣ × ℍˣ =>
      (FreeGroup.lift ![xy.1, xy.2] w : ℍ).re) :=
  quaternionRealPartRangeContainsInterval_refuted

-- The lower endpoint is attained for the first generator at a negative real quaternion.
example : (-5 / 27 : ℝ) ∈ Set.range fun xy : ℍˣ × ℍˣ =>
    (FreeGroup.lift ![xy.1, xy.2] (FreeGroup.of (0 : Fin 2)) : ℍ).re := by
  let t : ℝ := -5 / 27
  have ht : (t : ℍ) ≠ 0 := by
    intro h
    have he : t = 0 := by
      simpa only [Quaternion.re_coe, Quaternion.re_zero] using congrArg (fun q : ℍ ↦ q.re) h
    norm_num [t] at he
  refine ⟨(Units.mk0 (t : ℍ) ht, 1), ?_⟩
  change (FreeGroup.lift ![Units.mk0 (t : ℍ) ht, (1 : ℍˣ)] (FreeGroup.of (0 : Fin 2)) : ℍ).re = t
  rw [FreeGroup.lift_apply_of]
  exact Quaternion.re_coe t

end MathlibExtTest.GroupTheory.QuaternionWordMapRealPartRange
