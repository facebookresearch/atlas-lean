/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Semicontinuity.BergeMaximum

/-!
# Tests for Berge's maximum theorem

* A moving singleton correspondence `φ x = {x}` with `f x y = x * y`.
* A kinked value: `φ ≡ Icc (-1) 1`, `f x y = x * y` has value `|x|`, continuous but not
  differentiable at `0`.
* Upper hemicontinuity of the argmax in the kinked example, where the argmax jumps from `{-1}`
  through `Icc (-1) 1` to `{1}` at `x = 0`.
-/

@[expose] public section

open Topology Filter Set MathlibExt.Topology.BergeMaximum

namespace MathlibExtTest.Topology.Semicontinuity.BergeMaximum

example : Continuous fun x : ℝ => sSup ((fun y => x * y) '' {x}) := by
  have h := berge_maximum_continuous_value (f := fun x y : ℝ => x * y) (φ := fun x : ℝ => {x})
    (show Continuous ↿(fun x y : ℝ => x * y) from continuous_fst.mul continuous_snd)
    (fun x => isCompact_singleton) (fun x => singleton_nonempty x)
    (upperHemicontinuous_singleton_iff.mpr continuous_id)
    (lowerHemicontinuous_singleton_iff.mpr continuous_id)
  exact h

example : (∀ x : ℝ, sSup ((fun y => x * y) '' Set.Icc (-1 : ℝ) 1) = |x|) ∧
    Continuous fun x : ℝ => |x| := by
  have hfc : ∀ x : ℝ, Continuous fun y : ℝ => x * y := fun x => by continuity
  have hval : ∀ x : ℝ, sSup ((fun y => x * y) '' Set.Icc (-1 : ℝ) 1) = |x| := by
    intro x
    apply le_antisymm
    · refine csSup_le ?_ ?_
      · have hne : (Set.Icc (-1 : ℝ) 1).Nonempty := nonempty_Icc.mpr (by norm_num)
        exact hne.image (fun y => x * y)
      · rintro _ ⟨y, hy, rfl⟩
        rw [mem_Icc] at hy
        calc x * y ≤ |x * y| := le_abs_self _
          _ = |x| * |y| := abs_mul x y
          _ ≤ |x| * 1 := mul_le_mul_of_nonneg_left (abs_le.mpr ⟨hy.1, hy.2⟩) (abs_nonneg x)
          _ = |x| := mul_one _
    · rcases lt_or_ge x 0 with hx | hx
      · have h1 : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := mem_Icc.mpr ⟨le_rfl, by norm_num⟩
        have hle : x * (-1) ≤ sSup ((fun y => x * y) '' Set.Icc (-1 : ℝ) 1) :=
          le_csSup (isCompact_Icc.bddAbove_image (hfc x).continuousOn)
            (mem_image_of_mem _ h1)
        have heq : x * (-1) = |x| := by rw [abs_of_neg hx]; ring
        rw [← heq]
        exact hle
      · have h1 : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := mem_Icc.mpr ⟨by norm_num, le_rfl⟩
        have hle : x * 1 ≤ sSup ((fun y => x * y) '' Set.Icc (-1 : ℝ) 1) :=
          le_csSup (isCompact_Icc.bddAbove_image (hfc x).continuousOn)
            (mem_image_of_mem _ h1)
        rw [mul_one] at hle
        rw [abs_of_nonneg hx]
        exact hle
  refine ⟨hval, ?_⟩
  have hcont : Continuous fun x : ℝ => sSup ((fun y => x * y) '' Set.Icc (-1 : ℝ) 1) :=
    berge_maximum_continuous_value (f := fun x y : ℝ => x * y)
      (φ := fun _ : ℝ => Set.Icc (-1 : ℝ) 1)
      (show Continuous ↿(fun x y : ℝ => x * y) from continuous_fst.mul continuous_snd)
      (fun _ => isCompact_Icc) (fun _ => nonempty_Icc.mpr (show (-1 : ℝ) ≤ 1 by norm_num))
      UpperHemicontinuous.const LowerHemicontinuous.const
  simpa [hval] using hcont

example : UpperHemicontinuous fun x : ℝ =>
    {y ∈ Set.Icc (-1 : ℝ) 1 | ∀ y' ∈ Set.Icc (-1 : ℝ) 1, x * y' ≤ x * y} :=
  berge_maximum_upperHemicontinuous_argmax (f := fun x y : ℝ => x * y)
    (φ := fun _ : ℝ => Set.Icc (-1 : ℝ) 1)
    (show Continuous ↿(fun x y : ℝ => x * y) from continuous_fst.mul continuous_snd)
    (fun _ => isCompact_Icc) (fun _ => nonempty_Icc.mpr (show (-1 : ℝ) ≤ 1 by norm_num))
    UpperHemicontinuous.const LowerHemicontinuous.const

end MathlibExtTest.Topology.Semicontinuity.BergeMaximum
