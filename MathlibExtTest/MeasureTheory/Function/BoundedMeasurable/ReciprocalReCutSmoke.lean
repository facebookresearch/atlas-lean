/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.MeasureTheory.Function.BoundedMeasurable.ReciprocalReCut
import Mathlib.Tactic.NormNum

/-!
An empty source admits the bound minus one and still gives norm zero. On a one-point
measurable space, the constant two has norm two. Its reciprocal cut retains the endpoint
at threshold two and vanishes at threshold three.
-/

open MeasureTheory
open MathlibExt.MeasureTheory.Function
open BoundedMeasurableFunction

namespace MathlibExtTest.BoundedMeasurable.ReciprocalReCut

noncomputable section

local instance : MeasurableSpace Empty := ⊥
local instance : MeasurableSpace Unit := ⊤

private def emptyWithNegativeBound : BoundedMeasurableFunction Empty :=
  ofBound (fun _ : Empty => (2 : ℂ)) measurable_const (-1) (fun x => nomatch x)

private def boundedTwo : BoundedMeasurableFunction Unit :=
  ofBound (fun _ : Unit => (2 : ℂ)) measurable_const 2 (fun _ => by simp)

example : ‖emptyWithNegativeBound‖ = 0 := by
  refine le_antisymm ?_ (norm_nonneg _)
  calc
    ‖emptyWithNegativeBound‖ ≤ max (-1 : ℝ) 0 :=
      norm_ofBound_le_max (fun _ : Empty => (2 : ℂ))
        measurable_const (-1) (fun x => nomatch x)
    _ = 0 := max_eq_right (by norm_num)

example : ‖boundedTwo‖ = 2 := by
  refine le_antisymm ?_ ?_
  · exact norm_ofBound_le (fun _ : Unit => (2 : ℂ))
      measurable_const 2 (fun _ => by simp) (by norm_num)
  · simpa only [boundedTwo, ofBound_apply, Complex.norm_two] using
      norm_apply_le_norm boundedTwo ()

example :
    reciprocalReCut (fun x : Unit => boundedTwo x) boundedTwo.measurable
      2 (by norm_num) () = (1 : ℂ) / 2 := by
  rw [reciprocalReCut_apply]
  simp only [boundedTwo, ofBound_apply]
  norm_num

example :
    reciprocalReCut (fun x : Unit => boundedTwo x) boundedTwo.measurable
      3 (by norm_num) () = 0 := by
  rw [reciprocalReCut_apply]
  simp only [boundedTwo, ofBound_apply]
  norm_num

end

end MathlibExtTest.BoundedMeasurable.ReciprocalReCut
