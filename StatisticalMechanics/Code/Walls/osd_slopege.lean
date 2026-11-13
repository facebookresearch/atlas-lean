/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

























































import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Code.OSSS.Integration

open Real Set

set_option linter.style.longLine false

namespace StatMech
namespace Walls














theorem osd_slope_ge_diffOn (a b m : ℝ) (hab : a ≤ b) (T : ℝ → ℝ)
    (hdiff : DifferentiableOn ℝ T (Icc a b))
    (hbound : ∀ x ∈ Icc a b, m ≤ deriv T x) :
    m * (b - a) ≤ T b - T a := by
  
  have hcont : ContinuousOn T (Icc a b) := hdiff.continuousOn
  
  
  have hkey := (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv hcont
    (by rw [interior_Icc]; exact hdiff.mono Ioo_subset_Icc_self)
    (by rw [interior_Icc]; exact fun x hx => hbound x (Ioo_subset_Icc_self hx))
    a (left_mem_Icc.mpr hab) b (right_mem_Icc.mpr hab) hab
  exact hkey








theorem osd_slope_ge (a b m : ℝ) (hab : a ≤ b) (T T' : ℝ → ℝ)
    (hd : ∀ x ∈ Icc a b, HasDerivAt T (T' x) x)
    (hbound : ∀ x ∈ Icc a b, m ≤ T' x) :
    m * (b - a) ≤ T b - T a := by
  have hdiff : DifferentiableOn ℝ T (Icc a b) :=
    fun x hx => (hd x hx).differentiableAt.differentiableWithinAt
  refine osd_slope_ge_diffOn a b m hab T hdiff ?_
  intro x hx
  rw [(hd x hx).deriv]
  exact hbound x hx






theorem osd_slope_ge_of_hasDerivAt (a b m : ℝ) (hab : a ≤ b) (T T' : ℝ → ℝ)
    (hd : ∀ x, HasDerivAt T (T' x) x)
    (hbound : ∀ x ∈ Icc a b, m ≤ T' x) :
    m * (b - a) ≤ T b - T a :=
  osd_slope_ge a b m hab T T' (fun x _ => hd x) hbound

end Walls
end StatMech
