/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































import Mathlib
import Code.RSW.Defs
import Code.RSW.Strip
import Code.RSW.SelfDuality
import Code.Universality.Defs
import Code.Inequalities.IncreasingEvent

open Set MeasureTheory
open scoped ENNReal NNReal

namespace StatMech

namespace RSW

namespace BoxCrossing

open StatMech.Lattice
open StatMech.RSW.Box
open StatMech.RSW.Strip
open StatMech.Universality


















theorem sqrt_trick_real {m s : ℝ} (hm1 : m ≤ 1)
    (h : (1 - m) ^ 2 ≤ 1 - s) : 1 - Real.sqrt (1 - s) ≤ m := by
  have h1m : (0 : ℝ) ≤ 1 - m := by linarith
  have hsqrt : Real.sqrt ((1 - m) ^ 2) ≤ Real.sqrt (1 - s) := Real.sqrt_le_sqrt h
  rw [Real.sqrt_sq h1m] at hsqrt
  linarith





theorem complFKG_union_bound {E : Type*} (μ : Measure (ConfigSpace E))
    [IsProbabilityMeasure μ] {A B : Set (ConfigSpace E)}
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hFKGc : μ.real Aᶜ * μ.real Bᶜ ≤ μ.real (Aᶜ ∩ Bᶜ)) :
    μ.real Aᶜ * μ.real Bᶜ ≤ 1 - μ.real (A ∪ B) := by
  have hcomplU : μ.real (Aᶜ ∩ Bᶜ) = 1 - μ.real (A ∪ B) := by
    rw [← Set.compl_union, measureReal_compl (hA.union hB), probReal_univ]
  rwa [hcomplU] at hFKGc








theorem sqrt_trick {E : Type*} (μ : Measure (ConfigSpace E)) [IsProbabilityMeasure μ]
    {A B : Set (ConfigSpace E)} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hm : μ.real A = μ.real B)
    (hFKGc : μ.real Aᶜ * μ.real Bᶜ ≤ μ.real (Aᶜ ∩ Bᶜ)) :
    1 - Real.sqrt (1 - μ.real (A ∪ B)) ≤ μ.real A := by
  set m := μ.real A with hmdef
  have hcomplA : μ.real Aᶜ = 1 - m := by rw [measureReal_compl hA, probReal_univ]
  have hcomplB : μ.real Bᶜ = 1 - m := by rw [measureReal_compl hB, probReal_univ, ← hm]
  have hbound := complFKG_union_bound μ hA hB hFKGc
  rw [hcomplA, hcomplB] at hbound
  have hkey : (1 - m) ^ 2 ≤ 1 - μ.real (A ∪ B) := by nlinarith [hbound]
  exact sqrt_trick_real (by rw [hmdef]; exact measureReal_le_one) hkey













def squareCrossingEvent (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  horizontalCrossingEvent 0 n 0 n


def squareDualCrossingEvent (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  dualVerticalCrossingEvent 0 n 0 n
















theorem square_crossing_ge_half (μ : Measure (ConfigSpace (Sym2 (Site 2))))
    [IsProbabilityMeasure μ] (n : ℤ)
    (hdualExists : (squareCrossingEvent n)ᶜ ⊆ squareDualCrossingEvent n)
    (hselfDual : μ.real (squareDualCrossingEvent n) = μ.real (squareCrossingEvent n))
    (hmeas : MeasurableSet (squareCrossingEvent n)) :
    (1 : ℝ) / 2 ≤ μ.real (squareCrossingEvent n) := by
  
  have hcompl : μ.real (squareCrossingEvent n)ᶜ = 1 - μ.real (squareCrossingEvent n) := by
    rw [measureReal_compl hmeas, probReal_univ]
  have hmono : μ.real (squareCrossingEvent n)ᶜ ≤ μ.real (squareDualCrossingEvent n) :=
    measureReal_mono hdualExists
  rw [hselfDual] at hmono
  rw [hcompl] at hmono
  linarith












def rectangleCrossingEvent (n : ℤ) : Set (ConfigSpace (Sym2 (Site 2))) :=
  horizontalCrossingEvent 0 (2 * n) 0 n



def rectLeftHalfEvent (n : ℤ) (hn : 0 ≤ n) {z : Site 2} (hz0 : z 0 = n) (hzc : 0 ≤ z 1)
    (hzd : z 1 ≤ n) : Set (ConfigSpace (Sym2 (Site 2))) :=
  leftHalfCrossingEvent 0 n 0 n z
    (rightSide_subset (mem_shared_column (a := 0) (m := n) (b := 2 * n) (c := 0) (d := n)
      hn (by linarith) hz0 hzc hzd).1)



def rectRightHalfEvent (n : ℤ) (hn : 0 ≤ n) {z : Site 2} (hz0 : z 0 = n) (hzc : 0 ≤ z 1)
    (hzd : z 1 ≤ n) : Set (ConfigSpace (Sym2 (Site 2))) :=
  rightHalfCrossingEvent n (2 * n) 0 n z
    (leftSide_subset (mem_shared_column (a := 0) (m := n) (b := 2 * n) (c := 0) (d := n)
      hn (by linarith) hz0 hzc hzd).2)






theorem rect_glue_subset (n : ℤ) (hn : 0 ≤ n) {z : Site 2} (hz0 : z 0 = n) (hzc : 0 ≤ z 1)
    (hzd : z 1 ≤ n) :
    rectLeftHalfEvent n hn hz0 hzc hzd ∩ rectRightHalfEvent n hn hz0 hzc hzd
      ⊆ rectangleCrossingEvent n := by
  have hmb : (n : ℤ) ≤ 2 * n := by linarith
  exact halfCrossing_glue_subset (a := 0) (m := n) (b := 2 * n) (c := 0) (d := n)
    hn hmb hz0 hzc hzd







theorem measureReal_rectangleCrossing_ge_halves
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsFiniteMeasure μ]
    (hpa : PositivelyAssociated μ) (n : ℤ) (hn : 0 ≤ n) {z : Site 2} (hz0 : z 0 = n)
    (hzc : 0 ≤ z 1) (hzd : z 1 ≤ n) :
    μ.real (rectLeftHalfEvent n hn hz0 hzc hzd) * μ.real (rectRightHalfEvent n hn hz0 hzc hzd)
      ≤ μ.real (rectangleCrossingEvent n) := by
  have hmb : (n : ℤ) ≤ 2 * n := by linarith
  exact measureReal_horizontalCrossing_ge_halves (a := 0) (m := n) (b := 2 * n) (c := 0) (d := n)
    hn hmb hz0 hzc hzd μ hpa


























theorem box_crossing_lower_bound
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) (n : ℤ) (hn : 0 ≤ n) {z : Site 2} (hz0 : z 0 = n)
    (hzc : 0 ≤ z 1) (hzd : z 1 ≤ n)
    (hrouteLeft : (1 : ℝ) / 2 ≤ μ.real (rectLeftHalfEvent n hn hz0 hzc hzd))
    (hrouteRight : (1 : ℝ) / 2 ≤ μ.real (rectRightHalfEvent n hn hz0 hzc hzd)) :
    (1 : ℝ) / 4 ≤ μ.real (rectangleCrossingEvent n) := by
  have hprod : (1 : ℝ) / 4
      ≤ μ.real (rectLeftHalfEvent n hn hz0 hzc hzd)
          * μ.real (rectRightHalfEvent n hn hz0 hzc hzd) := by
    have h1 : (0 : ℝ) ≤ μ.real (rectLeftHalfEvent n hn hz0 hzc hzd) := measureReal_nonneg
    nlinarith [hrouteLeft, hrouteRight, h1]
  exact le_trans hprod
    (measureReal_rectangleCrossing_ge_halves μ hpa n hn hz0 hzc hzd)





theorem box_crossing_lower_bound_pos
    (μ : Measure (ConfigSpace (Sym2 (Site 2)))) [IsProbabilityMeasure μ]
    (hpa : PositivelyAssociated μ) (n : ℤ) (hn : 0 ≤ n) {z : Site 2} (hz0 : z 0 = n)
    (hzc : 0 ≤ z 1) (hzd : z 1 ≤ n)
    (hrouteLeft : (1 : ℝ) / 2 ≤ μ.real (rectLeftHalfEvent n hn hz0 hzc hzd))
    (hrouteRight : (1 : ℝ) / 2 ≤ μ.real (rectRightHalfEvent n hn hz0 hzc hzd)) :
    ∃ c : ℝ, 0 < c ∧ c ≤ μ.real (rectangleCrossingEvent n) :=
  ⟨1 / 4, by norm_num,
    box_crossing_lower_bound μ hpa n hn hz0 hzc hzd hrouteLeft hrouteRight⟩

end BoxCrossing

end RSW

end StatMech
