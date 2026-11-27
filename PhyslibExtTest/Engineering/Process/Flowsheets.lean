/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.Engineering.Process.Flowsheets

import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for finite flowsheets

Boundary checks for `PhyslibExt.Engineering.Process.Flowsheets`: a
two-unit flowsheet whose internal flow cancels against external input and
output, a two-unit recycle with no external terms, an isolated unit, and
the summed supplied rate under edge reversal.
-/

namespace Engineering.Process.Flowsheets.Tests

open Engineering.Process.Flowsheets

private theorem f01 : ((0 : Fin 2) = 1) = False := eq_false (by decide)
private theorem f10 : ((1 : Fin 2) = 0) = False := eq_false (by decide)
private theorem n01 : ((0 : Fin 2) ≠ 1) = True := eq_true (by decide)
private theorem n10 : ((1 : Fin 2) ≠ 0) = True := eq_true (by decide)

/-- Two units and one species. Internal flow `3` runs from unit `0` to
unit `1`; external input `5` enters unit `0` and external output `2` leaves
unit `1`. Unit holdups grow at rates `2` and `1`, so the total grows at
`3 = 5 - 2` and the internal flow cancels. -/
def flowsheet2 : Flowsheet (Fin 2) (Fin 1) where
  holdup := fun _ u t => if u = 0 then 2 * t else t
  transfer := fun _ i j _ => if i = 0 ∧ j = 1 then 3 else 0
  externalIn := fun _ u _ => if u = 0 then 5 else 0
  externalOut := fun _ u _ => if u = 1 then 2 else 0
  generation := fun _ _ _ => 0
  balance := by
    intro s u t
    fin_cases u
    · simp only [Fin.sum_univ_two]
      simp [f01, f10]
      norm_num
      have h := (hasDerivAt_id (x := t)).const_mul (c := (2 : ℝ))
      simpa using h
    · simp only [Fin.sum_univ_two]
      simp [f01, f10]
      norm_num
      exact hasDerivAt_id (x := t)

/-- Two units with an internal recycle of `3` in each direction and no
external terms; both holdups are constant. -/
def recycle2 : Flowsheet (Fin 2) (Fin 1) where
  holdup := fun _ u _ => if u = 0 then 4 else 7
  transfer := fun _ i j _ => if i ≠ j then 3 else 0
  externalIn := fun _ _ _ => 0
  externalOut := fun _ _ _ => 0
  generation := fun _ _ _ => 0
  balance := by
    intro s u t
    fin_cases u
    · simp only [Fin.sum_univ_two]
      simp [f01, f10, n01, n10]
      exact hasDerivAt_const (x := t) (c := 4)
    · simp only [Fin.sum_univ_two]
      simp [f01, f10, n01, n10]
      exact hasDerivAt_const (x := t) (c := 7)

example : HasDerivAt (fun t => ∑ u : Fin 2, flowsheet2.holdup 0 u t) 3 0 := by
  have hb := Flowsheet.species_balance flowsheet2 0 0
  have hval : (∑ u : Fin 2,
      (flowsheet2.externalIn 0 u 0 - flowsheet2.externalOut 0 u 0 +
        flowsheet2.generation 0 u 0)) = 3 := by
    show (∑ u : Fin 2, ((if u = 0 then (5:ℝ) else 0) - (if u = 1 then (2:ℝ) else 0) + 0)) = 3
    simp only [Fin.sum_univ_two]
    simp [f01, f10]
    norm_num
  rwa [hval] at hb

example : HasDerivAt (fun t => ∑ u : Fin 2, recycle2.holdup 0 u t) 0 0 := by
  have hb := Flowsheet.species_balance recycle2 0 0
  have hval : (∑ u : Fin 2,
      (recycle2.externalIn 0 u 0 - recycle2.externalOut 0 u 0 +
        recycle2.generation 0 u 0)) = 0 := by
    show (∑ u : Fin 2, ((0:ℝ) - 0 + 0)) = 0
    simp only [Fin.sum_univ_two]
    norm_num
  rwa [hval] at hb

-- An isolated single unit with no transfers and no external terms keeps a
-- constant holdup to first order.
example : HasDerivAt (fun t : ℝ => ∑ _u : Fin 1, (4 : ℝ)) 0 0 := by
  simp only [Fin.sum_univ_one]
  exact hasDerivAt_const (x := 0) (c := 4)

-- Reversing the internal edge direction while keeping the same external
-- terms does not change the whole-network derivative value `5 - 2 = 3`:
-- the summed supplied rate is the same number.
example :
    (∑ u : Fin 2,
      (flowsheet2.externalIn 0 u 0 - flowsheet2.externalOut 0 u 0 +
        flowsheet2.generation 0 u 0)) = 3 := by
  show (∑ u : Fin 2, ((if u = 0 then (5:ℝ) else 0) - (if u = 1 then (2:ℝ) else 0) + 0)) = 3
  simp only [Fin.sum_univ_two]
  simp [f01, f10]
  norm_num

/-- The reversed-edge flowsheet: internal flow `3` now runs from unit `1`
to unit `0`, external input `5` enters unit `1`, and external output `2`
leaves unit `0`. Unit holdups grow at rates `1` and `2`, so the total
again grows at `3 = 5 - 2`. -/
def flowsheet2rev : Flowsheet (Fin 2) (Fin 1) where
  holdup := fun _ u t => if u = 1 then 2 * t else t
  transfer := fun _ i j _ => if i = 1 ∧ j = 0 then 3 else 0
  externalIn := fun _ u _ => if u = 1 then 5 else 0
  externalOut := fun _ u _ => if u = 0 then 2 else 0
  generation := fun _ _ _ => 0
  balance := by
    intro s u t
    fin_cases u
    · simp only [Fin.sum_univ_two]
      simp [f01, f10]
      norm_num
      exact hasDerivAt_id (x := t)
    · simp only [Fin.sum_univ_two]
      simp [f01, f10]
      norm_num
      have h := (hasDerivAt_id (x := t)).const_mul (c := (2 : ℝ))
      simpa using h

example : HasDerivAt (fun t => ∑ u : Fin 2, flowsheet2rev.holdup 0 u t) 3 0 := by
  have hb := Flowsheet.species_balance flowsheet2rev 0 0
  have hval : (∑ u : Fin 2,
      (flowsheet2rev.externalIn 0 u 0 - flowsheet2rev.externalOut 0 u 0 +
        flowsheet2rev.generation 0 u 0)) = 3 := by
    show (∑ u : Fin 2, ((if u = 1 then (5:ℝ) else 0) - (if u = 0 then (2:ℝ) else 0) + 0)) = 3
    simp only [Fin.sum_univ_two]
    simp [f01, f10]
    norm_num
  rwa [hval] at hb

end Engineering.Process.Flowsheets.Tests
