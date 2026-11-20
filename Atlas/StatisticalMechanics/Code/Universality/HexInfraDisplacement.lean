/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































import Mathlib
import Code.Universality.HexLattice
import Code.Universality.HexWall3

namespace StatMech.Universality

open HexWalk List
open scoped BigOperators Real









noncomputable def hexInfra_midAccum (m : ℂ) (h : ℤ) : List ℤ → ℂ
  | [] => m
  | t :: ts => hexInfra_midAccum (m + HexWalk.halfStep h + HexWalk.halfStep (h + t)) (h + t) ts

@[simp] theorem hexInfra_midAccum_nil (m : ℂ) (h : ℤ) : hexInfra_midAccum m h [] = m := rfl

@[simp] theorem hexInfra_midAccum_cons (m : ℂ) (h t : ℤ) (ts : List ℤ) :
    hexInfra_midAccum m h (t :: ts)
      = hexInfra_midAccum (m + HexWalk.halfStep h + HexWalk.halfStep (h + t)) (h + t) ts := rfl


def hexInfra_headAccum (h : ℤ) : List ℤ → ℤ
  | [] => h
  | t :: ts => hexInfra_headAccum (h + t) ts

@[simp] theorem hexInfra_headAccum_nil (h : ℤ) : hexInfra_headAccum h [] = h := rfl

@[simp] theorem hexInfra_headAccum_cons (h t : ℤ) (ts : List ℤ) :
    hexInfra_headAccum h (t :: ts) = hexInfra_headAccum (h + t) ts := rfl


theorem hexInfra_verticesAux_ne_nil (m : ℂ) (h : ℤ) (ts : List ℤ) :
    HexWalk.verticesAux m h ts ≠ [] := by
  cases ts with
  | nil => simp [HexWalk.verticesAux]
  | cons t ts => simp [HexWalk.verticesAux]




theorem hexInfra_verticesAux_getLast? (m : ℂ) (h : ℤ) (ts : List ℤ) :
    (HexWalk.verticesAux m h ts).getLast?
      = some (hexInfra_midAccum m h ts + HexWalk.halfStep (hexInfra_headAccum h ts)) := by
  induction ts generalizing m h with
  | nil => simp [HexWalk.verticesAux]
  | cons t ts ih =>
    rw [HexWalk.verticesAux_cons, List.getLast?_cons, ih]
    simp



theorem hexInfra_verticesAux_getLast_mem (m : ℂ) (h : ℤ) (ts : List ℤ) :
    hexInfra_midAccum m h ts + HexWalk.halfStep (hexInfra_headAccum h ts)
      ∈ HexWalk.verticesAux m h ts :=
  List.mem_of_getLast? (hexInfra_verticesAux_getLast? m h ts)








noncomputable def hexInfra_stepReSum (h : ℤ) : List ℤ → ℝ
  | [] => 0
  | t :: ts =>
      (HexWalk.halfStep h).re + (HexWalk.halfStep (h + t)).re + hexInfra_stepReSum (h + t) ts

@[simp] theorem hexInfra_stepReSum_nil (h : ℤ) : hexInfra_stepReSum h [] = 0 := rfl

@[simp] theorem hexInfra_stepReSum_cons (h t : ℤ) (ts : List ℤ) :
    hexInfra_stepReSum h (t :: ts)
      = (HexWalk.halfStep h).re + (HexWalk.halfStep (h + t)).re + hexInfra_stepReSum (h + t) ts :=
  rfl



theorem hexInfra_midAccum_re (m : ℂ) (h : ℤ) (ts : List ℤ) :
    (hexInfra_midAccum m h ts).re = m.re + hexInfra_stepReSum h ts := by
  induction ts generalizing m h with
  | nil => simp
  | cons t ts ih =>
    rw [hexInfra_midAccum_cons, ih, hexInfra_stepReSum_cons]
    simp only [Complex.add_re]
    ring



theorem hexInfra_ofTurns_last_re (a : ℂ) (h0 : ℤ) (ts : List ℤ) :
    (hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)).re
      = a.re + hexInfra_stepReSum h0 ts + (HexWalk.halfStep (hexInfra_headAccum h0 ts)).re := by
  rw [Complex.add_re, hexInfra_midAccum_re]







theorem hexInfra_halfStep_re_abs_le (h : ℤ) : |(HexWalk.halfStep h).re| ≤ 1 / 2 := by
  have hre : (HexWalk.halfStep h).re
      = (1 / 2) * Real.cos (Real.pi / 6 + (h : ℝ) * (Real.pi / 3)) := by
    unfold HexWalk.halfStep hexUnit
    rw [show (Complex.I * ((Real.pi : ℂ) / 6 + (((h : ℝ)) : ℂ) * ((Real.pi : ℂ) / 3)))
          = ((Real.pi / 6 + (h : ℝ) * (Real.pi / 3) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re]
    norm_num
  rw [hre, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  nlinarith [Real.abs_cos_le_one (Real.pi / 6 + (h : ℝ) * (Real.pi / 3))]


theorem hexInfra_halfStep_re_le (h : ℤ) : (HexWalk.halfStep h).re ≤ 1 / 2 :=
  (abs_le.mp (hexInfra_halfStep_re_abs_le h)).2








theorem hexInfra_stepReSum_le_length (h : ℤ) (ts : List ℤ) :
    hexInfra_stepReSum h ts ≤ ts.length := by
  induction ts generalizing h with
  | nil => simp
  | cons t ts ih =>
    rw [hexInfra_stepReSum_cons, List.length_cons]
    have h1 := hexInfra_halfStep_re_le h
    have h2 := hexInfra_halfStep_re_le (h + t)
    have hih := ih (h + t)
    push_cast
    linarith





theorem hexInfra_verticesAux_last_re_le (m : ℂ) (h : ℤ) (ts : List ℤ) :
    (hexInfra_midAccum m h ts + HexWalk.halfStep (hexInfra_headAccum h ts)).re
      ≤ m.re + (ts.length + 1) := by
  rw [Complex.add_re, hexInfra_midAccum_re]
  have h1 := hexInfra_stepReSum_le_length h ts
  have h2 := hexInfra_halfStep_re_le (hexInfra_headAccum h ts)
  linarith







noncomputable def hexInfra_stepIncrements (h : ℤ) : List ℤ → List ℝ
  | [] => []
  | t :: ts =>
      ((HexWalk.halfStep h).re + (HexWalk.halfStep (h + t)).re)
        :: hexInfra_stepIncrements (h + t) ts

@[simp] theorem hexInfra_stepIncrements_nil (h : ℤ) : hexInfra_stepIncrements h [] = [] := rfl

@[simp] theorem hexInfra_stepIncrements_cons (h t : ℤ) (ts : List ℤ) :
    hexInfra_stepIncrements h (t :: ts)
      = ((HexWalk.halfStep h).re + (HexWalk.halfStep (h + t)).re)
          :: hexInfra_stepIncrements (h + t) ts := rfl


theorem hexInfra_stepReSum_eq_sum_increments (h : ℤ) (ts : List ℤ) :
    hexInfra_stepReSum h ts = (hexInfra_stepIncrements h ts).sum := by
  induction ts generalizing h with
  | nil => simp
  | cons t ts ih => rw [hexInfra_stepReSum_cons, hexInfra_stepIncrements_cons, List.sum_cons, ih]





theorem hexInfra_stepReSum_ge_of_advance (h : ℤ) (ts : List ℤ) (δ : ℝ)
    (hadv : ∀ x ∈ hexInfra_stepIncrements h ts, δ ≤ x) :
    (δ * ts.length : ℝ) ≤ hexInfra_stepReSum h ts := by
  induction ts generalizing h with
  | nil => simp
  | cons t ts ih =>
    rw [hexInfra_stepReSum_cons, List.length_cons]
    have hhead : δ ≤ (HexWalk.halfStep h).re + (HexWalk.halfStep (h + t)).re :=
      hadv _ (by rw [hexInfra_stepIncrements_cons]; exact List.mem_cons_self)
    have htail : ∀ x ∈ hexInfra_stepIncrements (h + t) ts, δ ≤ x := fun x hx =>
      hadv x (by rw [hexInfra_stepIncrements_cons]; exact List.mem_cons_of_mem _ hx)
    have := ih (h + t) htail
    push_cast
    nlinarith [this, hhead]















theorem hexInfra_reachesWidth_of_last_re (a : ℂ) (h0 : ℤ) (T : ℕ) (ts : List ℤ)
    (hdisp : (T : ℝ)
      ≤ hexInfra_stepReSum h0 ts + (HexWalk.halfStep (hexInfra_headAccum h0 ts)).re) :
    hexWall3_ReachesWidth a h0 T ts := by
  refine ⟨hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts), ?_, ?_⟩
  · exact hexInfra_verticesAux_getLast_mem a h0 ts
  · rw [hexInfra_ofTurns_last_re]; linarith









theorem hexInfra_reachesWidth_of_advance (a : ℂ) (h0 : ℤ) (T : ℕ) (ts : List ℤ) (δ : ℝ)
    (hadv : ∀ x ∈ hexInfra_stepIncrements h0 ts, δ ≤ x)
    (hlast : 0 ≤ (HexWalk.halfStep (hexInfra_headAccum h0 ts)).re)
    (hsteps : (T : ℝ) ≤ δ * ts.length) :
    hexWall3_ReachesWidth a h0 T ts := by
  apply hexInfra_reachesWidth_of_last_re a h0 T ts
  have := hexInfra_stepReSum_ge_of_advance h0 ts δ hadv
  linarith










theorem hexInfra_singleRight_stepReSum :
    hexInfra_stepReSum 0 [(-1 : ℤ)] + (HexWalk.halfStep (hexInfra_headAccum 0 [(-1 : ℤ)])).re
      = (HexWalk.halfStep 0).re + 2 * (HexWalk.halfStep (-1)).re := by
  simp only [hexInfra_stepReSum_cons, hexInfra_stepReSum_nil, hexInfra_headAccum_cons,
    hexInfra_headAccum_nil]
  rw [show (0 : ℤ) + (-1) = -1 by ring]
  ring





theorem hexInfra_singleRight_reaches (a : ℂ) :
    hexWall3_ReachesWidth a 0 1 [(-1 : ℤ)] :=
  hexWall3_reachesWidth_witness a

end StatMech.Universality
