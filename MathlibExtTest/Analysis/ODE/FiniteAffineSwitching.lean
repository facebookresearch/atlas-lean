/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.ODE.FiniteAffineSwitching

import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

@[expose] public section

open MathlibExt.Analysis.ODE.FiniteAffineSwitching Set

namespace MathlibExtTest.Analysis.ODE.FiniteAffineSwitching

/-- The two-level fixture is a genuine switched trajectory. -/
example : IsSwitchedTrajectory twoLevelA twoLevelForcing twoLevelTimes 0 twoLevelTrajectory :=
  twoLevel_isSwitchedTrajectory

/-- The reset trajectory is not a switched trajectory. -/
example : ¬ IsSwitchedTrajectory twoLevelA twoLevelForcing twoLevelTimes 0 resetTrajectory :=
  reset_not_continuousOn.2.2

/-- Constant forcing levels on the closed pieces: `1` on `[0, 1]` and `0` on `[1, 2]`. -/
noncomputable def twoLevelPieces (k : Fin 2) (_ : ℝ) : ℝ := if k = 0 then 1 else 0

private lemma times_zero : twoLevelTimes 0 = (0 : ℝ) := by simp [twoLevelTimes]

private lemma times_one : twoLevelTimes 1 = (1 : ℝ) := by simp [twoLevelTimes]

private lemma times_two : twoLevelTimes 2 = (2 : ℝ) := by
  simp [twoLevelTimes, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]

private lemma times_last : twoLevelTimes (Fin.last 2) = (2 : ℝ) := by
  rw [show Fin.last 2 = (2 : Fin 3) by decide]
  exact times_two

private lemma times_strictMono : StrictMono twoLevelTimes := by
  refine Fin.strictMono_iff_lt_succ.mpr fun i => ?_
  fin_cases i
  · change twoLevelTimes 0 < twoLevelTimes 1
    rw [times_zero, times_one]
    norm_num
  · change twoLevelTimes 1 < twoLevelTimes 2
    rw [times_one, times_two]
    norm_num

private lemma pieces_continuousOn (k : Fin 2) :
    ContinuousOn (twoLevelPieces k) (Icc (twoLevelTimes k.castSucc) (twoLevelTimes k.succ)) := by
  change ContinuousOn (fun _ : ℝ => if k = 0 then (1 : ℝ) else 0) _
  exact continuousOn_const

private lemma forcing_eqOn (k : Fin 2) :
    EqOn twoLevelForcing (twoLevelPieces k)
      (Ioo (twoLevelTimes k.castSucc) (twoLevelTimes k.succ)) := by
  intro t ht
  fin_cases k
  · change t ∈ Ioo (twoLevelTimes 0) (twoLevelTimes 1) at ht
    rw [times_zero, times_one] at ht
    change twoLevelForcing t = twoLevelPieces 0 t
    simp [twoLevelForcing, twoLevelPieces, ht.2]
  · change t ∈ Ioo (twoLevelTimes 1) (twoLevelTimes 2) at ht
    rw [times_one, times_two] at ht
    change twoLevelForcing t = twoLevelPieces 1 t
    simp [twoLevelForcing, twoLevelPieces, not_lt.mpr ht.1.le]

/-- `switchedTrajectory_exists_unique` on the two-level data: the trajectory it produces is a
switched trajectory, agrees with `twoLevelTrajectory` on the horizon `[0, 2]`, reaches
`1 - e^{-1}` at the switch, follows Duhamel's formula from the switch state on `[1, 2]`, has
one-sided derivative `-x` there, and satisfies the integral equation on `[0, 2]`. -/
example : ∃ x : ℝ → ℝ,
    IsSwitchedTrajectory twoLevelA twoLevelForcing twoLevelTimes 0 x ∧
    EqOn x twoLevelTrajectory (Icc 0 2) ∧
    x 1 = 1 - Real.exp (-1) ∧
    (∀ t ∈ Icc (1 : ℝ) 2, x t = (NormedSpace.exp ((t - 1) • twoLevelA)) (x 1) +
      ∫ s in (1 : ℝ)..t, (NormedSpace.exp ((t - s) • twoLevelA)) (twoLevelForcing s)) ∧
    (∀ t ∈ Icc (1 : ℝ) 2, HasDerivWithinAt x (twoLevelA (x t)) (Icc 1 2) t) ∧
    ∀ t ∈ Icc (0 : ℝ) 2,
      x t = 0 + ∫ s in (0 : ℝ)..t, (twoLevelA (x s) + twoLevelForcing s) := by
  obtain ⟨x, hx, hform, hderiv, -, hint, huniq⟩ :=
    switchedTrajectory_exists_unique twoLevelA twoLevelTimes times_strictMono twoLevelForcing
      twoLevelPieces pieces_continuousOn forcing_eqOn 0
  have hagree : EqOn x twoLevelTrajectory (Icc 0 2) := by
    have h := huniq twoLevelTrajectory twoLevel_isSwitchedTrajectory
    rw [times_zero, times_last] at h
    exact h.symm
  have hc : twoLevelTimes (1 : Fin 2).castSucc = (1 : ℝ) := times_one
  have hs : twoLevelTimes (1 : Fin 2).succ = (2 : ℝ) := times_two
  refine ⟨x, hx, hagree, ?_, ?_, ?_, ?_⟩
  · rw [hagree ⟨by norm_num, by norm_num⟩]
    simp [twoLevelTrajectory]
  · intro t ht
    have h := hform 1 t (by rw [hc, hs]; exact ht)
    rwa [hc] at h
  · intro t ht
    have h := hderiv 1 t (by rw [hc, hs]; exact ht)
    have hp : twoLevelPieces 1 t = 0 := by simp [twoLevelPieces]
    rwa [hc, hs, hp, add_zero] at h
  · intro t ht
    have h := hint t (by rw [times_zero, times_last]; exact ht)
    rwa [times_zero] at h

end MathlibExtTest.Analysis.ODE.FiniteAffineSwitching
