/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectDevelopedEndpointSpan
import Mathlib.Analysis.SpecialFunctions.Log.Basic



open Filter Topology

namespace StatMech.FrontierD

noncomputable section



def fkRectDevelopedReflectedEndpointLowerOf
    (crossingFloor : Real) (n : Nat) : Real :=
  (crossingFloor / (((3 * n + 1) ^ 2 : Nat) : Real)) ^ 2

theorem fkRectDevelopedReflectedEndpointLowerOf_pos
    {crossingFloor : Real} (hcrossingFloor : 0 < crossingFloor) (n : Nat) :
    0 < fkRectDevelopedReflectedEndpointLowerOf crossingFloor n := by
  unfold fkRectDevelopedReflectedEndpointLowerOf
  positivity


def fkRectDevelopedReflectedEndpointLower (q : Real) (n : Nat) : Real :=
  fkRectDevelopedReflectedEndpointLowerOf (1 / (2 * (1 + q))) n

theorem fkRectDevelopedReflectedEndpointLower_pos
    {q : Real} (hq : 1 ≤ q) (n : Nat) :
    0 < fkRectDevelopedReflectedEndpointLower q n := by
  unfold fkRectDevelopedReflectedEndpointLower
  exact fkRectDevelopedReflectedEndpointLowerOf_pos (by positivity) n



theorem fkRectDevelopedReflectedEndpointLowerOf_negLogRate_tendsto_zero
    {crossingFloor : Real} (hcrossingFloor : 0 < crossingFloor) :
    Tendsto (fun n =>
      -Real.log
          (fkRectDevelopedReflectedEndpointLowerOf crossingFloor n) /
        (2 * (n + 1) : Real)) atTop (nhds 0) := by
  let C : Real := crossingFloor
  let m : Nat → Real := fun n => (3 * n + 1 : Nat)
  have hC : 0 < C := by simpa [C] using hcrossingFloor
  have hmNat : Tendsto (fun n : Nat => 3 * n + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    omega
  have hm : Tendsto m atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hmNat
  have hlogDivM : Tendsto (fun n => Real.log (m n) / m n)
      atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop
      1 0 1 one_ne_zero).comp hm
    simpa [pow_one] using h
  have hnPlus : Tendsto (fun n : Nat => ((n + 1 : Nat) : Real))
      atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hratio : Tendsto (fun n : Nat =>
      m n / (2 * (n + 1) : Real)) atTop (nhds (3 / 2 : Real)) := by
    have hinv : Tendsto (fun n : Nat =>
        (1 : Real) / (n + 1 : Real)) atTop (nhds 0) :=
      by simpa only [Nat.cast_add, Nat.cast_one] using
        hnPlus.const_div_atTop 1
    have h := (tendsto_const_nhds : Tendsto
      (fun _ : Nat => (3 / 2 : Real)) atTop (nhds (3 / 2 : Real))).sub hinv
    convert h using 1
    · funext n
      dsimp [m]
      push_cast
      field_simp
      ring
    · norm_num
  have hlogScale : Tendsto (fun n : Nat =>
      Real.log (m n) / (2 * (n + 1) : Real)) atTop (nhds 0) := by
    have h := hlogDivM.mul hratio
    convert h using 1
    · funext n
      have hmpos : 0 < m n := by
        dsimp [m]
        positivity
      field_simp
    · ring
  have hconst : Tendsto (fun n : Nat =>
      (-2 * Real.log C) / (2 * (n + 1) : Real))
      atTop (nhds 0) := by
    have hden : Tendsto (fun n : Nat => (2 * (n + 1) : Real))
        atTop atTop := by
      have hp : Tendsto (fun n : Nat => (n : Real) + 1)
          atTop atTop := by
        simpa only [Nat.cast_add, Nat.cast_one] using hnPlus
      exact hp.const_mul_atTop (by norm_num : (0 : Real) < 2)
    exact tendsto_const_nhds.div_atTop hden
  have hsum := hconst.add (hlogScale.const_mul 4)
  have hsum' : Tendsto (fun n : Nat =>
      (-2 * Real.log C) / (2 * (n + 1) : Real) +
        4 * (Real.log (m n) / (2 * (n + 1) : Real)))
      atTop (nhds 0) := by
    simpa using hsum
  apply hsum'.congr'
  filter_upwards with n
  have hmpos : 0 < m n := by
    dsimp [m]
    positivity
  have hM : (0 : Real) < (((3 * n + 1) ^ 2 : Nat) : Real) := by
    positivity
  unfold fkRectDevelopedReflectedEndpointLowerOf
  rw [Real.log_pow, Real.log_div hC.ne' hM.ne']
  dsimp [C, m]
  push_cast
  rw [Real.log_pow]
  ring


theorem fkRectDevelopedReflectedEndpointLower_negLogRate_tendsto_zero
    {q : Real} (hq : 1 ≤ q) :
    Tendsto (fun n =>
      -Real.log (fkRectDevelopedReflectedEndpointLower q n) /
        (2 * (n + 1) : Real)) atTop (nhds 0) := by
  simpa [fkRectDevelopedReflectedEndpointLower] using
    (fkRectDevelopedReflectedEndpointLowerOf_negLogRate_tendsto_zero
      (show 0 < 1 / (2 * (1 + q)) by positivity))

end

end StatMech.FrontierD
