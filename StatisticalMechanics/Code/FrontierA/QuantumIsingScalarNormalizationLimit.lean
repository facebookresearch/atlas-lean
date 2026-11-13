/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.QuantumIsingUniformArcosh
import Mathlib.Analysis.Calculus.Deriv.Slope





open Filter Set
open scoped Topology

namespace StatMech.FrontierA



theorem quantumIsingTrotterScalarNormalization_tendsto_zero
    (beta h : Real) (hbeta : 0 < beta) (hh : 0 < h) :
    Tendsto (fun n : Nat =>
      (n + 1 : Real) * Real.log
        (1 - (beta * h / (2 * (n + 1 : Real))) ^ 2))
      atTop (nhds 0) := by
  let t : Nat -> Real := fun n => beta * h / (2 * (n + 1 : Real))
  let x : Nat -> Real := fun n => 1 - t n ^ 2
  have ht : Tendsto t atTop (nhds 0) := by
    have hlim := (tendsto_const_div_atTop_nhds_zero_nat (beta * h / 2)).comp
      (tendsto_add_atTop_nat 1)
    convert hlim using 1
    funext n
    dsimp only [t]
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    field_simp
  have hx : Tendsto x atTop (nhds 1) := by
    have hsquare := ht.pow 2
    have hsub := (tendsto_const_nhds : Tendsto (fun _ : Nat => (1 : Real))
      atTop (nhds 1)).sub hsquare
    simpa [x] using hsub
  have hxne : forall n, x n ≠ 1 := by
    intro n hxn
    have ht0 : t n ≠ 0 := by
      dsimp only [t]
      exact div_ne_zero (mul_ne_zero hbeta.ne' hh.ne') (by positivity)
    apply ht0
    have hsq : t n ^ 2 = 0 := by
      dsimp only [x] at hxn
      linarith
    exact sq_eq_zero_iff.mp hsq
  have hxWithin : Tendsto x atTop (nhdsWithin 1 ({1} : Set Real)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hx, Eventually.of_forall fun n => by simpa using hxne n⟩
  have hslope : Tendsto (fun n => Real.log (x n) / (x n - 1))
      atTop (nhds 1) := by
    have h := (Real.hasDerivAt_log (one_ne_zero : (1 : Real) ≠ 0)).tendsto_slope.comp
      hxWithin
    convert h using 1
    · funext n
      simp [Function.comp_apply, slope, vsub_eq_sub, Real.log_one,
        div_eq_mul_inv, mul_comm]
    · norm_num
  have hscaled : Tendsto (fun n : Nat => (n + 1 : Real) * t n ^ 2)
      atTop (nhds 0) := by
    have hlim := (tendsto_const_div_atTop_nhds_zero_nat ((beta * h / 2) ^ 2)).comp
      (tendsto_add_atTop_nat 1)
    convert hlim using 1
    funext n
    dsimp only [t]
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
    have hn : (n + 1 : Real) ≠ 0 := by positivity
    field_simp [hn]
  have hprod := hscaled.neg.mul hslope
  convert hprod using 1
  · funext n
    have ht0 : t n ≠ 0 := by
      dsimp only [t]
      exact div_ne_zero (mul_ne_zero hbeta.ne' hh.ne') (by positivity)
    dsimp only [x, t]
    rw [show 1 - (beta * h / (2 * (n + 1 : Real))) ^ 2 - 1 =
        -((beta * h / (2 * (n + 1 : Real))) ^ 2) by ring]
    field_simp [ht0]
  · norm_num

end StatMech.FrontierA
