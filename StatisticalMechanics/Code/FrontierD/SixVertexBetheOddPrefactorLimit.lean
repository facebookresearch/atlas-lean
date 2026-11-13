/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.FrontierD.SixVertexBetheOddOffsetReduction
import Mathlib.Analysis.SpecialFunctions.Log.Basic

open Finset Filter Topology

namespace StatMech.FrontierD

noncomputable section




theorem sixVertexFixedOddChargeBethePrefactor_log_div_width_tendsto_zero
    {c : Real} (hc : 2 < c) {r : Nat} (hr : Odd r) :
    Tendsto (fun k : Nat ↦
      Real.log (sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth r k)
        (sixVertexFixedChargeBetheRoots hc r k)
        (sixVertexFixedChargeBetheCentralIndex r k)) /
          (sixVertexFourWidth r k : Real)) atTop (nhds 0) := by
  let N : Nat → Nat := sixVertexFourWidth r
  let C : Real := c ^ 2 * (2 * (r : Real))
  have hrpos : 0 < r := hr.pos
  have hC : 0 < C := by
    dsimp only [C]
    positivity
  have hNnat : Tendsto N atTop atTop := by
    rw [tendsto_atTop]
    intro b
    filter_upwards [eventually_ge_atTop b] with k hk
    dsimp only [N, sixVertexFourWidth]
    omega
  have hNreal : Tendsto (fun k ↦ (N k : Real)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hNnat
  have hconst : Tendsto (fun k ↦ Real.log C / (N k : Real))
      atTop (nhds 0) := by
    exact tendsto_const_nhds.div_atTop hNreal
  have hlogN : Tendsto (fun k ↦ Real.log (N k : Real) / (N k : Real))
      atTop (nhds 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp
      hNreal
    convert h using 1
    funext k
    norm_num
  have hupper : Tendsto (fun k ↦ Real.log (c ^ 2 * (N k : Real)) /
      (N k : Real)) atTop (nhds 0) := by
    have hc2 : c ^ 2 ≠ 0 := pow_ne_zero 2 (by linarith)
    have hlogMul (k : Nat) :
        Real.log (c ^ 2 * (N k : Real)) / (N k : Real) =
          Real.log (c ^ 2) / (N k : Real) +
            Real.log (N k : Real) / (N k : Real) := by
      have hNk : (N k : Real) ≠ 0 := by
        exact_mod_cast (sixVertexFourWidth_pos r k).ne'
      rw [Real.log_mul hc2 hNk]
      ring
    have hfirst : Tendsto (fun k ↦ Real.log (c ^ 2) / (N k : Real))
        atTop (nhds 0) := tendsto_const_nhds.div_atTop hNreal
    have hsum := hfirst.add hlogN
    simpa only [add_zero] using hsum.congr'
      (Eventually.of_forall fun k ↦ (hlogMul k).symm)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hconst hupper
  · filter_upwards with k
    let P := sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheRoots hc r k)
      (sixVertexFixedChargeBetheCentralIndex r k)
    have hb := sixVertexFixedOddChargeBethePrefactor_bounds hc hr k
    have hP : 0 < P := hC.trans hb.1
    have hlog : Real.log C ≤ Real.log P := by
      exact Real.strictMonoOn_log.monotoneOn hC hP hb.1.le
    have hNpos : 0 < (N k : Real) := by
      exact_mod_cast sixVertexFourWidth_pos r k
    exact div_le_div_of_nonneg_right hlog hNpos.le
  · filter_upwards with k
    let P := sixVertexZeroPhaseBethePrefactor c (sixVertexFourWidth r k)
      (sixVertexFixedChargeBetheRoots hc r k)
      (sixVertexFixedChargeBetheCentralIndex r k)
    have hb := sixVertexFixedOddChargeBethePrefactor_bounds hc hr k
    have hP : 0 < P := hC.trans hb.1
    have hUpper : 0 < c ^ 2 * (N k : Real) := by
      have hc2pos : 0 < c ^ 2 := sq_pos_of_pos (by linarith)
      have hNpos : 0 < (N k : Real) := by
        exact_mod_cast sixVertexFourWidth_pos r k
      positivity
    have hlog : Real.log P ≤ Real.log (c ^ 2 * (N k : Real)) := by
      exact Real.strictMonoOn_log.monotoneOn hP hUpper hb.2
    have hNpos : 0 < (N k : Real) := by
      exact_mod_cast sixVertexFourWidth_pos r k
    exact div_le_div_of_nonneg_right hlog hNpos.le

end

end StatMech.FrontierD
