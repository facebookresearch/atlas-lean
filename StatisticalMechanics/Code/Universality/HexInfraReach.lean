/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































import Mathlib
import Code.Universality.HexLattice
import Code.Universality.HexWall3
import Code.Universality.HexInfraDisplacement
import Code.Universality.HexBridgeDecomp

namespace StatMech.Universality

open HexWalk List
open scoped BigOperators Real












noncomputable def hexInfra_disp (h0 : ℤ) (ts : List ℤ) : ℝ :=
  hexInfra_stepReSum h0 ts + (HexWalk.halfStep (hexInfra_headAccum h0 ts)).re



theorem hexInfra_lastVertex_re (a : ℂ) (h0 : ℤ) (ts : List ℤ) :
    (hexInfra_midAccum a h0 ts + HexWalk.halfStep (hexInfra_headAccum h0 ts)).re
      = a.re + hexInfra_disp h0 ts := by
  rw [hexInfra_ofTurns_last_re, hexInfra_disp, add_assoc]


















def hexInfra_IsDispBridge (h0 : ℤ) (b : HexBridge) : Prop :=
  (b.width : ℝ) ≤ hexInfra_disp h0 b.content









theorem hexInfra_reachesWidth_of_dispBridge (a : ℂ) (h0 : ℤ) (b : HexBridge)
    (hb : hexInfra_IsDispBridge h0 b) :
    hexWall3_ReachesWidth a h0 b.width b.content :=
  hexInfra_reachesWidth_of_last_re a h0 b.width b.content hb










theorem hexInfra_dispBridge_colDomination (a : ℂ) (h0 : ℤ) (b : HexBridge) (χ : ℝ)
    (hsummable hle_one) {x : ℝ}
    (hx0 : 0 ≤ x) (hχ : 0 < χ) (hxχ : x ≤ χ)
    (hb : hexInfra_IsDispBridge h0 b)
    (hSAW : (HexWalk.ofTurns a h0 b.content).IsLegalSAW) :
    x ^ (HexWalk.ofTurns a h0 b.content).numVertices
      ≤ (hexWall3_column a h0 b.width χ hsummable hle_one).colSum x :=
  hexWall3_colDomination_uncond a h0 b χ hsummable hle_one hx0 hχ hxχ
    (hexInfra_reachesWidth_of_dispBridge a h0 b hb) hSAW












noncomputable def hexInfra_dispBridgeOfContent (h0 : ℤ) (ts : List ℤ)
    (hne : ts ≠ []) (hpos : 0 < ⌊hexInfra_disp h0 ts⌋₊) : HexBridge where
  width := ⌊hexInfra_disp h0 ts⌋₊
  width_pos := hpos
  content := ts
  content_ne := hne

@[simp] theorem hexInfra_dispBridgeOfContent_content (h0 : ℤ) (ts : List ℤ) (hne hpos) :
    (hexInfra_dispBridgeOfContent h0 ts hne hpos).content = ts := rfl

@[simp] theorem hexInfra_dispBridgeOfContent_width (h0 : ℤ) (ts : List ℤ) (hne hpos) :
    (hexInfra_dispBridgeOfContent h0 ts hne hpos).width = ⌊hexInfra_disp h0 ts⌋₊ := rfl





theorem hexInfra_dispBridgeOfContent_isDispBridge (h0 : ℤ) (ts : List ℤ) (hne hpos)
    (hd : 0 ≤ hexInfra_disp h0 ts) :
    hexInfra_IsDispBridge h0 (hexInfra_dispBridgeOfContent h0 ts hne hpos) := by
  unfold hexInfra_IsDispBridge
  rw [hexInfra_dispBridgeOfContent_width, hexInfra_dispBridgeOfContent_content]
  exact Nat.floor_le hd






theorem hexInfra_dispBridgeOfContent_reaches (a : ℂ) (h0 : ℤ) (ts : List ℤ) (hne hpos)
    (hd : 0 ≤ hexInfra_disp h0 ts) :
    hexWall3_ReachesWidth a h0
      (hexInfra_dispBridgeOfContent h0 ts hne hpos).width
      (hexInfra_dispBridgeOfContent h0 ts hne hpos).content :=
  hexInfra_reachesWidth_of_dispBridge a h0 (hexInfra_dispBridgeOfContent h0 ts hne hpos)
    (hexInfra_dispBridgeOfContent_isDispBridge h0 ts hne hpos hd)











theorem hexInfra_disp_singleRight :
    hexInfra_disp 0 [(-1 : ℤ)] = (HexWalk.halfStep 0).re + 2 * (HexWalk.halfStep (-1)).re :=
  hexInfra_singleRight_stepReSum


theorem hexInfra_disp_singleRight_ge_one : (1 : ℝ) ≤ hexInfra_disp 0 [(-1 : ℤ)] := by
  rw [hexInfra_disp_singleRight, hexWall3_halfStep_re, hexWall3_halfStep_re]
  have e0 : Real.pi / 6 + ((0 : ℤ) : ℝ) * (Real.pi / 3) = Real.pi / 6 := by push_cast; ring
  have em1 : Real.pi / 6 + ((-1 : ℤ) : ℝ) * (Real.pi / 3) = -(Real.pi / 6) := by push_cast; ring
  rw [e0, em1, Real.cos_neg, Real.cos_pi_div_six]
  have hs3 : (4 : ℝ) / 3 ≤ Real.sqrt 3 := by
    rw [show (4 : ℝ) / 3 = Real.sqrt ((4 / 3) ^ 2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by norm_num)
  nlinarith [hs3]


theorem hexInfra_disp_singleRight_lt_two : hexInfra_disp 0 [(-1 : ℤ)] < 2 := by
  rw [hexInfra_disp_singleRight, hexWall3_halfStep_re, hexWall3_halfStep_re]
  have e0 : Real.pi / 6 + ((0 : ℤ) : ℝ) * (Real.pi / 3) = Real.pi / 6 := by push_cast; ring
  have em1 : Real.pi / 6 + ((-1 : ℤ) : ℝ) * (Real.pi / 3) = -(Real.pi / 6) := by push_cast; ring
  rw [e0, em1, Real.cos_neg, Real.cos_pi_div_six]
  have hs3 : Real.sqrt 3 ≤ 2 := by
    rw [show (2 : ℝ) = Real.sqrt (2 ^ 2) by rw [Real.sqrt_sq]; norm_num]
    exact Real.sqrt_le_sqrt (by norm_num)
  nlinarith [hs3]




theorem hexInfra_floor_disp_singleRight : ⌊hexInfra_disp 0 [(-1 : ℤ)]⌋₊ = 1 := by
  have hle : (1 : ℝ) ≤ hexInfra_disp 0 [(-1 : ℤ)] := hexInfra_disp_singleRight_ge_one
  have hlt : hexInfra_disp 0 [(-1 : ℤ)] < 2 := hexInfra_disp_singleRight_lt_two
  rw [Nat.floor_eq_iff (by linarith)]
  exact ⟨by push_cast; linarith, by push_cast; linarith⟩




noncomputable def hexInfra_witnessDispBridge : HexBridge :=
  hexInfra_dispBridgeOfContent 0 [(-1 : ℤ)] (by simp)
    (by rw [hexInfra_floor_disp_singleRight]; exact one_pos)

@[simp] theorem hexInfra_witnessDispBridge_width : hexInfra_witnessDispBridge.width = 1 := by
  unfold hexInfra_witnessDispBridge
  rw [hexInfra_dispBridgeOfContent_width, hexInfra_floor_disp_singleRight]

@[simp] theorem hexInfra_witnessDispBridge_content :
    hexInfra_witnessDispBridge.content = [(-1 : ℤ)] := rfl



theorem hexInfra_singleRight_isDispBridge :
    hexInfra_IsDispBridge 0 hexInfra_witnessDispBridge :=
  hexInfra_dispBridgeOfContent_isDispBridge 0 [(-1 : ℤ)] _ _
    (le_trans (by norm_num) hexInfra_disp_singleRight_ge_one)





theorem hexInfra_witnessDispBridge_reaches (a : ℂ) :
    hexWall3_ReachesWidth a 0 hexInfra_witnessDispBridge.width
      hexInfra_witnessDispBridge.content :=
  hexInfra_reachesWidth_of_dispBridge a 0 hexInfra_witnessDispBridge
    hexInfra_singleRight_isDispBridge

end StatMech.Universality
