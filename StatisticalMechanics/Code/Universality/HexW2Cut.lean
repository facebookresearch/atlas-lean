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
import Code.Universality.HexInfraCut
import Code.Universality.HexSurgerySeams
import Code.Universality.HexInjections
import Code.Universality.HexBridgeRecon

namespace StatMech.Universality

open HexWalk List Filter
open scoped BigOperators Real













noncomputable def hexW2_partialDisp (h0 : ℤ) (ts : List ℤ) (k : ℕ) : ℝ :=
  hexInfra_stepReSum h0 (ts.take k)
    + (HexWalk.halfStep (hexInfra_headAccum h0 (ts.take k))).re












theorem hexW2_exists_firstArgmax (h0 : ℤ) (ts : List ℤ) :
    ∃ cp, cp ≤ ts.length
      ∧ (∀ k ≤ ts.length, hexW2_partialDisp h0 ts k ≤ hexW2_partialDisp h0 ts cp)
      ∧ (∀ k, k < cp → hexW2_partialDisp h0 ts k < hexW2_partialDisp h0 ts cp) := by
  classical
  set n := ts.length with hn
  set f := fun k => hexW2_partialDisp h0 ts k with hf
  obtain ⟨c, hc_mem, hc_max⟩ :=
    Finset.exists_max_image (Finset.range (n + 1)) f ⟨0, by simp⟩
  rw [Finset.mem_range] at hc_mem
  set M := f c with hM
  have hmaxval : ∀ k ≤ n, f k ≤ M := fun k hk =>
    hc_max k (Finset.mem_range.mpr (by omega))
  have hexP : ∃ k, k ≤ n ∧ f k = M := ⟨c, by omega, rfl⟩
  refine ⟨Nat.find hexP, (Nat.find_spec hexP).1, ?_, ?_⟩
  · intro k hk
    show f k ≤ f (Nat.find hexP)
    rw [(Nat.find_spec hexP).2]
    exact hmaxval k hk
  · intro k hkcp
    show f k < f (Nat.find hexP)
    have hnotP : ¬ (k ≤ n ∧ f k = M) :=
      (Nat.lt_find_iff hexP k).mp hkcp k le_rfl
    have hkn : k ≤ n := by have := Nat.find_spec hexP; omega
    have hle : f k ≤ M := hmaxval k hkn
    rw [(Nat.find_spec hexP).2]
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd ⟨hkn, h⟩ hnotP




noncomputable def hexW2_cutPos (h0 : ℤ) (ts : List ℤ) : ℕ :=
  (hexW2_exists_firstArgmax h0 ts).choose


theorem hexW2_cutPos_le (h0 : ℤ) (ts : List ℤ) :
    hexW2_cutPos h0 ts ≤ ts.length :=
  (hexW2_exists_firstArgmax h0 ts).choose_spec.1



theorem hexW2_cutPos_max (h0 : ℤ) (ts : List ℤ) (k : ℕ) (hk : k ≤ ts.length) :
    hexW2_partialDisp h0 ts k ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts) :=
  (hexW2_exists_firstArgmax h0 ts).choose_spec.2.1 k hk



theorem hexW2_cutPos_first (h0 : ℤ) (ts : List ℤ) (k : ℕ) (hk : k < hexW2_cutPos h0 ts) :
    hexW2_partialDisp h0 ts k < hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts) :=
  (hexW2_exists_firstArgmax h0 ts).choose_spec.2.2 k hk














theorem hexW2_prefix_reachesWidth (a : ℂ) (h0 : ℤ) (T : ℕ) (ts : List ℤ)
    (hT : (T : ℝ) ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts)) :
    hexWall3_ReachesWidth a h0 T (ts.take (hexW2_cutPos h0 ts)) :=
  hexInfra_prefix_reachesWidth a h0 T ts (hexW2_cutPos h0 ts) hT






noncomputable def hexW2_cutWidth (h0 : ℤ) (ts : List ℤ) : ℕ :=
  ⌊hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts)⌋₊




theorem hexW2_prefix_reachesCutWidth (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hnn : 0 ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts)) :
    hexWall3_ReachesWidth a h0 (hexW2_cutWidth h0 ts) (ts.take (hexW2_cutPos h0 ts)) :=
  hexW2_prefix_reachesWidth a h0 (hexW2_cutWidth h0 ts) ts (Nat.floor_le hnn)




theorem hexW2_cutWidth_pos (h0 : ℤ) (ts : List ℤ)
    (hone : (1 : ℝ) ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts)) :
    0 < hexW2_cutWidth h0 ts := by
  rw [hexW2_cutWidth, Nat.floor_pos]; exact hone





theorem hexW2_prefix_legal (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hleg : (HexWalk.ofTurns a h0 ts).IsLegalSAW) :
    (HexWalk.ofTurns a h0 (ts.take (hexW2_cutPos h0 ts))).IsLegalSAW :=
  hexCut_legal_take a h0 ts (hexW2_cutPos h0 ts) hleg







theorem hexW2_suffix_legal (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hleg : (HexWalk.ofTurns a h0 ts).IsLegalSAW) :
    (HexWalk.ofTurns (hexDropMid a h0 ts (hexW2_cutPos h0 ts))
        (h0 + (ts.take (hexW2_cutPos h0 ts)).sum)
        (ts.drop (hexW2_cutPos h0 ts))).IsLegalSAW :=
  hexCut_legal_drop a h0 ts (hexW2_cutPos h0 ts) (hexW2_cutPos_le h0 ts) hleg














theorem hexW2_displacement_split (h0 : ℤ) (ts : List ℤ) :
    hexInfra_stepReSum h0 ts
      = hexInfra_stepReSum h0 (ts.take (hexW2_cutPos h0 ts))
        + hexInfra_stepReSum (hexInfra_headAccum h0 (ts.take (hexW2_cutPos h0 ts)))
            (ts.drop (hexW2_cutPos h0 ts)) :=
  hexInfra_stepReSum_take_drop h0 ts (hexW2_cutPos h0 ts)










theorem hexW2_partialDisp_zero (h0 : ℤ) (ts : List ℤ) :
    hexW2_partialDisp h0 ts 0 = (HexWalk.halfStep h0).re := by
  unfold hexW2_partialDisp
  simp






theorem hexW2_cutPos_pos (h0 : ℤ) (ts : List ℤ)
    (hone : (1 : ℝ) ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts)) :
    0 < hexW2_cutPos h0 ts := by
  rcases Nat.eq_zero_or_pos (hexW2_cutPos h0 ts) with hcp0 | hpos
  swap
  · exact hpos
  exfalso
  rw [hcp0] at hone
  rw [hexW2_partialDisp_zero] at hone
  have hhalf : (HexWalk.halfStep h0).re ≤ 1 / 2 := hexInfra_halfStep_re_le h0
  linarith



theorem hexW2_prefix_content_ne (h0 : ℤ) (ts : List ℤ)
    (hone : (1 : ℝ) ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts)) :
    ts.take (hexW2_cutPos h0 ts) ≠ [] := by
  have hpos := hexW2_cutPos_pos h0 ts hone
  have hcple := hexW2_cutPos_le h0 ts
  intro hnil
  rw [List.take_eq_nil_iff] at hnil
  rcases hnil with h | h
  · omega
  · subst h; simp at hcple; omega















noncomputable def hexW2_prefixBridge (h0 : ℤ) (ts : List ℤ)
    (hone : (1 : ℝ) ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts)) : HexBridge where
  width := hexW2_cutWidth h0 ts
  width_pos := hexW2_cutWidth_pos h0 ts hone
  content := ts.take (hexW2_cutPos h0 ts)
  content_ne := hexW2_prefix_content_ne h0 ts hone

@[simp] theorem hexW2_prefixBridge_width (h0 : ℤ) (ts : List ℤ) (hone) :
    (hexW2_prefixBridge h0 ts hone).width = hexW2_cutWidth h0 ts := rfl

@[simp] theorem hexW2_prefixBridge_content (h0 : ℤ) (ts : List ℤ) (hone) :
    (hexW2_prefixBridge h0 ts hone).content = ts.take (hexW2_cutPos h0 ts) := rfl








theorem hexW2_prefixBridge_reaches_legal (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hone : (1 : ℝ) ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts))
    (hleg : (HexWalk.ofTurns a h0 ts).IsLegalSAW) :
    hexWall3_ReachesWidth a h0 (hexW2_prefixBridge h0 ts hone).width
        (hexW2_prefixBridge h0 ts hone).content
      ∧ (HexWalk.ofTurns a h0 (hexW2_prefixBridge h0 ts hone).content).IsLegalSAW := by
  refine ⟨?_, ?_⟩
  · rw [hexW2_prefixBridge_width, hexW2_prefixBridge_content]
    exact hexW2_prefix_reachesCutWidth a h0 ts (le_trans zero_le_one hone)
  · rw [hexW2_prefixBridge_content]
    exact hexW2_prefix_legal a h0 ts hleg







theorem hexW2_prefixBridge_mem (a : ℂ) (h0 : ℤ) (ts : List ℤ)
    (hone : (1 : ℝ) ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts))
    (hleg : (HexWalk.ofTurns a h0 ts).IsLegalSAW) :
    hexWall3_mem a h0 (hexW2_prefixBridge h0 ts hone).width
      (hexW2_prefixBridge h0 ts hone).content :=
  let hb := hexW2_prefixBridge_reaches_legal a h0 ts hone hleg
  hexWall3_bridge_mem a h0 (hexW2_prefixBridge h0 ts hone) hb.1 hb.2


















theorem hexW2_singleRight_partialDisp_one :
    hexW2_partialDisp 0 [(-1 : ℤ)] 1
      = (HexWalk.halfStep 0).re + 2 * (HexWalk.halfStep (-1)).re := by
  unfold hexW2_partialDisp
  rw [List.take_succ_cons, List.take_zero]
  exact hexInfra_singleRight_stepReSum






theorem hexW2_singleRight_positiveWidth :
    (1 : ℝ) ≤ hexW2_partialDisp 0 [(-1 : ℤ)] (hexW2_cutPos 0 [(-1 : ℤ)]) := by
  have hdisp1 : (1 : ℝ) ≤ hexW2_partialDisp 0 [(-1 : ℤ)] 1 := by
    rw [hexW2_singleRight_partialDisp_one, hexWall3_halfStep_re, hexWall3_halfStep_re]
    have e0 : Real.pi / 6 + ((0 : ℤ) : ℝ) * (Real.pi / 3) = Real.pi / 6 := by push_cast; ring
    have em1 : Real.pi / 6 + ((-1 : ℤ) : ℝ) * (Real.pi / 3) = -(Real.pi / 6) := by
      push_cast; ring
    rw [e0, em1, Real.cos_neg, Real.cos_pi_div_six]
    have hs3 : (4 : ℝ) / 3 ≤ Real.sqrt 3 := by
      rw [show (4 : ℝ) / 3 = Real.sqrt ((4 / 3) ^ 2) by rw [Real.sqrt_sq]; norm_num]
      exact Real.sqrt_le_sqrt (by norm_num)
    nlinarith [hs3]
  have hmax := hexW2_cutPos_max 0 [(-1 : ℤ)] 1 (by simp)
  linarith







theorem hexW2_singleRight_cutPos_pos :
    0 < hexW2_cutPos 0 [(-1 : ℤ)] :=
  hexW2_cutPos_pos 0 [(-1 : ℤ)] hexW2_singleRight_positiveWidth








theorem hexW2_singleRight_prefixBridge_mem (a : ℂ) :
    hexWall3_mem a 0
      (hexW2_prefixBridge 0 [(-1 : ℤ)] hexW2_singleRight_positiveWidth).width
      (hexW2_prefixBridge 0 [(-1 : ℤ)] hexW2_singleRight_positiveWidth).content :=
  hexW2_prefixBridge_mem a 0 [(-1 : ℤ)] hexW2_singleRight_positiveWidth
    (hexWall3_isLegalSAW_witness a)




























noncomputable def hexW2_highestCut (a : ℂ) (h0 : ℤ) {x : ℝ} (hx : 0 < x)
    (memD : List ℤ → Prop)
    (B : Type)
    (wtB : B → ℝ) (wtB_nn : ∀ b, 0 ≤ wtB b)
    (split : {ts // memD ts} → B × B)
    (hwtB1 : ∀ d, wtB (split d).1 = hexSAWwt a h0 x (d.1.take (hexW2_cutPos h0 d.1)))
    (hwtB2 : ∀ d, wtB (split d).2 =
      hexSAWwt (hexDropMid a h0 d.1 (hexW2_cutPos h0 d.1))
        (h0 + (d.1.take (hexW2_cutPos h0 d.1)).sum) x (d.1.drop (hexW2_cutPos h0 d.1)))
    (split_inj : Function.Injective split)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 x d.1))
    (hBsum : Summable wtB) :
    HexHighestCut x⁻¹ :=
  hexHighestCutClosed a h0 hx memD B wtB wtB_nn
    (fun d => hexW2_cutPos h0 d.1)
    (fun d => hexW2_cutPos_le h0 d.1)
    split hwtB1 hwtB2 split_inj hDsum hBsum






noncomputable def hexW2_highestCut_chi (a : ℂ) (h0 : ℤ)
    (memD : List ℤ → Prop)
    (B : Type)
    (wtB : B → ℝ) (wtB_nn : ∀ b, 0 ≤ wtB b)
    (split : {ts // memD ts} → B × B)
    (hwtB1 : ∀ d, wtB (split d).1 = hexSAWwt a h0 hexChiE (d.1.take (hexW2_cutPos h0 d.1)))
    (hwtB2 : ∀ d, wtB (split d).2 =
      hexSAWwt (hexDropMid a h0 d.1 (hexW2_cutPos h0 d.1))
        (h0 + (d.1.take (hexW2_cutPos h0 d.1)).sum) hexChiE (d.1.drop (hexW2_cutPos h0 d.1)))
    (split_inj : Function.Injective split)
    (hDsum : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
    (hBsum : Summable wtB) :
    HexHighestCut hexChiE⁻¹ :=
  hexW2_highestCut a h0 hexChiE_pos memD B wtB wtB_nn split hwtB1 hwtB2 split_inj hDsum hBsum

end StatMech.Universality
