/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































































import Mathlib
import Code.Universality.HexW2Weight

namespace StatMech.Universality

open HexWalk List
open scoped BigOperators













theorem hexW2S_verticesAux_translate (c m : ℂ) (h : ℤ) (ts : List ℤ) :
    HexWalk.verticesAux (m + c) h ts = (HexWalk.verticesAux m h ts).map (· + c) := by
  induction ts generalizing m h with
  | nil =>
    rw [HexWalk.verticesAux_nil, HexWalk.verticesAux_nil, List.map_singleton]
    ring_nf
  | cons t ts ih =>
    rw [HexWalk.verticesAux_cons, HexWalk.verticesAux_cons, List.map_cons]
    congr 1
    · ring
    · rw [show m + c + HexWalk.halfStep h + HexWalk.halfStep (h + t)
          = (m + HexWalk.halfStep h + HexWalk.halfStep (h + t)) + c by ring]
      exact ih _ _




theorem hexW2S_isSAW_translate (c m : ℂ) (h : ℤ) (ts : List ℤ) :
    (HexWalk.ofTurns (m + c) h ts).IsSAW ↔ (HexWalk.ofTurns m h ts).IsSAW := by
  unfold HexWalk.IsSAW HexWalk.vertices HexWalk.ofTurns
  simp only
  rw [hexW2S_verticesAux_translate, List.nodup_map_iff (add_left_injective c)]




theorem hexW2S_isLegalSAW_translate (c m : ℂ) (h : ℤ) (ts : List ℤ) :
    (HexWalk.ofTurns (m + c) h ts).IsLegalSAW ↔ (HexWalk.ofTurns m h ts).IsLegalSAW := by
  unfold HexWalk.IsLegalSAW HexWalk.LegalTurns HexWalk.ofTurns
  simp only
  rw [show (HexWalk.mk (m + c) h ts).IsSAW ↔ (HexWalk.mk m h ts).IsSAW from
    hexW2S_isSAW_translate c m h ts]




theorem hexW2S_hexSAWwt_translate (c m : ℂ) (h : ℤ) (x : ℝ) (ts : List ℤ) :
    hexSAWwt (m + c) h x ts = hexSAWwt m h x ts := by
  unfold hexSAWwt
  have hiff := hexW2S_isLegalSAW_translate c m h ts
  by_cases hl : (HexWalk.ofTurns m h ts).IsLegalSAW
  · rw [if_pos (hiff.mpr hl), if_pos hl]
    rfl
  · rw [if_neg (fun hh => hl (hiff.mp hh)), if_neg hl]





theorem hexW2S_hexSAWwt_mid_indep (m m' : ℂ) (h : ℤ) (x : ℝ) (ts : List ℤ) :
    hexSAWwt m' h x ts = hexSAWwt m h x ts := by
  have := hexW2S_hexSAWwt_translate (m' - m) m h x ts
  rwa [add_sub_cancel] at this












theorem hexW2S_hexSAWwt_mono_fugacity (a : ℂ) (h0 : ℤ) {x χ : ℝ} (hx : 0 ≤ x)
    (hxχ : x ≤ χ) (ts : List ℤ) :
    hexSAWwt a h0 x ts ≤ hexSAWwt a h0 χ ts := by
  unfold hexSAWwt
  split
  · exact pow_le_pow_left₀ hx hxχ _
  · exact le_refl _









theorem hexW2S_diff_summable (a : ℂ) (h0 : ℤ) {x χ : ℝ} (hx : 0 ≤ x) (hxχ : x ≤ χ)
    (memD : List ℤ → Prop)
    (hDcrit : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 χ d.1)) :
    Summable (fun d : {ts // memD ts} => hexSAWwt a h0 x d.1) :=
  hDcrit.of_nonneg_of_le (fun d => hexSAWwt_nonneg a h0 hx d.1)
    (fun d => hexW2S_hexSAWwt_mono_fugacity a h0 hx hxχ d.1)














theorem hexW2S_trivialHalf_wt (mid : ℂ) (h0 : ℤ) (x : ℝ) :
    hexW2_halfWt x ⟨mid, h0, []⟩ = x := by
  change hexSAWwt mid h0 x [] = x
  rw [hexSAWwt_of_isLegalSAW mid h0 x (HexWalk.trivialWalk_isLegalSAW mid h0)]
  rw [show (HexWalk.ofTurns mid h0 []).numVertices = 1 from rfl, pow_one]








theorem hexW2S_halfWt_not_summable {x : ℝ} (hx : 0 < x) :
    ¬ Summable (hexW2_halfWt x) := by
  intro hsum
  have hc : (Function.support (hexW2_halfWt x)).Countable := hsum.countable_support
  
  set g : ℝ → HexW2Half := fun t => ⟨(t : ℂ), 0, []⟩ with hg
  have hginj : Function.Injective g := by
    intro a b hab
    have : ((a : ℂ)) = ((b : ℂ)) := (HexW2Half.mk.injEq ..).mp hab |>.1
    exact Complex.ofReal_injective this
  have hsub : Set.range g ⊆ Function.support (hexW2_halfWt x) := by
    rintro _ ⟨t, rfl⟩
    change hexW2_halfWt x ⟨(t : ℂ), 0, []⟩ ≠ 0
    rw [hexW2S_trivialHalf_wt]; exact ne_of_gt hx
  have hrangeC : (Set.range g).Countable := hc.mono hsub
  haveI : Countable (Set.range g) := hrangeC.to_subtype
  have : Countable ℝ :=
    Function.Injective.countable (f := Set.rangeFactorization g)
      (fun a b hab => hginj (congrArg Subtype.val hab))
  exact not_countable this














structure HexW2SBridge where
  
  head : ℤ
  
  turns : List ℤ




noncomputable def hexW2S_bridgeWt (x : ℝ) (b : HexW2SBridge) : ℝ :=
  hexSAWwt 0 b.head x b.turns


theorem hexW2S_bridgeWt_nonneg {x : ℝ} (hx : 0 ≤ x) (b : HexW2SBridge) :
    0 ≤ hexW2S_bridgeWt x b :=
  hexSAWwt_nonneg 0 b.head hx b.turns






theorem hexW2S_bridgeWt_eq_halfWt (x : ℝ) (mid : ℂ) (head : ℤ) (turns : List ℤ) :
    hexW2S_bridgeWt x ⟨head, turns⟩ = hexW2_halfWt x ⟨mid, head, turns⟩ := by
  change hexSAWwt 0 head x turns = hexSAWwt mid head x turns
  exact hexW2S_hexSAWwt_mid_indep mid 0 head x turns









theorem hexW2S_bridge_summable {x χ : ℝ} (hx : 0 ≤ x) (hxχ : x ≤ χ)
    (bridgeMem : ℤ × List ℤ → Prop)
    (hBcrit : Summable (fun b : {b // bridgeMem b} => hexSAWwt 0 b.1.1 χ b.1.2)) :
    Summable (fun b : {b // bridgeMem b} => hexW2S_bridgeWt x ⟨b.1.1, b.1.2⟩) :=
  hBcrit.of_nonneg_of_le (fun b => hexSAWwt_nonneg 0 b.1.1 hx b.1.2)
    (fun b => hexW2S_hexSAWwt_mono_fugacity 0 b.1.1 hx hxχ b.1.2)


















noncomputable def hexW2S_highestCut_summClosed (a : ℂ) (h0 : ℤ) {x χ : ℝ} (hx : 0 < x)
    (hxle : x ≤ χ)
    (memD : List ℤ → Prop)
    (bridgeMem : ℤ × List ℤ → Prop)
    (split : {ts // memD ts} → {b : ℤ × List ℤ // bridgeMem b} × {b : ℤ × List ℤ // bridgeMem b})
    (hwtB1 : ∀ d, hexW2S_bridgeWt x ⟨(split d).1.1.1, (split d).1.1.2⟩
        = hexSAWwt a h0 x (d.1.take (hexW2_cutPos h0 d.1)))
    (hwtB2 : ∀ d, hexW2S_bridgeWt x ⟨(split d).2.1.1, (split d).2.1.2⟩
        = hexSAWwt (hexDropMid a h0 d.1 (hexW2_cutPos h0 d.1))
            (h0 + (d.1.take (hexW2_cutPos h0 d.1)).sum) x (d.1.drop (hexW2_cutPos h0 d.1)))
    (split_inj : Function.Injective split)
    (hDcrit : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 χ d.1))
    (hBcrit : Summable (fun b : {b : ℤ × List ℤ // bridgeMem b} => hexSAWwt 0 b.1.1 χ b.1.2)) :
    HexHighestCut x⁻¹ :=
  hexW2_highestCut a h0 hx memD
    ({b : ℤ × List ℤ // bridgeMem b})
    (fun b => hexW2S_bridgeWt x ⟨b.1.1, b.1.2⟩)
    (fun b => hexW2S_bridgeWt_nonneg (le_of_lt hx) ⟨b.1.1, b.1.2⟩)
    split hwtB1 hwtB2 split_inj
    (hexW2S_diff_summable a h0 (le_of_lt hx) hxle memD hDcrit)
    (hexW2S_bridge_summable (le_of_lt hx) hxle bridgeMem hBcrit)










noncomputable def hexW2S_highestCut_summClosed_chi (a : ℂ) (h0 : ℤ)
    (memD : List ℤ → Prop)
    (bridgeMem : ℤ × List ℤ → Prop)
    (split : {ts // memD ts} → {b : ℤ × List ℤ // bridgeMem b} × {b : ℤ × List ℤ // bridgeMem b})
    (hwtB1 : ∀ d, hexW2S_bridgeWt hexChiE ⟨(split d).1.1.1, (split d).1.1.2⟩
        = hexSAWwt a h0 hexChiE (d.1.take (hexW2_cutPos h0 d.1)))
    (hwtB2 : ∀ d, hexW2S_bridgeWt hexChiE ⟨(split d).2.1.1, (split d).2.1.2⟩
        = hexSAWwt (hexDropMid a h0 d.1 (hexW2_cutPos h0 d.1))
            (h0 + (d.1.take (hexW2_cutPos h0 d.1)).sum) hexChiE (d.1.drop (hexW2_cutPos h0 d.1)))
    (split_inj : Function.Injective split)
    (hDcrit : Summable (fun d : {ts // memD ts} => hexSAWwt a h0 hexChiE d.1))
    (hBcrit : Summable (fun b : {b : ℤ × List ℤ // bridgeMem b} =>
      hexSAWwt 0 b.1.1 hexChiE b.1.2)) :
    HexHighestCut hexChiE⁻¹ :=
  hexW2S_highestCut_summClosed a h0 hexChiE_pos (le_refl hexChiE) memD bridgeMem split
    hwtB1 hwtB2 split_inj hDcrit hBcrit














theorem hexW2S_diff_summable_of_finite (a : ℂ) (h0 : ℤ) {x χ : ℝ} (hx : 0 ≤ x)
    (hxχ : x ≤ χ) (memD : List ℤ → Prop) [Finite {ts // memD ts}] :
    Summable (fun d : {ts // memD ts} => hexSAWwt a h0 x d.1) :=
  hexW2S_diff_summable a h0 hx hxχ memD Summable.of_finite






theorem hexW2S_bridge_summable_of_finite {x χ : ℝ} (hx : 0 ≤ x) (hxχ : x ≤ χ)
    (bridgeMem : ℤ × List ℤ → Prop) [Finite {b // bridgeMem b}] :
    Summable (fun b : {b // bridgeMem b} => hexW2S_bridgeWt x ⟨b.1.1, b.1.2⟩) :=
  hexW2S_bridge_summable hx hxχ bridgeMem Summable.of_finite

end StatMech.Universality
