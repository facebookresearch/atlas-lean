/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















import Code.Universality.HexW2Weight

namespace StatMech.Universality

open HexWalk


def hexHW_LiteralPositiveWalk (a : ℂ) (h0 : ℤ) (ts : List ℤ) : Prop :=
  (HexWalk.ofTurns a h0 ts).IsLegalSAW ∧
    (1 : ℝ) ≤ hexW2_partialDisp h0 ts (hexW2_cutPos h0 ts)


noncomputable def hexHW_literalSplit (a : ℂ) (h0 : ℤ) :
    {ts : List ℤ // hexHW_LiteralPositiveWalk a h0 ts} → HexW2Half × HexW2Half :=
  hexW2_split a h0 (hexHW_LiteralPositiveWalk a h0)



theorem hexHW_literalSplit_injective (a : ℂ) (h0 : ℤ) :
    Function.Injective (hexHW_literalSplit a h0) :=
  hexW2_split_injective a h0 (hexHW_LiteralPositiveWalk a h0)














theorem hexHW_literal_bridge_decomp (a : ℂ) (h0 : ℤ)
    (d : {ts : List ℤ // hexHW_LiteralPositiveWalk a h0 ts}) :
    let cp := hexW2_cutPos h0 d.1
    let b := hexW2_prefixBridge h0 d.1 d.2.2
    d.1 = (hexHW_literalSplit a h0 d).1.turns ++
        (hexHW_literalSplit a h0 d).2.turns
      ∧ b.content = (hexHW_literalSplit a h0 d).1.turns
      ∧ 0 < b.width
      ∧ hexWall3_ReachesWidth a h0 b.width b.content
      ∧ (HexWalk.ofTurns a h0 b.content).IsLegalSAW
      ∧ (HexWalk.ofTurns
          (hexDropMid a h0 d.1 cp)
          (h0 + (d.1.take cp).sum)
          (hexHW_literalSplit a h0 d).2.turns).IsLegalSAW
      ∧ (∀ k ≤ d.1.length,
          hexW2_partialDisp h0 d.1 k ≤ hexW2_partialDisp h0 d.1 cp)
      ∧ (∀ k, k < cp →
          hexW2_partialDisp h0 d.1 k < hexW2_partialDisp h0 d.1 cp) := by
  dsimp only
  have hleg : (HexWalk.ofTurns a h0 d.1).IsLegalSAW := d.2.1
  have hone : (1 : ℝ) ≤
      hexW2_partialDisp h0 d.1 (hexW2_cutPos h0 d.1) := d.2.2
  have hb := hexW2_prefixBridge_reaches_legal a h0 d.1 hone hleg
  refine ⟨?_, rfl, (hexW2_prefixBridge h0 d.1 hone).width_pos,
    hb.1, hb.2, ?_, ?_, ?_⟩
  · exact (List.take_append_drop (hexW2_cutPos h0 d.1) d.1).symm
  · exact hexW2_suffix_legal a h0 d.1 hleg
  · intro k hk
    exact hexW2_cutPos_max h0 d.1 k hk
  · intro k hk
    exact hexW2_cutPos_first h0 d.1 k hk



theorem hexHW_literal_bridge_decomp_injective (a : ℂ) (h0 : ℤ) :
    Function.Injective (hexHW_literalSplit a h0) ∧
      ∀ d : {ts : List ℤ // hexHW_LiteralPositiveWalk a h0 ts},
        let cp := hexW2_cutPos h0 d.1
        let b := hexW2_prefixBridge h0 d.1 d.2.2
        d.1 = (hexHW_literalSplit a h0 d).1.turns ++
            (hexHW_literalSplit a h0 d).2.turns
          ∧ b.content = (hexHW_literalSplit a h0 d).1.turns
          ∧ 0 < b.width
          ∧ hexWall3_ReachesWidth a h0 b.width b.content
          ∧ (HexWalk.ofTurns a h0 b.content).IsLegalSAW
          ∧ (HexWalk.ofTurns
              (hexDropMid a h0 d.1 cp)
              (h0 + (d.1.take cp).sum)
              (hexHW_literalSplit a h0 d).2.turns).IsLegalSAW
          ∧ (∀ k ≤ d.1.length,
              hexW2_partialDisp h0 d.1 k ≤ hexW2_partialDisp h0 d.1 cp)
          ∧ (∀ k, k < cp →
              hexW2_partialDisp h0 d.1 k < hexW2_partialDisp h0 d.1 cp) :=
  ⟨hexHW_literalSplit_injective a h0, hexHW_literal_bridge_decomp a h0⟩

end StatMech.Universality
