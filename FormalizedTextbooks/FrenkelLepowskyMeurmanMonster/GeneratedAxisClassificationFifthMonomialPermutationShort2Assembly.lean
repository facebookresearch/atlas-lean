/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort2Packet0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort2Packet1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort2Packet2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort2Packet3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort2Packet4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort2Packet5
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort2Packet6
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort2Packet7
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort2PairPacket0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort2PairPacket1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort2PairPacket2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort2PairPacket3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort2PairPacket4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort2PairPacket5
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort2PairPacket6
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort2PairPacket7
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort2PairPacket8
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort2PairPacket9
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort2PairPacket10
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShort2PairPacket11
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationWhole

/-! Complete exact physical transport and preferred phases fix the original short block. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

private def octadFamily (b : Fin 8) (a : Fin 7) : Fin 56 :=
  ⟨7 * b.val + a.val, by omega⟩

private theorem octad_rows
    (hp : representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedFifthMonomialPermutationSpinPlan 2))
    (a : Fin 7) (b : Fin 8) (e : Fin 64) :
    localShortOperator (generatedFifthMonomialPermutationCorrectedFiber 2)
      (griessConwayEncode generatedFifthAxis).2.1
        (generatedFifthXiEvenShortIndex
          (generatedFifthXiShortCachedEven (Sum.inr (octadFamily b a, e)))) =
      (griessConwayEncode generatedFifthAxis).2.1
        (generatedFifthXiEvenShortIndex
          (generatedFifthXiShortCachedEven (Sum.inr (octadFamily b a, e)))) := by
  fin_cases b
  · exact generatedFifth_permutation_short2_packet0_coordinate hp a e
  · exact generatedFifth_permutation_short2_packet1_coordinate hp a e
  · exact generatedFifth_permutation_short2_packet2_coordinate hp a e
  · exact generatedFifth_permutation_short2_packet3_coordinate hp a e
  · exact generatedFifth_permutation_short2_packet4_coordinate hp a e
  · exact generatedFifth_permutation_short2_packet5_coordinate hp a e
  · exact generatedFifth_permutation_short2_packet6_coordinate hp a e
  · exact generatedFifth_permutation_short2_packet7_coordinate hp a e

private def pairFirst (b : Fin 12) (a : Fin 2) : Fin 24 :=
  ⟨2 * b.val + a.val, by omega⟩

private theorem pair_rows
    (hp : representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedFifthMonomialPermutationSpinPlan 2))
    (s a : Fin 2) (b : Fin 12) (i : Fin 24) (hi : pairFirst b a < i) :
    let p : {p : Fin 24 × Fin 24 // p.1 < p.2} := ⟨(pairFirst b a, i), hi⟩
    localShortOperator (generatedFifthMonomialPermutationCorrectedFiber 2)
      (griessConwayEncode generatedFifthAxis).2.1
        (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven (Sum.inl (s, p)))) =
      (griessConwayEncode generatedFifthAxis).2.1
        (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven (Sum.inl (s, p)))) := by
  fin_cases b
  · exact generatedFifth_permutation_short2_pair_packet0_coordinate hp s a i hi
  · exact generatedFifth_permutation_short2_pair_packet1_coordinate hp s a i hi
  · exact generatedFifth_permutation_short2_pair_packet2_coordinate hp s a i hi
  · exact generatedFifth_permutation_short2_pair_packet3_coordinate hp s a i hi
  · exact generatedFifth_permutation_short2_pair_packet4_coordinate hp s a i hi
  · exact generatedFifth_permutation_short2_pair_packet5_coordinate hp s a i hi
  · exact generatedFifth_permutation_short2_pair_packet6_coordinate hp s a i hi
  · exact generatedFifth_permutation_short2_pair_packet7_coordinate hp s a i hi
  · exact generatedFifth_permutation_short2_pair_packet8_coordinate hp s a i hi
  · exact generatedFifth_permutation_short2_pair_packet9_coordinate hp s a i hi
  · exact generatedFifth_permutation_short2_pair_packet10_coordinate hp s a i hi
  · exact generatedFifth_permutation_short2_pair_packet11_coordinate hp s a i hi

/-- All actual short coordinates are fixed by this corrected original spatial word. -/
theorem generatedFifth_monomial_permutation_short_fixed_2
    (hp : representativeSpinPlanValid generatedFourthMonomialLetterModel
      representativeSpinIdentityModel (generatedFifthMonomialPermutationSpinPlan 2)) :
    localShortOperator (generatedFifthMonomialPermutationCorrectedFiber 2)
      (griessConwayEncode generatedFifthAxis).2.1 =
        (griessConwayEncode generatedFifthAxis).2.1 := by
  apply generatedFifth_monomial_permutation_short_fixed_of_rows 2
  · intro s p
    let b : Fin 12 := ⟨p.val.1.val / 2, by omega⟩
    let a : Fin 2 := ⟨p.val.1.val % 2, by omega⟩
    have he : pairFirst b a = p.val.1 := by
      apply Fin.ext
      dsimp [pairFirst, a, b]
      omega
    have hi : pairFirst b a < p.val.2 := by rw [he]; exact p.property
    have hpair : (⟨(pairFirst b a, p.val.2), hi⟩ :
        {p : Fin 24 × Fin 24 // p.1 < p.2}) = p := by
      apply Subtype.ext
      exact Prod.ext he rfl
    simpa only [hpair] using pair_rows hp s a b p.val.2 hi
  · intro j e
    let b : Fin 8 := ⟨j.val / 7, by omega⟩
    let a : Fin 7 := ⟨j.val % 7, by omega⟩
    have he : octadFamily b a = j := by
      apply Fin.ext
      dsimp [octadFamily, a, b]
      omega
    simpa only [he] using octad_rows hp a b e

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
