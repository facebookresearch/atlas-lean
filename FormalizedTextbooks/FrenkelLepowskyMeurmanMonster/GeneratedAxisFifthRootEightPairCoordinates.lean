/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFifthRootEightPairData

/-! Complete original real pair coordinates follow from the checked sparse source inverse. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

private theorem source_of_label (i : GeneratedAxisGlobalFifthShortPacketIndex)
    (s : Fin 2) (p : Fin 276)
    (hi : generatedAxisGlobalFifthRoot08ShortLabel i = Sum.inl (s, p)) :
    generatedFifthRootEightPairSource ⟨276 * s.val + p.val, by omega⟩ =
      (generatedAxisGlobalFifthPacketNumber i).val := by
  have h := generatedFifthRootEight_pair_source_forward (generatedAxisGlobalFifthPacketNumber i)
  change (match generatedAxisGlobalFifthRoot08ShortLabel i with
    | Sum.inl (s, p) => generatedFifthRootEightPairSource ⟨276 * s.val + p.val, by omega⟩ =
        (generatedAxisGlobalFifthPacketNumber i).val
    | Sum.inr _ => True) at h
  rw [hi] at h
  exact h

/-- The full actual incoming pair coefficient, including every original source and central sign. -/
theorem generatedFifthRootEight_incoming_pair_coordinate (s : Fin 2) (p : Fin 276) :
    (griessConwayEncode (rhoLocal generatedFifthRootEightLocal generatedFifthAxis)).2.1 (Sum.inl
      (s, p)) =
      if h : generatedFifthRootEightPairSource ⟨276 * s.val + p.val, by omega⟩ < 4136 then
        let i := generatedAxisGlobalFifthPacketFromNumber
          ⟨generatedFifthRootEightPairSource ⟨276 * s.val + p.val, by omega⟩, h⟩
        generatedAxisGlobalFifthShortPacketCoefficient i *
          qSign (generatedAxisGlobalFifthRoot08ShortPhase i)
      else 0 := by
  rw [generatedFifthRootEightLocal, generatedAxisGlobalFifthRoot08Packet_actual]
  change (∑ i : GeneratedAxisGlobalFifthShortPacketIndex,
      (generatedAxisGlobalFifthShortPacketCoefficient i *
        qSign (generatedAxisGlobalFifthRoot08ShortPhase i)) •
        Pi.single (generatedAxisGlobalFifthRoot08ShortLabel i) (1 : ℝ)) (Sum.inl (s, p)) = _
  rw [Finset.sum_apply]
  split_ifs with h
  · let n : Fin 4136 := ⟨generatedFifthRootEightPairSource ⟨276 * s.val + p.val, by omega⟩, h⟩
    let j := generatedAxisGlobalFifthPacketFromNumber n
    have hj : generatedAxisGlobalFifthRoot08ShortLabel j = Sum.inl (s, p) := by
      have hh := generatedFifthRootEight_pair_source_reverse s p h
      change generatedFifthRootEightIncomingShortLabel n = _ at hh
      change generatedFifthRootEightIncomingShortLabel (generatedAxisGlobalFifthPacketNumber j) = _
      rw [generatedAxisGlobalFifthPacketNumber_fromNumber]
      exact hh
    rw [Finset.sum_eq_single j]
    · simp only [hj, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one, j, n]
    · intro i _ hij
      have hi : generatedAxisGlobalFifthRoot08ShortLabel i ≠ Sum.inl (s, p) := by
        intro hi
        have hp := source_of_label i s p hi
        have hn : generatedAxisGlobalFifthPacketNumber i = n := by
          apply Fin.ext
          exact hp.symm
        have he := congrArg generatedAxisGlobalFifthPacketFromNumber hn
        rw [generatedAxisGlobalFifthPacketFromNumber_number] at he
        exact hij he
      simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hi.symm, mul_zero]
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    have hi : generatedAxisGlobalFifthRoot08ShortLabel i ≠ Sum.inl (s, p) := by
      intro hi
      have hp := source_of_label i s p hi
      have hb := (generatedAxisGlobalFifthPacketNumber i).isLt
      apply h
      rw [hp]
      exact hb
    simp only [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hi.symm, mul_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
