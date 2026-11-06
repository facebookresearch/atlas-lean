/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthQCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthShortOctadQ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisTriality
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisFourthQShortBasisOdd

/-! The tensor subgroup fixes the full actual fifth axis, including all short phases. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

/-- Every outgoing odd-short coordinate vanishes in the actual fifth axis. -/
theorem generatedFifth_final_odd_zero (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode generatedFifthAxis).2.1 (Sum.inr (Sum.inr (d, i))) = 0 := by
  rw [generatedFifthAxis_local_expression]
  exact generatedFourthQShortBasis_triality_odd_zero _ generatedFifth_middle_tensor_zero d i

/-- Any octad outside the 56 genuine outgoing families has zero actual short coefficient. -/
theorem generatedFifth_final_octad_zero (o : Fin 759) (e : Fin 64)
    (ho : ¬∃ j : Fin 56, generatedFifthEvenRootOctad j = o) :
    (griessConwayEncode generatedFifthAxis).2.1 (Sum.inr (Sum.inl (o, e))) = 0 := by
  rw [generatedFifthAxis_local_expression, generatedFourthQShortBasis_triality_octad]
  apply Finset.sum_eq_zero
  intro f hf
  have hz : localShortOperator generatedFifthLocalFiber
      (griessConwayEncode (sExtra (conwayShortAxis
        (Sum.inr (Sum.inl (generatedFourthOctad, 0))) 0))).2.1
          (Sum.inr (Sum.inl (o, f))) = 0 := by
    apply not_ne_iff.mp
    intro hn
    rcases (generatedFifth_middle_nonzero_iff _).mp hn with ⟨j, hj⟩ | ⟨j, hj⟩
    · simp only [generatedFifthOddRootOutputLabel, Sum.inr.injEq, reduceCtorEq] at hj
    · change Sum.inr (Sum.inl (generatedFifthEvenRootOctad j,
        generatedFifthEvenRootSign j)) = Sum.inr (Sum.inl (o, f)) at hj
      exact ho ⟨j, congrArg Prod.fst (Sum.inl.inj (Sum.inr.inj hj))⟩
  rw [generatedFourth_local_short, hz, mul_zero]

/-- All actual supported short-coordinate phases of every tensor candidate are fixed. -/
theorem generatedFifth_candidate_short_phases (b : ZMod 2) (k : Fin 16)
    (r : GriessShortIndex) (hr : (griessConwayEncode generatedFifthAxis).2.1 r ≠ 0) :
    localAxisQPhase r (generatedFifthQCandidate b k) = 1 := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · exact generatedFifth_candidate_pair_Q_phase b k s p
  · have ho : ∃ j : Fin 56, generatedFifthEvenRootOctad j = o := by
      by_contra h
      exact hr (generatedFifth_final_octad_zero o e h)
    obtain ⟨j, rfl⟩ := ho
    exact generatedFifth_candidate_octad_Q_phase b k j e
  · exact False.elim (hr (generatedFifth_final_odd_zero d i))

/-- Every literal tensor candidate genuinely fixes the full original fifth axis. -/
theorem generatedFifth_candidate_full_fixed (b : ZMod 2) (k : Fin 16) :
    rhoLocal (inclQ (generatedFifthQCandidate b k)) generatedFifthAxis = generatedFifthAxis :=
  (generatedFourthQ_full_fixed_iff _ _).mpr
    ⟨generatedFifth_candidate_short_phases b k, generatedFifth_candidate_tensor_fixed b k⟩

/-- Full actual extraspecial fixation is exactly the proved tensor subgroup. -/
theorem generatedFifth_Q_full_fixed_iff (q : Q) :
    rhoLocal (inclQ q) generatedFifthAxis = generatedFifthAxis ↔
      q ∈ generatedFifthTensorQStabilizer := by
  constructor
  · intro h
    exact ((generatedFourthQ_full_fixed_iff q _).mp h).2
  · intro h
    obtain ⟨b, k, rfl⟩ := (generatedFifth_tensor_Q_mem_iff q).mp h
    exact generatedFifth_candidate_full_fixed b k

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
