/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationMatrix
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShortAction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignWhole

/-! Exact support and norm soundness for the corrected original monomial action. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

/-- Fixing every genuine pair and the 56 outgoing families fixes the entire short block. -/
theorem generatedFifth_monomial_permutation_short_fixed_of_rows (k : Fin 6)
    (hp : ∀ s : Fin 2, ∀ p : {p : Fin 24 × Fin 24 // p.1 < p.2},
      localShortOperator (generatedFifthMonomialPermutationCorrectedFiber k)
        (griessConwayEncode generatedFifthAxis).2.1
          (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven (Sum.inl (s, p)))) =
        (griessConwayEncode generatedFifthAxis).2.1
          (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven (Sum.inl (s, p)))))
    (ho : ∀ j : Fin 56, ∀ e : Fin 64,
      localShortOperator (generatedFifthMonomialPermutationCorrectedFiber k)
        (griessConwayEncode generatedFifthAxis).2.1
          (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven (Sum.inr (j, e)))) =
        (griessConwayEncode generatedFifthAxis).2.1
          (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven (Sum.inr (j, e))))) :
    localShortOperator (generatedFifthMonomialPermutationCorrectedFiber k)
      (griessConwayEncode generatedFifthAxis).2.1 =
        (griessConwayEncode generatedFifthAxis).2.1 := by
  classical
  let X := (griessConwayEncode generatedFifthAxis).2.1
  let Y := localShortOperator (generatedFifthMonomialPermutationCorrectedFiber k) X
  have hn : (∑ r, Y r ^ 2) = ∑ r, X r ^ 2 := by
    have h := localShortRepresentation_pairing
      (generatedFifthMonomialPermutationCorrectedFiber k) X X
    change (∑ r, Y r * Y r) = ∑ r, X r * X r at h
    simpa only [pow_two] using h
  apply generatedFourth_real_eq_of_norm_support X Y hn
  intro r hr
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · have hlt : (griessCoordinatePair p).1 < (griessCoordinatePair p).2 :=
      (Finset.mem_filter.mp (griessCoordinatePairEquiv p).property).2
    simpa only [generatedFifthXiShortCachedEven, generatedFifthXiEvenShortIndex,
      griessPairIndex_pair] using hp s ⟨griessCoordinatePair p, hlt⟩
  · have hx : ∃ j : Fin 56, generatedFifthEvenRootOctad j = o := by
      by_contra h
      exact hr (generatedFifth_final_octad_zero o e h)
    obtain ⟨j, rfl⟩ := hx
    exact ho j e
  · exact False.elim (hr (generatedFifth_final_odd_zero d i))

/-- Complete actual matrix, short and tensor fixation gives equality of the original fifth axis. -/
theorem generatedFifth_monomial_permutation_full_fixed_of_blocks (k : Fin 6)
    (hs : localShortOperator (generatedFifthMonomialPermutationCorrectedFiber k)
      (griessConwayEncode generatedFifthAxis).2.1 =
        (griessConwayEncode generatedFifthAxis).2.1)
    (ht : localTensorRepresentation (generatedFifthMonomialPermutationCorrectedFiber k)
      (griessConwayEncode generatedFifthAxis).2.2 =
        (griessConwayEncode generatedFifthAxis).2.2) :
    rhoLocal (localFiberIntoH (generatedFifthMonomialPermutationCorrectedFiber k))
      generatedFifthAxis = generatedFifthAxis := by
  apply Function.LeftInverse.injective griessConwayDecode_encode
  apply Prod.ext
  · exact generatedFifth_monomial_permutation_matrix_fixed k
  · apply Prod.ext
    · rw [generatedFourth_local_short]
      exact hs
    · rw [generatedFourth_local_tensor]
      exact ht

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
