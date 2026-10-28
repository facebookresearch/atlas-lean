/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialPermutationShortAction

/-! Original spatial permutation certificates identify the genuine preferred short labels. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A cached integer transport certifies the exact original normalized spatial action. -/
theorem generatedFifth_monomial_permutation_physical (k : Fin 6)
    (r s : generatedFifthXiShortCachedLabel) (c : ℤ)
    (h : ∀ i : Fin 24,
      generatedFifthXiShortCachedIntegral r
        ((generatedFifthMonomialSpatialPermutation k).val.symm i) =
        c * generatedFifthXiShortCachedIntegral s i) :
    (generatedFifthMonomialSpatialFiber k).val.2.val
        (griessShortVector (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven r))) =
      (c : ℝ) • griessShortVector
        (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven s)) := by
  rw [generatedFifth_monomial_spatial]
  funext i
  change griessShortVector
      (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven r))
        ((generatedFifthMonomialSpatialPermutation k).val.symm i) = _
  simp only [griessShortVector, ← generatedFifthXiShortCachedIntegral_actual,
    Pi.smul_apply, smul_eq_mul]
  rw [h]
  push_cast
  ring

/-- A true signed integer transport yields the genuine spatial line transport. -/
theorem generatedFifth_monomial_permutation_physical_sign (k : Fin 6)
    (r s : generatedFifthXiShortCachedLabel) (c : ℤ) (hc : c = 1 ∨ c = -1)
    (h : ∀ i : Fin 24,
      generatedFifthXiShortCachedIntegral r
        ((generatedFifthMonomialSpatialPermutation k).val.symm i) =
        c * generatedFifthXiShortCachedIntegral s i) :
    (generatedFifthMonomialSpatialFiber k).val.2.val
        (griessShortVector (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven r))) =
          griessShortVector (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven s)) ∨
      (generatedFifthMonomialSpatialFiber k).val.2.val
        (griessShortVector (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven r))) =
          -griessShortVector
            (generatedFifthXiEvenShortIndex (generatedFifthXiShortCachedEven s)) := by
  have hv := generatedFifth_monomial_permutation_physical k r s c h
  rcases hc with rfl | rfl
  · exact Or.inl (by simpa using hv)
  · exact Or.inr (by simpa using hv)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
