/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerShortSourceFormulaGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthGolayMaskCacheActual
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerMiddleShortKeyValueCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerTensorSourceSparse
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthActualMiddleShortSource
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOctadSourceSlotNumerator

/-! Exact complete source formulas and bounded quantifiers retain every preferred
short coordinate. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators

/-- The complete original preferred-short formula with verified source lookups and Parker signs. -/
def generatedNinthLowerShortSourceCachedInteger : GriessShortIndex → ℤ
  | Sum.inl (s, p) => generatedNinthLowerPairSourceInteger s p
  | Sum.inr (Sum.inl (o, e)) =>
      2 * generatedNinthFinalOctadSlotFastNumerator o e
  | Sum.inr (Sum.inr (d, i)) =>
      4 * generatedTwelfthGolayPhaseCache d *
        (generatedNinthMiddleSparseNumerator ⟨d.val, by omega⟩ i +
          generatedNinthMiddleSparseNumerator ⟨d.val + 2048, by omega⟩ i)

/-- Every original preferred-short coordinate retains its complete integer source formula. -/
theorem generatedNinth_lower_short_source_cached_actual (r : GriessShortIndex) :
    generatedNinthLowerShortSourceCachedInteger r = generatedNinthLowerShortSourceInteger r := by
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · rfl
  · change 2 * generatedNinthFinalOctadSlotFastNumerator o e =
      generatedNinthLowerShortSourceInteger (Sum.inr (Sum.inl (o, e)))
    apply Int.cast_injective (α := ℝ)
    simp only [Int.cast_mul, Int.cast_ofNat]
    have h := generatedNinth_actual_short_source_formula (Sum.inr (Sum.inl (o, e)))
    rw [generatedNinth_final_octad_slot_fast_of_certificates
      generatedNinth_short_row_certificate_all o e] at h
    linarith
  · simp only [generatedNinthLowerShortSourceCachedInteger, generatedNinthLowerShortSourceInteger,
      generatedTwelfth_golay_phase_cache_actual, generatedNinth_middle_sparse_numerator_actual]

/-- Sixteen complete64-coordinate blocks cover every original1024-coordinate interval. -/
theorem generatedNinth_lower_short_predicate1024_of_blocks (p : Fin 1024 → Prop)
    (h : ∀ b : Fin 16, ∀ u : Fin 64, p ⟨b.val * 64 + u.val, by omega⟩) :
    ∀ n : Fin 1024, p n := by
  intro n
  let b : Fin 16 := ⟨n.val / 64, by omega⟩
  let u : Fin 64 := ⟨n.val % 64, Nat.mod_lt _ (by decide)⟩
  have he : (⟨b.val * 64 + u.val, by omega⟩ : Fin 1024) = n := by
    apply Fin.ext
    dsimp [b, u]
    omega
  simpa only [he] using h b u

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
