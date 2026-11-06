/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPositiveFinalShortSourcePacked
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightIncomingOctadSparseActual

/-! Complete original short evaluation with exact sparse packed octad inputs. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- All original short-source families, using previously checked exact entry lookups. -/
def generatedRootEightPositiveFinalShortSparseNumerator : GriessShortIndex → ℤ
  | Sum.inl (s, p) =>
      8 * (generatedFifthRootEightShortCachedCoefficient (Sum.inl (0, p)) -
        generatedFifthRootEightShortCachedCoefficient (Sum.inl (1, p))) +
      (if s = 0 then 1 else -1) * generatedRootEightIncomingMatrixCachedNumerator
        (griessCoordinatePair p).1 (griessCoordinatePair p).2
  | Sum.inr (Sum.inl (o, e)) =>
      2 * ((generatedRootEightIncomingOctadSparseEntries o).map
        (fun f => generatedFifthSignFourierCache e f.1 * f.2)).sum
  | Sum.inr (Sum.inr (d, i)) =>
      2 * (if ((golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) : ZMod 2) = 0 then 1 else -1) *
        (generatedRootEightIncomingPositiveTensorNumerator ⟨d.val, by omega⟩ i +
          generatedRootEightIncomingPositiveTensorNumerator ⟨d.val + 2048, by omega⟩ i)

/-- Every original signed numerator is retained by evaluation over its actual sparse entries. -/
theorem generatedRootEight_positive_final_short_sparse_actual (r : GriessShortIndex) :
    generatedRootEightPositiveFinalShortSparseNumerator r =
      generatedRootEightPositiveFinalShortNumerator r := by
  rw [← generatedRootEight_positive_final_short_packed_actual]
  rcases r with ⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)
  · rfl
  · simp only [generatedRootEightPositiveFinalShortSparseNumerator,
      generatedRootEightPositiveFinalShortPackedNumerator]
    rw [← generatedRootEight_sparse_coefficient_sum]
    simp only [generatedRootEight_incoming_octad_sparse_actual]
  · rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
