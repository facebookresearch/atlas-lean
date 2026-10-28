/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerTensorSourceCached
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerMiddleShortKeyValueCache

/-! The exact whole source uses verified direct key/value lookups and complete Golay masks. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The complete original tensor numerator with direct verified incoming source lookups. -/
def generatedNinthLowerTensorSourceFastInteger (n : Fin 4096) (i : Fin 24) : ℤ :=
  let d : Fin 2048 := ⟨n.val % 2048, Nat.mod_lt _ (by decide)⟩
  let sigma : ℤ := if (generatedTwelfthGolayMaskCache d).testBit i.val then -1 else 1
  let parker := generatedTwelfthGolayPhaseCache d
  (if n.val < 2048 then 4 else -4) * sigma * generatedNinthLowerIncomingCachedCoefficient d i +
    sigma * parker * (generatedNinthMiddleNumerator ⟨d.val, by omega⟩ i -
      generatedNinthMiddleNumerator ⟨d.val + 2048, by omega⟩ i)

/-- Every spin label and spatial column retains the complete original signed source numerator. -/
theorem generatedNinth_lower_tensor_source_fast_actual (n : Fin 4096) (i : Fin 24) :
    generatedNinthLowerTensorSourceFastInteger n i =
      generatedNinthLowerTensorSourceInteger n i := by
  calc
    generatedNinthLowerTensorSourceFastInteger n i =
        generatedNinthLowerTensorSourceCachedInteger n i := by
      simp only [generatedNinthLowerTensorSourceFastInteger,
        generatedNinthLowerTensorSourceCachedInteger,
        generatedNinth_lower_incoming_cached_coefficient_actual]
    _ = generatedNinthLowerTensorSourceInteger n i :=
      generatedNinth_lower_tensor_source_cached_actual n i

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
