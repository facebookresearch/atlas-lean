/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalOctadCacheFiber0
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalOctadCacheFiber1
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalOctadCacheFiber2
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalOctadCacheFiber3
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalOctadCacheFiber4
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalOctadCacheFiber5
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalOctadCacheFiber6

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationSixthFinalOctadCacheEnumeration

/-! The short executable sum is exactly the complete original octad transform. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every occurring family has exactly its listed genuine middle rows. -/
theorem generatedSixth_final_octad_cache_fiber (f : Fin 231) :
    Finset.univ.filter (fun j : Fin 273 => generatedSixthMiddleOctadCode j =
      generatedSixthFinalOctadCacheCode f) = generatedSixthFinalOctadCacheRows f := by
  have blocks (b : Fin 7) (j : Fin 33) :
      Finset.univ.filter (fun r : Fin 273 => generatedSixthMiddleOctadCode r =
        generatedSixthFinalOctadCacheCode ⟨b.val * 33 + j.val, by omega⟩) =
          generatedSixthFinalOctadCacheRows ⟨b.val * 33 + j.val, by omega⟩ := by
    fin_cases b
    · exact generatedSixth_final_octad_cache_fiber0 j
    · exact generatedSixth_final_octad_cache_fiber1 j
    · exact generatedSixth_final_octad_cache_fiber2 j
    · exact generatedSixth_final_octad_cache_fiber3 j
    · exact generatedSixth_final_octad_cache_fiber4 j
    · exact generatedSixth_final_octad_cache_fiber5 j
    · exact generatedSixth_final_octad_cache_fiber6 j
  let b : Fin 7 := ⟨f.val / 33, by omega⟩
  let j : Fin 33 := ⟨f.val % 33, Nat.mod_lt _ (by decide)⟩
  have he : (⟨b.val * 33 + j.val, by omega⟩ : Fin 231) = f := by
    apply Fin.ext
    dsimp [b, j]
    omega
  have h := blocks b j
  rw [he] at h
  exact h

/-- The cached one or three terms equal all 273 original signed terms. -/
theorem generatedSixth_final_octad_cached_numerator (f : Fin 231) (e : Fin 64) :
    generatedSixthFinalOctadCachedNumerator f e =
      generatedSixthFinalOctadNumerator (generatedSixthFinalOctadCacheCode f) e := by
  unfold generatedSixthFinalOctadCachedNumerator generatedSixthFinalOctadNumerator
  rw [← Finset.sum_filter, generatedSixth_final_octad_cache_fiber]


/-- Each genuine final family coefficient has the checked one or three term numerator. -/
theorem generatedSixth_final_octad_cached_coordinate (f : Fin 231) (e : Fin 64) :
    (griessConwayEncode generatedSixthAxis).2.1
      (Sum.inr (Sum.inl (generatedSixthFinalOctadCacheOctad f, e))) =
        (generatedSixthFinalOctadCachedNumerator f e : ℝ) / 32 := by
  rw [generatedSixth_final_octad_coordinate, generatedSixth_final_octad_cache_label,
    ← generatedSixth_final_octad_cached_numerator]

/-- All octads outside the genuine displayed families have zero coefficient. -/
theorem generatedSixth_final_octad_cached_zero (o : Fin 759) (e : Fin 64)
    (ho : ¬ ∃ f : Fin 231, generatedSixthFinalOctadCacheOctad f = o) :
    (griessConwayEncode generatedSixthAxis).2.1 (Sum.inr (Sum.inl (o, e))) = 0 := by
  apply generatedSixth_final_octad_zero_outside
  rintro ⟨j, hj⟩
  exact ho ⟨generatedSixthFinalOctadCacheOwner j,
    (generatedSixth_final_octad_cache_coverage j).symm.trans hj⟩

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
