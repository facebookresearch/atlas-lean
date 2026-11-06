/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryTwoProjectionGeneration

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoverySourceCompactCanonicalFixers
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Finiteness

/-! Canonical compact-axis full-fixer assembly. All new proof bodies are uncompiled drafts.
Every full preferred mask, central phase and signed tensor coordinate remains certified. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The restricted projection is the original genuine H-to-Co1 homomorphism. -/
def generatedTenthSourceCompactCanonicalProjection :
    generatedTenthSourceCompactAxisStabilizer →* Co1 :=
  projH.comp generatedTenthSourceCompactAxisStabilizer.subtype

/-- Only values attained by whole-axis compact-source fixers belong to this image. -/
def generatedTenthSourceCompactCanonicalProjectedStabilizer : Subgroup Co1 :=
  generatedTenthSourceCompactCanonicalProjection.range

private theorem spatial_le_of_eleven (P : Subgroup Co1)
    (hall : ∀ i : Fin 11, generatedTenthAxisLowerRecoveryThreeProjectionActual i ∈ P) :
    generatedTenthCo1SpatialStabilizer ≤ P := by
  have hsigns : ∀ k : Fin 7, generatedTenthAxisLowerRecoveryOriginalProjection
      (golaySignIsometry (generatedTenthAxisLowerRecoveryCode
        (generatedTenthAxisLowerRecoverySignBasis k))) ∈
      P := by
    intro k
    have h := hall ⟨k.val, by omega⟩
    have hk : k.val < 7 := k.isLt
    simpa only [generatedTenthAxisLowerRecoveryThreeProjectionActual,
      generatedTenthAxisLowerRecoveryCompactSpatial,
      generatedTenthAxisLowerRecoveryCompactStandardSpatial, hk, ↓reduceDIte,
      generatedTenthAxisLowerRecoveryOriginalProjection, MonoidHom.comp_apply] using h
  have hperms : ∀ k : Fin 2, generatedTenthAxisLowerRecoveryOriginalProjection
      (generatedTenthAxisLowerRecoverySignedPermutationSpatial k) ∈
      P := by
    intro k
    have h := hall ⟨k.val + 7, by omega⟩
    have hk7 : ¬k.val + 7 < 7 := by omega
    have hk9 : k.val + 7 < 9 := by omega
    have hk : k.val + 7 - 7 = k.val := by omega
    simpa only [generatedTenthAxisLowerRecoveryThreeProjectionActual,
      generatedTenthAxisLowerRecoveryCompactSpatial,
      generatedTenthAxisLowerRecoveryCompactStandardSpatial, hk7, hk9, ↓reduceDIte, hk,
      generatedTenthAxisLowerRecoveryOriginalProjection, MonoidHom.comp_apply] using h
  have hroots : ∀ k : Fin 2, generatedTenthAxisLowerRecoveryOriginalProjection
      (generatedTenthE7OrbitSpatialLetter k) ∈ P := by
    intro k
    have h := hall ⟨k.val + 9, by omega⟩
    have hk7 : ¬k.val + 9 < 7 := by omega
    have hk9 : ¬k.val + 9 < 9 := by omega
    have hk : k.val + 9 - 9 = k.val := by omega
    simpa only [generatedTenthAxisLowerRecoveryThreeProjectionActual,
      generatedTenthAxisLowerRecoveryCompactSpatial,
      generatedTenthAxisLowerRecoveryCompactStandardSpatial, hk7, hk9, ↓reduceDIte, hk,
      generatedTenthAxisLowerRecoveryOriginalProjection, MonoidHom.comp_apply] using h
  let R := P.comap generatedTenthAxisLowerRecoveryOriginalProjection
  let S := P.comap generatedTenthAxisLowerRecoverySpatialProjection
  have ha : generatedTenthE7ActualAnchorStabilizer ≤ S := by
    intro a ha
    change generatedTenthAxisLowerRecoveryOriginalProjection a.val ∈ P
    exact generatedTenth_axis_lower_recovery_signed_anchor_generation R hsigns hperms ⟨a, ha⟩
  have hl : ∀ k : Fin 2, generatedTenthE7RootOrbitLetter k ∈ S := by
    intro k
    change generatedTenthAxisLowerRecoveryOriginalProjection
      (generatedTenthE7OrbitSpatialLetter k) ∈ P
    exact hroots k
  have hs : S = ⊤ := generatedTenth_axis_lower_recovery_subgroup_eq_top S ha hl
  rintro c ⟨g, hg, hc⟩
  obtain ⟨k, hk⟩ := generatedTenthE7OriginalMatrixGroupEquiv.surjective ⟨g, hg⟩
  have hkg : generatedTenthE7OrbitConjugation k.val = g := congrArg Subtype.val hk
  have hkm : k ∈ S := by rw [hs]; trivial
  change QuotientGroup.mk' signsSubgroup (generatedTenthE7OrbitConjugation k.val) ∈ P at hkm
  rwa [hkg, hc] at hkm

/-- The same literal joint9*1 and original10 projection relations hold for canonical fixers. -/
theorem generatedTenth_source_compact_canonical_projected_mem
    (hfix : ∀ g : Fin 2, rhoLocal (localFiberIntoH (generatedTenthTwoFixerTensorFiber g))
      generatedTenthSourceCompactAxis = generatedTenthSourceCompactAxis) (g : Fin 2) :
    generatedTenthAxisLowerRecoveryTwoProjectionActual g ∈
      generatedTenthSourceCompactCanonicalProjectedStabilizer := by
  fin_cases g
  · refine ⟨⟨localFiberIntoH generatedTenthTwoFixerJointFiber, ?_⟩, ?_⟩
    · change rhoLocal (localFiberIntoH generatedTenthTwoFixerJointFiber)
        generatedTenthSourceCompactAxis = generatedTenthSourceCompactAxis
      simpa only [generatedTenthTwoFixerTensorFiber, ↓reduceIte] using hfix 0
    · exact generatedTenth_two_fixer_joint_projection
  · refine ⟨⟨localFiberIntoH generatedTenthTwoFixerOriginalTenFiber, ?_⟩, ?_⟩
    · change rhoLocal (localFiberIntoH generatedTenthTwoFixerOriginalTenFiber)
        generatedTenthSourceCompactAxis = generatedTenthSourceCompactAxis
      have hn : (1 : Fin 2) ≠ 0 := by decide
      simpa only [generatedTenthTwoFixerTensorFiber, ite_eq_right hn] using hfix 1
    · exact generatedTenth_two_fixer_original_ten_projection

/-- Genuine two-generator words attain the whole actual matrix quotient in the canonical image. -/
theorem generatedTenth_source_compact_canonical_spatial_le
    (hfix : ∀ g : Fin 2, rhoLocal (localFiberIntoH (generatedTenthTwoFixerTensorFiber g))
      generatedTenthSourceCompactAxis = generatedTenthSourceCompactAxis) :
    generatedTenthCo1SpatialStabilizer ≤
      generatedTenthSourceCompactCanonicalProjectedStabilizer := by
  apply spatial_le_of_eleven
  exact generatedTenth_axis_lower_recovery_two_projection_candidates_mem
    generatedTenth_compact_spatial_binary_all
    generatedTenthSourceCompactCanonicalProjectedStabilizer
    (generatedTenth_source_compact_canonical_projected_mem hfix)

/-- Actual spatial containment supplies the lower bound on the attained image. -/
theorem generatedTenth_source_compact_canonical_projected_lower
    (hfix : ∀ g : Fin 2, rhoLocal (localFiberIntoH (generatedTenthTwoFixerTensorFiber g))
      generatedTenthSourceCompactAxis = generatedTenthSourceCompactAxis) :
    2903040 ≤ Nat.card generatedTenthSourceCompactCanonicalProjectedStabilizer := by
  let : Finite Co1 := co1_finite
  have h := Subgroup.card_le_of_le (generatedTenth_source_compact_canonical_spatial_le hfix)
  rwa [generatedTenth_Co1_spatial_stabilizer_card] at h

/-- A genuine homomorphic image has no more elements than its entire finite stabilizer source. -/
theorem generatedTenth_source_compact_canonical_image_card_le :
    Nat.card generatedTenthSourceCompactCanonicalProjectedStabilizer ≤
      Nat.card generatedTenthSourceCompactAxisStabilizer := by
  let : Finite H := h_finite
  let f : generatedTenthSourceCompactAxisStabilizer →
      generatedTenthSourceCompactCanonicalProjectedStabilizer :=
    fun h => ⟨generatedTenthSourceCompactCanonicalProjection h, ⟨h, rfl⟩⟩
  apply Nat.card_le_card_of_surjective f
  rintro ⟨c, hc⟩
  obtain ⟨h, hh⟩ := hc
  exact ⟨h, Subtype.ext hh⟩

/-- The frozen original full-axis upper bound transfers through actual local orbit equivalence. -/
theorem generatedTenth_source_compact_canonical_upper :
    Nat.card generatedTenthSourceCompactAxisStabilizer ≤ 2903040 := by
  rw [generatedTenth_source_compact_axis_stabilizer_card]
  exact generatedTenth_local_axis_stabilizer_upper

/-- Only the two genuine whole-axis fixers remain in the canonical exact-cardinality theorem. -/
theorem generatedTenth_source_compact_canonical_card
    (hfix : ∀ g : Fin 2, rhoLocal (localFiberIntoH (generatedTenthTwoFixerTensorFiber g))
      generatedTenthSourceCompactAxis = generatedTenthSourceCompactAxis) :
    Nat.card generatedTenthSourceCompactAxisStabilizer = 2903040 := by
  exact Nat.le_antisymm generatedTenth_source_compact_canonical_upper
    ((generatedTenth_source_compact_canonical_projected_lower hfix).trans
      generatedTenth_source_compact_canonical_image_card_le)

/-- The actual original Tenth stabilizer has the same exact count via genuine H conjugacy. -/
theorem generatedTenth_source_compact_canonical_original_card
    (hfix : ∀ g : Fin 2, rhoLocal (localFiberIntoH (generatedTenthTwoFixerTensorFiber g))
      generatedTenthSourceCompactAxis = generatedTenthSourceCompactAxis) :
    Nat.card generatedTenthLocalAxisStabilizer = 2903040 := by
  exact generatedTenth_source_compact_canonical_count_transfer
    (generatedTenth_source_compact_canonical_card hfix)

/-- Complete canonical input and unchanged full action certificates close the original count. -/
theorem generatedTenth_source_compact_canonical_original_card_of_certificates
    (destination : Fin 2 → Fin 98280 → Fin 98280)
    (phase : Fin 2 → Fin 98280 → ZMod 2)
    (hC : GeneratedTenthSourceCompactCanonicalCInputCondition)
    (hT : GeneratedTenthSourceCompactCanonicalTInputCondition)
    (hsupport : ∀ g, GeneratedTenthTwoFixerCSupportCondition g (destination g) (phase g))
    (hphysical : GeneratedTenthTwoFixerTensorPhysicalCondition)
    (hstart : GeneratedTenthTwoFixerTensorStartCondition)
    (hpairs : GeneratedTenthTwoFixerTensorPairCondition)
    (hfinish : GeneratedTenthTwoFixerTensorFinishCondition) :
    Nat.card generatedTenthLocalAxisStabilizer = 2903040 := by
  exact generatedTenth_source_compact_canonical_original_card
    (generatedTenth_source_compact_canonical_two_fixers destination phase hC hT
      hsupport hphysical hstart hpairs hfinish)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
