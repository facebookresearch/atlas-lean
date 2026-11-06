/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthAxisLowerRecoveryRootTwoIncomingShortGeneric
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQCache02
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsFifthQFast
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationNortonRelationsShortLookup

/-! Root02 incoming C binds the complete original4136 source rows to the genuine
97-factor full-Q action. Every source/target preferred lift and central phase is
an explicit certificate obligation. The actual whole cache identity is conditional
on those finite certificates, including all zero source rows. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false
-- Complete source-address and packet expressions have a deep constructor spine.
set_option maxRecDepth 100000

/-- The displayed mask is interpreted as the full preferred zero-central Q lift. -/
def generatedTenthAxisLowerRecoveryRootTwoIncomingShortPackedQ (m : ℕ) : Q :=
  ⟨ofAdd (monsterCo1GeometryBinaryMaskDecode m), 1⟩

/-- Every row requires actual preferred lifts and the entire phase-preserving Q image. -/
structure GeneratedTenthRootTwoIncomingShortRowCertificate (k : Fin 4136) : Prop where
  sourcePreferred : generatedTenthAxisLowerRecoveryRootTwoIncomingShortPackedQ
    (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowSourceMask k) =
    generatedAxisGlobalFifthShortPacketQ
      (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowSource k)
  targetPreferred : generatedTenthAxisLowerRecoveryRootTwoIncomingShortPackedQ
    (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowTargetMask k) =
    griessShortQ (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowTarget k)
  fullQImage : generatedAxisGlobalFifthQFast 2
      (generatedTenthAxisLowerRecoveryRootTwoIncomingShortPackedQ
        (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowSourceMask k)) =
    qCentral (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowPhase k) *
      generatedTenthAxisLowerRecoveryRootTwoIncomingShortPackedQ
        (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowTargetMask k)

/-- Each finite full-Q row binds the actual original97-factor source word. -/
theorem generatedTenth_root_two_incoming_short_row_Q_actual (k : Fin 4136)
    (h : GeneratedTenthRootTwoIncomingShortRowCertificate k) :
    spinConjugation (generatedAxisGlobalFifthShortWordFiber 2).val.1
        (griessShortQ (generatedAxisGlobalFifthShortPacketLabel
          (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowSource k))) =
      qCentral (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowPhase k) * griessShortQ
        (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowTarget k) := by
  rw [generatedAxisGlobalFifthShortWord_QImage,
    generatedAxisGlobalFifthQFast_actual 2 generatedAxisGlobalFifthQCache02_actual]
  have hh := h.fullQImage
  rw [h.sourcePreferred, h.targetPreferred, generatedAxisGlobalFifthShortPacketQ_actual] at hh
  exact hh

/-- The full row identifies its actual spatial preferred-short target. -/
theorem generatedTenth_root_two_incoming_short_row_target_actual (k : Fin 4136)
    (h : GeneratedTenthRootTwoIncomingShortRowCertificate k) :
    generatedTenthRootTwoGenericSourceTarget (generatedAxisGlobalFifthShortWordFiber 2)
      (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowSource k) =
        generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowTarget k := by
  apply griessShortClassEquiv.injective
  apply Subtype.ext
  apply leechHyperbolicCoordinates.injective
  have hb := congrArg (fun q : Q => toAdd q.base)
    (generatedTenth_root_two_incoming_short_row_Q_actual k h)
  rw [qCentral_mul_base, griessShortQ_image_base] at hb
  exact hb

/-- The complete preferred phase is fixed by the full original Q coefficient. -/
theorem generatedTenth_root_two_incoming_short_row_phase_actual (k : Fin 4136)
    (h : GeneratedTenthRootTwoIncomingShortRowCertificate k) :
    localShortPhase (generatedAxisGlobalFifthShortWordFiber 2)
      (generatedAxisGlobalFifthShortPacketLabel
        (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowSource k)) =
        generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowPhase k := by
  have hc := congrArg (fun q : Q => toAdd q.coeff)
    (generatedTenth_root_two_incoming_short_row_Q_actual k h)
  rw [qCentral_mul_coeff, griessShortQ_coeff, add_zero] at hc
  exact hc

/-- The original integer numerator retains the certified preferred output phase. -/
def generatedTenthAxisLowerRecoveryRootTwoIncomingShortSignedRowNumerator (k : Fin 4136) : ℤ :=
  if generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowPhase k = 0 then
    generatedNinthOriginalShortNumerator
      (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowSource k)
  else -generatedNinthOriginalShortNumerator
    (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowSource k)

/-- Genuine original source coefficients give each actual incoming signed row. -/
theorem generatedTenth_root_two_incoming_short_signed_row_actual (k : Fin 4136)
    (h : GeneratedTenthRootTwoIncomingShortRowCertificate k) :
    (griessConwayEncode (rhoLocal (localFiberIntoH (generatedAxisGlobalFifthShortWordFiber 2))
      generatedFifthAxis)).2.1 (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowTarget k) =
        (generatedTenthAxisLowerRecoveryRootTwoIncomingShortSignedRowNumerator k : ℝ) / 16 := by
  rw [generatedFourth_local_short,
    ← generatedTenth_root_two_incoming_short_row_target_actual k h,
    generatedTenthRootTwoGenericSourceTarget, localShortOperator_image,
    generatedTenth_root_two_incoming_short_row_phase_actual k h]
  have hn := generatedNinth_original_short_numerator_actual
    (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowSource k)
  change (griessConwayEncode generatedFifthAxis).2.1
      (generatedAxisGlobalFifthShortPacketLabel
        (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowSource k)) = _ at hn
  rw [hn]
  unfold generatedTenthAxisLowerRecoveryRootTwoIncomingShortSignedRowNumerator qSign
  by_cases hc : generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowPhase k = 0
  · simp [hc]
  · simp [hc]
    ring

/-- The exact chronological original source row address. -/
def generatedTenthAxisLowerRecoveryRootTwoIncomingShortSourceRowAddress :
  GeneratedAxisGlobalFifthShortPacketIndex → Fin 4136
  | Sum.inl (s, p) => ⟨s.val * 276 + p.val, by omega⟩
  | Sum.inr (j, e) => ⟨552 + j.val * 64 + e.val, by omega⟩

/-- The complete row catalogue covers every original pair and supported octad label. -/
theorem generatedTenth_root_two_incoming_short_source_row_address
    (a : GeneratedAxisGlobalFifthShortPacketIndex) :
    generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowSource
      (generatedTenthAxisLowerRecoveryRootTwoIncomingShortSourceRowAddress a) = a := by
  rcases a with ⟨s, p⟩ | ⟨j, e⟩
  · simp only [generatedTenthAxisLowerRecoveryRootTwoIncomingShortSourceRowAddress,
    generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowSource]
    split
    · congr 1
      apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega
    · exfalso; omega
  · simp only [generatedTenthAxisLowerRecoveryRootTwoIncomingShortSourceRowAddress,
    generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowSource]
    split
    · exfalso; omega
    · congr 1
      apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega

/-- The three preferred physical short families have disjoint injective addresses. -/
theorem generatedTenth_root_two_incoming_short_address_injective :
    Function.Injective generatedTenthAxisLowerRecoveryRootTwoIncomingShortAddress := by
  rintro (⟨s, p⟩ | (⟨o, e⟩ | ⟨d, i⟩)) (⟨s', p'⟩ | (⟨o', e'⟩ | ⟨d', i'⟩)) h
  all_goals simp only [generatedTenthAxisLowerRecoveryRootTwoIncomingShortAddress] at h
  · apply congrArg Sum.inl
    apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · apply congrArg (Sum.inr ∘ Sum.inl)
    apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega
  · apply congrArg (Sum.inr ∘ Sum.inr)
    apply Prod.ext <;> apply Fin.ext <;> dsimp <;> omega

/-- All finite dictionary/source bindings required to close the actual incoming C identity. -/
structure GeneratedTenthRootTwoIncomingShortCertificate : Prop where
  descriptorLength : generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowDescriptors.size = 4136
  dictionaryLength : generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryWords.size = 3856
  keys : ∀ a : Fin 3856, generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryKey a =
    generatedTenthAxisLowerRecoveryRootTwoIncomingShortAddress
      (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowTarget
      (generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryRow a))
  coverage : ∀ k : Fin 4136, generatedTenthAxisLowerRecoveryRootTwoIncomingShortCoefficient
    (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowTarget k) =
    generatedTenthAxisLowerRecoveryRootTwoIncomingShortSignedRowNumerator k
  rows : ∀ k : Fin 4136, GeneratedTenthRootTwoIncomingShortRowCertificate k

/-- The complete literal coefficient is the same generic balanced-tree lookup. -/
private theorem generatedTenth_root_two_incoming_short_coefficient_generic (r : GriessShortIndex) :
    generatedTenthAxisLowerRecoveryRootTwoIncomingShortCoefficient r =
      generatedTenthRootTwoGenericDictionaryCoefficient
        generatedTenthAxisLowerRecoveryRootTwoIncomingShortAddress
        generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryKey
        generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryNumerator
        generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryTree r := by
  unfold generatedTenthAxisLowerRecoveryRootTwoIncomingShortCoefficient
    generatedTenthRootTwoGenericDictionaryCoefficient
  cases hlookup : generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryTree.lookup
    generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryKey
    (generatedTenthAxisLowerRecoveryRootTwoIncomingShortAddress r) <;> rfl

/-- All actual incoming short coefficients, including every outside-support zero, are bound. -/
theorem generatedTenth_root_two_incoming_short_actual
    (h : GeneratedTenthRootTwoIncomingShortCertificate) (r : GriessShortIndex) :
    (griessConwayEncode (rhoLocal (localFiberIntoH (generatedAxisGlobalFifthShortWordFiber 2))
      generatedFifthAxis)).2.1 r = (generatedTenthAxisLowerRecoveryRootTwoIncomingShortCoefficient r
        : ℝ) / 16 := by
  have hcoverage : ∀ k : Fin 4136, generatedTenthRootTwoGenericDictionaryCoefficient
      generatedTenthAxisLowerRecoveryRootTwoIncomingShortAddress
      generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryKey
      generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryNumerator
      generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryTree
      (generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowTarget k) =
        generatedTenthAxisLowerRecoveryRootTwoIncomingShortSignedRowNumerator k := by
    intro k
    exact (generatedTenth_root_two_incoming_short_coefficient_generic _).symm.trans (h.coverage k)
  rw [generatedTenth_root_two_incoming_short_coefficient_generic]
  apply generatedTenth_root_two_generic_cache_actual _
    generatedTenthAxisLowerRecoveryRootTwoIncomingShortAddress
    generatedTenth_root_two_incoming_short_address_injective
      generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryKey
    generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryNumerator
      generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryTree
      generatedTenthAxisLowerRecoveryRootTwoIncomingShortDictionaryRow
    generatedTenthAxisLowerRecoveryRootTwoIncomingShortRowTarget
      generatedTenthAxisLowerRecoveryRootTwoIncomingShortSignedRowNumerator 16 h.keys hcoverage
  · intro s hs
    obtain ⟨a, ha⟩ := generatedTenth_root_two_generic_actual_nonzero_covered
      (generatedAxisGlobalFifthShortWordFiber 2) s hs
    let k := generatedTenthAxisLowerRecoveryRootTwoIncomingShortSourceRowAddress a
    refine ⟨k, ?_⟩
    have hk := generatedTenth_root_two_incoming_short_row_target_actual k (h.rows k)
    rw [generatedTenth_root_two_incoming_short_source_row_address] at hk
    exact hk.symm.trans ha
  · intro k
    exact generatedTenth_root_two_incoming_short_signed_row_actual k (h.rows k)

/-- Every original incoming odd short column uses this same source-bound whole dictionary. -/
theorem generatedTenth_root_two_incoming_short_odd_actual
    (h : GeneratedTenthRootTwoIncomingShortCertificate) (d : Fin 2048) (i : Fin 24) :
    (griessConwayEncode (rhoLocal (localFiberIntoH (generatedAxisGlobalFifthShortWordFiber 2))
      generatedFifthAxis)).2.1 (Sum.inr (Sum.inr (d, i))) =
        (generatedTenthAxisLowerRecoveryRootTwoIncomingShortIncomingCoefficient d i : ℝ) / 16 :=
  generatedTenth_root_two_incoming_short_actual h _

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
