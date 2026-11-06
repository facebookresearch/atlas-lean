/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveOctadDiagonalLocal

/-! The forward triality image of the intermediate octad-family vector: complete rational packet,
exact 120-coordinate sparse short support, and zero tensor coordinates. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

/-- The candidate octad-diagonal transition vector. -/
abbrev generatedAxisGlobalTwelveOctadDiagonalX : GriessSpace :=
  sExtra (rhoLocal generatedAxisGlobalTwelveOctadDiagonalLocal (generatedOctadLocalAxis 0 0))

/-- The complete rational packet of the transition vector. -/
def generatedAxisGlobalTwelveOctadDiagonalXPacket : GeneratedAxisGlobalRationalPacket :=
  generatedAxisGlobalRationalTriality generatedAxisGlobalTwelveOctadDiagonalUPacket

/-- The packet gives every actual coordinate of the transition vector. -/
theorem generatedAxisGlobalTwelveOctadDiagonalXPacket_actual :
    griessConwayEncode generatedAxisGlobalTwelveOctadDiagonalX = generatedAxisGlobalRationalPacketReal generatedAxisGlobalTwelveOctadDiagonalXPacket :=
  generatedAxisGlobalRationalTriality_of_actual _ _ generatedAxisGlobalTwelveOctadDiagonalUPacket_actual

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
/-- Every stored transition key is the exact catalogue number of its label. -/
theorem generatedAxisGlobalTwelveOctadDiagonalXTree_valid :
    GeneratedAxisGlobalSparseLookupValid
      (fun k => generatedAxisGlobalShortNumber (generatedAxisGlobalTwelveOctadDiagonalXLabel k)) generatedAxisGlobalTwelveOctadDiagonalXTree := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
/-- All transition labels round trip through the lookup. -/
theorem generatedAxisGlobalTwelveOctadDiagonalXSource_roundtrip : ∀ k : Fin 120,
    generatedAxisGlobalTwelveOctadDiagonalXSource (generatedAxisGlobalTwelveOctadDiagonalXLabel k) = some k := by
  decide +kernel

/-- Every successful transition lookup returns the label at that coordinate. -/
theorem generatedAxisGlobalTwelveOctadDiagonalXSource_sound (r : GriessShortIndex) (k : Fin 120)
    (h : generatedAxisGlobalTwelveOctadDiagonalXSource r = some k) : generatedAxisGlobalTwelveOctadDiagonalXLabel k = r :=
  generatedAxisGlobalShortNumber_injective
    (generatedAxisGlobalSparseLookup_sound _ _ generatedAxisGlobalTwelveOctadDiagonalXTree_valid _ _ h)

/-- The admissible label families: pairs and the fourteen active octads. -/
def generatedAxisGlobalTwelveOctadDiagonalFamilyOK : GriessShortIndex → Bool
  | Sum.inl _ => true
  | Sum.inr (Sum.inl (o, _)) => (List.ofFn generatedAxisGlobalTwelveOctadDiagonalActiveOctad).contains o
  | Sum.inr (Sum.inr _) => false

/-- An admissible label is a pair label or a label on an active octad. -/
theorem generatedAxisGlobalTwelveOctadDiagonalFamilyOK_spec (r : GriessShortIndex) (h : generatedAxisGlobalTwelveOctadDiagonalFamilyOK r = true) :
    (∃ s p, r = Sum.inl (s, p)) ∨
      ∃ a e, r = Sum.inr (Sum.inl (generatedAxisGlobalTwelveOctadDiagonalActiveOctad a, e)) := by
  rcases r with ⟨s, p⟩ | ⟨o, e⟩ | ⟨d, j⟩
  · exact Or.inl ⟨s, p, rfl⟩
  · right
    have hm : o ∈ List.ofFn generatedAxisGlobalTwelveOctadDiagonalActiveOctad := List.contains_iff_mem.mp h
    obtain ⟨a, ha⟩ := List.mem_ofFn.mp hm
    exact ⟨a, e, by rw [ha]⟩
  · simp [generatedAxisGlobalTwelveOctadDiagonalFamilyOK] at h

set_option maxRecDepth 10000 in
set_option maxHeartbeats 20000000 in
/-- Every intermediate and transition label is admissible. -/
theorem generatedAxisGlobalTwelveOctadDiagonalLabel_familyOK : ∀ k : Fin 120,
    generatedAxisGlobalTwelveOctadDiagonalFamilyOK (generatedAxisGlobalTwelveOctadDiagonalULabel k) = true ∧ generatedAxisGlobalTwelveOctadDiagonalFamilyOK (generatedAxisGlobalTwelveOctadDiagonalXLabel k) = true := by
  decide +kernel

/-- Every intermediate and transition label is a pair label or a label on an active octad. -/
theorem generatedAxisGlobalTwelveOctadDiagonalLabel_family (k : Fin 120) :
    ((∃ s p, generatedAxisGlobalTwelveOctadDiagonalULabel k = Sum.inl (s, p)) ∨
      ∃ a e, generatedAxisGlobalTwelveOctadDiagonalULabel k = Sum.inr (Sum.inl (generatedAxisGlobalTwelveOctadDiagonalActiveOctad a, e))) ∧
    ((∃ s p, generatedAxisGlobalTwelveOctadDiagonalXLabel k = Sum.inl (s, p)) ∨
      ∃ a e, generatedAxisGlobalTwelveOctadDiagonalXLabel k = Sum.inr (Sum.inl (generatedAxisGlobalTwelveOctadDiagonalActiveOctad a, e))) :=
  ⟨generatedAxisGlobalTwelveOctadDiagonalFamilyOK_spec _ (generatedAxisGlobalTwelveOctadDiagonalLabel_familyOK k).1,
    generatedAxisGlobalTwelveOctadDiagonalFamilyOK_spec _ (generatedAxisGlobalTwelveOctadDiagonalLabel_familyOK k).2⟩

/-- A coordinate outside the pair labels and the active octads carries no intermediate label. -/
theorem generatedAxisGlobalTwelveOctadDiagonalUShortQ_zero (r : GriessShortIndex)
    (hr : (∀ s p, r ≠ Sum.inl (s, p)) ∧ ∀ a e, r ≠ Sum.inr (Sum.inl (generatedAxisGlobalTwelveOctadDiagonalActiveOctad a, e))) :
    generatedAxisGlobalTwelveOctadDiagonalUShortQ r = 0 := by
  unfold generatedAxisGlobalTwelveOctadDiagonalUShortQ
  cases h : generatedAxisGlobalTwelveOctadDiagonalUSource r with
  | none => rfl
  | some k =>
    exfalso
    have hk := generatedAxisGlobalTwelveOctadDiagonalUSource_sound r k h
    rcases (generatedAxisGlobalTwelveOctadDiagonalLabel_family k).1 with ⟨s, p, hs⟩ | ⟨a, e, he⟩
    · exact hr.1 s p (hk.symm.trans hs)
    · exact hr.2 a e (hk.symm.trans he)

/-- A coordinate outside the pair labels and the active octads carries no transition label. -/
theorem generatedAxisGlobalTwelveOctadDiagonalXShortQ_zero (r : GriessShortIndex)
    (hr : (∀ s p, r ≠ Sum.inl (s, p)) ∧ ∀ a e, r ≠ Sum.inr (Sum.inl (generatedAxisGlobalTwelveOctadDiagonalActiveOctad a, e))) :
    generatedAxisGlobalTwelveOctadDiagonalXShortQ r = 0 := by
  unfold generatedAxisGlobalTwelveOctadDiagonalXShortQ
  cases h : generatedAxisGlobalTwelveOctadDiagonalXSource r with
  | none => rfl
  | some k =>
    exfalso
    have hk := generatedAxisGlobalTwelveOctadDiagonalXSource_sound r k h
    rcases (generatedAxisGlobalTwelveOctadDiagonalLabel_family k).2 with ⟨s, p, hs⟩ | ⟨a, e, he⟩
    · exact hr.1 s p (hk.symm.trans hs)
    · exact hr.2 a e (hk.symm.trans he)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 80000000 in
/-- Both pair families have exactly the candidate transition coefficients. -/
theorem generatedAxisGlobalTwelveOctadDiagonalXPair_certificate : ∀ s : Fin 2, ∀ p : Fin 276,
    generatedAxisGlobalTwelveOctadDiagonalXPacket.2.1 (Sum.inl (s, p)) = generatedAxisGlobalTwelveOctadDiagonalXShortQ (Sum.inl (s, p)) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 200000000 in
/-- The Fourier outputs on the first seven active octads have the candidate coefficients. -/
theorem generatedAxisGlobalTwelveOctadDiagonalXOctadA_certificate : ∀ a : Fin 7, ∀ e : Fin 64,
    generatedAxisGlobalTwelveOctadDiagonalXPacket.2.1 (Sum.inr (Sum.inl (generatedAxisGlobalTwelveOctadDiagonalActiveOctad (Fin.castAdd 7 a), e))) =
      generatedAxisGlobalTwelveOctadDiagonalXShortQ (Sum.inr (Sum.inl (generatedAxisGlobalTwelveOctadDiagonalActiveOctad (Fin.castAdd 7 a), e))) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 200000000 in
/-- The Fourier outputs on the last seven active octads have the candidate coefficients. -/
theorem generatedAxisGlobalTwelveOctadDiagonalXOctadB_certificate : ∀ a : Fin 7, ∀ e : Fin 64,
    generatedAxisGlobalTwelveOctadDiagonalXPacket.2.1 (Sum.inr (Sum.inl (generatedAxisGlobalTwelveOctadDiagonalActiveOctad (Fin.natAdd 7 a), e))) =
      generatedAxisGlobalTwelveOctadDiagonalXShortQ (Sum.inr (Sum.inl (generatedAxisGlobalTwelveOctadDiagonalActiveOctad (Fin.natAdd 7 a), e))) := by
  decide +kernel

/-- The complete transition short coordinates are the sparse candidate coefficients. -/
theorem generatedAxisGlobalTwelveOctadDiagonalXShort_sparse (r : GriessShortIndex) :
    generatedAxisGlobalTwelveOctadDiagonalXPacket.2.1 r = generatedAxisGlobalTwelveOctadDiagonalXShortQ r := by
  rcases r with ⟨s, p⟩ | ⟨o, e⟩ | ⟨d, j⟩
  · exact generatedAxisGlobalTwelveOctadDiagonalXPair_certificate s p
  · by_cases ho : ∃ a, generatedAxisGlobalTwelveOctadDiagonalActiveOctad a = o
    · obtain ⟨a, rfl⟩ := ho
      obtain ⟨b, rfl | rfl⟩ : ∃ b : Fin 7, a = Fin.castAdd 7 b ∨ a = Fin.natAdd 7 b := by
        by_cases h : a.val < 7
        · exact ⟨⟨a.val, h⟩, Or.inl (Fin.ext rfl)⟩
        · exact ⟨⟨a.val - 7, by omega⟩, Or.inr (Fin.ext (by simp; omega))⟩
      · exact generatedAxisGlobalTwelveOctadDiagonalXOctadA_certificate b e
      · exact generatedAxisGlobalTwelveOctadDiagonalXOctadB_certificate b e
    · have hz : ∀ f : Fin 64, (∀ s p, (Sum.inr (Sum.inl (o, f)) : GriessShortIndex) ≠
          Sum.inl (s, p)) ∧ ∀ a e', (Sum.inr (Sum.inl (o, f)) : GriessShortIndex) ≠
            Sum.inr (Sum.inl (generatedAxisGlobalTwelveOctadDiagonalActiveOctad a, e')) := by
        intro f
        refine ⟨fun s p h => ?_, fun a e' h => ?_⟩
        · cases h
        · simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
          exact ho ⟨a, h.1.symm⟩
      rw [generatedAxisGlobalTwelveOctadDiagonalXShortQ_zero _ (hz e)]
      simp only [generatedAxisGlobalTwelveOctadDiagonalXPacket, generatedAxisGlobalRationalTriality,
        generatedAxisGlobalTrialityShortQ, generatedAxisGlobalTwelveOctadDiagonalUPacket]
      apply Finset.sum_eq_zero
      intro f _
      rw [generatedAxisGlobalTwelveOctadDiagonalUShortQ_zero _ (hz f), mul_zero]
  · have hz : (∀ s p, (Sum.inr (Sum.inr (d, j)) : GriessShortIndex) ≠ Sum.inl (s, p)) ∧
        ∀ a e, (Sum.inr (Sum.inr (d, j)) : GriessShortIndex) ≠
          Sum.inr (Sum.inl (generatedAxisGlobalTwelveOctadDiagonalActiveOctad a, e)) := by
      refine ⟨fun s p h => ?_, fun a e h => ?_⟩
      · cases h
      · cases h
    rw [generatedAxisGlobalTwelveOctadDiagonalXShortQ_zero _ hz]
    simp only [generatedAxisGlobalTwelveOctadDiagonalXPacket, generatedAxisGlobalRationalTriality,
      generatedAxisGlobalTrialityShortQ, generatedAxisGlobalTwelveOctadDiagonalUPacket, Pi.zero_apply, add_zero, mul_zero,
      zero_div]

/-- Every transition tensor coordinate is zero. -/
theorem generatedAxisGlobalTwelveOctadDiagonalXTensor_zero : generatedAxisGlobalTwelveOctadDiagonalXPacket.2.2 = 0 := by
  funext t j
  simp only [generatedAxisGlobalTwelveOctadDiagonalXPacket, generatedAxisGlobalRationalTriality,
    generatedAxisGlobalTrialityScaledTensorQ, generatedAxisGlobalTwelveOctadDiagonalUPacket, Pi.zero_apply, sub_self, mul_zero,
    zero_div, add_zero]
  rw [generatedAxisGlobalTwelveOctadDiagonalUShortQ_zero]
  · simp
  · refine ⟨fun s p h => ?_, fun a e h => ?_⟩
    · cases h
    · cases h

/-- The actual transition short coordinates are the sparse candidate coefficients. -/
theorem generatedAxisGlobalTwelveOctadDiagonalXShort_actual (r : GriessShortIndex) :
    (griessConwayEncode generatedAxisGlobalTwelveOctadDiagonalX).2.1 r = (generatedAxisGlobalTwelveOctadDiagonalXShortQ r : ℝ) := by
  rw [generatedAxisGlobalTwelveOctadDiagonalXPacket_actual]
  change ((generatedAxisGlobalTwelveOctadDiagonalXPacket.2.1 r : ℚ) : ℝ) = _
  rw [generatedAxisGlobalTwelveOctadDiagonalXShort_sparse]

/-- The actual transition tensor coordinates are zero. -/
theorem generatedAxisGlobalTwelveOctadDiagonalXTensor_actual : (griessConwayEncode generatedAxisGlobalTwelveOctadDiagonalX).2.2 = 0 := by
  rw [generatedAxisGlobalTwelveOctadDiagonalXPacket_actual]
  funext t j
  simp [generatedAxisGlobalRationalPacketReal, generatedAxisGlobalTwelveOctadDiagonalXTensor_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
