/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTwelfthCompleteShortActions
public import Mathlib.Data.Fintype.Card

/-! A genuine signed permutation fixes its entire finite vector once every nonzero source
coefficient has the correct image. Bijectivity preserves the complement of the support. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Checking the nonzero source coefficients suffices for complete genuine short fixation. -/
theorem generatedTwelfth_short_fixer_of_nonzero_sources (f : localFiberSubgroup)
    (X : GriessShortIndex → ℝ)
    (h : ∀ r, X r ≠ 0 → localShortRepresentation f X
      (griessShortPermutation f.val.2 r) = X (griessShortPermutation f.val.2 r)) :
    localShortRepresentation f X = X := by
  classical
  let S := {r : GriessShortIndex // X r ≠ 0}
  have hforward (r : S) : X (griessShortPermutation f.val.2 r.val) ≠ 0 := by
    have hs := localShortOperator_image f X r.val
    have hh := h r.val r.property
    change localShortOperator f X (griessShortPermutation f.val.2 r.val) = _ at hh
    rw [hh] at hs
    have hsign : qSign (localShortPhase f r.val) ≠ 0 := by
      intro hz
      have hsq := qSign_sq (localShortPhase f r.val)
      rw [hz, zero_mul] at hsq
      norm_num at hsq
    intro hz
    rw [hz] at hs
    exact (mul_ne_zero hsign r.property) hs.symm
  let F : S → S := fun r => ⟨griessShortPermutation f.val.2 r.val, hforward r⟩
  have hF : Function.Injective F := by
    intro r s hs
    apply Subtype.ext
    apply (griessShortPermutation f.val.2).injective
    exact congrArg Subtype.val hs
  have honto : Function.Surjective F := Finite.surjective_of_injective hF
  funext s
  obtain ⟨r, rfl⟩ := (griessShortPermutation f.val.2).surjective s
  by_cases hr : X r ≠ 0
  · exact h r hr
  · have hz : X (griessShortPermutation f.val.2 r) = 0 := by
      by_contra hnonzero
      obtain ⟨u, hu⟩ := honto ⟨griessShortPermutation f.val.2 r, hnonzero⟩
      have he : griessShortPermutation f.val.2 u.val = griessShortPermutation f.val.2 r :=
        congrArg Subtype.val hu
      have hur : u.val = r := (griessShortPermutation f.val.2).injective he
      exact hr (hur ▸ u.property)
    change localShortOperator f X (griessShortPermutation f.val.2 r) = _
    rw [localShortOperator_image, not_ne_iff.mp hr, mul_zero, hz]

/-- A single full preferred-Q certificate identifies its actual source image. -/
theorem generatedTwelfth_complete_short_image_of_condition (i : Fin 12) (r : GriessShortIndex)
    (h : generatedTwelfthCompleteShortCondition i (generatedNinthLowerSpinShortAddress r)) :
    spinConjugation (generatedTwelfthCertifiedFiber i).val.1 (monsterNortonShortQ r) =
      qCentral (generatedTwelfthCompleteShortPhase i r) *
        monsterNortonShortQ (generatedTwelfthCompleteShortDestination i r) := by
  simp only [generatedTwelfthCompleteShortCondition,
    generatedNinth_lower_spin_short_index_address] at h
  change spinConjugation (generatedTwelfthSpinCompact i) (monsterNortonShortQ r) = _
  rw [generatedTwelfth_spin_compact_full_Q_fast,
    ← generatedTwelfth_complete_short_q_mask_actual r,
    ← generatedTwelfth_complete_short_q_mask_actual (generatedTwelfthCompleteShortDestination i r)]
  exact h.1

/-- Complete actual cache binding and certificates on its nonzero sources give full fixation,
including every zero coordinate, by the genuine finite permutation of the support. -/
theorem generatedTwelfth_complete_short_fix_of_support_cache (i : Fin 12)
    (h : ∀ a, generatedTwelfthCompleteShortInputInteger
      (generatedNinthLowerSpinShortIndex a) ≠ 0 → generatedTwelfthCompleteShortCondition i a)
    (X : GriessShortIndex → ℝ)
    (hinput : ∀ r, 128 * X r = (generatedTwelfthCompleteShortInputInteger r : ℝ)) :
    localShortRepresentation (generatedTwelfthCertifiedFiber i) X = X := by
  apply generatedTwelfth_short_fixer_of_nonzero_sources
  intro r hr
  have hnonzero : generatedTwelfthCompleteShortInputInteger r ≠ 0 := by
    intro hz
    have hh := hinput r
    rw [hz, Int.cast_zero] at hh
    apply hr
    linarith
  have hc := h (generatedNinthLowerSpinShortAddress r)
    (by simpa only [generatedNinth_lower_spin_short_index_address] using hnonzero)
  have hq := generatedTwelfth_complete_short_image_of_condition i r hc
  have hd : griessShortPermutation (generatedTwelfthCertifiedFiber i).val.2 r =
      generatedTwelfthCompleteShortDestination i r := by
    rw [monsterNortonShortQ_eq, monsterNortonShortQ_eq] at hq
    apply griessShortClassEquiv.injective
    apply Subtype.ext
    apply leechHyperbolicCoordinates.injective
    have hb := congrArg (fun q : Q => toAdd q.base) hq
    rw [qCentral_mul_base, griessShortQ_image_base] at hb
    exact hb
  have ho := monsterNortonShortOperator_of_Q_image (generatedTwelfthCertifiedFiber i)
    r (generatedTwelfthCompleteShortDestination i r)
    (generatedTwelfthCompleteShortPhase i r) hq X
  change localShortOperator (generatedTwelfthCertifiedFiber i) X
    (griessShortPermutation (generatedTwelfthCertifiedFiber i).val.2 r) = _
  rw [hd, ho]
  simp only [generatedTwelfthCompleteShortCondition,
    generatedNinth_lower_spin_short_index_address] at hc
  have hz := congrArg (fun z : ℤ => (z : ℝ)) hc.2
  simp only [Int.cast_mul, nortonUIntegerSign_real] at hz
  rw [← hinput r, ← hinput (generatedTwelfthCompleteShortDestination i r)] at hz
  nlinarith

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
