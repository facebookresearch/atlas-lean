/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinShortPackedActions
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthLowerSpinDirectCompatibility
public import Mathlib.Data.Fintype.Card

/-! A genuine signed permutation preserves the finite support and its zero complement.
Full preferred-Q checks on every nonzero source suffice for complete actual short fixation. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Checking the nonzero source coefficients suffices for complete genuine short fixation. -/
theorem generatedNinth_lower_spin_short_fixer_of_nonzero_sources (f : localFiberSubgroup)
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

/-- Exact preferred-Q checks on all nonzero cached sources yield complete actual fixation. -/
theorem generatedNinth_lower_spin_direct_short_fix_of_support_cache (i : Fin 11)
    (h : ∀ a, generatedNinthLowerSpinShortInputInteger
      (generatedNinthLowerSpinShortIndex a) ≠ 0 → generatedNinthLowerSpinShortPackedCondition i a)
    (X : GriessShortIndex → ℝ)
    (hinput : ∀ r, 256 * X r = (generatedNinthLowerSpinShortInputInteger r : ℝ)) :
    localShortRepresentation (generatedNinthLowerSpinDirectFiber i) X = X := by
  apply generatedNinth_lower_spin_short_fixer_of_nonzero_sources
  intro r hr
  have hnonzero : generatedNinthLowerSpinShortInputInteger r ≠ 0 := by
    intro hz
    have hh := hinput r
    rw [hz, Int.cast_zero] at hh
    apply hr
    linarith
  have hp := h (generatedNinthLowerSpinShortAddress r)
    (by simpa only [generatedNinth_lower_spin_short_index_address] using hnonzero)
  have hc := generatedNinth_lower_spin_short_condition_of_packed i
    (generatedNinthLowerSpinShortAddress r) hp
  simp only [generatedNinthLowerSpinShortCondition,
    generatedNinth_lower_spin_short_index_address] at hc
  have hq : spinConjugation (generatedNinthLowerSpinDirectFiber i).val.1
      (monsterNortonShortQ r) = qCentral (generatedNinthLowerSpinShortPhase i r) *
        monsterNortonShortQ (generatedNinthLowerSpinShortDestination i r) := by
    change spinConjugation (generatedNinthLowerSpinCompact i) (monsterNortonShortQ r) = _
    rw [generatedNinth_lower_spin_short_q_fast_actual,
      ← generatedNinth_lower_spin_short_q_mask_actual r,
      ← generatedNinth_lower_spin_short_q_mask_actual
        (generatedNinthLowerSpinShortDestination i r)]
    exact hc.1
  have hd : griessShortPermutation (generatedNinthLowerSpinDirectFiber i).val.2 r =
      generatedNinthLowerSpinShortDestination i r := by
    rw [monsterNortonShortQ_eq, monsterNortonShortQ_eq] at hq
    apply griessShortClassEquiv.injective
    apply Subtype.ext
    apply leechHyperbolicCoordinates.injective
    have hb := congrArg (fun q : Q => toAdd q.base) hq
    rw [qCentral_mul_base, griessShortQ_image_base] at hb
    exact hb
  have ho := monsterNortonShortOperator_of_Q_image (generatedNinthLowerSpinDirectFiber i)
    r (generatedNinthLowerSpinShortDestination i r) (generatedNinthLowerSpinShortPhase i r) hq X
  change localShortOperator (generatedNinthLowerSpinDirectFiber i) X
    (griessShortPermutation (generatedNinthLowerSpinDirectFiber i).val.2 r) = _
  rw [hd, ho]
  have hz := congrArg (fun z : ℤ => (z : ℝ)) hc.2
  simp only [Int.cast_mul, nortonUIntegerSign_real] at hz
  rw [← hinput r, ← hinput (generatedNinthLowerSpinShortDestination i r)] at hz
  nlinarith

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
