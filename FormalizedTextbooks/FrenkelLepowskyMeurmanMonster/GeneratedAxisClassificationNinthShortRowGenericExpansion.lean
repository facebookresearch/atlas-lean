/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowIndex
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthShortRowCertificates
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationNinthOriginalShortIndex

/-! A family of full original row certificates gives an exact finite expansion of every actual
middle short coordinate. Injectivity comes from the genuine preferred-short permutation and
original source
embedding; no separate numerical distinctness assumption is used. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

variable (hcert : ∀ k : Fin 4136, GeneratedNinthShortRowCertificate k)
include hcert

/-- Every displayed target is the actual original preferred-short image of its source row. -/
theorem generatedNinth_short_row_target_all_of_certificates (k : Fin 4136) :
    generatedNinthMiddleShortSourceIndex (generatedNinthShortRowSource k) =
      generatedNinthShortRowTarget k :=
  generatedNinth_short_row_target_actual k (hcert k)

/-- All displayed target indices are distinct actual preferred short coordinates. -/
theorem generatedNinth_short_row_target_injective_of_certificates :
    Function.Injective generatedNinthShortRowTarget := by
  intro a b h
  apply generatedNinth_short_row_source_injective
  apply generatedNinth_original_short_index_injective
  apply (griessShortPermutation generatedNinthLocalFiber.val.2).injective
  simpa only [← generatedNinth_short_row_target_all_of_certificates hcert,
    generatedNinthMiddleShortSourceIndex] using h

/-- Every actual nonzero middle short coordinate is a checked original source-table target. -/
theorem generatedNinth_short_row_nonzero_covered_of_certificates (r : GriessShortIndex)
    (hr : (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.1 r ≠ 0) :
    ∃ k : Fin 4136, generatedNinthShortRowTarget k = r ∧
      generatedNinthOriginalShortNumerator (generatedNinthShortRowSource k) ≠ 0 := by
  obtain ⟨a, ha, hn⟩ := generatedNinth_middle_short_nonzero_covered r hr
  obtain ⟨k, hk⟩ := generatedNinth_short_row_source_surjective a
  refine ⟨k, ?_, ?_⟩
  · rw [← generatedNinth_short_row_target_all_of_certificates hcert, hk, ha]
  · simpa only [hk] using hn

/-- Every actual middle short coordinate is the finite sum of its checked full-phase source rows. -/
theorem generatedNinth_short_row_expansion_of_certificates (r : GriessShortIndex) :
    (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
      generatedFifthAxis)).2.1 r =
        ∑ k : Fin 4136, if generatedNinthShortRowTarget k = r then
          qSign (generatedNinthShortRowPhase k) *
            ((generatedNinthOriginalShortNumerator (generatedNinthShortRowSource k) : ℝ) / 16)
          else 0 := by
  classical
  by_cases h : ∃ k : Fin 4136, generatedNinthShortRowTarget k = r
  · obtain ⟨k, hk⟩ := h
    rw [Finset.sum_eq_single k]
    · simpa only [hk, ite_true] using
        generatedNinth_short_row_coefficient_actual k (hcert k)
    · intro j _ hj
      have ht : generatedNinthShortRowTarget j ≠ r := by
        intro h'
        exact hj (generatedNinth_short_row_target_injective_of_certificates hcert
          (h'.trans hk.symm))
      simp only [ht, ite_false]
    · simp
  · have hz : (griessConwayEncode (rhoLocal (localFiberIntoH generatedNinthLocalFiber)
        generatedFifthAxis)).2.1 r = 0 := by
      apply not_ne_iff.mp
      intro hn
      obtain ⟨k, hk, _⟩ := generatedNinth_short_row_nonzero_covered_of_certificates hcert r hn
      exact h ⟨k, hk⟩
    rw [hz]
    symm
    apply Finset.sum_eq_zero
    intro k _
    have ht : generatedNinthShortRowTarget k ≠ r := fun hk => h ⟨k, hk⟩
    simp only [ht, ite_false]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
