/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Finite transversal certificates for the independently presented C322 source group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.Y555LocalPresentationSignedWords
public import Mathlib.GroupTheory.Index

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Finite right-generator transitions suffice to cover every actual positive source word. -/
theorem y322PositiveWord_finite_cover {size : ℕ} (K : Subgroup Y322Presentation)
    (representative : Fin size → Y322Presentation) (base : Fin size)
    (hbase : representative base = 1)
    (step : ∀ i : Fin size, ∀ v : Fin 8, ∃ h ∈ K, ∃ j : Fin size,
      representative i * PresentedGroup.of v = h * representative j)
    (word : List (Fin 8)) :
    ∃ h ∈ K, ∃ i : Fin size, y322PositiveWord word = h * representative i := by
  induction word using List.reverseRecOn with
  | nil => exact ⟨1, K.one_mem, base, by simp [y322PositiveWord, hbase]⟩
  | append_singleton word v ih =>
    obtain ⟨h, hh, i, hi⟩ := ih
    obtain ⟨k, hk, j, hj⟩ := step i v
    refine ⟨h * k, K.mul_mem hh hk, j, ?_⟩
    have hv : y322PositiveWord [v] = PresentedGroup.of v := by
      simp [y322PositiveWord]
    rw [y322PositiveWord_append, hv, hi, mul_assoc, hj, ← mul_assoc]

/-- The same checked finite transitions cover the original presented group, including inverses. -/
theorem y322Presentation_finite_cover {size : ℕ} (K : Subgroup Y322Presentation)
    (representative : Fin size → Y322Presentation) (base : Fin size)
    (hbase : representative base = 1)
    (step : ∀ i : Fin size, ∀ v : Fin 8, ∃ h ∈ K, ∃ j : Fin size,
      representative i * PresentedGroup.of v = h * representative j)
    (g : Y322Presentation) : ∃ h ∈ K, ∃ i : Fin size, g = h * representative i := by
  apply PresentedGroup.induction_on g
  intro w
  refine Quot.inductionOn w ?_
  intro letters
  change ∃ h ∈ K, ∃ i : Fin size,
    PresentedGroup.mk y322Relations (FreeGroup.mk letters) = h * representative i
  rw [y322SignedWord_value]
  exact y322PositiveWord_finite_cover K representative base hbase step _

/-- An actual finite right-transversal cover bounds the original subgroup index. -/
theorem y322Presentation_index_le_of_cover {size : ℕ} (K : Subgroup Y322Presentation)
    (representative : Fin size → Y322Presentation)
    (cover : ∀ g : Y322Presentation, ∃ h ∈ K, ∃ i : Fin size, g = h * representative i) :
    K.index ≤ size := by
  have hs : Function.Surjective
      (fun i : Fin size => (QuotientGroup.mk (representative i)⁻¹ : Y322Presentation ⧸ K)) := by
    intro q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨h, hh, i, hi⟩ := cover g⁻¹
    refine ⟨i, QuotientGroup.eq.mpr ?_⟩
    have hg : g = (representative i)⁻¹ * h⁻¹ := by
      simpa only [mul_inv_rev, inv_inv] using congrArg (fun x => x⁻¹) hi
    rw [inv_inv, hg, ← mul_assoc, mul_inv_cancel, one_mul]
    exact K.inv_mem hh
  simpa only [Subgroup.index_eq_card, Nat.card_fin] using Nat.card_le_card_of_surjective _ hs

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
