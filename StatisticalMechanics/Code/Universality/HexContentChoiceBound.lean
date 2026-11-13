/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Mathlib

namespace StatMech.Universality

open scoped BigOperators





theorem finiteChoice_sum_le_prod
    {ι κ β : Type*} [DecidableEq ι]
    (active : Finset ι) (choices : ι → Finset κ) (objects : Finset β)
    (encode : β → ∀ i, i ∈ active → κ)
    (hencode : ∀ b ∈ objects, encode b ∈ active.pi choices)
    (hinjective : Set.InjOn encode (objects : Set β))
    (choiceWeight : ∀ i, κ → ℝ) (objectWeight : β → ℝ)
    (hweight : ∀ b ∈ objects,
      objectWeight b =
        ∏ i ∈ active.attach, choiceWeight i.1 (encode b i.1 i.2))
    (hnonneg : ∀ p ∈ active.pi choices,
      0 ≤ ∏ i ∈ active.attach, choiceWeight i.1 (p i.1 i.2)) :
    ∑ b ∈ objects, objectWeight b ≤
      ∏ i ∈ active, ∑ k ∈ choices i, choiceWeight i k := by
  classical
  let encodedWeight : (∀ i, i ∈ active → κ) → ℝ :=
    fun p => ∏ i ∈ active.attach, choiceWeight i.1 (p i.1 i.2)
  have himage : objects.image encode ⊆ active.pi choices := by
    intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨b, hb, rfl⟩ := hp
    exact hencode b hb
  have heq :
      ∑ b ∈ objects, objectWeight b =
        ∑ p ∈ objects.image encode, encodedWeight p := by
    rw [Finset.sum_image hinjective]
    apply Finset.sum_congr rfl
    intro b hb
    exact hweight b hb
  rw [heq]
  calc
    (∑ p ∈ objects.image encode, encodedWeight p) ≤
        ∑ p ∈ active.pi choices, encodedWeight p :=
      Finset.sum_le_sum_of_subset_of_nonneg himage
        (fun p hp _ => hnonneg p hp)
    _ = ∏ i ∈ active, ∑ k ∈ choices i, choiceWeight i k := by
      exact (Finset.prod_sum active choices choiceWeight).symm

end StatMech.Universality
