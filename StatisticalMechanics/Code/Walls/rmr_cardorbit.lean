/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































import Code.Inequalities.PerOrbitCardClose

open Finset

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]










noncomputable def slabBox (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    Finset (ConfigSpace α) :=
  poc_slabBox A B k



noncomputable def slabImg (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    Finset (ConfigSpace α) :=
  poc_slabImg A B k

@[simp] theorem slabBox_def (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    slabBox A B k = poc_slabBox A B k := rfl

@[simp] theorem slabImg_def (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    slabImg A B k = poc_slabImg A B k := rfl





theorem mem_slabBox {A B : Set (ConfigSpace α)} {k : ConfigSpace α × ConfigSpace α}
    {ω : ConfigSpace α} :
    ω ∈ slabBox A B k ↔
      ω ∈ disjointOccurrence A B ∧ orbitKey (ω, poc_keyFlip k ω) = k := by
  simp only [slabBox, poc_slabBox, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_slabImg {A B : Set (ConfigSpace α)} {k : ConfigSpace α × ConfigSpace α}
    {ω : ConfigSpace α} :
    ω ∈ slabImg A B k ↔
      ω ∈ A ∧ poc_keyFlip k ω ∈ B ∧ orbitKey (ω, poc_keyFlip k ω) = k := by
  simp only [slabImg, poc_slabImg, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_boxOrbit {A B : Set (ConfigSpace α)} {k : ConfigSpace α × ConfigSpace α}
    {p : ConfigSpace α × ConfigSpace α} :
    p ∈ boxOrbit A B k ↔ p.1 ∈ disjointOccurrence A B ∧ orbitKey p = k := by
  simp only [boxOrbit, Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_imgOrbit {A B : Set (ConfigSpace α)} {k : ConfigSpace α × ConfigSpace α}
    {q : ConfigSpace α × ConfigSpace α} :
    q ∈ imgOrbit A B k ↔ q.1 ∈ A ∧ q.2 ∈ B ∧ orbitKey q = k := by
  simp only [imgOrbit, Finset.mem_filter, Finset.mem_univ, true_and]







omit [Fintype α] [DecidableEq α] in


theorem pair_eq_of_orbitKey {p : ConfigSpace α × ConfigSpace α}
    {k : ConfigSpace α × ConfigSpace α} (hk : orbitKey p = k) :
    p = (p.1, poc_keyFlip k p.1) :=
  Prod.ext rfl (poc_snd_eq p k hk)









noncomputable def boxOrbitEquivSlabBox (A B : Set (ConfigSpace α))
    (k : ConfigSpace α × ConfigSpace α) :
    {p // p ∈ boxOrbit A B k} ≃ {ω // ω ∈ slabBox A B k} where
  toFun p := ⟨p.1.1, by
    obtain ⟨hbox, hk⟩ := mem_boxOrbit.mp p.2
    rw [mem_slabBox]
    refine ⟨hbox, ?_⟩
    rw [← pair_eq_of_orbitKey hk]; exact hk⟩
  invFun ω := ⟨(ω.1, poc_keyFlip k ω.1), by
    obtain ⟨hbox, hk⟩ := mem_slabBox.mp ω.2
    rw [mem_boxOrbit]; exact ⟨hbox, hk⟩⟩
  left_inv p := by
    obtain ⟨_, hk⟩ := mem_boxOrbit.mp p.2
    exact Subtype.ext (pair_eq_of_orbitKey hk).symm
  right_inv ω := rfl




noncomputable def imgOrbitEquivSlabImg (A B : Set (ConfigSpace α))
    (k : ConfigSpace α × ConfigSpace α) :
    {q // q ∈ imgOrbit A B k} ≃ {ω // ω ∈ slabImg A B k} where
  toFun q := ⟨q.1.1, by
    obtain ⟨hA, hB, hk⟩ := mem_imgOrbit.mp q.2
    rw [mem_slabImg]
    refine ⟨hA, ?_, ?_⟩
    · rw [← poc_snd_eq q.1 k hk]; exact hB
    · rw [← pair_eq_of_orbitKey hk]; exact hk⟩
  invFun ω := ⟨(ω.1, poc_keyFlip k ω.1), by
    obtain ⟨hA, hB, hk⟩ := mem_slabImg.mp ω.2
    rw [mem_imgOrbit]; exact ⟨hA, hB, hk⟩⟩
  left_inv q := by
    obtain ⟨_, _, hk⟩ := mem_imgOrbit.mp q.2
    exact Subtype.ext (pair_eq_of_orbitKey hk).symm
  right_inv ω := rfl





theorem cardOrbit_box (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    #(boxOrbit A B k) = #(slabBox A B k) := by
  rw [← Fintype.card_coe (boxOrbit A B k), ← Fintype.card_coe (slabBox A B k)]
  exact Fintype.card_congr (boxOrbitEquivSlabBox A B k)



theorem cardOrbit_img (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    #(imgOrbit A B k) = #(slabImg A B k) := by
  rw [← Fintype.card_coe (imgOrbit A B k), ← Fintype.card_coe (slabImg A B k)]
  exact Fintype.card_congr (imgOrbitEquivSlabImg A B k)







theorem cardOrbit (A B : Set (ConfigSpace α)) (k : ConfigSpace α × ConfigSpace α) :
    #(boxOrbit A B k) = #(slabBox A B k) ∧ #(imgOrbit A B k) = #(slabImg A B k) :=
  ⟨cardOrbit_box A B k, cardOrbit_img A B k⟩

end StatMech.Walls
