/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Mathlib
import Code.Lattice.PlanarTopology

open Set

namespace StatMech.FrontierA

open StatMech.Lattice

variable {d : ℕ}


def realizedL1Distances (A B : Set (Site d)) : Set ℕ :=
  {n | ∃ x ∈ A, ∃ y ∈ B, l1dist d x y = n}



noncomputable def setL1Distance (A B : Set (Site d)) : ℕ :=
  sInf (realizedL1Distances A B)


theorem realizedL1Distances_nonempty {A B : Set (Site d)}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    (realizedL1Distances A B).Nonempty := by
  obtain ⟨x, hx⟩ := hA
  obtain ⟨y, hy⟩ := hB
  exact ⟨l1dist d x y, x, hx, y, hy, rfl⟩


theorem exists_pair_setL1Distance {A B : Set (Site d)}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    ∃ x ∈ A, ∃ y ∈ B, l1dist d x y = setL1Distance A B := by
  have hmem := Nat.sInf_mem (realizedL1Distances_nonempty hA hB)
  simpa [setL1Distance, realizedL1Distances] using hmem


def nearestSourceSet (A B : Set (Site d)) : Set (Site d) :=
  {x | x ∈ A ∧ ∃ y ∈ B, l1dist d x y = setL1Distance A B}

theorem nearestSourceSet_subset (A B : Set (Site d)) :
    nearestSourceSet A B ⊆ A := fun _ hx => hx.1


theorem nearestSourceSet_nonempty {A B : Set (Site d)}
    (hA : A.Nonempty) (hB : B.Nonempty) :
    (nearestSourceSet A B).Nonempty := by
  obtain ⟨x, hx, y, hy, hxy⟩ := exists_pair_setL1Distance hA hB
  exact ⟨x, hx, y, hy, hxy⟩




theorem mem_nearestSourceSet_iff {A B : Set (Site d)} {x : Site d} :
    x ∈ nearestSourceSet A B ↔
      x ∈ A ∧ ∃ y ∈ B, ∀ x' ∈ A, ∀ y' ∈ B,
        l1dist d x y ≤ l1dist d x' y' := by
  constructor
  · rintro ⟨hx, y, hy, hxy⟩
    refine ⟨hx, y, hy, ?_⟩
    intro x' hx' y' hy'
    rw [hxy]
    exact Nat.sInf_le ⟨x', hx', y', hy', rfl⟩
  · rintro ⟨hx, y, hy, hmin⟩
    have hnonempty : (realizedL1Distances A B).Nonempty :=
      ⟨l1dist d x y, x, hx, y, hy, rfl⟩
    obtain ⟨u, hu, v, hv, huv⟩ :=
      (show setL1Distance A B ∈ realizedL1Distances A B by
        exact Nat.sInf_mem hnonempty)
    refine ⟨hx, y, hy, le_antisymm ?_ ?_⟩
    · exact hmin u hu v hv |>.trans_eq huv
    · exact Nat.sInf_le ⟨x, hx, y, hy, rfl⟩



noncomputable def nearestSourceFinset (A B : Set (Site d)) : Finset (Site d) :=
  by
    classical
    exact if h : (nearestSourceSet A B).Finite then h.toFinset else ∅


theorem mem_nearestSourceFinset_iff {A B : Set (Site d)}
    (hfin : (nearestSourceSet A B).Finite) (x : Site d) :
    x ∈ nearestSourceFinset A B ↔ x ∈ nearestSourceSet A B := by
  classical
  simp [nearestSourceFinset, hfin]



theorem mem_nearestSourceSet_of_mem_finset {A B : Set (Site d)} {x : Site d}
    (hx : x ∈ nearestSourceFinset A B) : x ∈ nearestSourceSet A B := by
  classical
  by_cases hfin : (nearestSourceSet A B).Finite
  · exact (mem_nearestSourceFinset_iff hfin x).1 hx
  · simp [nearestSourceFinset, hfin] at hx



theorem mem_nearestSourceFinset_iff_finite {A B : Set (Site d)} {x : Site d} :
    x ∈ nearestSourceFinset A B ↔
      (nearestSourceSet A B).Finite ∧ x ∈ nearestSourceSet A B := by
  classical
  by_cases hfin : (nearestSourceSet A B).Finite
  · simp [nearestSourceFinset, hfin, Set.Finite.mem_toFinset]
  · simp [nearestSourceFinset, hfin]



theorem nearestSourceFinset_card (A B : Set (Site d)) :
    (nearestSourceFinset A B).card = (nearestSourceSet A B).ncard := by
  classical
  by_cases hfin : (nearestSourceSet A B).Finite
  · simp [nearestSourceFinset, hfin, Set.ncard, Set.Finite.toFinset]
  · have hinf : (nearestSourceSet A B).Infinite := by
      by_contra hni
      exact hfin (Set.not_infinite.mp hni)
    simp [nearestSourceFinset, hfin, hinf.ncard]



theorem nearestSourceFinset_nonempty {A B : Set (Site d)}
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hfin : (nearestSourceSet A B).Finite) :
    (nearestSourceFinset A B).Nonempty := by
  obtain ⟨x, hx⟩ := nearestSourceSet_nonempty hA hB
  exact ⟨x, (mem_nearestSourceFinset_iff hfin x).2 hx⟩


theorem l1dist_translate (a x y : Site d) :
    l1dist d (a + x) (a + y) = l1dist d x y := by
  unfold l1dist
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  simp only [Pi.add_apply]
  ring


def translateSiteSet (a : Site d) (A : Set (Site d)) : Set (Site d) :=
  (fun x => a + x) '' A


theorem realizedL1Distances_translate (a : Site d) (A B : Set (Site d)) :
    realizedL1Distances (translateSiteSet a A) (translateSiteSet a B) =
      realizedL1Distances A B := by
  ext n
  simp only [realizedL1Distances, Set.mem_setOf_eq, translateSiteSet,
    Set.mem_image]
  constructor
  · rintro ⟨x', ⟨x, hx, rfl⟩, y', ⟨y, hy, rfl⟩, hxy⟩
    exact ⟨x, hx, y, hy, (l1dist_translate a x y).symm.trans hxy⟩
  · rintro ⟨x, hx, y, hy, hxy⟩
    exact ⟨a + x, ⟨x, hx, rfl⟩, a + y, ⟨y, hy, rfl⟩,
      (l1dist_translate a x y).trans hxy⟩


theorem setL1Distance_translate (a : Site d) (A B : Set (Site d)) :
    setL1Distance (translateSiteSet a A) (translateSiteSet a B) =
      setL1Distance A B := by
  unfold setL1Distance
  rw [realizedL1Distances_translate]


theorem nearestSourceSet_translate (a : Site d) (A B : Set (Site d)) :
    nearestSourceSet (translateSiteSet a A) (translateSiteSet a B) =
      translateSiteSet a (nearestSourceSet A B) := by
  ext z
  constructor
  · rintro ⟨⟨x, hx, hxz⟩, y', ⟨y, hy, rfl⟩, hdist⟩
    subst z
    refine ⟨x, ⟨hx, y, hy, ?_⟩, rfl⟩
    rw [l1dist_translate, setL1Distance_translate] at hdist
    exact hdist
  · rintro ⟨x, ⟨hx, y, hy, hdist⟩, rfl⟩
    refine ⟨⟨x, hx, rfl⟩, a + y, ⟨y, hy, rfl⟩, ?_⟩
    rw [l1dist_translate, setL1Distance_translate]
    exact hdist


theorem nearestSourceFinset_translate (a : Site d) (A B : Set (Site d)) :
    nearestSourceFinset (translateSiteSet a A) (translateSiteSet a B) =
      (nearestSourceFinset A B).image (fun x => a + x) := by
  classical
  have hinj : Function.Injective (fun x : Site d => a + x) := fun _ _ h =>
    add_left_cancel h
  unfold nearestSourceFinset
  rw [nearestSourceSet_translate]
  by_cases hfin : (nearestSourceSet A B).Finite
  · have himg : (translateSiteSet a (nearestSourceSet A B)).Finite := hfin.image _
    rw [dif_pos himg, dif_pos hfin]
    exact Set.Finite.toFinset_image (fun x => a + x) hfin himg
  · have himg : ¬ (translateSiteSet a (nearestSourceSet A B)).Finite := by
      intro hf
      have hpre : nearestSourceSet A B =
          (fun z : Site d => -a + z) ''
            translateSiteSet a (nearestSourceSet A B) := by
        ext x
        constructor
        · intro hx
          exact ⟨a + x, ⟨x, hx, rfl⟩, by simp⟩
        · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
          simpa using hy
      apply hfin
      rw [hpre]
      exact hf.image _
    simp [himg, hfin]

end StatMech.FrontierA
