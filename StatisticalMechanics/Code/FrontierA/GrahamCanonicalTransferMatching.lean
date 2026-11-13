/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamCanonicalTransferComponentCut
import Code.Walls.gc7componenteven










open Finset
open scoped symmDiff

namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]



noncomputable def canonicalMaskRightImages
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    Finset (rightMaskFiber ends m j k l zero p) := by
  classical
  exact Finset.univ.filter fun q =>
    ∃ r : leftMaskFiber ends m j k l zero p,
      CanonicalTransferWorks ends m k zero r.1.1 c.1.1 ∧
        q.1.1 = balancedSwap m
          (canonicalMiddleTransfer ends m r.1.1 k zero)
          (canonicalOuterTransfer ends m r.1.1 k zero) c.1.1

@[simp] theorem mem_canonicalMaskRightImages_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p)
    (q : rightMaskFiber ends m j k l zero p) :
    q ∈ canonicalMaskRightImages ends m j k l zero p c ↔
      ∃ r : leftMaskFiber ends m j k l zero p,
        CanonicalTransferWorks ends m k zero r.1.1 c.1.1 ∧
          q.1.1 = balancedSwap m
            (canonicalMiddleTransfer ends m r.1.1 k zero)
            (canonicalOuterTransfer ends m r.1.1 k zero) c.1.1 := by
  classical
  simp [canonicalMaskRightImages]



theorem canonicalMaskRightImages_nonempty
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    (canonicalMaskRightImages ends m j k l zero p c).Nonempty := by
  let q := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p c c
      (canonicalTransferWorks_self hloop hjk hkl hk0 c)
  refine ⟨q, (mem_canonicalMaskRightImages_iff
    ends m j k l zero p c q).mpr ⟨c,
      canonicalTransferWorks_self hloop hjk hkl hk0 c, ?_⟩⟩
  rfl


theorem rightMaskFiber_rowClass_zero_injective
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Function.Injective (fun q : rightMaskFiber ends m j k l zero p =>
      rowClass m q.1.1 0) := by
  intro q r hqr
  apply Subtype.ext
  apply Subtype.ext
  apply eq_of_rowClass_zero_of_fourColorMaskProfile_eq m q.1.1 r.1.1
  · exact q.2.trans r.2.symm
  · exact hqr


theorem leftMaskFiber_rowClass_zero_injective
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Function.Injective (fun c : leftMaskFiber ends m j k l zero p =>
      rowClass m c.1.1 0) := by
  intro c d hcd
  apply Subtype.ext
  apply Subtype.ext
  apply eq_of_rowClass_zero_of_fourColorMaskProfile_eq m c.1.1 d.1.1
  · exact c.2.trans d.2.symm
  · exact hcd



theorem rowClass_zero_canonicalTransferMapOfWorks
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (a c : leftMaskFiber ends m j k l zero p)
    (hworks : CanonicalTransferWorks ends m k zero a.1.1 c.1.1) :
    rowClass m (canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p a c hworks).1.1 0 =
        canonicalTranslatedRow ends m k zero a.1.1 c.1.1 := by
  have hv := canonicalTransfers_valid_on_sameMask hloop hjk hkl a c
  change rowClass m
    (balancedSwap m
      (canonicalMiddleTransfer ends m a.1.1 k zero)
      (canonicalOuterTransfer ends m a.1.1 k zero) c.1.1) 0 = _
  rw [rowClass_balancedSwap_zero hv.1 hv.2.1]
  rfl



noncomputable def canonicalWorkingTranslatedRows
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) : Finset (Finset I) := by
  classical
  exact (Finset.univ.filter fun r : leftMaskFiber ends m j k l zero p =>
    CanonicalTransferWorks ends m k zero r.1.1 c.1.1).image fun r =>
      canonicalTranslatedRow ends m k zero r.1.1 c.1.1

@[simp] theorem mem_canonicalWorkingTranslatedRows_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) (K : Finset I) :
    K ∈ canonicalWorkingTranslatedRows ends m j k l zero p c ↔
      ∃ r : leftMaskFiber ends m j k l zero p,
        CanonicalTransferWorks ends m k zero r.1.1 c.1.1 ∧
          canonicalTranslatedRow ends m k zero r.1.1 c.1.1 = K := by
  classical
  simp [canonicalWorkingTranslatedRows]



theorem image_rowClass_zero_canonicalMaskRightImages
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    (canonicalMaskRightImages ends m j k l zero p c).image
        (fun q => rowClass m q.1.1 0) =
      canonicalWorkingTranslatedRows ends m j k l zero p c := by
  classical
  ext K
  constructor
  · intro hK
    obtain ⟨q, hq, hrow⟩ := Finset.mem_image.mp hK
    obtain ⟨r, hworks, hqraw⟩ := (mem_canonicalMaskRightImages_iff
      ends m j k l zero p c q).mp hq
    rw [mem_canonicalWorkingTranslatedRows_iff]
    refine ⟨r, hworks, ?_⟩
    rw [← hrow, hqraw]
    have hv := canonicalTransfers_valid_on_sameMask hloop hjk hkl r c
    rw [rowClass_balancedSwap_zero hv.1 hv.2.1]
    rfl
  · intro hK
    obtain ⟨r, hworks, hrow⟩ :=
      (mem_canonicalWorkingTranslatedRows_iff
        ends m j k l zero p c K).mp hK
    let q := canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p r c hworks
    apply Finset.mem_image.mpr
    refine ⟨q, (mem_canonicalMaskRightImages_iff
      ends m j k l zero p c q).mpr ⟨r, hworks, rfl⟩, ?_⟩
    rw [← hrow]
    have hv := canonicalTransfers_valid_on_sameMask hloop hjk hkl r c
    change rowClass m
      (balancedSwap m
        (canonicalMiddleTransfer ends m r.1.1 k zero)
        (canonicalOuterTransfer ends m r.1.1 k zero) c.1.1) 0 = _
    rw [rowClass_balancedSwap_zero hv.1 hv.2.1]
    rfl



theorem card_canonicalMaskRightImages_eq_card_translatedRows
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    (canonicalMaskRightImages ends m j k l zero p c).card =
      (canonicalWorkingTranslatedRows ends m j k l zero p c).card := by
  classical
  calc
    _ = ((canonicalMaskRightImages ends m j k l zero p c).image
        (fun q => rowClass m q.1.1 0)).card :=
      (Finset.card_image_of_injective _
        (rightMaskFiber_rowClass_zero_injective
          ends m j k l zero p)).symm
    _ = _ := congrArg Finset.card
      (image_rowClass_zero_canonicalMaskRightImages
        ends m j k l zero hloop hjk hkl p c)



theorem exists_mem_canonicalMaskRightImages_iff_adjacent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p) :
    (∃ q : rightMaskFiber ends m j k l zero p,
      q ∈ canonicalMaskRightImages ends m j k l zero p c ∧
        q ∈ canonicalMaskRightImages ends m j k l zero p d) ↔
      CanonicalMaskTransferAdjacent ends m j k l zero p c d := by
  constructor
  · rintro ⟨q, hqc, hqd⟩
    obtain ⟨a, -, hqa⟩ := (mem_canonicalMaskRightImages_iff
      ends m j k l zero p c q).mp hqc
    obtain ⟨b, -, hqb⟩ := (mem_canonicalMaskRightImages_iff
      ends m j k l zero p d q).mp hqd
    exact ⟨q, a, b, hqa, hqb⟩
  · rintro ⟨q, a, b, hqa, hqb⟩
    have hac : CanonicalTransferWorks ends m k zero a.1.1 c.1.1 := by
      rw [CanonicalTransferWorks, ← hqa]
      exact q.1.2.2.2.2.2
    have hbd : CanonicalTransferWorks ends m k zero b.1.1 d.1.1 := by
      rw [CanonicalTransferWorks, ← hqb]
      exact q.1.2.2.2.2.2
    exact ⟨q,
      (mem_canonicalMaskRightImages_iff
        ends m j k l zero p c q).mpr ⟨a, hac, hqa⟩,
      (mem_canonicalMaskRightImages_iff
        ends m j k l zero p d q).mpr ⟨b, hbd, hqb⟩⟩



theorem canonicalMaskRightImages_disjoint_of_not_orbit
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p)
    (hcd : ¬ CanonicalMaskTransferOrbit ends m j k l zero p c d) :
    Disjoint
      (canonicalMaskRightImages ends m j k l zero p c)
      (canonicalMaskRightImages ends m j k l zero p d) := by
  classical
  rw [Finset.disjoint_left]
  intro q hqc hqd
  apply hcd
  exact Relation.ReflTransGen.single
    ((exists_mem_canonicalMaskRightImages_iff_adjacent
      ends m j k l zero p c d).mp ⟨q, hqc, hqd⟩)



noncomputable def canonicalMaskRightNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p)) :
    Finset (rightMaskFiber ends m j k l zero p) := by
  classical
  exact Finset.univ.filter fun q =>
    ∃ c ∈ S, q ∈ canonicalMaskRightImages ends m j k l zero p c

@[simp] theorem mem_canonicalMaskRightNeighborhood_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (q : rightMaskFiber ends m j k l zero p) :
    q ∈ canonicalMaskRightNeighborhood ends m j k l zero p S ↔
      ∃ c ∈ S, q ∈ canonicalMaskRightImages
        ends m j k l zero p c := by
  classical
  simp [canonicalMaskRightNeighborhood]



noncomputable def canonicalReferenceNeighborhoodEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (r : leftMaskFiber ends m j k l zero p)
    (hworks : ∀ c ∈ S,
      CanonicalTransferWorks ends m k zero r.1.1 c.1.1) :
    ↑S ↪ ↑(canonicalMaskRightNeighborhood
      ends m j k l zero p S) where
  toFun c := by
    let q := canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p r c.1 (hworks c.1 c.2)
    refine ⟨q, (mem_canonicalMaskRightNeighborhood_iff
      ends m j k l zero p S q).mpr ⟨c.1, c.2, ?_⟩⟩
    exact (mem_canonicalMaskRightImages_iff
      ends m j k l zero p c.1 q).mpr ⟨r, hworks c.1 c.2, rfl⟩
  inj' := by
    intro c d hcd
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    have hraw := congrArg
      (fun q : ↑(canonicalMaskRightNeighborhood
        ends m j k l zero p S) => q.1.1.1) hcd
    change balancedSwap m
        (canonicalMiddleTransfer ends m r.1.1 k zero)
        (canonicalOuterTransfer ends m r.1.1 k zero) c.1.1.1 =
      balancedSwap m
        (canonicalMiddleTransfer ends m r.1.1 k zero)
        (canonicalOuterTransfer ends m r.1.1 k zero) d.1.1.1 at hraw
    have hinv := congrArg
      (balancedSwap m
        (canonicalMiddleTransfer ends m r.1.1 k zero)
        (canonicalOuterTransfer ends m r.1.1 k zero)) hraw
    simpa only [balancedSwap_involutive] using hinv



theorem card_le_canonicalMaskRightNeighborhood_of_reference
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (r : leftMaskFiber ends m j k l zero p)
    (hworks : ∀ c ∈ S,
      CanonicalTransferWorks ends m k zero r.1.1 c.1.1) :
    S.card ≤
      (canonicalMaskRightNeighborhood ends m j k l zero p S).card := by
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective
    (canonicalReferenceNeighborhoodEmbedding
      ends m j k l zero hloop hjk hkl p S r hworks)
    (canonicalReferenceNeighborhoodEmbedding
      ends m j k l zero hloop hjk hkl p S r hworks).injective


theorem canonicalMaskRightNeighborhood_union
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    [DecidableEq (rightMaskFiber ends m j k l zero p)]
    (S T : Finset (leftMaskFiber ends m j k l zero p)) :
    canonicalMaskRightNeighborhood ends m j k l zero p (S ∪ T) =
      canonicalMaskRightNeighborhood ends m j k l zero p S ∪
        canonicalMaskRightNeighborhood ends m j k l zero p T := by
  ext q
  rw [mem_canonicalMaskRightNeighborhood_iff, Finset.mem_union]
  constructor
  · rintro ⟨c, hc, hq⟩
    rw [Finset.mem_union] at hc
    rcases hc with hcS | hcT
    · exact Or.inl ((mem_canonicalMaskRightNeighborhood_iff
        ends m j k l zero p S q).mpr ⟨c, hcS, hq⟩)
    · exact Or.inr ((mem_canonicalMaskRightNeighborhood_iff
        ends m j k l zero p T q).mpr ⟨c, hcT, hq⟩)
  · rintro (hqS | hqT)
    · obtain ⟨c, hc, hq⟩ := (mem_canonicalMaskRightNeighborhood_iff
        ends m j k l zero p S q).mp hqS
      exact ⟨c, Finset.mem_union_left T hc, hq⟩
    · obtain ⟨c, hc, hq⟩ := (mem_canonicalMaskRightNeighborhood_iff
        ends m j k l zero p T q).mp hqT
      exact ⟨c, Finset.mem_union_right S hc, hq⟩


theorem canonicalMaskRightNeighborhood_disjoint_of_orbitSeparated
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S T : Finset (leftMaskFiber ends m j k l zero p))
    (hsep : ∀ c ∈ S, ∀ d ∈ T,
      ¬ CanonicalMaskTransferOrbit ends m j k l zero p c d) :
    Disjoint
      (canonicalMaskRightNeighborhood ends m j k l zero p S)
      (canonicalMaskRightNeighborhood ends m j k l zero p T) := by
  classical
  rw [Finset.disjoint_left]
  intro q hqS hqT
  obtain ⟨c, hcS, hqc⟩ := (mem_canonicalMaskRightNeighborhood_iff
    ends m j k l zero p S q).mp hqS
  obtain ⟨d, hdT, hqd⟩ := (mem_canonicalMaskRightNeighborhood_iff
    ends m j k l zero p T q).mp hqT
  apply hsep c hcS d hdT
  exact Relation.ReflTransGen.single
    ((exists_mem_canonicalMaskRightImages_iff_adjacent
      ends m j k l zero p c d).mp ⟨q, hqc, hqd⟩)



theorem card_le_canonicalMaskRightNeighborhood_union_of_orbitSeparated
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    [DecidableEq (rightMaskFiber ends m j k l zero p)]
    (S T : Finset (leftMaskFiber ends m j k l zero p))
    (hST : Disjoint S T)
    (hsep : ∀ c ∈ S, ∀ d ∈ T,
      ¬ CanonicalMaskTransferOrbit ends m j k l zero p c d)
    (hS : S.card ≤
      (canonicalMaskRightNeighborhood ends m j k l zero p S).card)
    (hT : T.card ≤
      (canonicalMaskRightNeighborhood ends m j k l zero p T).card) :
    (S ∪ T).card ≤
      (canonicalMaskRightNeighborhood ends m j k l zero p (S ∪ T)).card := by
  rw [canonicalMaskRightNeighborhood_union]
  rw [Finset.card_union_of_disjoint hST,
    Finset.card_union_of_disjoint
      (canonicalMaskRightNeighborhood_disjoint_of_orbitSeparated
        ends m j k l zero p S T hsep)]
  omega


theorem card_le_canonicalMaskRightNeighborhood_of_card_le_one
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (hcard : S.card ≤ 1) :
    S.card ≤
      (canonicalMaskRightNeighborhood ends m j k l zero p S).card := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨c, hc⟩ := hS
    apply card_le_canonicalMaskRightNeighborhood_of_reference
      ends m j k l zero hloop hjk hkl p S c
    intro d hd
    have hdc : d = c := (Finset.card_le_one.mp hcard) d hd c hc
    subst d
    exact canonicalTransferWorks_self hloop hjk hkl hk0 c
  · have hzero : S.card = 0 := Finset.card_eq_zero.mpr
      (Finset.not_nonempty_iff_eq_empty.mp hS)
    omega



def CanonicalMaskRightHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ S : Finset (leftMaskFiber ends m j k l zero p),
    S.card ≤
      (canonicalMaskRightNeighborhood ends m j k l zero p S).card



theorem canonicalMaskRightHall_iff_exists_matching
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    CanonicalMaskRightHall ends m j k l zero p ↔
      ∃ f : leftMaskFiber ends m j k l zero p ↪
          rightMaskFiber ends m j k l zero p,
        ∀ c, f c ∈ canonicalMaskRightImages ends m j k l zero p c := by
  classical
  let rel := fun c : leftMaskFiber ends m j k l zero p =>
    fun q : rightMaskFiber ends m j k l zero p =>
      q ∈ canonicalMaskRightImages ends m j k l zero p c
  have hhall := Fintype.all_card_le_filter_rel_iff_exists_injective rel
  constructor
  · intro h
    have h' : ∀ S : Finset (leftMaskFiber ends m j k l zero p),
        S.card ≤ (Finset.univ.filter fun q =>
          ∃ c ∈ S, rel c q).card := by
      simpa only [CanonicalMaskRightHall,
        canonicalMaskRightNeighborhood] using h
    obtain ⟨f, hf, himage⟩ := hhall.mp h'
    exact ⟨⟨f, hf⟩, himage⟩
  · rintro ⟨f, himage⟩
    have h' : ∀ S : Finset (leftMaskFiber ends m j k l zero p),
        S.card ≤ (Finset.univ.filter fun q =>
          ∃ c ∈ S, rel c q).card :=
      hhall.mpr ⟨f, f.injective, himage⟩
    simpa only [CanonicalMaskRightHall,
      canonicalMaskRightNeighborhood] using h'



theorem GrahamFiberMinor_of_canonicalMaskRightHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hhall : ∀ p : Finset I × Finset I,
      CanonicalMaskRightHall ends m j k l zero p) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_maskFiberEmbeddings
  intro p
  exact Classical.choose
    ((canonicalMaskRightHall_iff_exists_matching
      ends m j k l zero p).mp (hhall p))


theorem canonicalMaskRightNeighborhood_mono
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    {S T : Finset (leftMaskFiber ends m j k l zero p)}
    (hST : S ⊆ T) :
    canonicalMaskRightNeighborhood ends m j k l zero p S ⊆
      canonicalMaskRightNeighborhood ends m j k l zero p T := by
  intro q hq
  obtain ⟨c, hcS, hqc⟩ := (mem_canonicalMaskRightNeighborhood_iff
    ends m j k l zero p S q).mp hq
  exact (mem_canonicalMaskRightNeighborhood_iff
    ends m j k l zero p T q).mpr ⟨c, hST hcS, hqc⟩



theorem exists_other_of_erase_canonicalMaskRightNeighborhood_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : leftMaskFiber ends m j k l zero p) (hc : c ∈ S)
    (herase : canonicalMaskRightNeighborhood
        ends m j k l zero p (S.erase c) =
      canonicalMaskRightNeighborhood ends m j k l zero p S)
    (q : rightMaskFiber ends m j k l zero p)
    (hqc : q ∈ canonicalMaskRightImages ends m j k l zero p c) :
    ∃ d ∈ S, d ≠ c ∧
      q ∈ canonicalMaskRightImages ends m j k l zero p d := by
  classical
  have hqS : q ∈ canonicalMaskRightNeighborhood
      ends m j k l zero p S :=
    (mem_canonicalMaskRightNeighborhood_iff
      ends m j k l zero p S q).mpr ⟨c, hc, hqc⟩
  have hqErase : q ∈ canonicalMaskRightNeighborhood
      ends m j k l zero p (S.erase c) := by
    rw [herase]
    exact hqS
  obtain ⟨d, hdErase, hqd⟩ :=
    (mem_canonicalMaskRightNeighborhood_iff
      ends m j k l zero p (S.erase c) q).mp hqErase
  have hd := Finset.mem_erase.mp hdErase
  exact ⟨d, hd.2, hd.1, hqd⟩



theorem exists_other_mem_canonicalWorkingTranslatedRows_of_erase_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : leftMaskFiber ends m j k l zero p) (hc : c ∈ S)
    (herase : canonicalMaskRightNeighborhood
        ends m j k l zero p (S.erase c) =
      canonicalMaskRightNeighborhood ends m j k l zero p S)
    (K : Finset I)
    (hK : K ∈ canonicalWorkingTranslatedRows
      ends m j k l zero p c) :
    ∃ d ∈ S, d ≠ c ∧ K ∈ canonicalWorkingTranslatedRows
      ends m j k l zero p d := by
  classical
  rw [← image_rowClass_zero_canonicalMaskRightImages
    ends m j k l zero hloop hjk hkl p c] at hK
  obtain ⟨q, hqc, hrow⟩ := Finset.mem_image.mp hK
  obtain ⟨d, hdS, hdc, hqd⟩ :=
    exists_other_of_erase_canonicalMaskRightNeighborhood_eq
      ends m j k l zero p S c hc herase q hqc
  refine ⟨d, hdS, hdc, ?_⟩
  rw [← image_rowClass_zero_canonicalMaskRightImages
    ends m j k l zero hloop hjk hkl p d]
  exact Finset.mem_image.mpr ⟨q, hqd, hrow⟩



theorem exists_canonicalMaskRightMatching_of_properHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (c : leftMaskFiber ends m j k l zero p) (hc : c ∈ S) :
    ∃ f : ↑(S.erase c) ↪ rightMaskFiber ends m j k l zero p,
      ∀ x, f x ∈ canonicalMaskRightImages ends m j k l zero p x.1 := by
  classical
  let rel := fun x : ↑(S.erase c) =>
    fun q : rightMaskFiber ends m j k l zero p =>
      q ∈ canonicalMaskRightImages ends m j k l zero p x.1
  have hHall : ∀ A : Finset ↑(S.erase c), A.card ≤
      (Finset.univ.filter fun q => ∃ x ∈ A, rel x q).card := by
    intro A
    let T := A.image fun x => x.1
    have hTS : T ⊆ S := by
      intro x hx
      obtain ⟨y, hyA, rfl⟩ := Finset.mem_image.mp hx
      exact (Finset.mem_erase.mp y.2).2
    have hcT : c ∉ T := by
      intro h
      obtain ⟨y, -, hy⟩ := Finset.mem_image.mp h
      exact (Finset.mem_erase.mp y.2).1 hy
    have hTproper : T ⊂ S :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨hTS, fun hTS' => hcT (hTS' ▸ hc)⟩
    have hcardA : A.card = T.card :=
      (Finset.card_image_of_injective A Subtype.val_injective).symm
    have hneighborhood :
        (Finset.univ.filter fun q => ∃ x ∈ A, rel x q) =
          canonicalMaskRightNeighborhood ends m j k l zero p T := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_univ, true_and,
        mem_canonicalMaskRightNeighborhood_iff, T, rel]
      constructor
      · rintro ⟨x, hxA, hqx⟩
        exact ⟨x.1, Finset.mem_image.mpr ⟨x, hxA, rfl⟩, hqx⟩
      · rintro ⟨x, hxT, hqx⟩
        obtain ⟨y, hyA, hy⟩ := Finset.mem_image.mp hxT
        exact ⟨y, hyA, hy ▸ hqx⟩
    rw [hcardA, hneighborhood]
    exact hproper T hTproper
  obtain ⟨f, hf, himage⟩ :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective rel).mp hHall
  exact ⟨⟨f, hf⟩, himage⟩



theorem exists_canonicalMaskRightNearPerfectEquiv
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (htight : (canonicalMaskRightNeighborhood
        ends m j k l zero p S).card + 1 = S.card)
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (c : leftMaskFiber ends m j k l zero p) (hc : c ∈ S) :
    ∃ f : ↑(S.erase c) ≃
        ↑(canonicalMaskRightNeighborhood ends m j k l zero p S),
      ∀ x, (f x).1 ∈ canonicalMaskRightImages
        ends m j k l zero p x.1 := by
  classical
  obtain ⟨f, hf⟩ := exists_canonicalMaskRightMatching_of_properHall
    ends m j k l zero p S hproper c hc
  let g : ↑(S.erase c) ->
      ↑(canonicalMaskRightNeighborhood ends m j k l zero p S) :=
    fun x => ⟨f x, (mem_canonicalMaskRightNeighborhood_iff
      ends m j k l zero p S (f x)).mpr
        ⟨x.1, (Finset.mem_erase.mp x.2).2, hf x⟩⟩
  have hginj : Function.Injective g := by
    intro x y hxy
    apply f.injective
    exact congrArg Subtype.val hxy
  have hcard : Fintype.card ↑(S.erase c) =
      Fintype.card
        ↑(canonicalMaskRightNeighborhood ends m j k l zero p S) := by
    simp only [Fintype.card_coe]
    rw [Finset.card_erase_of_mem hc]
    omega
  have hgbij : Function.Bijective g :=
    (Fintype.bijective_iff_injective_and_card g).mpr ⟨hginj, hcard⟩
  let e := Equiv.ofBijective g hgbij
  refine ⟨e, ?_⟩
  intro x
  change (g x).1 ∈ canonicalMaskRightImages
    ends m j k l zero p x.1
  exact hf x



theorem exists_canonicalMaskRightAugmentedEquiv
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (htight : (canonicalMaskRightNeighborhood
        ends m j k l zero p S).card + 1 = S.card)
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (c : leftMaskFiber ends m j k l zero p) (hc : c ∈ S) :
    ∃ f : ↑S ≃ Option
        ↑(canonicalMaskRightNeighborhood ends m j k l zero p S),
      f ⟨c, hc⟩ = none ∧
        ∀ x : ↑S, x.1 ≠ c -> ∃ q,
          f x = some q ∧
            q.1 ∈ canonicalMaskRightImages
              ends m j k l zero p x.1 := by
  classical
  obtain ⟨e, he⟩ := exists_canonicalMaskRightNearPerfectEquiv
    ends m j k l zero p S htight hproper c hc
  have hset : (↑S : Set (leftMaskFiber ends m j k l zero p)) =
      ↑(insert c (S.erase c)) := by
    rw [Finset.insert_erase hc]
  let eDomain : ↑S ≃ ↑(insert c (S.erase c)) := Equiv.setCongr hset
  let eSplit : ↑(insert c (S.erase c)) ≃ Option ↑(S.erase c) :=
    Finset.subtypeInsertEquivOption (Finset.notMem_erase c S)
  let f := eDomain.trans (eSplit.trans (Equiv.optionCongr e))
  refine ⟨f, ?_, ?_⟩
  · have hval : ↑(eDomain ⟨c, hc⟩) = c := rfl
    simp [f, eSplit, Finset.subtypeInsertEquivOption, hval]
  · intro x hxc
    let xe : ↑(S.erase c) :=
      ⟨x.1, Finset.mem_erase.mpr ⟨hxc, x.2⟩⟩
    refine ⟨e xe, ?_, he xe⟩
    have hval : ↑(eDomain x) = x.1 := rfl
    simp [f, eSplit, Finset.subtypeInsertEquivOption, hval, xe]
    exact hxc


abbrev canonicalMaskRightAugmentedEquivType
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p)) :=
  ↑S ≃ Option ↑(canonicalMaskRightNeighborhood
    ends m j k l zero p S)


def CanonicalMaskRightAugmentedMatching
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType
      ends m j k l zero p S) : Prop :=
  f c = none ∧
    ∀ x : ↑S, x ≠ c -> ∃ q,
      f x = some q ∧ q.1 ∈ canonicalMaskRightImages
        ends m j k l zero p x.1



noncomputable def canonicalMaskRightAugmentedAssignedImage
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (x : ↑S) (hxc : x ≠ c) :
    ↑(canonicalMaskRightNeighborhood ends m j k l zero p S) :=
  (hf.2 x hxc).choose

theorem canonicalMaskRightAugmentedAssignedImage_apply
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (x : ↑S) (hxc : x ≠ c) :
    f x = some (canonicalMaskRightAugmentedAssignedImage
      ends m j k l zero p S c f hf x hxc) :=
  (hf.2 x hxc).choose_spec.1

theorem canonicalMaskRightAugmentedAssignedImage_mem
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (x : ↑S) (hxc : x ≠ c) :
    (canonicalMaskRightAugmentedAssignedImage
      ends m j k l zero p S c f hf x hxc).1 ∈
        canonicalMaskRightImages ends m j k l zero p x.1 :=
  (hf.2 x hxc).choose_spec.2



noncomputable def canonicalMaskRightAugmentedAssignedRows
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S T : Finset (leftMaskFiber ends m j k l zero p))
    (hTS : T ⊆ S)
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f) :
    Finset (rightMaskFiber ends m j k l zero p) := by
  classical
  exact (T.erase c.1).attach.image fun x =>
    (canonicalMaskRightAugmentedAssignedImage
      ends m j k l zero p S c f hf
      ⟨x.1, hTS (Finset.mem_of_mem_erase x.2)⟩ (by
        intro h
        exact (Finset.mem_erase.mp x.2).1 (congrArg Subtype.val h))).1

theorem canonicalMaskRightAugmentedAssignedRows_contains
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S T : Finset (leftMaskFiber ends m j k l zero p))
    (hTS : T ⊆ S)
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (u : ↑S) (huT : u.1 ∈ T) (huc : u ≠ c) :
    ∃ qS : ↑(canonicalMaskRightNeighborhood
        ends m j k l zero p S),
      f u = some qS ∧ qS.1 ∈ canonicalMaskRightAugmentedAssignedRows
        ends m j k l zero p S T hTS c f hf := by
  classical
  let qS := canonicalMaskRightAugmentedAssignedImage
    ends m j k l zero p S c f hf u huc
  refine ⟨qS, canonicalMaskRightAugmentedAssignedImage_apply
    ends m j k l zero p S c f hf u huc, ?_⟩
  have huErase : u.1 ∈ T.erase c.1 := Finset.mem_erase.mpr ⟨by
    intro h
    exact huc (Subtype.ext h), huT⟩
  let x : ↑(T.erase c.1) := ⟨u.1, huErase⟩
  rw [canonicalMaskRightAugmentedAssignedRows]
  apply Finset.mem_image.mpr
  refine ⟨x, Finset.mem_attach _ _, ?_⟩
  let xS : ↑S := ⟨x.1, hTS (Finset.mem_of_mem_erase x.2)⟩
  have hxc : xS ≠ c := by
    intro h
    exact (Finset.mem_erase.mp x.2).1 (congrArg Subtype.val h)
  have hxS : xS = u :=
    Subtype.ext rfl
  change (canonicalMaskRightAugmentedAssignedImage
    ends m j k l zero p S c f hf xS hxc).1 = qS.1
  apply congrArg Subtype.val
  apply Option.some.inj
  calc
    some (canonicalMaskRightAugmentedAssignedImage
        ends m j k l zero p S c f hf xS hxc) = f xS :=
      (canonicalMaskRightAugmentedAssignedImage_apply
        ends m j k l zero p S c f hf xS hxc).symm
    _ = f u := congrArg f hxS
    _ = some qS := canonicalMaskRightAugmentedAssignedImage_apply
      ends m j k l zero p S c f hf u huc

theorem card_canonicalMaskRightAugmentedAssignedRows
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S T : Finset (leftMaskFiber ends m j k l zero p))
    (hTS : T ⊆ S)
    (c : ↑S) (hcT : c.1 ∈ T)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f) :
    (canonicalMaskRightAugmentedAssignedRows
      ends m j k l zero p S T hTS c f hf).card + 1 = T.card := by
  classical
  let g : ↑(T.erase c.1) -> rightMaskFiber ends m j k l zero p := fun x =>
    (canonicalMaskRightAugmentedAssignedImage
      ends m j k l zero p S c f hf
      ⟨x.1, hTS (Finset.mem_of_mem_erase x.2)⟩ (by
        intro h
        exact (Finset.mem_erase.mp x.2).1 (congrArg Subtype.val h))).1
  have hg : Function.Injective g := by
    intro x y hxy
    let xS : ↑S := ⟨x.1, hTS (Finset.mem_of_mem_erase x.2)⟩
    let yS : ↑S := ⟨y.1, hTS (Finset.mem_of_mem_erase y.2)⟩
    have hxc : xS ≠ c := by
      intro h
      exact (Finset.mem_erase.mp x.2).1 (congrArg Subtype.val h)
    have hyc : yS ≠ c := by
      intro h
      exact (Finset.mem_erase.mp y.2).1 (congrArg Subtype.val h)
    let qx := canonicalMaskRightAugmentedAssignedImage
      ends m j k l zero p S c f hf xS hxc
    let qy := canonicalMaskRightAugmentedAssignedImage
      ends m j k l zero p S c f hf yS hyc
    have hq : qx = qy := Subtype.ext hxy
    have hfx := canonicalMaskRightAugmentedAssignedImage_apply
      ends m j k l zero p S c f hf xS hxc
    have hfy := canonicalMaskRightAugmentedAssignedImage_apply
      ends m j k l zero p S c f hf yS hyc
    have hfxy : f xS = f yS := calc
      f xS = some qx := hfx
      _ = some qy := congrArg some hq
      _ = f yS := hfy.symm
    have hxyS : xS = yS := f.injective hfxy
    apply Subtype.ext
    exact congrArg (fun z : ↑S => z.1) hxyS
  have hpos : 0 < T.card := Finset.card_pos.mpr ⟨c.1, hcT⟩
  change (Finset.image g (T.erase c.1).attach).card + 1 = T.card
  rw [Finset.card_image_of_injective _ hg, Finset.card_attach,
    Finset.card_erase_of_mem hcT]
  omega

theorem canonicalMaskRightAugmentedAssignedRows_subset_neighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S T : Finset (leftMaskFiber ends m j k l zero p))
    (hTS : T ⊆ S)
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f) :
    canonicalMaskRightAugmentedAssignedRows
        ends m j k l zero p S T hTS c f hf ⊆
      canonicalMaskRightNeighborhood ends m j k l zero p T := by
  classical
  intro q hq
  rw [canonicalMaskRightAugmentedAssignedRows] at hq
  obtain ⟨x, -, hqx⟩ := Finset.mem_image.mp hq
  have hxT : x.1 ∈ T := Finset.mem_of_mem_erase x.2
  have hxS : x.1 ∈ S := hTS hxT
  let xS : ↑S := ⟨x.1, hxS⟩
  have hxc : xS ≠ c := by
    intro h
    exact (Finset.mem_erase.mp x.2).1 (congrArg Subtype.val h)
  have hmem := canonicalMaskRightAugmentedAssignedImage_mem
    ends m j k l zero p S c f hf xS hxc
  apply (mem_canonicalMaskRightNeighborhood_iff
    ends m j k l zero p T q).mpr
  refine ⟨x.1, hxT, ?_⟩
  rw [← hqx]
  exact hmem



theorem canonicalMaskRightAugmentedAssignedRows_full_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (htight : (canonicalMaskRightNeighborhood
        ends m j k l zero p S).card + 1 = S.card)
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f) :
    canonicalMaskRightAugmentedAssignedRows ends m j k l zero p
        S S Finset.Subset.rfl c f hf =
      canonicalMaskRightNeighborhood ends m j k l zero p S := by
  classical
  apply Finset.eq_of_subset_of_card_le
    (canonicalMaskRightAugmentedAssignedRows_subset_neighborhood
      ends m j k l zero p S S Finset.Subset.rfl c f hf)
  have hcard := card_canonicalMaskRightAugmentedAssignedRows
    ends m j k l zero p S S Finset.Subset.rfl c c.2 f hf
  omega



noncomputable def canonicalMaskRightAugmentedAssignedEquiv
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f) :
    {u : ↑S // u ≠ c} ≃
      ↑(canonicalMaskRightNeighborhood ends m j k l zero p S) := by
  classical
  let g : {u : ↑S // u ≠ c} ->
      ↑(canonicalMaskRightNeighborhood ends m j k l zero p S) := fun u =>
    canonicalMaskRightAugmentedAssignedImage
      ends m j k l zero p S c f hf u.1 u.2
  have hinj : Function.Injective g := by
    intro u v huv
    apply Subtype.ext
    apply f.injective
    calc
      f u.1 = some (g u) := canonicalMaskRightAugmentedAssignedImage_apply
        ends m j k l zero p S c f hf u.1 u.2
      _ = some (g v) := congrArg some huv
      _ = f v.1 := (canonicalMaskRightAugmentedAssignedImage_apply
        ends m j k l zero p S c f hf v.1 v.2).symm
  have hsurj : Function.Surjective g := by
    intro q
    let x : ↑S := f.symm (some q)
    have hxc : x ≠ c := by
      intro h
      have happly : f x = some q := by simp [x]
      rw [h, hf.1] at happly
      simp at happly
    let u : {u : ↑S // u ≠ c} := ⟨x, hxc⟩
    refine ⟨u, ?_⟩
    apply Option.some.inj
    calc
      some (g u) = f x := (canonicalMaskRightAugmentedAssignedImage_apply
        ends m j k l zero p S c f hf x hxc).symm
      _ = some q := by simp [x]
  exact Equiv.ofBijective g ⟨hinj, hsurj⟩



theorem canonicalMaskRightSecondRows_collision_or_equiv
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (s : {u : ↑S // u ≠ c} ->
      ↑(canonicalMaskRightNeighborhood ends m j k l zero p S))
    (hne : ∀ u, s u ≠ canonicalMaskRightAugmentedAssignedImage
      ends m j k l zero p S c f hf u.1 u.2) :
    (∃ u v, u ≠ v ∧ s u = s v) ∨
      ∃ e : {u : ↑S // u ≠ c} ≃
          ↑(canonicalMaskRightNeighborhood ends m j k l zero p S),
        (∀ u, e u = s u) ∧
        ∀ u, e u ≠ canonicalMaskRightAugmentedAssignedImage
          ends m j k l zero p S c f hf u.1 u.2 := by
  classical
  by_cases hinj : Function.Injective s
  · right
    have hcard : Fintype.card {u : ↑S // u ≠ c} =
        Fintype.card ↑(canonicalMaskRightNeighborhood
          ends m j k l zero p S) :=
      Fintype.card_congr (canonicalMaskRightAugmentedAssignedEquiv
        ends m j k l zero p S c f hf)
    have hbij : Function.Bijective s :=
      (Fintype.bijective_iff_injective_and_card s).mpr ⟨hinj, hcard⟩
    let e := Equiv.ofBijective s hbij
    exact ⟨e, fun _ => rfl, hne⟩
  · left
    obtain ⟨u, v, huv, huvne⟩ := Function.not_injective_iff.mp hinj
    exact ⟨u, v, huvne, huv⟩





theorem canonicalMaskRightFullSecondRows_repetition_or_equiv
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (hsecond : ∀ u : {u : ↑S // u ≠ c},
      ∃ r : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S),
        r ≠ canonicalMaskRightAugmentedAssignedImage
          ends m j k l zero p S c f hf u.1 u.2 ∧
        r.1 ∈ canonicalMaskRightImages ends m j k l zero p u.1.1) :
    (∃ u v : {u : ↑S // u ≠ c},
        ∃ r : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S),
          u ≠ v ∧
          r ≠ canonicalMaskRightAugmentedAssignedImage
            ends m j k l zero p S c f hf u.1 u.2 ∧
          r ≠ canonicalMaskRightAugmentedAssignedImage
            ends m j k l zero p S c f hf v.1 v.2 ∧
          r.1 ∈ canonicalMaskRightImages ends m j k l zero p u.1.1 ∧
          r.1 ∈ canonicalMaskRightImages ends m j k l zero p v.1.1) ∨
      ∃ e : {u : ↑S // u ≠ c} ≃
          ↑(canonicalMaskRightNeighborhood ends m j k l zero p S),
        ∀ u,
          e u ≠ canonicalMaskRightAugmentedAssignedImage
            ends m j k l zero p S c f hf u.1 u.2 ∧
          (e u).1 ∈ canonicalMaskRightImages
            ends m j k l zero p u.1.1 := by
  classical
  let s : {u : ↑S // u ≠ c} ->
      ↑(canonicalMaskRightNeighborhood ends m j k l zero p S) := fun u =>
    (hsecond u).choose
  have hs : ∀ u,
      s u ≠ canonicalMaskRightAugmentedAssignedImage
          ends m j k l zero p S c f hf u.1 u.2 ∧
        (s u).1 ∈ canonicalMaskRightImages
          ends m j k l zero p u.1.1 := fun u => (hsecond u).choose_spec
  rcases canonicalMaskRightSecondRows_collision_or_equiv
      ends m j k l zero p S c f hf s (fun u => (hs u).1) with
    hrepeat | hequiv
  · left
    obtain ⟨u, v, huv, hsuv⟩ := hrepeat
    refine ⟨u, v, s u, huv, (hs u).1, ?_, (hs u).2, ?_⟩
    · rw [hsuv]
      exact (hs v).1
    · rw [hsuv]
      exact (hs v).2
  · right
    obtain ⟨e, he, hene⟩ := hequiv
    refine ⟨e, ?_⟩
    intro u
    refine ⟨hene u, ?_⟩
    rw [he u]
    exact (hs u).2



theorem canonicalMaskRightSecondRowEquiv_collisionPerm
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (e : {u : ↑S // u ≠ c} ≃
      ↑(canonicalMaskRightNeighborhood ends m j k l zero p S))
    (hene : ∀ u, e u ≠ canonicalMaskRightAugmentedAssignedImage
      ends m j k l zero p S c f hf u.1 u.2)
    (hemem : ∀ u, (e u).1 ∈ canonicalMaskRightImages
      ends m j k l zero p u.1.1) :
    ∃ τ : Equiv.Perm {u : ↑S // u ≠ c},
      (∀ u, τ u ≠ u) ∧
      ∀ u,
        (e u).1 ∈ canonicalMaskRightImages
            ends m j k l zero p u.1.1 ∧
          (e u).1 ∈ canonicalMaskRightImages
            ends m j k l zero p (τ u).1.1 := by
  let base := canonicalMaskRightAugmentedAssignedEquiv
    ends m j k l zero p S c f hf
  let τ : Equiv.Perm {u : ↑S // u ≠ c} := e.trans base.symm
  refine ⟨τ, ?_, ?_⟩
  · intro u hfix
    apply hene u
    calc
      e u = base (τ u) := by simp [τ, base]
      _ = base u := congrArg base hfix
      _ = canonicalMaskRightAugmentedAssignedImage
          ends m j k l zero p S c f hf u.1 u.2 := rfl
  · intro u
    refine ⟨hemem u, ?_⟩
    have hbase : base (τ u) = e u := by simp [τ, base]
    have hmem := canonicalMaskRightAugmentedAssignedImage_mem
      ends m j k l zero p S c f hf (τ u).1 (τ u).2
    change (base (τ u)).1 ∈ canonicalMaskRightImages
      ends m j k l zero p (τ u).1.1 at hmem
    rwa [hbase] at hmem



theorem canonicalMaskRightRepeatedSecondRow_threePreimages
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (u v : {u : ↑S // u ≠ c})
    (r : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S))
    (huv : u ≠ v)
    (hru : r ≠ canonicalMaskRightAugmentedAssignedImage
      ends m j k l zero p S c f hf u.1 u.2)
    (hrv : r ≠ canonicalMaskRightAugmentedAssignedImage
      ends m j k l zero p S c f hf v.1 v.2)
    (hruMem : r.1 ∈ canonicalMaskRightImages
      ends m j k l zero p u.1.1)
    (hrvMem : r.1 ∈ canonicalMaskRightImages
      ends m j k l zero p v.1.1) :
    ∃ w : {u : ↑S // u ≠ c},
      u ≠ v ∧ w ≠ u ∧ w ≠ v ∧
      r.1 ∈ canonicalMaskRightImages ends m j k l zero p u.1.1 ∧
      r.1 ∈ canonicalMaskRightImages ends m j k l zero p v.1.1 ∧
      r.1 ∈ canonicalMaskRightImages ends m j k l zero p w.1.1 := by
  let base := canonicalMaskRightAugmentedAssignedEquiv
    ends m j k l zero p S c f hf
  let w : {u : ↑S // u ≠ c} := base.symm r
  have hbase : base w = r := by simp [w]
  have hwu : w ≠ u := by
    intro h
    apply hru
    calc
      r = base w := hbase.symm
      _ = base u := congrArg base h
      _ = canonicalMaskRightAugmentedAssignedImage
          ends m j k l zero p S c f hf u.1 u.2 := rfl
  have hwv : w ≠ v := by
    intro h
    apply hrv
    calc
      r = base w := hbase.symm
      _ = base v := congrArg base h
      _ = canonicalMaskRightAugmentedAssignedImage
          ends m j k l zero p S c f hf v.1 v.2 := rfl
  have hrw := canonicalMaskRightAugmentedAssignedImage_mem
    ends m j k l zero p S c f hf w.1 w.2
  change (base w).1 ∈ canonicalMaskRightImages
    ends m j k l zero p w.1.1 at hrw
  rw [hbase] at hrw
  exact ⟨w, huv, hwu, hwv, hruMem, hrvMem, hrw⟩



noncomputable def canonicalMaskRightAugmentedMatchingPairs
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c d : ↑S) : Finset
      (canonicalMaskRightAugmentedEquivType ends m j k l zero p S ×
        canonicalMaskRightAugmentedEquivType ends m j k l zero p S) := by
  classical
  exact Finset.univ.filter fun ef =>
    CanonicalMaskRightAugmentedMatching
        ends m j k l zero p S c ef.1 ∧
      CanonicalMaskRightAugmentedMatching
        ends m j k l zero p S d ef.2

@[simp] theorem mem_canonicalMaskRightAugmentedMatchingPairs_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c d : ↑S)
    (ef : canonicalMaskRightAugmentedEquivType
          ends m j k l zero p S ×
        canonicalMaskRightAugmentedEquivType ends m j k l zero p S) :
    ef ∈ canonicalMaskRightAugmentedMatchingPairs
        ends m j k l zero p S c d ↔
      CanonicalMaskRightAugmentedMatching
          ends m j k l zero p S c ef.1 ∧
        CanonicalMaskRightAugmentedMatching
          ends m j k l zero p S d ef.2 := by
  classical
  simp [canonicalMaskRightAugmentedMatchingPairs]

set_option maxHeartbeats 1000000 in



theorem canonicalMaskRightAugmentedMatchingPair_transition
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c d : ↑S)
    (ef : canonicalMaskRightAugmentedEquivType
          ends m j k l zero p S ×
        canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hef : ef ∈ canonicalMaskRightAugmentedMatchingPairs
      ends m j k l zero p S c d) :
    let σ : Equiv.Perm ↑S := ef.1.trans ef.2.symm
    σ c = d ∧ ∀ x : ↑S, x ≠ c ->
      ∃ q : rightMaskFiber ends m j k l zero p,
        q ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
          q ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1 := by
  classical
  have hmatch := (mem_canonicalMaskRightAugmentedMatchingPairs_iff
    ends m j k l zero p S c d ef).mp hef
  rcases hmatch with ⟨⟨hfc0, hfc⟩, ⟨hfd0, hfd⟩⟩
  dsimp only
  constructor
  · apply ef.2.injective
    simp [hfc0, hfd0]
  · intro x hxc
    obtain ⟨q, hfcx, hqx⟩ := hfc x hxc
    have hfdσ : ef.2 (ef.1.trans ef.2.symm x) = some q := by
      rw [← hfcx]
      simp
    have hσd : ef.1.trans ef.2.symm x ≠ d := by
      intro hval
      rw [hval, hfd0] at hfdσ
      simp at hfdσ
    obtain ⟨r, hfdr, hr⟩ := hfd (ef.1.trans ef.2.symm x) hσd
    have hrq : r = q := by
      rw [hfdσ] at hfdr
      exact Option.some.inj hfdr.symm
    subst r
    exact ⟨q.1, hqx, hr⟩

set_option maxHeartbeats 1000000 in




theorem canonicalMaskRightAugmentedMatchingPair_secondCommon_displacement
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c d : ↑S)
    (ef : canonicalMaskRightAugmentedEquivType
          ends m j k l zero p S ×
        canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hef : ef ∈ canonicalMaskRightAugmentedMatchingPairs
      ends m j k l zero p S c d)
    (x : ↑S) (hxc : x ≠ c) :
    let σ : Equiv.Perm ↑S := ef.1.trans ef.2.symm
    ∃ q : rightMaskFiber ends m j k l zero p,
      q ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
      q ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1 ∧
      ∀ r : rightMaskFiber ends m j k l zero p, r ≠ q ->
        r ∈ canonicalMaskRightImages ends m j k l zero p x.1 ->
        r ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1 ->
        ∃ u v : ↑S,
          u ≠ c ∧ v ≠ d ∧ u ≠ x ∧ v ≠ σ x ∧ σ u = v ∧
            r ∈ canonicalMaskRightImages ends m j k l zero p u.1 ∧
            r ∈ canonicalMaskRightImages ends m j k l zero p v.1 := by
  classical
  have hmatch := (mem_canonicalMaskRightAugmentedMatchingPairs_iff
    ends m j k l zero p S c d ef).mp hef
  rcases hmatch with ⟨⟨hfc0, hfc⟩, ⟨hfd0, hfd⟩⟩
  dsimp only
  obtain ⟨q, hfcx, hqx⟩ := hfc x hxc
  have hfdσ : ef.2 (ef.1.trans ef.2.symm x) = some q := by
    rw [← hfcx]
    simp
  have hσd : ef.1.trans ef.2.symm x ≠ d := by
    intro hval
    rw [hval, hfd0] at hfdσ
    simp at hfdσ
  obtain ⟨q', hfdq', hqσ⟩ := hfd (ef.1.trans ef.2.symm x) hσd
  have hq'q : q' = q := by
    rw [hfdσ] at hfdq'
    exact Option.some.inj hfdq'.symm
  subst q'
  refine ⟨q.1, hqx, hqσ, ?_⟩
  intro r hrq hrx hrσ
  have hrS : r ∈ canonicalMaskRightNeighborhood
      ends m j k l zero p S :=
    (mem_canonicalMaskRightNeighborhood_iff
      ends m j k l zero p S r).mpr ⟨x.1, x.2, hrx⟩
  let rS : ↑(canonicalMaskRightNeighborhood
      ends m j k l zero p S) := ⟨r, hrS⟩
  let u : ↑S := ef.1.symm (some rS)
  let v : ↑S := ef.2.symm (some rS)
  have hfcu : ef.1 u = some rS := by simp [u]
  have hfdv : ef.2 v = some rS := by simp [v]
  have huc : u ≠ c := by
    intro h
    rw [h, hfc0] at hfcu
    simp at hfcu
  have hvd : v ≠ d := by
    intro h
    rw [h, hfd0] at hfdv
    simp at hfdv
  have hux : u ≠ x := by
    intro h
    have heq : some rS = some q := by
      rw [← hfcu, h, hfcx]
    have hrSq : rS = q := Option.some.inj heq
    exact hrq (congrArg Subtype.val hrSq)
  have hvσ : v ≠ ef.1.trans ef.2.symm x := by
    intro h
    have heq : some rS = some q := by
      rw [← hfdv, h, hfdσ]
    have hrSq : rS = q := Option.some.inj heq
    exact hrq (congrArg Subtype.val hrSq)
  have hσuv : ef.1.trans ef.2.symm u = v := by
    apply ef.2.injective
    rw [hfdv]
    simp [hfcu]
  obtain ⟨ru, hfcru, hru⟩ := hfc u huc
  have hruS : ru = rS := by
    rw [hfcu] at hfcru
    exact Option.some.inj hfcru.symm
  subst ru
  obtain ⟨rv, hfdrv, hrv⟩ := hfd v hvd
  have hrvS : rv = rS := by
    rw [hfdv] at hfdrv
    exact Option.some.inj hfdrv.symm
  subst rv
  exact ⟨u, v, huc, hvd, hux, hvσ, hσuv, hru, hrv⟩




theorem exists_canonicalMaskRightNeighbor_not_mem_of_properHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (T : Finset (leftMaskFiber ends m j k l zero p)) (hTS : T ⊂ S)
    (R : Finset (rightMaskFiber ends m j k l zero p))
    (hcard : R.card < T.card) :
    ∃ x ∈ T, ∃ q : rightMaskFiber ends m j k l zero p,
      q ∈ canonicalMaskRightImages ends m j k l zero p x ∧ q ∉ R := by
  classical
  have hHall := hproper T hTS
  have hex : ∃ q ∈ canonicalMaskRightNeighborhood
      ends m j k l zero p T, q ∉ R := by
    by_contra h
    push Not at h
    have hsub : canonicalMaskRightNeighborhood
        ends m j k l zero p T ⊆ R := by
      intro q hq
      exact h q hq
    have hle := Finset.card_le_card hsub
    omega
  obtain ⟨q, hqT, hqR⟩ := hex
  obtain ⟨x, hxT, hqx⟩ := (mem_canonicalMaskRightNeighborhood_iff
    ends m j k l zero p T q).mp hqT
  exact ⟨x, hxT, q, hqx, hqR⟩



theorem exists_canonicalMaskRightNeighbor_ne_pair_of_properHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (T : Finset (leftMaskFiber ends m j k l zero p)) (hTS : T ⊂ S)
    (hcard : 2 < T.card)
    (q r : rightMaskFiber ends m j k l zero p) :
    ∃ x ∈ T, ∃ s : rightMaskFiber ends m j k l zero p,
      s ∈ canonicalMaskRightImages ends m j k l zero p x ∧
        s ≠ q ∧ s ≠ r := by
  classical
  obtain ⟨x, hxT, s, hsx, hs⟩ :=
    exists_canonicalMaskRightNeighbor_not_mem_of_properHall
      ends m j k l zero p S hproper T hTS {q, r} (by
        have hp := Finset.card_insert_le q ({r} : Finset
          (rightMaskFiber ends m j k l zero p))
        simp only [Finset.card_singleton] at hp
        omega)
  refine ⟨x, hxT, s, hsx, ?_, ?_⟩
  · intro hsq
    exact hs (by simp [hsq])
  · intro hsr
    exact hs (by simp [hsr])




theorem canonicalMaskRightExposure_terminal_or_escapes
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (htight : (canonicalMaskRightNeighborhood
        ends m j k l zero p S).card + 1 = S.card)
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (T : Finset (leftMaskFiber ends m j k l zero p)) (hTS : T ⊆ S)
    (R : Finset (rightMaskFiber ends m j k l zero p))
    (hR : R ⊆ canonicalMaskRightNeighborhood ends m j k l zero p T)
    (hdef : R.card + 1 = T.card) :
    (T = S ∧ R = canonicalMaskRightNeighborhood
        ends m j k l zero p S) ∨
      ∃ x ∈ T, ∃ q : rightMaskFiber ends m j k l zero p,
        q ∈ canonicalMaskRightImages ends m j k l zero p x ∧ q ∉ R := by
  classical
  by_cases hfull : T = S
  · left
    subst T
    refine ⟨rfl, Finset.eq_of_subset_of_card_le hR ?_⟩
    omega
  · right
    have hTS' : T ⊂ S :=
      (Finset.ssubset_iff_subset_ne).mpr ⟨hTS, hfull⟩
    exact exists_canonicalMaskRightNeighbor_not_mem_of_properHall
      ends m j k l zero p S hproper T hTS' R (by omega)





theorem exists_canonicalMaskRightAugmentedMatching_escape
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (T : Finset (leftMaskFiber ends m j k l zero p)) (hTS : T ⊂ S)
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (R : Finset (rightMaskFiber ends m j k l zero p))
    (hcard : R.card < T.card)
    (hassigned : ∀ u : ↑S, u.1 ∈ T -> u ≠ c ->
      ∃ qS : ↑(canonicalMaskRightNeighborhood
          ends m j k l zero p S),
        f u = some qS ∧ qS.1 ∈ R) :
    ∃ x ∈ T,
      ∃ qS : ↑(canonicalMaskRightNeighborhood
          ends m j k l zero p S),
        qS.1 ∈ canonicalMaskRightImages ends m j k l zero p x ∧
        qS.1 ∉ R ∧
        ∃ u : ↑S,
          f u = some qS ∧ u.1 ∉ T ∧
          (S \ insert u.1 T).card < (S \ T).card := by
  classical
  obtain ⟨x, hxT, q, hqx, hqR⟩ :=
    exists_canonicalMaskRightNeighbor_not_mem_of_properHall
      ends m j k l zero p S hproper T hTS R hcard
  have hxS : x ∈ S := hTS.1 hxT
  have hqS : q ∈ canonicalMaskRightNeighborhood
      ends m j k l zero p S :=
    (mem_canonicalMaskRightNeighborhood_iff
      ends m j k l zero p S q).mpr ⟨x, hxS, hqx⟩
  let qS : ↑(canonicalMaskRightNeighborhood
      ends m j k l zero p S) := ⟨q, hqS⟩
  let u : ↑S := f.symm (some qS)
  have hfu : f u = some qS := by simp [u]
  have huc : u ≠ c := by
    intro h
    have hfc0 := hf.1
    rw [h, hfc0] at hfu
    simp at hfu
  have huT : u.1 ∉ T := by
    intro huT
    obtain ⟨rS, hfur, hrR⟩ := hassigned u huT huc
    have hrq : rS = qS := by
      apply Option.some.inj
      exact hfur.symm.trans hfu
    exact hqR (by simpa only [qS, hrq] using hrR)
  have huS : u.1 ∈ S := u.2
  have hsdiff : S \ insert u.1 T ⊂ S \ T := by
    rw [Finset.ssubset_iff_subset_ne]
    constructor
    · intro y hy
      exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hy).1,
        fun hyT => (Finset.mem_sdiff.mp hy).2 (Finset.mem_insert_of_mem hyT)⟩
    · intro heq
      have huOld : u.1 ∈ S \ T := Finset.mem_sdiff.mpr ⟨huS, huT⟩
      have huNew : u.1 ∈ S \ insert u.1 T := heq.symm ▸ huOld
      exact (Finset.mem_sdiff.mp huNew).2 (Finset.mem_insert_self _ _)
  exact ⟨x, hxT, qS, hqx, hqR, u, hfu, huT,
    Finset.card_lt_card hsdiff⟩




theorem exists_canonicalMaskRightAugmentedMatching_strictExposure
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (T : Finset (leftMaskFiber ends m j k l zero p)) (hTS : T ⊂ S)
    (c : ↑S) (hcT : c.1 ∈ T)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f) :
    ∃ x ∈ T,
      ∃ qS : ↑(canonicalMaskRightNeighborhood
          ends m j k l zero p S),
        qS.1 ∈ canonicalMaskRightImages ends m j k l zero p x ∧
        qS.1 ∉ canonicalMaskRightAugmentedAssignedRows
          ends m j k l zero p S T hTS.1 c f hf ∧
        ∃ u : ↑S,
          f u = some qS ∧ u.1 ∉ T ∧
          (S \ insert u.1 T).card < (S \ T).card := by
  classical
  let R := canonicalMaskRightAugmentedAssignedRows
    ends m j k l zero p S T hTS.1 c f hf
  have hRcard := card_canonicalMaskRightAugmentedAssignedRows
    ends m j k l zero p S T hTS.1 c hcT f hf
  have hcard : R.card < T.card := by
    dsimp only [R]
    omega
  have hassigned : ∀ u : ↑S, u.1 ∈ T -> u ≠ c ->
      ∃ qS : ↑(canonicalMaskRightNeighborhood
          ends m j k l zero p S),
        f u = some qS ∧ qS.1 ∈ R := by
    intro u huT huc
    simpa only [R] using canonicalMaskRightAugmentedAssignedRows_contains
      ends m j k l zero p S T hTS.1 c f hf u huT huc
  simpa only [R] using exists_canonicalMaskRightAugmentedMatching_escape
    ends m j k l zero p S hproper T hTS c f hf R hcard hassigned




theorem canonicalMaskRightAugmentedExposureClosed_eq_full
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (T : Finset (leftMaskFiber ends m j k l zero p))
    (hTS : T ⊆ S) (hcT : c.1 ∈ T)
    (hclosed : ∀ x ∈ T, ∀ u : ↑S, ∀ huc : u ≠ c,
      (canonicalMaskRightAugmentedAssignedImage
          ends m j k l zero p S c f hf u huc).1 ∈
        canonicalMaskRightImages ends m j k l zero p x ->
      u.1 ∈ T) :
    T = S := by
  classical
  by_contra hne
  have hTS' : T ⊂ S :=
    (Finset.ssubset_iff_subset_ne).mpr ⟨hTS, hne⟩
  obtain ⟨x, hxT, qS, hqx, -, u, hfu, huT, -⟩ :=
    exists_canonicalMaskRightAugmentedMatching_strictExposure
      ends m j k l zero p S hproper T hTS' c hcT f hf
  have huc : u ≠ c := by
    intro h
    exact huT (h ▸ hcT)
  let qu := canonicalMaskRightAugmentedAssignedImage
    ends m j k l zero p S c f hf u huc
  have hqu := canonicalMaskRightAugmentedAssignedImage_apply
    ends m j k l zero p S c f hf u huc
  have hquq : qu = qS := by
    apply Option.some.inj
    exact hqu.symm.trans hfu
  apply huT
  apply hclosed x hxT u huc
  change qu.1 ∈ canonicalMaskRightImages ends m j k l zero p x
  rw [hquq]
  exact hqx



def CanonicalMaskRightSecondCommonDisplacement
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c d : ↑S)
    (ef : canonicalMaskRightAugmentedEquivType
          ends m j k l zero p S ×
        canonicalMaskRightAugmentedEquivType ends m j k l zero p S) : Prop :=
  let σ : Equiv.Perm ↑S := ef.1.trans ef.2.symm
  ∀ x : ↑S, x ≠ c ->
    ∃ q : rightMaskFiber ends m j k l zero p,
      q ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
      q ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1 ∧
      ∀ r : rightMaskFiber ends m j k l zero p, r ≠ q ->
        r ∈ canonicalMaskRightImages ends m j k l zero p x.1 ->
        r ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1 ->
        ∃ u v : ↑S,
          u ≠ c ∧ v ≠ d ∧ u ≠ x ∧ v ≠ σ x ∧ σ u = v ∧
            r ∈ canonicalMaskRightImages ends m j k l zero p u.1 ∧
            r ∈ canonicalMaskRightImages ends m j k l zero p v.1


noncomputable def canonicalPermMovedCard
    {A : Type*} [Fintype A] (σ : Equiv.Perm A) : Nat := by
  classical
  exact (Finset.univ.filter fun x => σ x ≠ x).card

set_option maxHeartbeats 1000000 in



theorem exists_minimal_canonicalMaskRightAugmentedMatchingPair
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (htight : (canonicalMaskRightNeighborhood
        ends m j k l zero p S).card + 1 = S.card)
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (c d : ↑S) :
    ∃ ef ∈ canonicalMaskRightAugmentedMatchingPairs
        ends m j k l zero p S c d,
      ∀ gh ∈ canonicalMaskRightAugmentedMatchingPairs
          ends m j k l zero p S c d,
        canonicalPermMovedCard
            (ef.1.trans ef.2.symm : Equiv.Perm ↑S) ≤
          canonicalPermMovedCard
            (gh.1.trans gh.2.symm : Equiv.Perm ↑S) := by
  classical
  let P := canonicalMaskRightAugmentedMatchingPairs
    ends m j k l zero p S c d
  have hP : P.Nonempty := by
    obtain ⟨fc, hfc0, hfc⟩ := exists_canonicalMaskRightAugmentedEquiv
      ends m j k l zero p S htight hproper c.1 c.2
    obtain ⟨fd, hfd0, hfd⟩ := exists_canonicalMaskRightAugmentedEquiv
      ends m j k l zero p S htight hproper d.1 d.2
    refine ⟨(fc, fd), ?_⟩
    rw [mem_canonicalMaskRightAugmentedMatchingPairs_iff]
    constructor
    · refine ⟨hfc0, ?_⟩
      intro x hxc
      apply hfc x
      intro hval
      exact hxc (Subtype.ext hval)
    · refine ⟨hfd0, ?_⟩
      intro x hxd
      apply hfd x
      intro hval
      exact hxd (Subtype.ext hval)
  obtain ⟨ef, hefP, hefmin⟩ := P.exists_min_image
    (fun gh => canonicalPermMovedCard
      (gh.1.trans gh.2.symm : Equiv.Perm ↑S)) hP
  exact ⟨ef, hefP, hefmin⟩

set_option maxHeartbeats 1000000 in



theorem exists_minimal_canonicalMaskRightPair_with_displacement
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (htight : (canonicalMaskRightNeighborhood
        ends m j k l zero p S).card + 1 = S.card)
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (c d : ↑S) :
    ∃ ef ∈ canonicalMaskRightAugmentedMatchingPairs
        ends m j k l zero p S c d,
      (∀ gh ∈ canonicalMaskRightAugmentedMatchingPairs
          ends m j k l zero p S c d,
        canonicalPermMovedCard
            (ef.1.trans ef.2.symm : Equiv.Perm ↑S) ≤
          canonicalPermMovedCard
            (gh.1.trans gh.2.symm : Equiv.Perm ↑S)) ∧
      CanonicalMaskRightSecondCommonDisplacement
        ends m j k l zero p S c d ef := by
  classical
  obtain ⟨ef, hef, hmin⟩ :=
    exists_minimal_canonicalMaskRightAugmentedMatchingPair
      ends m j k l zero p S htight hproper c d
  refine ⟨ef, hef, hmin, ?_⟩
  intro x hxc
  exact canonicalMaskRightAugmentedMatchingPair_secondCommon_displacement
    ends m j k l zero p S c d ef hef x hxc




theorem exists_canonicalMaskRightAlternatingPerm
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (htight : (canonicalMaskRightNeighborhood
        ends m j k l zero p S).card + 1 = S.card)
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (c d : leftMaskFiber ends m j k l zero p)
    (hc : c ∈ S) (hd : d ∈ S) :
    ∃ σ : Equiv.Perm ↑S,
      σ ⟨c, hc⟩ = ⟨d, hd⟩ ∧
        ∀ x : ↑S, x.1 ≠ c ->
          ∃ q : rightMaskFiber ends m j k l zero p,
            q ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
              q ∈ canonicalMaskRightImages
                ends m j k l zero p (σ x).1 := by
  classical
  obtain ⟨fc, hfc0, hfc⟩ := exists_canonicalMaskRightAugmentedEquiv
    ends m j k l zero p S htight hproper c hc
  obtain ⟨fd, hfd0, hfd⟩ := exists_canonicalMaskRightAugmentedEquiv
    ends m j k l zero p S htight hproper d hd
  let σ : Equiv.Perm ↑S := fc.trans fd.symm
  refine ⟨σ, ?_, ?_⟩
  · apply fd.injective
    simp [σ, hfc0, hfd0]
  · intro x hxc
    obtain ⟨q, hfcx, hqx⟩ := hfc x hxc
    have hfdσ : fd (σ x) = some q := by
      rw [← hfcx]
      simp [σ]
    have hσd : (σ x).1 ≠ d := by
      intro hval
      have hsub : σ x = ⟨d, hd⟩ := Subtype.ext hval
      rw [hsub, hfd0] at hfdσ
      simp at hfdσ
    obtain ⟨r, hfdr, hr⟩ := hfd (σ x) hσd
    have hrq : r = q := by
      rw [hfdσ] at hfdr
      exact Option.some.inj hfdr.symm
    subst r
    exact ⟨q.1, hqx, hr⟩



theorem exists_canonicalMaskTransferAdjacentPerm
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (htight : (canonicalMaskRightNeighborhood
        ends m j k l zero p S).card + 1 = S.card)
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (c d : leftMaskFiber ends m j k l zero p)
    (hc : c ∈ S) (hd : d ∈ S)
    (hcd : CanonicalMaskTransferAdjacent ends m j k l zero p c d) :
    ∃ σ : Equiv.Perm ↑S,
      σ ⟨c, hc⟩ = ⟨d, hd⟩ ∧
        ∀ x : ↑S, CanonicalMaskTransferAdjacent
          ends m j k l zero p x.1 (σ x).1 := by
  classical
  obtain ⟨σ, hσcd, hσ⟩ := exists_canonicalMaskRightAlternatingPerm
    ends m j k l zero p S htight hproper c d hc hd
  refine ⟨σ, hσcd, ?_⟩
  intro x
  by_cases hxc : x.1 = c
  · have hx : x = ⟨c, hc⟩ := Subtype.ext hxc
    subst x
    simpa only [hσcd] using hcd
  · obtain ⟨q, hqx, hqσ⟩ := hσ x hxc
    exact (exists_mem_canonicalMaskRightImages_iff_adjacent
      ends m j k l zero p x.1 (σ x).1).mp ⟨q, hqx, hqσ⟩




theorem exists_canonicalTranslatedRowPerm
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (htight : (canonicalMaskRightNeighborhood
        ends m j k l zero p S).card + 1 = S.card)
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (c d : leftMaskFiber ends m j k l zero p)
    (hc : c ∈ S) (hd : d ∈ S)
    (hcd : CanonicalMaskTransferAdjacent ends m j k l zero p c d) :
    ∃ σ : Equiv.Perm ↑S,
      σ ⟨c, hc⟩ = ⟨d, hd⟩ ∧
        ∀ x : ↑S, ∃ a b : leftMaskFiber ends m j k l zero p,
          RowSupportDisconnects ends m
              (canonicalTranslatedRow ends m k zero a.1.1 x.1.1.1) k zero ∧
            canonicalTranslatedRow ends m k zero a.1.1 x.1.1.1 =
              canonicalTranslatedRow ends m k zero b.1.1 (σ x).1.1.1 := by
  obtain ⟨σ, hσcd, hσ⟩ := exists_canonicalMaskTransferAdjacentPerm
    ends m j k l zero p S htight hproper c d hc hd hcd
  refine ⟨σ, hσcd, ?_⟩
  intro x
  exact (canonicalMaskTransferAdjacent_iff_exists_translatedRow
    hloop hjk hkl x.1 (σ x).1).mp (hσ x)


noncomputable def symmDiffFold
    {A : Type*} (s : Finset A) (f : A -> Finset I) : Finset I := by
  classical
  exact s.fold (fun X Y => X ∆ Y) ∅ f

theorem symmDiffFold_pair
    {A : Type*} (s : Finset A) (f g : A -> Finset I) :
    symmDiffFold s (fun x => f x ∆ g x) =
      symmDiffFold s f ∆ symmDiffFold s g := by
  classical
  unfold symmDiffFold
  simpa using (Finset.fold_op_distrib (s := s)
    (op := fun X Y : Finset I => X ∆ Y) (f := f) (g := g)
    (b₁ := (∅ : Finset I)) (b₂ := (∅ : Finset I)))

theorem symmDiffFold_equiv
    {A : Type*} [Fintype A] (e : Equiv.Perm A) (f : A -> Finset I) :
    symmDiffFold Finset.univ (fun x => f (e x)) =
      symmDiffFold Finset.univ f := by
  classical
  unfold symmDiffFold
  calc
    _ = (Finset.univ.map e.toEmbedding).fold
        (fun X Y : Finset I => X ∆ Y) ∅ f := by
      rw [Finset.fold_map]
      rfl
    _ = _ := by simp



theorem symmDiffFold_const
    {A : Type*} (s : Finset A) (C : Finset I) :
    symmDiffFold s (fun _ => C) =
      if s.card % 2 = 0 then ∅ else C := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [symmDiffFold]
  | @insert a s ha ih =>
      simp only [symmDiffFold, Finset.fold_insert ha,
        Finset.card_insert_of_notMem ha]
      change C ∆ symmDiffFold s (fun _ => C) =
        if (s.card + 1) % 2 = 0 then ∅ else C
      rw [ih]
      have hmod : s.card % 2 = 0 ∨ s.card % 2 = 1 := by omega
      rcases hmod with hmod | hmod <;> simp [hmod, Nat.add_mod]


theorem sources_symmDiffFold
    {A : Type*} (ends : I -> Sym2 W) (s : Finset A)
    (f : A -> Finset I) :
    StatMech.Sharpness.RandomCurrent.sources ends (symmDiffFold s f) =
      symmDiffFold s
        (fun a => StatMech.Sharpness.RandomCurrent.sources ends (f a)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [symmDiffFold, StatMech.Sharpness.RandomCurrent.sources,
      StatMech.Sharpness.RandomCurrent.degK]
  | @insert a s ha ih =>
      simp only [symmDiffFold, Finset.fold_insert ha]
      rw [StatMech.Sharpness.RandomCurrent.sources_symmDiff]
      change StatMech.Sharpness.RandomCurrent.sources ends (f a) ∆
          StatMech.Sharpness.RandomCurrent.sources ends (symmDiffFold s f) =
        StatMech.Sharpness.RandomCurrent.sources ends (f a) ∆
          symmDiffFold s
            (fun a => StatMech.Sharpness.RandomCurrent.sources ends (f a))
      rw [ih]



theorem sources_symmDiffFold_of_constant
    {A : Type*} (ends : I -> Sym2 W) (s : Finset A)
    (f : A -> Finset I) (C : Finset W)
    (hsrc : ∀ a ∈ s,
      StatMech.Sharpness.RandomCurrent.sources ends (f a) = C) :
    StatMech.Sharpness.RandomCurrent.sources ends (symmDiffFold s f) =
      if s.card % 2 = 0 then ∅ else C := by
  rw [sources_symmDiffFold]
  have hfold : symmDiffFold s
      (fun a => StatMech.Sharpness.RandomCurrent.sources ends (f a)) =
      symmDiffFold s (fun _ => C) := by
    unfold symmDiffFold
    apply Finset.fold_congr
    exact hsrc
  rw [hfold, symmDiffFold_const]



theorem sources_symmDiffFold_rightMaskRows
    {A : Type*} (ends : I -> Sym2 W) (m : Finset I)
    (j k l zero : W) (p : Finset I × Finset I)
    (s : Finset A) (Q : A -> rightMaskFiber ends m j k l zero p) :
    StatMech.Sharpness.RandomCurrent.sources ends
        (symmDiffFold s (fun x => rowClass m (Q x).1.1 0)) =
      if s.card % 2 = 0 then ∅ else {j, k} ∆ {k, l} := by
  apply sources_symmDiffFold_of_constant
  intro x _
  exact (rightPattern_rowBoundaries (Q x).1.2).1




theorem symmDiffFold_endpointCancellation
    {A : Type*} [Fintype A]
    (Q R : A -> Finset I) (σ : Equiv.Perm A) :
    symmDiffFold Finset.univ
        (fun x => Q x ∆ R x ∆ R (σ x)) =
      symmDiffFold Finset.univ Q := by
  rw [symmDiffFold_pair, symmDiffFold_pair,
    symmDiffFold_equiv σ R]
  simp

private theorem symmDiff_left_cancel_finset
    (X A B : Finset I) (h : X ∆ A = X ∆ B) : A = B := by
  have h' := congrArg (fun K : Finset I => X ∆ K) h
  simpa [symmDiff_assoc] using h'




theorem exists_referenceTransferFold_eq_of_translatedRowPerm
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (σ : Equiv.Perm ↑S)
    (hrows : ∀ x : ↑S, ∃ a b : leftMaskFiber ends m j k l zero p,
      RowSupportDisconnects ends m
          (canonicalTranslatedRow ends m k zero a.1.1 x.1.1.1) k zero ∧
        canonicalTranslatedRow ends m k zero a.1.1 x.1.1.1 =
          canonicalTranslatedRow ends m k zero b.1.1 (σ x).1.1.1) :
    ∃ a b : ↑S -> leftMaskFiber ends m j k l zero p,
      (∀ x, RowSupportDisconnects ends m
        (canonicalTranslatedRow ends m k zero (a x).1.1 x.1.1.1)
          k zero) ∧
      (∀ x, canonicalTranslatedRow ends m k zero (a x).1.1 x.1.1.1 =
        canonicalTranslatedRow ends m k zero
          (b x).1.1 (σ x).1.1.1) ∧
      symmDiffFold Finset.univ (fun x =>
          canonicalTransferUnion ends m k zero (a x).1.1) =
        symmDiffFold Finset.univ (fun x =>
          canonicalTransferUnion ends m k zero (b x).1.1) := by
  classical
  choose a b hdisc heq using hrows
  refine ⟨a, b, hdisc, heq, ?_⟩
  let R := fun x : ↑S => rowClass m x.1.1.1 0
  let A := fun x : ↑S =>
    canonicalTransferUnion ends m k zero (a x).1.1
  let B := fun x : ↑S =>
    canonicalTransferUnion ends m k zero (b x).1.1
  have hpoint : ∀ x, R x ∆ A x = R (σ x) ∆ B x := by
    intro x
    simpa only [R, A, B, canonicalTranslatedRow] using heq x
  have hfold : symmDiffFold Finset.univ (fun x => R x ∆ A x) =
      symmDiffFold Finset.univ (fun x => R (σ x) ∆ B x) := by
    unfold symmDiffFold
    apply Finset.fold_congr
    intro x _
    exact hpoint x
  rw [symmDiffFold_pair, symmDiffFold_pair,
    symmDiffFold_equiv σ R] at hfold
  exact symmDiff_left_cancel_finset _ _ _ hfold



theorem canonicalTranslatedRow_opposite_eq_of_eq
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a b x y : ↑m -> Fin 4)
    (hxy : canonicalTranslatedRow ends m k zero a x =
      canonicalTranslatedRow ends m k zero b y) :
    canonicalTranslatedRow ends m k zero b x =
      canonicalTranslatedRow ends m k zero a y := by
  unfold canonicalTranslatedRow at hxy ⊢
  let Ra := rowClass m x 0
  let Ry := rowClass m y 0
  let Ta := canonicalTransferUnion ends m k zero a
  let Tb := canonicalTransferUnion ends m k zero b
  change Ra ∆ Ta = Ry ∆ Tb at hxy
  change Ra ∆ Tb = Ry ∆ Ta
  calc
    Ra ∆ Tb = (Ra ∆ Ta) ∆ Ta ∆ Tb := by simp
    _ = (Ry ∆ Tb) ∆ Ta ∆ Tb := by rw [hxy]
    _ = Ry ∆ Ta := by
      calc
        (Ry ∆ Tb) ∆ Ta ∆ Tb =
            Ry ∆ Ta ∆ (Tb ∆ Tb) := by ac_rfl
        _ = Ry ∆ Ta := by simp




theorem canonicalTranslatedRow_opposite_rootCutBranches_iff_of_eq
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (a b x y : ↑m -> Fin 4)
    (hxy : canonicalTranslatedRow ends m k zero a x =
      canonicalTranslatedRow ends m k zero b y) :
    let Kx := canonicalTranslatedRow ends m k zero b x
    let Ky := canonicalTranslatedRow ends m k zero a y
    ((StatMech.Sharpness.RandomCurrent.connK ends Kx k zero ∧
          edgeComponent ends Kx zero = edgeComponent ends Kx k) ↔
        (StatMech.Sharpness.RandomCurrent.connK ends Ky k zero ∧
          edgeComponent ends Ky zero = edgeComponent ends Ky k)) ∧
      ((StatMech.Sharpness.RandomCurrent.connK ends (m \ Kx) k zero ∧
          edgeComponent ends (m \ Kx) zero =
            edgeComponent ends (m \ Kx) k) ↔
        (StatMech.Sharpness.RandomCurrent.connK ends (m \ Ky) k zero ∧
          edgeComponent ends (m \ Ky) zero =
            edgeComponent ends (m \ Ky) k)) := by
  dsimp only
  rw [canonicalTranslatedRow_opposite_eq_of_eq
    ends m k zero a b x y hxy]
  exact ⟨Iff.rfl, Iff.rfl⟩



theorem canonicalTransferWorks_opposite_iff_of_translatedRow_eq
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b x y : leftMaskFiber ends m j k l zero p)
    (hxy : canonicalTranslatedRow ends m k zero a.1.1 x.1.1 =
      canonicalTranslatedRow ends m k zero b.1.1 y.1.1) :
    CanonicalTransferWorks ends m k zero b.1.1 x.1.1 ↔
      CanonicalTransferWorks ends m k zero a.1.1 y.1.1 := by
  rw [canonicalTransferWorks_iff_translatedRowDisconnects
      hloop hjk hkl b x,
    canonicalTransferWorks_iff_translatedRowDisconnects
      hloop hjk hkl a y,
    canonicalTranslatedRow_opposite_eq_of_eq
      ends m k zero a.1.1 b.1.1 x.1.1 y.1.1 hxy]



theorem exists_two_common_canonicalMaskRightImages_of_collisionSquare
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b x y : leftMaskFiber ends m j k l zero p)
    (hxyne : x ≠ y)
    (hax : CanonicalTransferWorks ends m k zero a.1.1 x.1.1)
    (hxy : canonicalTranslatedRow ends m k zero a.1.1 x.1.1 =
      canonicalTranslatedRow ends m k zero b.1.1 y.1.1)
    (hbx : CanonicalTransferWorks ends m k zero b.1.1 x.1.1) :
    ∃ q₁ q₂ : rightMaskFiber ends m j k l zero p,
      q₁ ≠ q₂ ∧
        q₁ ∈ canonicalMaskRightImages ends m j k l zero p x ∧
        q₁ ∈ canonicalMaskRightImages ends m j k l zero p y ∧
        q₂ ∈ canonicalMaskRightImages ends m j k l zero p x ∧
        q₂ ∈ canonicalMaskRightImages ends m j k l zero p y := by
  have hdisc := (canonicalTransferWorks_iff_translatedRowDisconnects
    hloop hjk hkl a x).mp hax
  have hby : CanonicalTransferWorks ends m k zero b.1.1 y.1.1 :=
    (canonicalTransferWorks_iff_translatedRowDisconnects
      hloop hjk hkl b y).mpr (hxy ▸ hdisc)
  have hopp := canonicalTranslatedRow_opposite_eq_of_eq
    ends m k zero a.1.1 b.1.1 x.1.1 y.1.1 hxy
  have hay : CanonicalTransferWorks ends m k zero a.1.1 y.1.1 :=
    (canonicalTransferWorks_opposite_iff_of_translatedRow_eq
      hloop hjk hkl a b x y hxy).mp hbx
  let q₁ := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p a x hax
  let q₂ := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p b x hbx
  have hq₁x : q₁ ∈ canonicalMaskRightImages
      ends m j k l zero p x :=
    (mem_canonicalMaskRightImages_iff
      ends m j k l zero p x q₁).mpr ⟨a, hax, rfl⟩
  have hraw₁ := (canonicalBalancedSwaps_eq_iff_rowSymmDiff
    hloop hjk hkl a b x y).mpr hxy
  have hq₁y : q₁ ∈ canonicalMaskRightImages
      ends m j k l zero p y :=
    (mem_canonicalMaskRightImages_iff
      ends m j k l zero p y q₁).mpr ⟨b, hby, hraw₁⟩
  have hq₂x : q₂ ∈ canonicalMaskRightImages
      ends m j k l zero p x :=
    (mem_canonicalMaskRightImages_iff
      ends m j k l zero p x q₂).mpr ⟨b, hbx, rfl⟩
  have hraw₂ := (canonicalBalancedSwaps_eq_iff_rowSymmDiff
    hloop hjk hkl b a x y).mpr hopp
  have hq₂y : q₂ ∈ canonicalMaskRightImages
      ends m j k l zero p y :=
    (mem_canonicalMaskRightImages_iff
      ends m j k l zero p y q₂).mpr ⟨a, hay, hraw₂⟩
  have hTne : canonicalTransferUnion ends m k zero a.1.1 ≠
      canonicalTransferUnion ends m k zero b.1.1 := by
    intro hT
    have hrow : rowClass m x.1.1 0 = rowClass m y.1.1 0 :=
      symmDiff_left_cancel_finset
        (canonicalTransferUnion ends m k zero a.1.1) _ _ (by
          simpa only [canonicalTranslatedRow, hT, symmDiff_comm] using hxy)
    exact hxyne (leftMaskFiber_rowClass_zero_injective
      ends m j k l zero p hrow)
  refine ⟨q₁, q₂, ?_, hq₁x, hq₁y, hq₂x, hq₂y⟩
  intro hq
  have hrowq := congrArg
    (fun q : rightMaskFiber ends m j k l zero p => rowClass m q.1.1 0) hq
  dsimp only [q₁, q₂] at hrowq
  rw [rowClass_zero_canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p a x hax,
    rowClass_zero_canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p b x hbx] at hrowq
  apply hTne
  exact symmDiff_left_cancel_finset (rowClass m x.1.1 0) _ _ hrowq


def CanonicalTranslatedRowRootComponentCut
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (r c : ↑m -> Fin 4) : Prop :=
  let K := canonicalTranslatedRow ends m k zero r c
  (StatMech.Sharpness.RandomCurrent.connK ends K k zero ∧
      edgeComponent ends K zero = edgeComponent ends K k) ∨
    (StatMech.Sharpness.RandomCurrent.connK ends (m \ K) k zero ∧
      edgeComponent ends (m \ K) zero = edgeComponent ends (m \ K) k)

private theorem even_subset_pair_eq_empty_or_pair
    {A : Finset W} {a b : W} (hab : a ≠ b)
    (hsub : A ⊆ {a, b}) (heven : Even A.card) :
    A = ∅ ∨ A = {a, b} := by
  have hle : A.card ≤ 2 := by
    have := Finset.card_le_card hsub
    simpa [hab] using this
  obtain ⟨n, hn⟩ := heven
  by_cases hzero : A.card = 0
  · exact Or.inl (Finset.card_eq_zero.mp hzero)
  · right
    have hcard : A.card = 2 := by omega
    apply Finset.eq_of_subset_of_card_le hsub
    simp [hab, hcard]


theorem canonicalTranslatedRow_subset_m
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p) :
    canonicalTranslatedRow ends m k zero r.1.1 c.1.1 ⊆ m := by
  have hrow0sub : rowClass m c.1.1 0 ⊆ m := by
    intro i hi
    rw [rowClass_zero, Finset.mem_union] at hi
    rcases hi with hi | hi
    · exact colorClass_subset m c.1.1 0 hi
    · exact colorClass_subset m c.1.1 1 hi
  intro i hi
  rcases Finset.mem_symmDiff.mp hi with hi | hi
  · exact hrow0sub hi.1
  · exact canonicalTransferUnion_subset_m hloop hjk hkl r hi.1



theorem canonicalTranslatedRow_boundaries
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p) :
    StatMech.Sharpness.RandomCurrent.sources ends
        (canonicalTranslatedRow ends m k zero r.1.1 c.1.1) =
          {j, k} ∆ {k, l} ∧
      StatMech.Sharpness.RandomCurrent.sources ends
        (m \ canonicalTranslatedRow ends m k zero r.1.1 c.1.1) = ∅ := by
  have hrows := leftPattern_rowBoundaries c.1.2
  have hTsrc : StatMech.Sharpness.RandomCurrent.sources ends
      (canonicalTransferUnion ends m k zero r.1.1) = {k, l} := by
    have hv := canonicalTransfers_valid hloop hjk hkl r.1.2
    have hdisj : Disjoint
        (canonicalMiddleTransfer ends m r.1.1 k zero)
        (canonicalOuterTransfer ends m r.1.1 k zero) :=
      (middleMask_disjoint_outerMask m r.1.1).mono
        (by simpa only [middleMask] using hv.1)
        (by simpa only [outerMask] using hv.2.1)
    rw [canonicalTransferUnion,
      sources_union_of_disjoint hdisj,
      hv.2.2.1, hv.2.2.2]
    simp
  have hKsrc : StatMech.Sharpness.RandomCurrent.sources ends
      (canonicalTranslatedRow ends m k zero r.1.1 c.1.1) =
        {j, k} ∆ {k, l} := by
    rw [canonicalTranslatedRow,
      StatMech.Sharpness.RandomCurrent.sources_symmDiff,
      hrows.1, hTsrc]
  have hrow0sub : rowClass m c.1.1 0 ⊆ m := by
    intro i hi
    rw [rowClass_zero, Finset.mem_union] at hi
    rcases hi with hi | hi
    · exact colorClass_subset m c.1.1 0 hi
    · exact colorClass_subset m c.1.1 1 hi
  have htotal : StatMech.Sharpness.RandomCurrent.sources ends m =
      {j, k} ∆ {k, l} := by
    have hb : {k, l} =
        StatMech.Sharpness.RandomCurrent.sources ends m ∆ {j, k} := by
      rw [← hrows.2, rowClass_one_eq_sdiff,
        sources_sdiff_of_subset hrow0sub, hrows.1]
    calc
      StatMech.Sharpness.RandomCurrent.sources ends m =
          (StatMech.Sharpness.RandomCurrent.sources ends m ∆ {j, k}) ∆
            {j, k} := by simp
      _ = {k, l} ∆ {j, k} := by rw [← hb]
      _ = {j, k} ∆ {k, l} := symmDiff_comm _ _
  have hKsub : canonicalTranslatedRow ends m k zero r.1.1 c.1.1 ⊆ m := by
    intro i hi
    rcases Finset.mem_symmDiff.mp hi with hi | hi
    · exact hrow0sub hi.1
    · exact canonicalTransferUnion_subset_m hloop hjk hkl r hi.1
  refine ⟨hKsrc, ?_⟩
  rw [sources_sdiff_of_subset hKsub, htotal, hKsrc, symmDiff_self]
  rfl



theorem canonicalTranslatedRow_sourcePair_connected
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hjl : j ≠ l)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p) :
    StatMech.Sharpness.RandomCurrent.connK ends
      (canonicalTranslatedRow ends m k zero r.1.1 c.1.1) j l := by
  let K := canonicalTranslatedRow ends m k zero r.1.1 c.1.1
  have hKsub : K ⊆ m := canonicalTranslatedRow_subset_m
    hloop hjk hkl r c
  have hsrc0 := (canonicalTranslatedRow_boundaries
    hloop hjk hkl r c).1
  have hpair : ({j, k} : Finset W) ∆ {k, l} = {j, l} := by
    ext x
    simp only [Finset.mem_symmDiff, Finset.mem_insert,
      Finset.mem_singleton]
    aesop
  have hsrc : StatMech.Sharpness.RandomCurrent.sources ends K =
      {j, l} := by
    rw [hsrc0, hpair]
  exact StatMech.Walls.gc6_pairingPath_abstract ends K K
    (fun i hi => hloop i (hKsub hi)) Finset.Subset.rfl hsrc hjl



theorem canonicalTranslatedRow_conn_source_iff
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero u : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hjl : j ≠ l)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p) :
    StatMech.Sharpness.RandomCurrent.connK ends
        (canonicalTranslatedRow ends m k zero r.1.1 c.1.1) u j ↔
      StatMech.Sharpness.RandomCurrent.connK ends
        (canonicalTranslatedRow ends m k zero r.1.1 c.1.1) u l := by
  have hjlConn := canonicalTranslatedRow_sourcePair_connected
    hloop hjk hkl hjl r c
  constructor
  · exact fun huj => huj.trans hjlConn
  · exact fun hul => hul.trans
      (StatMech.Sharpness.RandomCurrent.connK_symm ends _ hjlConn)




theorem canonicalTranslatedRow_component_sources_empty_or_full
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero u : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p) :
    let K := canonicalTranslatedRow ends m k zero r.1.1 c.1.1
    let A := {j, k} ∆ {k, l}
    StatMech.Sharpness.RandomCurrent.sources ends
          (edgeComponent ends K u) = ∅ ∨
      StatMech.Sharpness.RandomCurrent.sources ends
          (edgeComponent ends K u) = A := by
  classical
  let K := canonicalTranslatedRow ends m k zero r.1.1 c.1.1
  let A : Finset W := {j, k} ∆ {k, l}
  change StatMech.Sharpness.RandomCurrent.sources ends
        (edgeComponent ends K u) = ∅ ∨
    StatMech.Sharpness.RandomCurrent.sources ends
        (edgeComponent ends K u) = A
  have hKsrc : StatMech.Sharpness.RandomCurrent.sources ends K = A :=
    (canonicalTranslatedRow_boundaries hloop hjk hkl r c).1
  have hKsub : K ⊆ m := canonicalTranslatedRow_subset_m
    hloop hjk hkl r c
  have hloopK : ∀ i ∈ K, ¬ (ends i).IsDiag :=
    fun i hi => hloop i (hKsub hi)
  have hEsrc : StatMech.Sharpness.RandomCurrent.sources ends
      (edgeComponent ends K u) =
      A ∩ StatMech.Sharpness.RandomCurrent.compOf ends K u := by
    rw [sources_edgeComponent, hKsrc]
  have hEsubA : StatMech.Sharpness.RandomCurrent.sources ends
      (edgeComponent ends K u) ⊆ A := by
    rw [hEsrc]
    exact Finset.inter_subset_left
  have hEeven : Even (StatMech.Sharpness.RandomCurrent.sources ends
      (edgeComponent ends K u)).card := by
    rw [hEsrc, ← hKsrc]
    exact StatMech.Walls.gc7_componentEven_sources ends K hloopK u
  by_cases hjl : j = l
  · left
    have hpairs : ({j, k} : Finset W) = {k, l} := by
      ext x
      simp only [Finset.mem_insert, Finset.mem_singleton]
      aesop
    have hA : A = ∅ := by
      change {j, k} ∆ {k, l} = ∅
      rw [hpairs]
      exact symmDiff_self _
    exact Finset.eq_empty_iff_forall_notMem.mpr fun x hx =>
      (by simpa [hA] using hEsubA hx)
  · have hA : A = {j, l} := by
      change {j, k} ∆ {k, l} = {j, l}
      ext x
      simp only [Finset.mem_symmDiff, Finset.mem_insert,
        Finset.mem_singleton]
      aesop
    have hpair := even_subset_pair_eq_empty_or_pair hjl
      (by simpa [hA] using hEsubA) hEeven
    simpa [hA] using hpair





theorem canonicalTranslatedRow_rootComponent_boundaryCertificate
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p)
    (hcut : CanonicalTranslatedRowRootComponentCut
      ends m k zero r.1.1 c.1.1) :
    let K := canonicalTranslatedRow ends m k zero r.1.1 c.1.1
    let A := {j, k} ∆ {k, l}
    StatMech.Sharpness.RandomCurrent.sources ends K = A ∧
      StatMech.Sharpness.RandomCurrent.sources ends (m \ K) = ∅ ∧
      ((StatMech.Sharpness.RandomCurrent.connK ends K k zero ∧
          edgeComponent ends K zero = edgeComponent ends K k ∧
          ((StatMech.Sharpness.RandomCurrent.sources ends
                (edgeComponent ends K zero) = ∅ ∧
              StatMech.Sharpness.RandomCurrent.sources ends
                (K \ edgeComponent ends K zero) = A) ∨
            (StatMech.Sharpness.RandomCurrent.sources ends
                (edgeComponent ends K zero) = A ∧
              StatMech.Sharpness.RandomCurrent.sources ends
                (K \ edgeComponent ends K zero) = ∅))) ∨
        (StatMech.Sharpness.RandomCurrent.connK ends (m \ K) k zero ∧
          edgeComponent ends (m \ K) zero =
            edgeComponent ends (m \ K) k ∧
          StatMech.Sharpness.RandomCurrent.sources ends
            (edgeComponent ends (m \ K) zero) = ∅ ∧
          StatMech.Sharpness.RandomCurrent.sources ends
            ((m \ K) \ edgeComponent ends (m \ K) zero) = ∅)) := by
  classical
  let K := canonicalTranslatedRow ends m k zero r.1.1 c.1.1
  let A : Finset W := {j, k} ∆ {k, l}
  have hbounds := canonicalTranslatedRow_boundaries hloop hjk hkl r c
  have hKsrc : StatMech.Sharpness.RandomCurrent.sources ends K = A :=
    hbounds.1
  have hLsrc : StatMech.Sharpness.RandomCurrent.sources ends (m \ K) = ∅ :=
    hbounds.2
  have hEsub : edgeComponent ends K zero ⊆ K := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  have hLEsub : edgeComponent ends (m \ K) zero ⊆ m \ K := by
    intro i hi
    rw [edgeComponent, Finset.mem_filter] at hi
    exact hi.1
  refine ⟨hKsrc, hLsrc, ?_⟩
  rcases hcut with hcut | hcut
  · left
    refine ⟨hcut.1, hcut.2, ?_⟩
    have hclass : StatMech.Sharpness.RandomCurrent.sources ends
          (edgeComponent ends K zero) = ∅ ∨
        StatMech.Sharpness.RandomCurrent.sources ends
          (edgeComponent ends K zero) = A := by
      simpa only [K, A] using
        (canonicalTranslatedRow_component_sources_empty_or_full
          (u := zero) hloop hjk hkl r c)
    rcases hclass with hEempty | hEfull
    · left
      refine ⟨hEempty, ?_⟩
      rw [sources_sdiff_of_subset hEsub, hKsrc, hEempty]
      simp [A]
    · right
      refine ⟨hEfull, ?_⟩
      rw [sources_sdiff_of_subset hEsub, hKsrc, hEfull]
      exact symmDiff_self A
  · right
    refine ⟨hcut.1, hcut.2, ?_, ?_⟩
    · rw [sources_edgeComponent, hLsrc]
      simp
    · rw [sources_sdiff_of_subset hLEsub, hLsrc,
        sources_edgeComponent, hLsrc]
      simp



theorem canonicalTransferWorks_failed_translatedRow_component
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p)
    (hbad : ¬ CanonicalTransferWorks ends m k zero r.1.1 c.1.1) :
    let K := canonicalTranslatedRow ends m k zero r.1.1 c.1.1
    (StatMech.Sharpness.RandomCurrent.connK ends K k zero ∧
        edgeComponent ends K zero = edgeComponent ends K k) ∨
      (StatMech.Sharpness.RandomCurrent.connK ends (m \ K) k zero ∧
        edgeComponent ends (m \ K) zero = edgeComponent ends (m \ K) k) := by
  let K := canonicalTranslatedRow ends m k zero r.1.1 c.1.1
  have hdisc : ¬ RowSupportDisconnects ends m K k zero := by
    intro h
    exact hbad ((canonicalTransferWorks_iff_translatedRowDisconnects
      hloop hjk hkl r c).mpr h)
  by_cases hK : StatMech.Sharpness.RandomCurrent.connK ends K k zero
  · exact Or.inl ⟨hK, (edgeComponent_eq_of_conn ends K k zero hK).symm⟩
  · have hcomp : StatMech.Sharpness.RandomCurrent.connK
        ends (m \ K) k zero := by
      by_contra hcomp
      exact hdisc ⟨hK, hcomp⟩
    exact Or.inr ⟨hcomp,
      (edgeComponent_eq_of_conn ends (m \ K) k zero hcomp).symm⟩

theorem canonicalTransferWorks_failed_rootComponentCut
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p)
    (hbad : ¬ CanonicalTransferWorks ends m k zero r.1.1 c.1.1) :
    CanonicalTranslatedRowRootComponentCut
      ends m k zero r.1.1 c.1.1 :=
  canonicalTransferWorks_failed_translatedRow_component
    hloop hjk hkl r c hbad




theorem canonicalMaskRightAugmentedExposure_failedOpposite_or_square
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (x u : ↑S) (huc : u ≠ c) (hxu : x ≠ u)
    (hshare : (canonicalMaskRightAugmentedAssignedImage
        ends m j k l zero p S c f hf u huc).1 ∈
      canonicalMaskRightImages ends m j k l zero p x.1) :
    ∃ a b : leftMaskFiber ends m j k l zero p,
      CanonicalTransferWorks ends m k zero a.1.1 x.1.1.1 ∧
      CanonicalTransferWorks ends m k zero b.1.1 u.1.1.1 ∧
      canonicalTranslatedRow ends m k zero a.1.1 x.1.1.1 =
        canonicalTranslatedRow ends m k zero b.1.1 u.1.1.1 ∧
      (¬ CanonicalTransferWorks ends m k zero b.1.1 x.1.1.1 ∨
        ∃ q₁ q₂ : rightMaskFiber ends m j k l zero p,
          q₁ ≠ q₂ ∧
          q₁ ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
          q₁ ∈ canonicalMaskRightImages ends m j k l zero p u.1 ∧
          q₂ ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
          q₂ ∈ canonicalMaskRightImages ends m j k l zero p u.1) := by
  classical
  let qS := canonicalMaskRightAugmentedAssignedImage
    ends m j k l zero p S c f hf u huc
  have hqu := canonicalMaskRightAugmentedAssignedImage_mem
    ends m j k l zero p S c f hf u huc
  obtain ⟨a, hax, hqa⟩ := (mem_canonicalMaskRightImages_iff
    ends m j k l zero p x.1 qS.1).mp hshare
  obtain ⟨b, hbu, hqb⟩ := (mem_canonicalMaskRightImages_iff
    ends m j k l zero p u.1 qS.1).mp hqu
  have hraw : balancedSwap m
        (canonicalMiddleTransfer ends m a.1.1 k zero)
        (canonicalOuterTransfer ends m a.1.1 k zero) x.1.1.1 =
      balancedSwap m
        (canonicalMiddleTransfer ends m b.1.1 k zero)
        (canonicalOuterTransfer ends m b.1.1 k zero) u.1.1.1 :=
    hqa.symm.trans hqb
  have htrans := (canonicalBalancedSwaps_eq_iff_rowSymmDiff
    hloop hjk hkl a b x.1 u.1).mp hraw
  refine ⟨a, b, hax, hbu, htrans, ?_⟩
  by_cases hbx : CanonicalTransferWorks ends m k zero b.1.1 x.1.1.1
  · right
    exact exists_two_common_canonicalMaskRightImages_of_collisionSquare
      hloop hjk hkl a b x.1 u.1 (fun h => hxu (Subtype.ext h))
        hax htrans hbx
  · exact Or.inl hbx




theorem canonicalMaskRightAugmentedExposure_componentCut_or_square
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (x u : ↑S) (huc : u ≠ c) (hxu : x ≠ u)
    (hshare : (canonicalMaskRightAugmentedAssignedImage
        ends m j k l zero p S c f hf u huc).1 ∈
      canonicalMaskRightImages ends m j k l zero p x.1) :
    ∃ a b : leftMaskFiber ends m j k l zero p,
      CanonicalTransferWorks ends m k zero a.1.1 x.1.1.1 ∧
      CanonicalTransferWorks ends m k zero b.1.1 u.1.1.1 ∧
      canonicalTranslatedRow ends m k zero a.1.1 x.1.1.1 =
        canonicalTranslatedRow ends m k zero b.1.1 u.1.1.1 ∧
      (((StatMech.Sharpness.RandomCurrent.connK ends
              (canonicalTranslatedRow ends m k zero b.1.1 x.1.1.1) k zero ∧
            edgeComponent ends
                (canonicalTranslatedRow ends m k zero b.1.1 x.1.1.1) zero =
              edgeComponent ends
                (canonicalTranslatedRow ends m k zero b.1.1 x.1.1.1) k) ∨
          (StatMech.Sharpness.RandomCurrent.connK ends
              (m \ canonicalTranslatedRow ends m k zero b.1.1 x.1.1.1)
                k zero ∧
            edgeComponent ends
                (m \ canonicalTranslatedRow ends m k zero b.1.1 x.1.1.1) zero =
              edgeComponent ends
                (m \ canonicalTranslatedRow ends m k zero b.1.1 x.1.1.1) k)) ∨
        ∃ q₁ q₂ : rightMaskFiber ends m j k l zero p,
          q₁ ≠ q₂ ∧
          q₁ ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
          q₁ ∈ canonicalMaskRightImages ends m j k l zero p u.1 ∧
          q₂ ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
          q₂ ∈ canonicalMaskRightImages ends m j k l zero p u.1) := by
  obtain ⟨a, b, hax, hbu, htrans, hcase⟩ :=
    canonicalMaskRightAugmentedExposure_failedOpposite_or_square
      hloop hjk hkl S c f hf x u huc hxu hshare
  refine ⟨a, b, hax, hbu, htrans, ?_⟩
  rcases hcase with hbad | hsquare
  · exact Or.inl (canonicalTransferWorks_failed_translatedRow_component
      hloop hjk hkl b x.1 hbad)
  · exact Or.inr hsquare




theorem canonicalMaskRightFullExposure_cut_or_secondRow
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (herase : ∀ x ∈ S,
      canonicalMaskRightNeighborhood ends m j k l zero p (S.erase x) =
        canonicalMaskRightNeighborhood ends m j k l zero p S)
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (u : {u : ↑S // u ≠ c}) :
    (∃ r x : leftMaskFiber ends m j k l zero p,
        x ∈ S ∧ CanonicalTranslatedRowRootComponentCut
          ends m k zero r.1.1 x.1.1) ∨
      ∃ s : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S),
        s ≠ canonicalMaskRightAugmentedAssignedImage
          ends m j k l zero p S c f hf u.1 u.2 ∧
        s.1 ∈ canonicalMaskRightImages ends m j k l zero p u.1.1 := by
  classical
  let qS := canonicalMaskRightAugmentedAssignedImage
    ends m j k l zero p S c f hf u.1 u.2
  have hqu := canonicalMaskRightAugmentedAssignedImage_mem
    ends m j k l zero p S c f hf u.1 u.2
  obtain ⟨x, hxS, hxu, hqx⟩ :=
    exists_other_of_erase_canonicalMaskRightNeighborhood_eq
      ends m j k l zero p S u.1.1 u.1.2 (herase u.1.1 u.1.2) qS.1 hqu
  let xS : ↑S := ⟨x, hxS⟩
  have hxune : xS ≠ u.1 := by
    intro h
    exact hxu (congrArg Subtype.val h)
  obtain ⟨a, b, hax, hbu, htrans, hcase⟩ :=
    canonicalMaskRightAugmentedExposure_failedOpposite_or_square
      hloop hjk hkl S c f hf xS u.1 u.2 hxune hqx
  rcases hcase with hbad | hsquare
  · left
    exact ⟨b, x, hxS, canonicalTransferWorks_failed_rootComponentCut
      hloop hjk hkl b x hbad⟩
  · right
    obtain ⟨q₁, q₂, hqne, hq₁x, hq₁u, hq₂x, hq₂u⟩ := hsquare
    by_cases hq₁ : q₁ = qS.1
    · have hq₂S : q₂ ∈ canonicalMaskRightNeighborhood
          ends m j k l zero p S :=
        (mem_canonicalMaskRightNeighborhood_iff
          ends m j k l zero p S q₂).mpr ⟨u.1.1, u.1.2, hq₂u⟩
      let s : ↑(canonicalMaskRightNeighborhood
          ends m j k l zero p S) := ⟨q₂, hq₂S⟩
      refine ⟨s, ?_, hq₂u⟩
      intro h
      apply hqne
      exact hq₁.trans (congrArg Subtype.val h).symm
    · have hq₁S : q₁ ∈ canonicalMaskRightNeighborhood
          ends m j k l zero p S :=
        (mem_canonicalMaskRightNeighborhood_iff
          ends m j k l zero p S q₁).mpr ⟨u.1.1, u.1.2, hq₁u⟩
      exact ⟨⟨q₁, hq₁S⟩, fun h => hq₁ (congrArg Subtype.val h), hq₁u⟩



theorem canonicalMaskRightFullExposure_secondRows_of_noCut
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (herase : ∀ x ∈ S,
      canonicalMaskRightNeighborhood ends m j k l zero p (S.erase x) =
        canonicalMaskRightNeighborhood ends m j k l zero p S)
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (hnoCut : ∀ r x : leftMaskFiber ends m j k l zero p, x ∈ S ->
      ¬ CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 x.1.1) :
    ∀ u : {u : ↑S // u ≠ c},
      ∃ s : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S),
        s ≠ canonicalMaskRightAugmentedAssignedImage
          ends m j k l zero p S c f hf u.1 u.2 ∧
        s.1 ∈ canonicalMaskRightImages ends m j k l zero p u.1.1 := by
  intro u
  rcases canonicalMaskRightFullExposure_cut_or_secondRow
      hloop hjk hkl S herase c f hf u with hcut | hsecond
  · obtain ⟨r, x, hxS, hcut⟩ := hcut
    exact (hnoCut r x hxS hcut).elim
  · exact hsecond

set_option maxHeartbeats 1000000 in




theorem canonicalMaskRightMatchingPair_failedOpposite_or_expands
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c d : ↑S)
    (ef : canonicalMaskRightAugmentedEquivType
          ends m j k l zero p S ×
        canonicalMaskRightAugmentedEquivType ends m j k l zero p S)
    (hef : ef ∈ canonicalMaskRightAugmentedMatchingPairs
      ends m j k l zero p S c d)
    (x : ↑S) (hxc : x ≠ c)
    (hmove : x ≠ (ef.1.trans ef.2.symm : Equiv.Perm ↑S) x) :
    ∃ q : rightMaskFiber ends m j k l zero p,
      q ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
      q ∈ canonicalMaskRightImages ends m j k l zero p
        ((ef.1.trans ef.2.symm : Equiv.Perm ↑S) x).1 ∧
      ∃ a b : leftMaskFiber ends m j k l zero p,
      CanonicalTransferWorks ends m k zero a.1.1 x.1.1.1 ∧
      CanonicalTransferWorks ends m k zero
        b.1.1 ((ef.1.trans ef.2.symm : Equiv.Perm ↑S) x).1.1.1 ∧
      canonicalTranslatedRow ends m k zero a.1.1 x.1.1.1 =
        canonicalTranslatedRow ends m k zero
          b.1.1 ((ef.1.trans ef.2.symm : Equiv.Perm ↑S) x).1.1.1 ∧
      (¬ CanonicalTransferWorks ends m k zero b.1.1 x.1.1.1 ∨
        ∃ r : rightMaskFiber ends m j k l zero p,
          r ≠ q ∧
          r ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
          r ∈ canonicalMaskRightImages ends m j k l zero p
            ((ef.1.trans ef.2.symm : Equiv.Perm ↑S) x).1 ∧
          ∃ u v : ↑S,
            u ≠ c ∧ v ≠ d ∧ u ≠ x ∧
            v ≠ (ef.1.trans ef.2.symm : Equiv.Perm ↑S) x ∧
            (ef.1.trans ef.2.symm : Equiv.Perm ↑S) u = v ∧
            r ∈ canonicalMaskRightImages ends m j k l zero p u.1 ∧
            r ∈ canonicalMaskRightImages ends m j k l zero p v.1) := by
  classical
  let σ : Equiv.Perm ↑S := ef.1.trans ef.2.symm
  obtain ⟨q, hqx, hqσ, hdisp⟩ :=
    canonicalMaskRightAugmentedMatchingPair_secondCommon_displacement
      ends m j k l zero p S c d ef hef x hxc
  obtain ⟨a, hax, hqa⟩ := (mem_canonicalMaskRightImages_iff
    ends m j k l zero p x.1 q).mp hqx
  obtain ⟨b, hbσ, hqb⟩ := (mem_canonicalMaskRightImages_iff
    ends m j k l zero p (σ x).1 q).mp hqσ
  have hraw : balancedSwap m
        (canonicalMiddleTransfer ends m a.1.1 k zero)
        (canonicalOuterTransfer ends m a.1.1 k zero) x.1.1.1 =
      balancedSwap m
        (canonicalMiddleTransfer ends m b.1.1 k zero)
        (canonicalOuterTransfer ends m b.1.1 k zero) (σ x).1.1.1 :=
    hqa.symm.trans hqb
  have htrans := (canonicalBalancedSwaps_eq_iff_rowSymmDiff
    hloop hjk hkl a b x.1 (σ x).1).mp hraw
  refine ⟨q, hqx, hqσ, a, b, hax, hbσ, htrans, ?_⟩
  by_cases hbx : CanonicalTransferWorks ends m k zero b.1.1 x.1.1.1
  · right
    obtain ⟨q₁, q₂, hqne, hq₁x, hq₁σ, hq₂x, hq₂σ⟩ :=
      exists_two_common_canonicalMaskRightImages_of_collisionSquare
        hloop hjk hkl a b x.1 (σ x).1
          (fun h => hmove (Subtype.ext h)) hax htrans hbx
    by_cases hq₁q : q₁ = q
    · obtain ⟨u, v, huc, hvd, hux, hvσ, hσuv, hq₂u, hq₂v⟩ :=
        hdisp q₂ (fun h => hqne (hq₁q.trans h.symm)) hq₂x hq₂σ
      exact ⟨q₂, (fun h => hqne (hq₁q.trans h.symm)), hq₂x, hq₂σ, u, v,
        huc, hvd, hux, hvσ, hσuv, hq₂u, hq₂v⟩
    · obtain ⟨u, v, huc, hvd, hux, hvσ, hσuv, hq₁u, hq₁v⟩ :=
        hdisp q₁ hq₁q hq₁x hq₁σ
      exact ⟨q₁, hq₁q, hq₁x, hq₁σ, u, v,
        huc, hvd, hux, hvσ, hσuv, hq₁u, hq₁v⟩
  · exact Or.inl hbx




theorem exists_tight_canonicalMaskRightHall_obstruction
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ S : Finset (leftMaskFiber ends m j k l zero p),
      S.Nonempty ∧
        (canonicalMaskRightNeighborhood ends m j k l zero p S).card + 1 =
          S.card ∧
        (∀ c ∈ S,
          canonicalMaskRightNeighborhood ends m j k l zero p (S.erase c) =
            canonicalMaskRightNeighborhood ends m j k l zero p S) ∧
        (∀ T : Finset (leftMaskFiber ends m j k l zero p), T ⊂ S ->
          T.card ≤ (canonicalMaskRightNeighborhood
            ends m j k l zero p T).card) ∧
        (∀ c ∈ S, ∀ d ∈ S,
          CanonicalMaskTransferOrbit ends m j k l zero p c d) ∧
        (∀ c ∈ S, ∃ d ∈ S, d ≠ c ∧
          CanonicalMaskTransferAdjacent ends m j k l zero p c d) := by
  classical
  rw [CanonicalMaskRightHall] at hfail
  push Not at hfail
  obtain ⟨S₀, hS₀⟩ := hfail
  let bad : Finset (Finset (leftMaskFiber ends m j k l zero p)) :=
    Finset.univ.filter fun S =>
      (canonicalMaskRightNeighborhood ends m j k l zero p S).card < S.card
  have hbad : bad.Nonempty := by
    refine ⟨S₀, ?_⟩
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hS₀
  obtain ⟨S, hSbad, hSmin⟩ := bad.exists_min_image Finset.card hbad
  have hlt : (canonicalMaskRightNeighborhood
      ends m j k l zero p S).card < S.card := by
    simpa only [bad, Finset.mem_filter, Finset.mem_univ, true_and] using hSbad
  have hSne : S.Nonempty := Finset.card_pos.mp (Nat.zero_lt_of_lt hlt)
  have hProperHall : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card := by
    intro T hTS
    by_contra h
    have hTbad : T ∈ bad := by
      simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
      omega
    have hmin := hSmin T hTbad
    have hcard := Finset.card_lt_card hTS
    omega
  have hHallEraseAll : ∀ c ∈ S, (S.erase c).card ≤
      (canonicalMaskRightNeighborhood
        ends m j k l zero p (S.erase c)).card := by
    intro c hc
    have hnotBad : S.erase c ∉ bad := by
      intro hmem
      have hle := hSmin (S.erase c) hmem
      rw [Finset.card_erase_of_mem hc] at hle
      omega
    by_contra h
    apply hnotBad
    simp only [bad, Finset.mem_filter, Finset.mem_univ, true_and]
    omega
  have herase : ∀ c ∈ S,
      canonicalMaskRightNeighborhood ends m j k l zero p (S.erase c) =
        canonicalMaskRightNeighborhood ends m j k l zero p S := by
    intro c hc
    have hsubset := canonicalMaskRightNeighborhood_mono
      ends m j k l zero p (Finset.erase_subset c S)
    apply Finset.eq_of_subset_of_card_le hsubset
    have hHallErase := hHallEraseAll c hc
    rw [Finset.card_erase_of_mem hc] at hHallErase
    omega
  have htight : (canonicalMaskRightNeighborhood
      ends m j k l zero p S).card + 1 = S.card := by
    obtain ⟨c, hc⟩ := hSne
    have hHallErase := hHallEraseAll c hc
    rw [herase c hc] at hHallErase
    rw [Finset.card_erase_of_mem hc] at hHallErase
    omega
  have horbit : ∀ c ∈ S, ∀ d ∈ S,
      CanonicalMaskTransferOrbit ends m j k l zero p c d := by
    intro c hc d hd
    by_contra hcd
    let A := S.filter fun x =>
      CanonicalMaskTransferOrbit ends m j k l zero p c x
    let B := S \ A
    have hAS : A ⊆ S := Finset.filter_subset _ _
    have hcA : c ∈ A := by
      simp only [A, Finset.mem_filter, hc, true_and]
      exact canonicalMaskTransferOrbit_refl ends m j k l zero p c
    have hdNotA : d ∉ A := by
      simp only [A, Finset.mem_filter, hd, true_and]
      exact hcd
    have hdB : d ∈ B := Finset.mem_sdiff.mpr ⟨hd, hdNotA⟩
    have hcNotB : c ∉ B := fun hcB => (Finset.mem_sdiff.mp hcB).2 hcA
    have hAproper : A ⊂ S := Finset.ssubset_iff_subset_ne.mpr
      ⟨hAS, fun hAS' => hdNotA (hAS' ▸ hd)⟩
    have hBproper : B ⊂ S := Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.sdiff_subset, fun hBS => hcNotB (hBS ▸ hc)⟩
    have hAB : Disjoint A B := by
      rw [Finset.disjoint_left]
      intro x hxA hxB
      exact (Finset.mem_sdiff.mp hxB).2 hxA
    have hsep : ∀ a ∈ A, ∀ b ∈ B,
        ¬ CanonicalMaskTransferOrbit ends m j k l zero p a b := by
      intro a haA b hbB hab
      have hca := (Finset.mem_filter.mp haA).2
      have hcb := hca.trans hab
      exact (Finset.mem_sdiff.mp hbB).2
        (Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hbB).1, hcb⟩)
    have hUnion :=
      card_le_canonicalMaskRightNeighborhood_union_of_orbitSeparated
        ends m j k l zero p A B hAB hsep
          (hProperHall A hAproper) (hProperHall B hBproper)
    rw [Finset.union_sdiff_of_subset hAS] at hUnion
    exact (Nat.not_lt_of_ge hUnion) hlt
  refine ⟨S, hSne, htight, herase, hProperHall, horbit, ?_⟩
  intro c hc
  obtain ⟨q, hqc⟩ := canonicalMaskRightImages_nonempty
    ends m j k l zero hloop hjk hkl hk0 p c
  have hqS : q ∈ canonicalMaskRightNeighborhood
      ends m j k l zero p S :=
    (mem_canonicalMaskRightNeighborhood_iff
      ends m j k l zero p S q).mpr ⟨c, hc, hqc⟩
  have hqErase : q ∈ canonicalMaskRightNeighborhood
      ends m j k l zero p (S.erase c) := by
    rw [herase c hc]
    exact hqS
  obtain ⟨d, hdErase, hqd⟩ := (mem_canonicalMaskRightNeighborhood_iff
    ends m j k l zero p (S.erase c) q).mp hqErase
  have hd := Finset.mem_erase.mp hdErase
  refine ⟨d, hd.2, ?_, ?_⟩
  · exact hd.1
  · exact (exists_mem_canonicalMaskRightImages_iff_adjacent
      ends m j k l zero p c d).mp ⟨q, hqc, hqd⟩





theorem exists_maximalOrbitCoverage_rootComponentCut_of_not_canonicalMaskRightHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ (S : Finset (leftMaskFiber ends m j k l zero p))
        (a r c : leftMaskFiber ends m j k l zero p),
      S.Nonempty ∧ a ∈ S ∧
      (canonicalMaskRightNeighborhood
        ends m j k l zero p S).card + 1 = S.card ∧
      (∀ x ∈ S,
        canonicalMaskRightNeighborhood ends m j k l zero p (S.erase x) =
          canonicalMaskRightNeighborhood ends m j k l zero p S) ∧
      (∀ T : Finset (leftMaskFiber ends m j k l zero p), T ⊂ S ->
        T.card ≤ (canonicalMaskRightNeighborhood
          ends m j k l zero p T).card) ∧
      (∀ d ∈ S,
        CanonicalMaskTransferOrbit ends m j k l zero p a d) ∧
      CanonicalMaskTransferOrbit ends m j k l zero p a r ∧
      (∀ t : leftMaskFiber ends m j k l zero p,
        CanonicalMaskTransferOrbit ends m j k l zero p a t ->
        (canonicalMaskOrbitCoverage ends m j k l zero p t).card ≤
          (canonicalMaskOrbitCoverage ends m j k l zero p r).card) ∧
      c ∈ S ∧
      c ∈ canonicalMaskOrbitCoverage ends m j k l zero p c ∧
      c ∉ canonicalMaskOrbitCoverage ends m j k l zero p r ∧
      CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 c.1.1 := by
  classical
  obtain ⟨S, hSne, htight, herase, hproper, horbit, -⟩ :=
    exists_tight_canonicalMaskRightHall_obstruction
      ends m j k l zero hloop hjk hkl hk0 p hfail
  obtain ⟨a, haS⟩ := hSne
  let O := canonicalMaskTransferOrbitFinset ends m j k l zero p a
  obtain ⟨r, hrO, hrMax⟩ := O.exists_max_image
    (fun x => (canonicalMaskOrbitCoverage ends m j k l zero p x).card)
    (canonicalMaskTransferOrbitFinset_nonempty
      ends m j k l zero p a)
  have har : CanonicalMaskTransferOrbit ends m j k l zero p a r := by
    rwa [mem_canonicalMaskTransferOrbitFinset_iff] at hrO
  have haSorbit : ∀ d ∈ S,
      CanonicalMaskTransferOrbit ends m j k l zero p a d := by
    intro d hdS
    exact horbit a haS d hdS
  have hrMax' : ∀ t : leftMaskFiber ends m j k l zero p,
      CanonicalMaskTransferOrbit ends m j k l zero p a t ->
      (canonicalMaskOrbitCoverage ends m j k l zero p t).card ≤
        (canonicalMaskOrbitCoverage ends m j k l zero p r).card := by
    intro t hat
    apply hrMax t
    rwa [mem_canonicalMaskTransferOrbitFinset_iff]
  by_cases hworks : ∀ d ∈ S,
      CanonicalTransferWorks ends m k zero r.1.1 d.1.1
  · have hle := card_le_canonicalMaskRightNeighborhood_of_reference
      ends m j k l zero hloop hjk hkl p S r hworks
    omega
  · push Not at hworks
    obtain ⟨c, hcS, hbad⟩ := hworks
    have hcCoverage : c ∈ canonicalMaskOrbitCoverage
        ends m j k l zero p c := by
      rw [mem_canonicalMaskOrbitCoverage_iff]
      exact ⟨canonicalMaskTransferOrbit_refl ends m j k l zero p c,
        canonicalTransferWorks_self hloop hjk hkl hk0 c⟩
    have hcNotCoverage : c ∉ canonicalMaskOrbitCoverage
        ends m j k l zero p r := by
      intro hc
      exact hbad ((mem_canonicalMaskOrbitCoverage_iff
        ends m j k l zero p r c).mp hc).2
    exact ⟨S, a, r, c, ⟨a, haS⟩, haS, htight, herase, hproper,
      haSorbit, har, hrMax', hcS, hcCoverage, hcNotCoverage,
      canonicalTransferWorks_failed_rootComponentCut
        hloop hjk hkl r c hbad⟩






theorem exists_maximalOrbitCoverage_quadrangleDichotomy_of_not_canonicalMaskRightHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ (S : Finset (leftMaskFiber ends m j k l zero p))
        (a r c : leftMaskFiber ends m j k l zero p),
      S.Nonempty ∧ a ∈ S ∧
      (canonicalMaskRightNeighborhood
        ends m j k l zero p S).card + 1 = S.card ∧
      (∀ d ∈ S,
        CanonicalMaskTransferOrbit ends m j k l zero p a d) ∧
      CanonicalMaskTransferOrbit ends m j k l zero p a r ∧
      (∀ t : leftMaskFiber ends m j k l zero p,
        CanonicalMaskTransferOrbit ends m j k l zero p a t ->
        (canonicalMaskOrbitCoverage ends m j k l zero p t).card ≤
          (canonicalMaskOrbitCoverage ends m j k l zero p r).card) ∧
      c ∈ S ∧
      CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 c.1.1 ∧
      ((∃ d : leftMaskFiber ends m j k l zero p,
          d ∈ canonicalMaskOrbitCoverage ends m j k l zero p r ∧
          d ∉ canonicalMaskOrbitCoverage ends m j k l zero p c) ∨
        (c ∈ canonicalCoverageExclusiveBadQuadrangles
            ends m j k l zero p c r ∧
          ∃ d : leftMaskFiber ends m j k l zero p,
            d ∈ canonicalCoverageExclusiveBadQuadrangles
              ends m j k l zero p r c)) := by
  classical
  obtain ⟨S, a, r, c, hSne, haS, htight, -, -, haSorbit,
      har, hrMax, hcS, hcCoverage, hcNotCoverage, hcut⟩ :=
    exists_maximalOrbitCoverage_rootComponentCut_of_not_canonicalMaskRightHall
      ends m j k l zero hloop hjk hkl hk0 p hfail
  have hcr : CanonicalMaskTransferOrbit ends m j k l zero p c r :=
    (canonicalMaskTransferOrbit_symm ends m j k l zero p
      (haSorbit c hcS)).trans har
  by_cases hdisc : RowsDisconnect ends m
      (canonicalQuadrangleCompletion ends m k zero
        c.1.1 r.1.1 c.1.1) k zero
  · let d := canonicalQuadrangleCompletionMemOfDisconnects
      ends m j k l zero hloop hjk hkl p c r c hdisc
    have hd := quadrangleCompletion_mem_coverage_sdiff
      hloop hjk hkl c r c hcr hcCoverage hcNotCoverage hdisc
    exact ⟨S, a, r, c, hSne, haS, htight, haSorbit, har, hrMax,
      hcS, hcut, Or.inl ⟨d, hd.1, hd.2⟩⟩
  · have hcBad : c ∈ canonicalCoverageExclusiveBadQuadrangles
        ends m j k l zero p c r := by
      rw [mem_canonicalCoverageExclusiveBadQuadrangles_iff]
      exact ⟨hcCoverage, hcNotCoverage, hdisc⟩
    have hcard := hrMax c (haSorbit c hcS)
    obtain ⟨d, hdBad⟩ :=
      exists_opposite_badQuadrangle_of_coverage_card_le
        hloop hjk hkl c r c hcr hcBad hcard
    exact ⟨S, a, r, c, hSne, haS, htight, haSorbit, har, hrMax,
      hcS, hcut, Or.inr ⟨hcBad, d, hdBad⟩⟩




def CanonicalMaskTransferOrbitInternallyComplete
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ r c : leftMaskFiber ends m j k l zero p,
    CanonicalMaskTransferOrbit ends m j k l zero p r c ->
      CanonicalTransferWorks ends m k zero r.1.1 c.1.1



def CanonicalMaskAdjacentWorksPropagates
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ r x y : leftMaskFiber ends m j k l zero p,
    CanonicalMaskTransferAdjacent ends m j k l zero p x y ->
      CanonicalTransferWorks ends m k zero r.1.1 x.1.1 ->
        CanonicalTransferWorks ends m k zero r.1.1 y.1.1



def CanonicalMaskOrbitCoverageMaximal
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (r : leftMaskFiber ends m j k l zero p) : Prop :=
  ∀ t : leftMaskFiber ends m j k l zero p,
    CanonicalMaskTransferOrbit ends m j k l zero p r t ->
      (canonicalMaskOrbitCoverage ends m j k l zero p t).card ≤
        (canonicalMaskOrbitCoverage ends m j k l zero p r).card


def CanonicalMaskAdjacentCoverageBoundary
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (r x y : leftMaskFiber ends m j k l zero p) : Prop :=
  CanonicalMaskTransferOrbit ends m j k l zero p r x ∧
    CanonicalMaskTransferAdjacent ends m j k l zero p x y ∧
    CanonicalTransferWorks ends m k zero r.1.1 x.1.1 ∧
    ¬ CanonicalTransferWorks ends m k zero r.1.1 y.1.1









def CanonicalMaskAdjacentNormalInvariant
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ x y : leftMaskFiber ends m j k l zero p,
    CanonicalMaskTransferAdjacent ends m j k l zero p x y ->
      canonicalNormalRow ends m k zero x.1.1 =
        canonicalNormalRow ends m k zero y.1.1



def CanonicalMaskNormalFiberComplete
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ r c : leftMaskFiber ends m j k l zero p,
    canonicalNormalRow ends m k zero r.1.1 =
        canonicalNormalRow ends m k zero c.1.1 ->
      CanonicalTransferWorks ends m k zero r.1.1 c.1.1



theorem mem_canonicalTransferUnion_iff_row_componentComplements
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {p : Finset I × Finset I}
    (c : leftMaskFiber ends m j k l zero p)
    {e : I} (hem : e ∈ m) {u : W} (hu : u ∈ ends e) :
    e ∈ canonicalTransferUnion ends m k zero c.1.1 ↔
      ((e ∈ rowClass m c.1.1 0 ∧
          u ∉ StatMech.FrontierA.grahamComponentComplement
            ends (rowClass m c.1.1 0) zero) ∨
        (e ∉ rowClass m c.1.1 0 ∧
          u ∉ StatMech.FrontierA.grahamComponentComplement
            ends (m \ rowClass m c.1.1 0) k)) := by
  rw [mem_canonicalTransferUnion_iff_rooted_endpoints]
  constructor
  · rintro (⟨he0, hall⟩ | ⟨he1, hall⟩)
    · left
      refine ⟨he0, ?_⟩
      rw [StatMech.FrontierA.grahamComponentComplement,
        StatMech.Sharpness.RandomCurrent.mem_notConnCompK]
      exact not_not.mpr (hall u hu)
    · right
      have he1' : e ∈ m \ rowClass m c.1.1 0 := by
        simpa only [rowClass_one_eq_sdiff] using he1
      have he1mem := Finset.mem_sdiff.mp he1'
      refine ⟨he1mem.2, ?_⟩
      rw [StatMech.FrontierA.grahamComponentComplement,
        StatMech.Sharpness.RandomCurrent.mem_notConnCompK]
      have hconn := hall u hu
      exact not_not.mpr (by
        simpa only [rowClass_one_eq_sdiff] using hconn)
  · rintro (⟨he0, hu0⟩ | ⟨he0, hu1⟩)
    · left
      refine ⟨he0, ?_⟩
      rw [StatMech.FrontierA.grahamComponentComplement,
        StatMech.Sharpness.RandomCurrent.mem_notConnCompK] at hu0
      have hzu : StatMech.Sharpness.RandomCurrent.connK
          ends (rowClass m c.1.1 0) zero u := not_not.mp hu0
      intro v hv
      by_cases huv : u = v
      · simpa [huv] using hzu
      · exact hzu.tail ⟨e, he0, hu, hv, huv⟩
    · right
      have he1 : e ∈ m \ rowClass m c.1.1 0 :=
        Finset.mem_sdiff.mpr ⟨hem, he0⟩
      refine ⟨?_, ?_⟩
      · rwa [rowClass_one_eq_sdiff]
      · rw [StatMech.FrontierA.grahamComponentComplement,
          StatMech.Sharpness.RandomCurrent.mem_notConnCompK] at hu1
        have hku : StatMech.Sharpness.RandomCurrent.connK
            ends (m \ rowClass m c.1.1 0) k u := not_not.mp hu1
        intro v hv
        rw [rowClass_one_eq_sdiff]
        by_cases huv : u = v
        · simpa [huv] using hku
        · exact hku.tail ⟨e, he1, hu, hv, huv⟩

private theorem mem_iff_mem_of_noCrossingK
    {ends : I -> Sym2 W} {K : Finset I} {S : Finset W}
    (hno : StatMech.Sharpness.RandomCurrent.NoCrossingK ends K S)
    {e : I} (he : e ∈ K) {u v : W}
    (hu : u ∈ ends e) (hv : v ∈ ends e) :
    u ∈ S ↔ v ∈ S := by
  rcases hno e he with hin | hout
  · exact iff_of_true (hin u hu) (hin v hv)
  · exact iff_of_false
      (fun huS => (Finset.mem_compl.mp (hout u hu)) huS)
      (fun hvS => (Finset.mem_compl.mp (hout v hv)) hvS)

private theorem noCrossingK_of_endpoint_membership_iff
    {ends : I -> Sym2 W} {K : Finset I} {S : Finset W}
    (hsame : ∀ e ∈ K, ∀ u ∈ ends e, ∀ v ∈ ends e,
      (u ∈ S ↔ v ∈ S)) :
    StatMech.Sharpness.RandomCurrent.NoCrossingK ends K S := by
  intro e he
  let u := (ends e).out.1
  have hu : u ∈ ends e := Sym2.out_fst_mem (ends e)
  by_cases huS : u ∈ S
  · left
    intro v hv
    exact (hsame e he u hu v hv).mp huS
  · right
    intro v hv
    rw [Finset.mem_compl]
    exact fun hvS => huS ((hsame e he u hu v hv).mpr hvS)

set_option maxHeartbeats 1000000 in
private theorem canonicalNormalCuts_boolean
    (er ec tr tc aru arv bru brv acu acv bcu bcv : Prop)
    (hAr : er -> (aru ↔ arv)) (hBr : ¬ er -> (bru ↔ brv))
    (hAc : ec -> (acu ↔ acv)) (hBc : ¬ ec -> (bcu ↔ bcv))
    (hTru : tr ↔ (er ∧ ¬ aru) ∨ (¬ er ∧ ¬ bru))
    (hTrv : tr ↔ (er ∧ ¬ arv) ∨ (¬ er ∧ ¬ brv))
    (hTcu : tc ↔ (ec ∧ ¬ acu) ∨ (¬ ec ∧ ¬ bcu))
    (hTcv : tc ↔ (ec ∧ ¬ acv) ∨ (¬ ec ∧ ¬ bcv))
    (hnormal : ((er ∧ ¬ tr) ∨ (tr ∧ ¬ er)) ↔
      ((ec ∧ ¬ tc) ∨ (tc ∧ ¬ ec))) :
    ((((ec ∧ ¬ tr) ∨ (tr ∧ ¬ ec)) ->
        (((¬ aru ∧ bcu) ∨ (¬ acu ∧ bru)) ↔
          ((¬ arv ∧ bcv) ∨ (¬ acv ∧ brv)))) ∧
      (¬ ((ec ∧ ¬ tr) ∨ (tr ∧ ¬ ec)) ->
        (((¬ aru ∧ ¬ acu) ∨ (bru ∧ bcu)) ↔
          ((¬ arv ∧ ¬ acv) ∨ (brv ∧ bcv))))) := by
  by_cases her : er <;> by_cases hec : ec <;>
    by_cases htr : tr <;> by_cases htc : tc <;>
    simp only [her, hec, htr, htc, true_and, false_and, and_true, and_false,
      not_true_eq_false, not_false_eq_true, false_or, true_or] at * <;>
    tauto




theorem canonicalMaskNormalFiberComplete
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I) :
    CanonicalMaskNormalFiberComplete ends m j k l zero p := by
  intro r c hnormal
  rw [canonicalTransferWorks_iff_translatedRowDisconnects
    hloop hjk hkl r c]
  let R := rowClass m r.1.1 0
  let C := rowClass m c.1.1 0
  let Tr := canonicalTransferUnion ends m k zero r.1.1
  let Tc := canonicalTransferUnion ends m k zero c.1.1
  let K := C ∆ Tr
  let Ar := StatMech.FrontierA.grahamComponentComplement ends R zero
  let Br := StatMech.FrontierA.grahamComponentComplement ends (m \ R) k
  let Ac := StatMech.FrontierA.grahamComponentComplement ends C zero
  let Bc := StatMech.FrontierA.grahamComponentComplement ends (m \ C) k
  let Srow := (Arᶜ ∩ Bc) ∪ (Acᶜ ∩ Br)
  let Scomp := (Arᶜ ∩ Acᶜ) ∪ (Br ∩ Bc)
  have hrGate : RowsDisconnect ends m r.1.1 k zero :=
    r.1.2.2.2.2.2
  have hcGate : RowsDisconnect ends m c.1.1 k zero :=
    c.1.2.2.2.2.2
  have hzeroAr : zero ∉ Ar :=
    StatMech.FrontierA.grahamComponentComplement_not_mem ends R zero
  have hkAr : k ∈ Ar := by
    dsimp only [Ar]
    rw [StatMech.FrontierA.grahamComponentComplement,
      StatMech.Sharpness.RandomCurrent.mem_notConnCompK]
    intro h
    exact hrGate.1
      (StatMech.Sharpness.RandomCurrent.connK_symm ends R h)
  have hkBr : k ∉ Br :=
    StatMech.FrontierA.grahamComponentComplement_not_mem ends (m \ R) k
  have hzeroBr : zero ∈ Br := by
    dsimp only [Br]
    rw [StatMech.FrontierA.grahamComponentComplement,
      StatMech.Sharpness.RandomCurrent.mem_notConnCompK]
    simpa only [R, rowClass_one_eq_sdiff] using hrGate.2
  have hzeroAc : zero ∉ Ac :=
    StatMech.FrontierA.grahamComponentComplement_not_mem ends C zero
  have hkAc : k ∈ Ac := by
    dsimp only [Ac]
    rw [StatMech.FrontierA.grahamComponentComplement,
      StatMech.Sharpness.RandomCurrent.mem_notConnCompK]
    intro h
    exact hcGate.1
      (StatMech.Sharpness.RandomCurrent.connK_symm ends C h)
  have hkBc : k ∉ Bc :=
    StatMech.FrontierA.grahamComponentComplement_not_mem ends (m \ C) k
  have hzeroBc : zero ∈ Bc := by
    dsimp only [Bc]
    rw [StatMech.FrontierA.grahamComponentComplement,
      StatMech.Sharpness.RandomCurrent.mem_notConnCompK]
    simpa only [C, rowClass_one_eq_sdiff] using hcGate.2
  have hzeroSrow : zero ∈ Srow := by
    simp only [Srow, Finset.mem_union, Finset.mem_inter,
      Finset.mem_compl, hzeroAr, hzeroBc, not_false_eq_true,
      true_and, true_or]
  have hkSrow : k ∉ Srow := by
    simp only [Srow, Finset.mem_union, Finset.mem_inter,
      Finset.mem_compl, hkAr, hkAc, hkBr, hkBc,
      not_true_eq_false, false_and, and_false, false_or, not_false_eq_true]
  have hzeroScomp : zero ∈ Scomp := by
    simp only [Scomp, Finset.mem_union, Finset.mem_inter,
      Finset.mem_compl, hzeroAr, hzeroAc, not_false_eq_true,
      true_and, true_or]
  have hkScomp : k ∉ Scomp := by
    simp only [Scomp, Finset.mem_union, Finset.mem_inter,
      Finset.mem_compl, hkAr, hkAc, hkBr, hkBc,
      not_true_eq_false, false_and, and_false, false_or, not_false_eq_true]
  have hKm : K ⊆ m := by
    simpa only [K, C, Tr] using
      canonicalTranslatedRow_subset_m hloop hjk hkl r c
  have hnormal' : R ∆ Tr = C ∆ Tc := by
    simpa only [R, C, Tr, Tc, canonicalNormalRow] using hnormal
  have hNoRow :
      StatMech.Sharpness.RandomCurrent.NoCrossingK ends K Srow := by
    apply noCrossingK_of_endpoint_membership_iff
    intro e heK u hu v hv
    have hem : e ∈ m := hKm heK
    have hAr : e ∈ R -> (u ∈ Ar ↔ v ∈ Ar) := by
      intro he
      exact mem_iff_mem_of_noCrossingK
        (StatMech.FrontierA.grahamComponentComplement_noCrossing
          ends R zero) he hu hv
    have hBr : e ∉ R -> (u ∈ Br ↔ v ∈ Br) := by
      intro he
      exact mem_iff_mem_of_noCrossingK
        (StatMech.FrontierA.grahamComponentComplement_noCrossing
          ends (m \ R) k) (Finset.mem_sdiff.mpr ⟨hem, he⟩) hu hv
    have hAc : e ∈ C -> (u ∈ Ac ↔ v ∈ Ac) := by
      intro he
      exact mem_iff_mem_of_noCrossingK
        (StatMech.FrontierA.grahamComponentComplement_noCrossing
          ends C zero) he hu hv
    have hBc : e ∉ C -> (u ∈ Bc ↔ v ∈ Bc) := by
      intro he
      exact mem_iff_mem_of_noCrossingK
        (StatMech.FrontierA.grahamComponentComplement_noCrossing
          ends (m \ C) k) (Finset.mem_sdiff.mpr ⟨hem, he⟩) hu hv
    have hTru :=
      mem_canonicalTransferUnion_iff_row_componentComplements r hem hu
    have hTrv :=
      mem_canonicalTransferUnion_iff_row_componentComplements r hem hv
    have hTcu :=
      mem_canonicalTransferUnion_iff_row_componentComplements c hem hu
    have hTcv :=
      mem_canonicalTransferUnion_iff_row_componentComplements c hem hv
    change e ∈ Tr ↔
      ((e ∈ R ∧ u ∉ Ar) ∨ (e ∉ R ∧ u ∉ Br)) at hTru
    change e ∈ Tr ↔
      ((e ∈ R ∧ v ∉ Ar) ∨ (e ∉ R ∧ v ∉ Br)) at hTrv
    change e ∈ Tc ↔
      ((e ∈ C ∧ u ∉ Ac) ∨ (e ∉ C ∧ u ∉ Bc)) at hTcu
    change e ∈ Tc ↔
      ((e ∈ C ∧ v ∉ Ac) ∨ (e ∉ C ∧ v ∉ Bc)) at hTcv
    have hn : e ∈ R ∆ Tr ↔ e ∈ C ∆ Tc := by rw [hnormal']
    simp only [Finset.mem_symmDiff] at hn
    change e ∈ C ∆ Tr at heK
    simp only [Finset.mem_symmDiff] at heK
    simp only [Srow, Finset.mem_union, Finset.mem_inter,
      Finset.mem_compl]
    exact (canonicalNormalCuts_boolean
      (e ∈ R) (e ∈ C) (e ∈ Tr) (e ∈ Tc)
      (u ∈ Ar) (v ∈ Ar) (u ∈ Br) (v ∈ Br)
      (u ∈ Ac) (v ∈ Ac) (u ∈ Bc) (v ∈ Bc)
      hAr hBr hAc hBc hTru hTrv hTcu hTcv hn).1 heK
  have hNoComp :
      StatMech.Sharpness.RandomCurrent.NoCrossingK ends (m \ K) Scomp := by
    apply noCrossingK_of_endpoint_membership_iff
    intro e heComp u hu v hv
    have heComp' := Finset.mem_sdiff.mp heComp
    have hem : e ∈ m := heComp'.1
    have heNotK : e ∉ K := heComp'.2
    have hAr : e ∈ R -> (u ∈ Ar ↔ v ∈ Ar) := by
      intro he
      exact mem_iff_mem_of_noCrossingK
        (StatMech.FrontierA.grahamComponentComplement_noCrossing
          ends R zero) he hu hv
    have hBr : e ∉ R -> (u ∈ Br ↔ v ∈ Br) := by
      intro he
      exact mem_iff_mem_of_noCrossingK
        (StatMech.FrontierA.grahamComponentComplement_noCrossing
          ends (m \ R) k) (Finset.mem_sdiff.mpr ⟨hem, he⟩) hu hv
    have hAc : e ∈ C -> (u ∈ Ac ↔ v ∈ Ac) := by
      intro he
      exact mem_iff_mem_of_noCrossingK
        (StatMech.FrontierA.grahamComponentComplement_noCrossing
          ends C zero) he hu hv
    have hBc : e ∉ C -> (u ∈ Bc ↔ v ∈ Bc) := by
      intro he
      exact mem_iff_mem_of_noCrossingK
        (StatMech.FrontierA.grahamComponentComplement_noCrossing
          ends (m \ C) k) (Finset.mem_sdiff.mpr ⟨hem, he⟩) hu hv
    have hTru :=
      mem_canonicalTransferUnion_iff_row_componentComplements r hem hu
    have hTrv :=
      mem_canonicalTransferUnion_iff_row_componentComplements r hem hv
    have hTcu :=
      mem_canonicalTransferUnion_iff_row_componentComplements c hem hu
    have hTcv :=
      mem_canonicalTransferUnion_iff_row_componentComplements c hem hv
    change e ∈ Tr ↔
      ((e ∈ R ∧ u ∉ Ar) ∨ (e ∉ R ∧ u ∉ Br)) at hTru
    change e ∈ Tr ↔
      ((e ∈ R ∧ v ∉ Ar) ∨ (e ∉ R ∧ v ∉ Br)) at hTrv
    change e ∈ Tc ↔
      ((e ∈ C ∧ u ∉ Ac) ∨ (e ∉ C ∧ u ∉ Bc)) at hTcu
    change e ∈ Tc ↔
      ((e ∈ C ∧ v ∉ Ac) ∨ (e ∉ C ∧ v ∉ Bc)) at hTcv
    have hn : e ∈ R ∆ Tr ↔ e ∈ C ∆ Tc := by rw [hnormal']
    simp only [Finset.mem_symmDiff] at hn
    change e ∉ C ∆ Tr at heNotK
    simp only [Finset.mem_symmDiff] at heNotK
    simp only [Scomp, Finset.mem_union, Finset.mem_inter,
      Finset.mem_compl]
    exact (canonicalNormalCuts_boolean
      (e ∈ R) (e ∈ C) (e ∈ Tr) (e ∈ Tc)
      (u ∈ Ar) (v ∈ Ar) (u ∈ Br) (v ∈ Br)
      (u ∈ Ac) (v ∈ Ac) (u ∈ Bc) (v ∈ Bc)
      hAr hBr hAc hBc hTru hTrv hTcu hTcv hn).2 heNotK
  change RowSupportDisconnects ends m K k zero
  exact ⟨fun hconn => hkSrow
      (connK_mem_of_noCrossing hNoRow hzeroSrow
        (StatMech.Sharpness.RandomCurrent.connK_symm ends K hconn)),
    fun hconn => hkScomp
      (connK_mem_of_noCrossing hNoComp hzeroScomp
        (StatMech.Sharpness.RandomCurrent.connK_symm ends (m \ K) hconn))⟩



theorem canonicalNormalRows_ne_of_not_canonicalTransferWorks
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p)
    (hbad : ¬ CanonicalTransferWorks ends m k zero r.1.1 c.1.1) :
    canonicalNormalRow ends m k zero r.1.1 ≠
      canonicalNormalRow ends m k zero c.1.1 := by
  intro hnormal
  exact hbad (canonicalMaskNormalFiberComplete
    ends m j k l zero hloop hjk hkl p r c hnormal)



theorem canonicalNormalRows_ne_of_rootComponentCut
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p)
    (hcut : CanonicalTranslatedRowRootComponentCut
      ends m k zero r.1.1 c.1.1) :
    canonicalNormalRow ends m k zero r.1.1 ≠
      canonicalNormalRow ends m k zero c.1.1 := by
  apply canonicalNormalRows_ne_of_not_canonicalTransferWorks
    hloop hjk hkl r c
  intro hworks
  have hdisc := (canonicalTransferWorks_iff_translatedRowDisconnects
    hloop hjk hkl r c).mp hworks
  rcases hcut with hcut | hcut
  · exact hdisc.1 hcut.1
  · exact hdisc.2 hcut.1



theorem card_le_canonicalMaskRightNeighborhood_of_normalFiber
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (r : leftMaskFiber ends m j k l zero p)
    (hnormal : ∀ c ∈ S,
      canonicalNormalRow ends m k zero r.1.1 =
        canonicalNormalRow ends m k zero c.1.1) :
    S.card ≤
      (canonicalMaskRightNeighborhood ends m j k l zero p S).card := by
  apply card_le_canonicalMaskRightNeighborhood_of_reference
    ends m j k l zero hloop hjk hkl p S r
  intro c hcS
  exact canonicalMaskNormalFiberComplete
    ends m j k l zero hloop hjk hkl p r c (hnormal c hcS)



def CanonicalCoverageExclusiveBoundaryCertificate
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (a b c : leftMaskFiber ends m j k l zero p) : Prop :=
  let d := canonicalQuadrangleCompletion ends m k zero
    a.1.1 b.1.1 c.1.1
  ((StatMech.Sharpness.RandomCurrent.connK
        ends (rowClass m d 0) k zero ∧
      StatMech.Sharpness.RandomCurrent.sources
        ends (edgeComponent ends (rowClass m d 0) zero) = {j, k} ∧
      StatMech.Sharpness.RandomCurrent.sources ends (rowClass m d 0 \
        edgeComponent ends (rowClass m d 0) zero) = ∅ ∧
      Disjoint (canonicalTransferUnion ends m k zero d)
        (rowClass m d 0 \
          edgeComponent ends (rowClass m d 0) zero)) ∨
    (StatMech.Sharpness.RandomCurrent.connK
        ends (rowClass m d 1) k zero ∧
      StatMech.Sharpness.RandomCurrent.sources
        ends (edgeComponent ends (rowClass m d 1) k) = {k, l} ∧
      StatMech.Sharpness.RandomCurrent.sources ends (rowClass m d 1 \
        edgeComponent ends (rowClass m d 1) k) = ∅ ∧
      Disjoint (canonicalTransferUnion ends m k zero d)
        (rowClass m d 1 \
          edgeComponent ends (rowClass m d 1) k)))



theorem canonicalCoverageExclusiveBadQuadrangle_boundaryCertificate
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p)
    (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b)
    (hc : c ∈ canonicalCoverageExclusiveBadQuadrangles
      ends m j k l zero p a b) :
    CanonicalCoverageExclusiveBoundaryCertificate
      ends m j k l zero p a b c := by
  simpa only [CanonicalCoverageExclusiveBoundaryCertificate] using
    (canonicalCoverageExclusiveBadQuadrangle_typedData
      hloop hjk hkl a b c hab hc).2.2.2.2.2




theorem canonicalMaskTransferAdjacent_oppositeRootCuts_or_twoCommonImages
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (x y : leftMaskFiber ends m j k l zero p)
    (hxyne : x ≠ y)
    (hxy : CanonicalMaskTransferAdjacent ends m j k l zero p x y) :
    (∃ a b : leftMaskFiber ends m j k l zero p,
        CanonicalTransferWorks ends m k zero a.1.1 x.1.1 ∧
        CanonicalTransferWorks ends m k zero b.1.1 y.1.1 ∧
        canonicalTranslatedRow ends m k zero a.1.1 x.1.1 =
          canonicalTranslatedRow ends m k zero b.1.1 y.1.1 ∧
        ¬ CanonicalTransferWorks ends m k zero b.1.1 x.1.1 ∧
        ¬ CanonicalTransferWorks ends m k zero a.1.1 y.1.1 ∧
        CanonicalTranslatedRowRootComponentCut
          ends m k zero b.1.1 x.1.1 ∧
        CanonicalTranslatedRowRootComponentCut
          ends m k zero a.1.1 y.1.1) ∨
      ∃ q₁ q₂ : rightMaskFiber ends m j k l zero p,
        q₁ ≠ q₂ ∧
        q₁ ∈ canonicalMaskRightImages ends m j k l zero p x ∧
        q₁ ∈ canonicalMaskRightImages ends m j k l zero p y ∧
        q₂ ∈ canonicalMaskRightImages ends m j k l zero p x ∧
        q₂ ∈ canonicalMaskRightImages ends m j k l zero p y := by
  obtain ⟨a, b, hax, hby, hrow⟩ :=
    (canonicalMaskTransferAdjacent_iff_exists_works_rowSymmDiff
      hloop hjk hkl x y).mp hxy
  have htrans : canonicalTranslatedRow ends m k zero a.1.1 x.1.1 =
      canonicalTranslatedRow ends m k zero b.1.1 y.1.1 := hrow
  have hopp := canonicalTransferWorks_opposite_iff_of_translatedRow_eq
    hloop hjk hkl a b x y htrans
  by_cases hbx : CanonicalTransferWorks ends m k zero b.1.1 x.1.1
  · exact Or.inr (exists_two_common_canonicalMaskRightImages_of_collisionSquare
      hloop hjk hkl a b x y hxyne hax htrans hbx)
  · have hay : ¬ CanonicalTransferWorks ends m k zero a.1.1 y.1.1 :=
      fun hay => hbx (hopp.mpr hay)
    exact Or.inl ⟨a, b, hax, hby, htrans, hbx, hay,
      canonicalTransferWorks_failed_rootComponentCut
        hloop hjk hkl b x hbx,
      canonicalTransferWorks_failed_rootComponentCut
        hloop hjk hkl a y hay⟩





theorem exists_collisionReferenceDifference_at_adjacentFailedCutCrossing
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r x y : leftMaskFiber ends m j k l zero p)
    (hxy : CanonicalMaskTransferAdjacent ends m j k l zero p x y)
    (hrx : CanonicalTransferWorks ends m k zero r.1.1 x.1.1)
    (hry : ¬ CanonicalTransferWorks ends m k zero r.1.1 y.1.1) :
    ∃ a b : leftMaskFiber ends m j k l zero p,
      CanonicalTransferWorks ends m k zero a.1.1 x.1.1 ∧
      CanonicalTransferWorks ends m k zero b.1.1 y.1.1 ∧
      canonicalTranslatedRow ends m k zero a.1.1 x.1.1 =
        canonicalTranslatedRow ends m k zero b.1.1 y.1.1 ∧
      ∃ e : I,
        e ∈ canonicalTransferUnion ends m k zero a.1.1 ∆
          canonicalTransferUnion ends m k zero b.1.1 ∧
        let Kx := canonicalTranslatedRow ends m k zero r.1.1 x.1.1
        let Ky := canonicalTranslatedRow ends m k zero r.1.1 y.1.1
        ((e ∈ Ky \ Kx ∧
            ∃ u v, u ∈ ends e ∧ v ∈ ends e ∧
              u ∉ StatMech.FrontierA.grahamComponentComplement
                ends Kx k ∧
              v ∈ StatMech.FrontierA.grahamComponentComplement
                ends Kx k) ∨
          (e ∈ (m \ Ky) \ (m \ Kx) ∧
            ∃ u v, u ∈ ends e ∧ v ∈ ends e ∧
              u ∉ StatMech.FrontierA.grahamComponentComplement
                ends (m \ Kx) k ∧
              v ∈ StatMech.FrontierA.grahamComponentComplement
                ends (m \ Kx) k)) := by
  obtain ⟨a, b, hax, hby, htrans⟩ :=
    (canonicalMaskTransferAdjacent_iff_exists_works_rowSymmDiff
      hloop hjk hkl x y).mp hxy
  let Kx := canonicalTranslatedRow ends m k zero r.1.1 x.1.1
  let Ky := canonicalTranslatedRow ends m k zero r.1.1 y.1.1
  have hKx : RowSupportDisconnects ends m Kx k zero :=
    (canonicalTransferWorks_iff_translatedRowDisconnects
      hloop hjk hkl r x).mp hrx
  have hKy : ¬ RowSupportDisconnects ends m Ky k zero :=
    fun h => hry ((canonicalTransferWorks_iff_translatedRowDisconnects
      hloop hjk hkl r y).mpr h)
  have hdiff : Kx ∆ Ky =
      canonicalTransferUnion ends m k zero a.1.1 ∆
        canonicalTransferUnion ends m k zero b.1.1 := by
    calc
      Kx ∆ Ky = rowClass m x.1.1 0 ∆ rowClass m y.1.1 0 := by
        dsimp only [Kx, Ky, canonicalTranslatedRow]
        calc
          (rowClass m x.1.1 0 ∆
              canonicalTransferUnion ends m k zero r.1.1) ∆
              (rowClass m y.1.1 0 ∆
                canonicalTransferUnion ends m k zero r.1.1) =
            (rowClass m x.1.1 0 ∆ rowClass m y.1.1 0) ∆
              (canonicalTransferUnion ends m k zero r.1.1 ∆
                canonicalTransferUnion ends m k zero r.1.1) := by ac_rfl
          _ = rowClass m x.1.1 0 ∆ rowClass m y.1.1 0 := by simp
      _ = canonicalTransferUnion ends m k zero a.1.1 ∆
          canonicalTransferUnion ends m k zero b.1.1 :=
        rowSymmDiff_eq_transferSymmDiff_of_translatedRow_eq
          a.1.1 b.1.1 x.1.1 y.1.1 htrans
  refine ⟨a, b, hax, hby, htrans, ?_⟩
  by_cases hconn : StatMech.Sharpness.RandomCurrent.connK
      ends Ky k zero
  · let S := StatMech.FrontierA.grahamComponentComplement ends Kx k
    have hkS : k ∉ S :=
      StatMech.FrontierA.grahamComponentComplement_not_mem ends Kx k
    have hzeroS : zero ∈ S := by
      dsimp only [S]
      rw [StatMech.FrontierA.grahamComponentComplement,
        StatMech.Sharpness.RandomCurrent.mem_notConnCompK]
      exact hKx.1
    obtain ⟨e, he, hcross⟩ := exists_crossing_edge_mem_sdiff_of_connK
      (StatMech.FrontierA.grahamComponentComplement_noCrossing
        ends Kx k) hkS hzeroS hconn
    have he' := Finset.mem_sdiff.mp he
    have heDiff : e ∈ Kx ∆ Ky :=
      Finset.mem_symmDiff.mpr (Or.inr ⟨he'.1, he'.2⟩)
    refine ⟨e, hdiff ▸ heDiff, ?_⟩
    dsimp only [Kx, Ky]
    exact Or.inl ⟨he, hcross⟩
  · have hconnComp : StatMech.Sharpness.RandomCurrent.connK
        ends (m \ Ky) k zero := by
      by_contra hnot
      exact hKy ⟨hconn, hnot⟩
    let S := StatMech.FrontierA.grahamComponentComplement
      ends (m \ Kx) k
    have hkS : k ∉ S :=
      StatMech.FrontierA.grahamComponentComplement_not_mem
        ends (m \ Kx) k
    have hzeroS : zero ∈ S := by
      dsimp only [S]
      rw [StatMech.FrontierA.grahamComponentComplement,
        StatMech.Sharpness.RandomCurrent.mem_notConnCompK]
      exact hKx.2
    obtain ⟨e, he, hcross⟩ := exists_crossing_edge_mem_sdiff_of_connK
      (StatMech.FrontierA.grahamComponentComplement_noCrossing
        ends (m \ Kx) k) hkS hzeroS hconnComp
    have he' := Finset.mem_sdiff.mp he
    have heKy := Finset.mem_sdiff.mp he'.1
    have heNotKx : e ∉ Ky := by
      intro heKyMem
      exact heKy.2 heKyMem
    have heKx : e ∈ Kx := by
      by_contra heKx
      exact he'.2 (Finset.mem_sdiff.mpr ⟨heKy.1, heKx⟩)
    have heDiff : e ∈ Kx ∆ Ky :=
      Finset.mem_symmDiff.mpr (Or.inl ⟨heKx, heNotKx⟩)
    refine ⟨e, hdiff ▸ heDiff, ?_⟩
    dsimp only [Kx, Ky]
    exact Or.inr ⟨he, hcross⟩





theorem exists_rootIncident_transferDifference_of_equalNormal_failed
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p)
    (hnormal : canonicalNormalRow ends m k zero r.1.1 =
      canonicalNormalRow ends m k zero c.1.1)
    (hbad : ¬ CanonicalTransferWorks ends m k zero r.1.1 c.1.1) :
    ∃ e : I,
      e ∈ canonicalTransferUnion ends m k zero r.1.1 ∆
        canonicalTransferUnion ends m k zero c.1.1 ∧
      let N := canonicalNormalRow ends m k zero r.1.1
      let K := canonicalTranslatedRow ends m k zero r.1.1 c.1.1
      ((e ∈ K \ N ∧ zero ∈ ends e) ∨
        (e ∈ (m \ K) \ (m \ N) ∧ k ∈ ends e)) := by
  let N := canonicalNormalRow ends m k zero r.1.1
  let K := canonicalTranslatedRow ends m k zero r.1.1 c.1.1
  have hN : N = rowClass m c.1.1 0 ∆
      canonicalTransferUnion ends m k zero c.1.1 := by
    simpa only [N, canonicalNormalRow] using hnormal
  have hdiff : K ∆ N =
      canonicalTransferUnion ends m k zero r.1.1 ∆
        canonicalTransferUnion ends m k zero c.1.1 := by
    dsimp only [K, canonicalTranslatedRow]
    rw [hN]
    calc
      (rowClass m c.1.1 0 ∆
          canonicalTransferUnion ends m k zero r.1.1) ∆
          (rowClass m c.1.1 0 ∆
            canonicalTransferUnion ends m k zero c.1.1) =
        (rowClass m c.1.1 0 ∆ rowClass m c.1.1 0) ∆
          (canonicalTransferUnion ends m k zero r.1.1 ∆
            canonicalTransferUnion ends m k zero c.1.1) := by ac_rfl
      _ = canonicalTransferUnion ends m k zero r.1.1 ∆
          canonicalTransferUnion ends m k zero c.1.1 := by simp
  have hK : ¬ RowSupportDisconnects ends m K k zero :=
    fun h => hbad ((canonicalTransferWorks_iff_translatedRowDisconnects
      hloop hjk hkl r c).mpr h)
  have hNzero : ∀ e ∈ N, zero ∉ ends e := by
    simpa only [N] using
      canonicalNormalRow_no_incident_zero hloop hjk hkl r.1.2
  have hNcompK : ∀ e ∈ m \ N, k ∉ ends e := by
    intro e he hek
    have he' := Finset.mem_sdiff.mp he
    exact he'.2 (by
      simpa only [N] using
        (mem_canonicalNormalRow_of_mem_k
          hloop hjk hkl r.1.2 he'.1 hek))
  by_cases hconn : StatMech.Sharpness.RandomCurrent.connK
      ends K k zero
  · have hno : StatMech.Sharpness.RandomCurrent.NoCrossingK
        ends N {zero} := by
      intro e he
      right
      intro w hw
      simp only [Finset.mem_compl, Finset.mem_singleton]
      exact fun hw0 => hNzero e he (hw0 ▸ hw)
    obtain ⟨e, he, u, v, hu, hv, -, hvS⟩ :=
      exists_crossing_edge_mem_sdiff_of_connK
        hno (by simpa [hk0]) (by simp) hconn
    have hvzero : v = zero := by simpa using hvS
    have hzeroEnd : zero ∈ ends e := by simpa [hvzero] using hv
    have he' := Finset.mem_sdiff.mp he
    have heDiff : e ∈ K ∆ N :=
      Finset.mem_symmDiff.mpr (Or.inl ⟨he'.1, he'.2⟩)
    refine ⟨e, hdiff ▸ heDiff, ?_⟩
    dsimp only [N, K]
    exact Or.inl ⟨he, hzeroEnd⟩
  · have hconnComp : StatMech.Sharpness.RandomCurrent.connK
        ends (m \ K) k zero := by
      by_contra hnot
      exact hK ⟨hconn, hnot⟩
    have hno : StatMech.Sharpness.RandomCurrent.NoCrossingK
        ends (m \ N) {k} := by
      intro e he
      right
      intro w hw
      simp only [Finset.mem_compl, Finset.mem_singleton]
      exact fun hwk => hNcompK e he (hwk ▸ hw)
    obtain ⟨e, he, u, v, hu, hv, -, hvS⟩ :=
      exists_crossing_edge_mem_sdiff_of_connK
        hno (by simpa using Ne.symm hk0) (by simp)
          (StatMech.Sharpness.RandomCurrent.connK_symm
            ends (m \ K) hconnComp)
    have hvk : v = k := by simpa using hvS
    have hkEnd : k ∈ ends e := by simpa [hvk] using hv
    have he' := Finset.mem_sdiff.mp he
    have heKcomp := Finset.mem_sdiff.mp he'.1
    have heNcomp : e ∉ m \ N := he'.2
    have heN : e ∈ N := by
      by_contra heNotN
      exact heNcomp (Finset.mem_sdiff.mpr ⟨heKcomp.1, heNotN⟩)
    have heNotK : e ∉ K := heKcomp.2
    have heDiff : e ∈ K ∆ N :=
      Finset.mem_symmDiff.mpr (Or.inr ⟨heN, heNotK⟩)
    refine ⟨e, hdiff ▸ heDiff, ?_⟩
    dsimp only [N, K]
    exact Or.inr ⟨he, hkEnd⟩



theorem canonicalMaskTransferOrbitInternallyComplete_of_adjacentWorksPropagates
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hprop : CanonicalMaskAdjacentWorksPropagates
      ends m j k l zero p) :
    CanonicalMaskTransferOrbitInternallyComplete
      ends m j k l zero p := by
  intro r c hrc
  induction hrc with
  | refl => exact canonicalTransferWorks_self hloop hjk hkl hk0 r
  | @tail x y _ hxy ih => exact hprop r x y hxy ih



theorem canonicalMaskTransferOrbitInternallyComplete_of_normalGeometry
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hinvariant : CanonicalMaskAdjacentNormalInvariant
      ends m j k l zero p)
    (hcomplete : CanonicalMaskNormalFiberComplete
      ends m j k l zero p) :
    CanonicalMaskTransferOrbitInternallyComplete
      ends m j k l zero p := by
  intro r c hrc
  apply hcomplete r c
  induction hrc with
  | refl => rfl
  | @tail x y _ hxy ih => exact ih.trans (hinvariant x y hxy)



theorem exists_adjacent_normalRow_ne_of_orbit_normalRow_ne
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (r c : leftMaskFiber ends m j k l zero p)
    (hrc : CanonicalMaskTransferOrbit ends m j k l zero p r c)
    (hne : canonicalNormalRow ends m k zero r.1.1 ≠
      canonicalNormalRow ends m k zero c.1.1) :
    ∃ x y : leftMaskFiber ends m j k l zero p,
      CanonicalMaskTransferOrbit ends m j k l zero p r x ∧
      CanonicalMaskTransferAdjacent ends m j k l zero p x y ∧
      canonicalNormalRow ends m k zero x.1.1 ≠
        canonicalNormalRow ends m k zero y.1.1 := by
  have extract : ∀ {d : leftMaskFiber ends m j k l zero p},
      CanonicalMaskTransferOrbit ends m j k l zero p r d ->
      canonicalNormalRow ends m k zero r.1.1 ≠
        canonicalNormalRow ends m k zero d.1.1 ->
      ∃ x y : leftMaskFiber ends m j k l zero p,
        CanonicalMaskTransferOrbit ends m j k l zero p r x ∧
        CanonicalMaskTransferAdjacent ends m j k l zero p x y ∧
        canonicalNormalRow ends m k zero x.1.1 ≠
          canonicalNormalRow ends m k zero y.1.1 := by
    intro d hrd
    induction hrd with
    | refl => exact fun hne => False.elim (hne rfl)
    | @tail x y hrx hxy ih =>
        intro hne
        by_cases hstep : canonicalNormalRow ends m k zero x.1.1 =
            canonicalNormalRow ends m k zero y.1.1
        · exact ih (fun hrxEq => hne (hrxEq.trans hstep))
        · exact ⟨x, y, hrx, hxy, hstep⟩
  exact extract hrc hne



theorem exists_adjacent_works_failed_of_orbit_failed
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (r c : leftMaskFiber ends m j k l zero p)
    (hself : CanonicalTransferWorks ends m k zero r.1.1 r.1.1)
    (hrc : CanonicalMaskTransferOrbit ends m j k l zero p r c)
    (hbad : ¬ CanonicalTransferWorks ends m k zero r.1.1 c.1.1) :
    ∃ x y : leftMaskFiber ends m j k l zero p,
      CanonicalMaskTransferOrbit ends m j k l zero p r x ∧
      CanonicalMaskTransferAdjacent ends m j k l zero p x y ∧
      CanonicalTransferWorks ends m k zero r.1.1 x.1.1 ∧
      ¬ CanonicalTransferWorks ends m k zero r.1.1 y.1.1 := by
  have extract : ∀ {d : leftMaskFiber ends m j k l zero p},
      CanonicalMaskTransferOrbit ends m j k l zero p r d ->
      ¬ CanonicalTransferWorks ends m k zero r.1.1 d.1.1 ->
      ∃ x y : leftMaskFiber ends m j k l zero p,
        CanonicalMaskTransferOrbit ends m j k l zero p r x ∧
        CanonicalMaskTransferAdjacent ends m j k l zero p x y ∧
        CanonicalTransferWorks ends m k zero r.1.1 x.1.1 ∧
        ¬ CanonicalTransferWorks ends m k zero r.1.1 y.1.1 := by
    intro d hrd
    induction hrd with
    | refl =>
        intro hbad
        exact False.elim (hbad hself)
    | @tail x y hrx hxy ih =>
        intro hbad
        by_cases hx : CanonicalTransferWorks
            ends m k zero r.1.1 x.1.1
        · exact ⟨x, y, hrx, hxy, hx, hbad⟩
        · exact ih hx
  exact extract hrc hbad



theorem canonicalMaskRightHall_of_orbitInternallyComplete
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (hcomplete : CanonicalMaskTransferOrbitInternallyComplete
      ends m j k l zero p) :
    CanonicalMaskRightHall ends m j k l zero p := by
  classical
  let rho := canonicalMaskOrbitMinimumReference ends m j k l zero p
  have hrho : IsCanonicalMaskOrbitSelector ends m j k l zero p rho :=
    canonicalMaskOrbitMinimumReference_selector ends m j k l zero p
  have hworks : ∀ c : leftMaskFiber ends m j k l zero p,
      CanonicalTransferWorks ends m k zero (rho c).1.1 c.1.1 := by
    intro c
    exact hcomplete (rho c) c
      (canonicalMaskTransferOrbit_symm ends m j k l zero p (hrho.1 c))
  let f := canonicalOrbitSelectorMaskFiberEmbedding
    ends m j k l zero hloop hjk hkl p rho hrho hworks
  rw [canonicalMaskRightHall_iff_exists_matching]
  refine ⟨f, ?_⟩
  intro c
  rw [mem_canonicalMaskRightImages_iff]
  exact ⟨rho c, hworks c, rfl⟩



theorem canonicalMaskRightHall_of_adjacentWorksPropagates
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hprop : CanonicalMaskAdjacentWorksPropagates
      ends m j k l zero p) :
    CanonicalMaskRightHall ends m j k l zero p :=
  canonicalMaskRightHall_of_orbitInternallyComplete
    ends m j k l zero hloop hjk hkl p
      (canonicalMaskTransferOrbitInternallyComplete_of_adjacentWorksPropagates
        ends m j k l zero hloop hjk hkl hk0 p hprop)


theorem canonicalMaskRightHall_of_normalGeometry
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (hinvariant : CanonicalMaskAdjacentNormalInvariant
      ends m j k l zero p)
    (hcomplete : CanonicalMaskNormalFiberComplete
      ends m j k l zero p) :
    CanonicalMaskRightHall ends m j k l zero p :=
  canonicalMaskRightHall_of_orbitInternallyComplete
    ends m j k l zero hloop hjk hkl p
      (canonicalMaskTransferOrbitInternallyComplete_of_normalGeometry
        ends m j k l zero p hinvariant hcomplete)


theorem GrahamFiberMinor_of_orbitInternallyComplete
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (hcomplete : ∀ p : Finset I × Finset I,
      CanonicalMaskTransferOrbitInternallyComplete
        ends m j k l zero p) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_canonicalMaskRightHall
  intro p
  exact canonicalMaskRightHall_of_orbitInternallyComplete
    ends m j k l zero hloop hjk hkl p (hcomplete p)


theorem GrahamFiberMinor_of_adjacentWorksPropagates
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hprop : ∀ p : Finset I × Finset I,
      CanonicalMaskAdjacentWorksPropagates
        ends m j k l zero p) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_canonicalMaskRightHall
  intro p
  exact canonicalMaskRightHall_of_adjacentWorksPropagates
    ends m j k l zero hloop hjk hkl hk0 p (hprop p)


theorem GrahamFiberMinor_of_normalGeometry
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (hinvariant : ∀ p : Finset I × Finset I,
      CanonicalMaskAdjacentNormalInvariant
        ends m j k l zero p)
    (hcomplete : ∀ p : Finset I × Finset I,
      CanonicalMaskNormalFiberComplete
        ends m j k l zero p) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_canonicalMaskRightHall
  intro p
  exact canonicalMaskRightHall_of_normalGeometry
    ends m j k l zero hloop hjk hkl p
      (hinvariant p) (hcomplete p)




theorem exists_orbitInternal_rootComponentCut_of_not_canonicalMaskRightHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ r c : leftMaskFiber ends m j k l zero p,
      CanonicalMaskTransferOrbit ends m j k l zero p r c ∧
      ¬ CanonicalTransferWorks ends m k zero r.1.1 c.1.1 ∧
      CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 c.1.1 := by
  obtain ⟨S, a, r, c, -, -, -, -, -, haSorbit, har, -, hcS, -,
      hcNotCoverage, hcut⟩ :=
    exists_maximalOrbitCoverage_rootComponentCut_of_not_canonicalMaskRightHall
      ends m j k l zero hloop hjk hkl hk0 p hfail
  have hrc : CanonicalMaskTransferOrbit ends m j k l zero p r c :=
    (canonicalMaskTransferOrbit_symm ends m j k l zero p har).trans
      (haSorbit c hcS)
  refine ⟨r, c, hrc, ?_, hcut⟩
  intro hworks
  exact hcNotCoverage ((mem_canonicalMaskOrbitCoverage_iff
    ends m j k l zero p r c).mpr ⟨hrc, hworks⟩)




theorem exists_normalGeometry_obstruction_of_not_canonicalMaskRightHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    (∃ x y : leftMaskFiber ends m j k l zero p,
        CanonicalMaskTransferAdjacent ends m j k l zero p x y ∧
        canonicalNormalRow ends m k zero x.1.1 ≠
          canonicalNormalRow ends m k zero y.1.1) ∨
      ∃ r c : leftMaskFiber ends m j k l zero p,
        canonicalNormalRow ends m k zero r.1.1 =
          canonicalNormalRow ends m k zero c.1.1 ∧
        ¬ CanonicalTransferWorks ends m k zero r.1.1 c.1.1 ∧
        CanonicalTranslatedRowRootComponentCut
          ends m k zero r.1.1 c.1.1 := by
  obtain ⟨r, c, hrc, hbad, hcut⟩ :=
    exists_orbitInternal_rootComponentCut_of_not_canonicalMaskRightHall
      ends m j k l zero hloop hjk hkl hk0 p hfail
  by_cases hnormal : canonicalNormalRow ends m k zero r.1.1 =
      canonicalNormalRow ends m k zero c.1.1
  · exact Or.inr ⟨r, c, hnormal, hbad, hcut⟩
  · obtain ⟨x, y, -, hxy, hne⟩ :=
      exists_adjacent_normalRow_ne_of_orbit_normalRow_ne
        ends m j k l zero p r c hrc hnormal
    exact Or.inl ⟨x, y, hxy, hne⟩




theorem exists_adjacent_orbitInternal_rootComponentCut_of_not_canonicalMaskRightHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ r x y : leftMaskFiber ends m j k l zero p,
      CanonicalMaskTransferOrbit ends m j k l zero p r x ∧
      CanonicalMaskTransferAdjacent ends m j k l zero p x y ∧
      CanonicalTransferWorks ends m k zero r.1.1 x.1.1 ∧
      ¬ CanonicalTransferWorks ends m k zero r.1.1 y.1.1 ∧
      CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 y.1.1 := by
  obtain ⟨r, c, hrc, hbad, -⟩ :=
    exists_orbitInternal_rootComponentCut_of_not_canonicalMaskRightHall
      ends m j k l zero hloop hjk hkl hk0 p hfail
  obtain ⟨x, y, hrx, hxy, hx, hy⟩ :=
    exists_adjacent_works_failed_of_orbit_failed
      ends m j k l zero p r c
        (canonicalTransferWorks_self hloop hjk hkl hk0 r) hrc hbad
  exact ⟨r, x, y, hrx, hxy, hx, hy,
    canonicalTransferWorks_failed_rootComponentCut
      hloop hjk hkl r y hy⟩





theorem exists_maximalCoverage_adjacentBoundary_quadrangleDichotomy_of_not_canonicalMaskRightHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ r x y : leftMaskFiber ends m j k l zero p,
      CanonicalMaskOrbitCoverageMaximal ends m j k l zero p r ∧
      CanonicalMaskAdjacentCoverageBoundary ends m j k l zero p r x y ∧
      CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 y.1.1 ∧
      ((∃ d : leftMaskFiber ends m j k l zero p,
          d ∈ canonicalMaskOrbitCoverage ends m j k l zero p r ∧
          d ∉ canonicalMaskOrbitCoverage ends m j k l zero p y) ∨
        (y ∈ canonicalCoverageExclusiveBadQuadrangles
            ends m j k l zero p y r ∧
          ∃ d : leftMaskFiber ends m j k l zero p,
            d ∈ canonicalCoverageExclusiveBadQuadrangles
              ends m j k l zero p r y)) := by
  classical
  obtain ⟨S, a, r, c, -, -, -, -, -, haSorbit, har, hrMax, hcS, -,
      hcNotCoverage, -⟩ :=
    exists_maximalOrbitCoverage_rootComponentCut_of_not_canonicalMaskRightHall
      ends m j k l zero hloop hjk hkl hk0 p hfail
  have hrc : CanonicalMaskTransferOrbit ends m j k l zero p r c :=
    (canonicalMaskTransferOrbit_symm ends m j k l zero p har).trans
      (haSorbit c hcS)
  have hbad : ¬ CanonicalTransferWorks
      ends m k zero r.1.1 c.1.1 := by
    intro hworks
    exact hcNotCoverage ((mem_canonicalMaskOrbitCoverage_iff
      ends m j k l zero p r c).mpr ⟨hrc, hworks⟩)
  obtain ⟨x, y, hrx, hxy, hx, hy⟩ :=
    exists_adjacent_works_failed_of_orbit_failed
      ends m j k l zero p r c
        (canonicalTransferWorks_self hloop hjk hkl hk0 r) hrc hbad
  have hry : CanonicalMaskTransferOrbit ends m j k l zero p r y :=
    hrx.tail hxy
  have hyr : CanonicalMaskTransferOrbit ends m j k l zero p y r :=
    canonicalMaskTransferOrbit_symm ends m j k l zero p hry
  have hrMax' : CanonicalMaskOrbitCoverageMaximal
      ends m j k l zero p r := by
    intro t hrt
    exact hrMax t (har.trans hrt)
  have hyCoverage : y ∈ canonicalMaskOrbitCoverage
      ends m j k l zero p y :=
    (mem_canonicalMaskOrbitCoverage_iff
      ends m j k l zero p y y).mpr ⟨
        canonicalMaskTransferOrbit_refl ends m j k l zero p y,
        canonicalTransferWorks_self hloop hjk hkl hk0 y⟩
  have hyNotCoverage : y ∉ canonicalMaskOrbitCoverage
      ends m j k l zero p r := by
    rw [mem_canonicalMaskOrbitCoverage_iff]
    exact fun h => hy h.2
  refine ⟨r, x, y, hrMax', ⟨hrx, hxy, hx, hy⟩,
    canonicalTransferWorks_failed_rootComponentCut
      hloop hjk hkl r y hy, ?_⟩
  by_cases hdisc : RowsDisconnect ends m
      (canonicalQuadrangleCompletion ends m k zero
        y.1.1 r.1.1 y.1.1) k zero
  · let d := canonicalQuadrangleCompletionMemOfDisconnects
      ends m j k l zero hloop hjk hkl p y r y hdisc
    have hd := quadrangleCompletion_mem_coverage_sdiff
      hloop hjk hkl y r y hyr hyCoverage hyNotCoverage hdisc
    exact Or.inl ⟨d, hd.1, hd.2⟩
  · have hyBad : y ∈ canonicalCoverageExclusiveBadQuadrangles
        ends m j k l zero p y r := by
      rw [mem_canonicalCoverageExclusiveBadQuadrangles_iff]
      exact ⟨hyCoverage, hyNotCoverage, hdisc⟩
    have hcard := hrMax' y hry
    obtain ⟨d, hdBad⟩ :=
      exists_opposite_badQuadrangle_of_coverage_card_le
        hloop hjk hkl y r y hyr hyBad hcard
    exact Or.inr ⟨hyBad, d, hdBad⟩




theorem exists_maximalCoverage_adjacentBoundary_opposingCertificates_of_not_canonicalMaskRightHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ r x y : leftMaskFiber ends m j k l zero p,
      CanonicalMaskOrbitCoverageMaximal ends m j k l zero p r ∧
      CanonicalMaskAdjacentCoverageBoundary ends m j k l zero p r x y ∧
      CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 y.1.1 ∧
      ((∃ d : leftMaskFiber ends m j k l zero p,
          d ∈ canonicalMaskOrbitCoverage ends m j k l zero p r ∧
          d ∉ canonicalMaskOrbitCoverage ends m j k l zero p y) ∨
        ∃ d : leftMaskFiber ends m j k l zero p,
          y ∈ canonicalCoverageExclusiveBadQuadrangles
            ends m j k l zero p y r ∧
          d ∈ canonicalCoverageExclusiveBadQuadrangles
            ends m j k l zero p r y ∧
          CanonicalCoverageExclusiveBoundaryCertificate
            ends m j k l zero p y r y ∧
          CanonicalCoverageExclusiveBoundaryCertificate
            ends m j k l zero p r y d) := by
  obtain ⟨r, x, y, hrMax, hboundary, hcut, hcase⟩ :=
    exists_maximalCoverage_adjacentBoundary_quadrangleDichotomy_of_not_canonicalMaskRightHall
      ends m j k l zero hloop hjk hkl hk0 p hfail
  refine ⟨r, x, y, hrMax, hboundary, hcut, ?_⟩
  rcases hcase with hdiff | ⟨hyBad, d, hdBad⟩
  · exact Or.inl hdiff
  · have hry : CanonicalMaskTransferOrbit ends m j k l zero p r y :=
      hboundary.1.tail hboundary.2.1
    have hyr : CanonicalMaskTransferOrbit ends m j k l zero p y r :=
      canonicalMaskTransferOrbit_symm ends m j k l zero p hry
    exact Or.inr ⟨d, hyBad, hdBad,
      canonicalCoverageExclusiveBadQuadrangle_boundaryCertificate
        hloop hjk hkl y r y hyr hyBad,
      canonicalCoverageExclusiveBadQuadrangle_boundaryCertificate
        hloop hjk hkl r y d hry hdBad⟩





theorem exists_maximalCoverage_adjacentBoundary_oppositeRootCuts_or_twoCommonImages_of_not_canonicalMaskRightHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ r x y : leftMaskFiber ends m j k l zero p,
      CanonicalMaskOrbitCoverageMaximal ends m j k l zero p r ∧
      CanonicalMaskAdjacentCoverageBoundary ends m j k l zero p r x y ∧
      CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 y.1.1 ∧
      ((∃ a b : leftMaskFiber ends m j k l zero p,
          CanonicalTransferWorks ends m k zero a.1.1 x.1.1 ∧
          CanonicalTransferWorks ends m k zero b.1.1 y.1.1 ∧
          canonicalTranslatedRow ends m k zero a.1.1 x.1.1 =
            canonicalTranslatedRow ends m k zero b.1.1 y.1.1 ∧
          ¬ CanonicalTransferWorks ends m k zero b.1.1 x.1.1 ∧
          ¬ CanonicalTransferWorks ends m k zero a.1.1 y.1.1 ∧
          CanonicalTranslatedRowRootComponentCut
            ends m k zero b.1.1 x.1.1 ∧
          CanonicalTranslatedRowRootComponentCut
            ends m k zero a.1.1 y.1.1) ∨
        ∃ q₁ q₂ : rightMaskFiber ends m j k l zero p,
          q₁ ≠ q₂ ∧
          q₁ ∈ canonicalMaskRightImages ends m j k l zero p x ∧
          q₁ ∈ canonicalMaskRightImages ends m j k l zero p y ∧
          q₂ ∈ canonicalMaskRightImages ends m j k l zero p x ∧
          q₂ ∈ canonicalMaskRightImages ends m j k l zero p y) := by
  obtain ⟨r, x, y, hrMax, hboundary, hcut, -⟩ :=
    exists_maximalCoverage_adjacentBoundary_quadrangleDichotomy_of_not_canonicalMaskRightHall
      ends m j k l zero hloop hjk hkl hk0 p hfail
  have hxyne : x ≠ y := by
    intro hxy
    subst y
    exact hboundary.2.2.2 hboundary.2.2.1
  exact ⟨r, x, y, hrMax, hboundary, hcut,
    canonicalMaskTransferAdjacent_oppositeRootCuts_or_twoCommonImages
      hloop hjk hkl x y hxyne hboundary.2.1⟩




theorem exists_rootComponentCut_of_tight_canonicalMaskRightNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (hSne : S.Nonempty)
    (htight : (canonicalMaskRightNeighborhood
      ends m j k l zero p S).card + 1 = S.card) :
    ∃ r ∈ S, ∃ c ∈ S,
      CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 c.1.1 := by
  classical
  obtain ⟨r, hrS⟩ := hSne
  by_cases hworks : ∀ c ∈ S,
      CanonicalTransferWorks ends m k zero r.1.1 c.1.1
  · have hle := card_le_canonicalMaskRightNeighborhood_of_reference
      ends m j k l zero hloop hjk hkl p S r hworks
    omega
  · push Not at hworks
    obtain ⟨c, hcS, hbad⟩ := hworks
    exact ⟨r, hrS, c, hcS,
      canonicalTransferWorks_failed_rootComponentCut
        hloop hjk hkl r c hbad⟩




theorem exists_distinctNormalRows_of_tight_canonicalMaskRightNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (hSne : S.Nonempty)
    (htight : (canonicalMaskRightNeighborhood
      ends m j k l zero p S).card + 1 = S.card) :
    ∃ r ∈ S, ∃ c ∈ S,
      canonicalNormalRow ends m k zero r.1.1 ≠
        canonicalNormalRow ends m k zero c.1.1 := by
  obtain ⟨r, hrS, c, hcS, hcut⟩ :=
    exists_rootComponentCut_of_tight_canonicalMaskRightNeighborhood
      ends m j k l zero hloop hjk hkl p S hSne htight
  exact ⟨r, hrS, c, hcS,
    canonicalNormalRows_ne_of_rootComponentCut
      hloop hjk hkl r c hcut⟩


theorem exists_rootComponentCut_of_not_canonicalMaskRightHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ S : Finset (leftMaskFiber ends m j k l zero p),
      ∃ r ∈ S, ∃ c ∈ S,
        CanonicalTranslatedRowRootComponentCut
          ends m k zero r.1.1 c.1.1 := by
  classical
  obtain ⟨S, hSne, htight, -, -, -, -⟩ :=
    exists_tight_canonicalMaskRightHall_obstruction
      ends m j k l zero hloop hjk hkl hk0 p hfail
  obtain ⟨r, hrS, c, hcS, hcut⟩ :=
    exists_rootComponentCut_of_tight_canonicalMaskRightNeighborhood
      ends m j k l zero hloop hjk hkl p S hSne htight
  exact ⟨S, r, hrS, c, hcS, hcut⟩



theorem canonicalMaskRightHall_of_no_rootComponentCut
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hno : ∀ r c : leftMaskFiber ends m j k l zero p,
      ¬ CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 c.1.1) :
    CanonicalMaskRightHall ends m j k l zero p := by
  by_contra hfail
  obtain ⟨S, r, -, c, -, hcut⟩ :=
    exists_rootComponentCut_of_not_canonicalMaskRightHall
      ends m j k l zero hloop hjk hkl hk0 p hfail
  exact hno r c hcut




def CanonicalMaskRightTightRootCutExcluded
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ S : Finset (leftMaskFiber ends m j k l zero p),
    S.Nonempty ->
    (canonicalMaskRightNeighborhood
      ends m j k l zero p S).card + 1 = S.card ->
    ∀ r ∈ S, ∀ c ∈ S,
      ¬ CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 c.1.1



noncomputable def canonicalMaskRightRestrictedCoverage
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (r : leftMaskFiber ends m j k l zero p) :
    Finset (leftMaskFiber ends m j k l zero p) := by
  classical
  exact S.filter fun c =>
    CanonicalTransferWorks ends m k zero r.1.1 c.1.1

@[simp] theorem mem_canonicalMaskRightRestrictedCoverage_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (r c : leftMaskFiber ends m j k l zero p) :
    c ∈ canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S r ↔
      c ∈ S ∧ CanonicalTransferWorks ends m k zero r.1.1 c.1.1 := by
  classical
  simp [canonicalMaskRightRestrictedCoverage]



theorem canonicalMaskRightRestrictedCoverage_eq_inter_orbitCoverage
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (r : leftMaskFiber ends m j k l zero p)
    (horbit : ∀ d ∈ S,
      CanonicalMaskTransferOrbit ends m j k l zero p r d) :
    canonicalMaskRightRestrictedCoverage ends m j k l zero p S r =
      S ∩ canonicalMaskOrbitCoverage ends m j k l zero p r := by
  classical
  ext d
  simp only [mem_canonicalMaskRightRestrictedCoverage_iff,
    Finset.mem_inter, mem_canonicalMaskOrbitCoverage_iff]
  constructor
  · exact fun hd => ⟨hd.1, horbit d hd.1, hd.2⟩
  · exact fun hd => ⟨hd.1, hd.2.2⟩




def CanonicalMaskRightTightRootCutCoverageMerge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ S : Finset (leftMaskFiber ends m j k l zero p),
    S.Nonempty ->
    (canonicalMaskRightNeighborhood
      ends m j k l zero p S).card + 1 = S.card ->
    ∀ r ∈ S, ∀ c ∈ S,
      CanonicalTranslatedRowRootComponentCut
          ends m k zero r.1.1 c.1.1 ->
        ∃ t ∈ S, ∀ d ∈ S,
          (CanonicalTransferWorks ends m k zero r.1.1 d.1.1 ∨
            CanonicalTransferWorks ends m k zero c.1.1 d.1.1) ->
          CanonicalTransferWorks ends m k zero t.1.1 d.1.1


theorem canonicalMaskRightTightRootCutCoverageMerge_of_excluded
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hno : CanonicalMaskRightTightRootCutExcluded
      ends m j k l zero p) :
    CanonicalMaskRightTightRootCutCoverageMerge
      ends m j k l zero p := by
  intro S hSne htight r hrS c hcS hcut
  exact False.elim (hno S hSne htight r hrS c hcS hcut)





theorem canonicalMaskRightHall_of_tightRootCutCoverageMerge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hmerge : CanonicalMaskRightTightRootCutCoverageMerge
      ends m j k l zero p) :
    CanonicalMaskRightHall ends m j k l zero p := by
  by_contra hfail
  obtain ⟨S, hSne, htight, -, -, -, -⟩ :=
    exists_tight_canonicalMaskRightHall_obstruction
      ends m j k l zero hloop hjk hkl hk0 p hfail
  classical
  obtain ⟨r, hrS, hrMax⟩ := S.exists_max_image
    (fun x => (canonicalMaskRightRestrictedCoverage
      ends m j k l zero p S x).card) hSne
  by_cases hworks : ∀ d ∈ S,
      CanonicalTransferWorks ends m k zero r.1.1 d.1.1
  · have hle := card_le_canonicalMaskRightNeighborhood_of_reference
      ends m j k l zero hloop hjk hkl p S r hworks
    omega
  · push Not at hworks
    obtain ⟨c, hcS, hbad⟩ := hworks
    have hcut := canonicalTransferWorks_failed_rootComponentCut
      hloop hjk hkl r c hbad
    obtain ⟨t, htS, htMerge⟩ :=
      hmerge S hSne htight r hrS c hcS hcut
    have hsub : canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S r ⊆
        canonicalMaskRightRestrictedCoverage
          ends m j k l zero p S t := by
      intro d hd
      rw [mem_canonicalMaskRightRestrictedCoverage_iff] at hd ⊢
      exact ⟨hd.1, htMerge d hd.1 (Or.inl hd.2)⟩
    have hcNot : c ∉ canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S r := by
      rw [mem_canonicalMaskRightRestrictedCoverage_iff]
      exact fun hc => hbad hc.2
    have hcIn : c ∈ canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S t := by
      rw [mem_canonicalMaskRightRestrictedCoverage_iff]
      exact ⟨hcS, htMerge c hcS (Or.inr
        (canonicalTransferWorks_self hloop hjk hkl hk0 c))⟩
    have hins : insert c (canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S r) ⊆
        canonicalMaskRightRestrictedCoverage
          ends m j k l zero p S t := by
      intro d hd
      rw [Finset.mem_insert] at hd
      rcases hd with rfl | hd
      · exact hcIn
      · exact hsub hd
    have hcard := Finset.card_le_card hins
    rw [Finset.card_insert_of_notMem hcNot] at hcard
    have hlt : (canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S r).card <
        (canonicalMaskRightRestrictedCoverage
          ends m j k l zero p S t).card := by
      omega
    exact (Nat.not_lt_of_ge (hrMax t htS)) hlt



theorem canonicalMaskRightHall_of_tightRootCutExcluded
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hno : CanonicalMaskRightTightRootCutExcluded
      ends m j k l zero p) :
    CanonicalMaskRightHall ends m j k l zero p := by
  by_contra hfail
  obtain ⟨S, hSne, htight, -, -, -, -⟩ :=
    exists_tight_canonicalMaskRightHall_obstruction
      ends m j k l zero hloop hjk hkl hk0 p hfail
  obtain ⟨r, hrS, c, hcS, hcut⟩ :=
    exists_rootComponentCut_of_tight_canonicalMaskRightNeighborhood
      ends m j k l zero hloop hjk hkl p S hSne htight
  exact hno S hSne htight r hrS c hcS hcut



theorem GrahamFiberMinor_of_no_canonicalTranslatedRowRootComponentCut
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hno : ∀ (p : Finset I × Finset I)
      (r c : leftMaskFiber ends m j k l zero p),
      ¬ CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 c.1.1) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_canonicalMaskRightHall
  intro p
  classical
  exact canonicalMaskRightHall_of_no_rootComponentCut
    ends m j k l zero hloop hjk hkl hk0 p (hno p)




theorem GrahamFiberMinor_of_tightRootCutCoverageMerge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hmerge : ∀ p : Finset I × Finset I,
      CanonicalMaskRightTightRootCutCoverageMerge
        ends m j k l zero p) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_canonicalMaskRightHall
  intro p
  classical
  exact canonicalMaskRightHall_of_tightRootCutCoverageMerge
    ends m j k l zero hloop hjk hkl hk0 p (hmerge p)




theorem GrahamFiberMinor_of_tightRootCutExcluded
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hno : ∀ p : Finset I × Finset I,
      CanonicalMaskRightTightRootCutExcluded
        ends m j k l zero p) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_canonicalMaskRightHall
  intro p
  classical
  exact canonicalMaskRightHall_of_tightRootCutExcluded
    ends m j k l zero hloop hjk hkl hk0 p (hno p)




theorem exists_canonicalTranslatedRowCycle_obstruction
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ S : Finset (leftMaskFiber ends m j k l zero p),
      (canonicalMaskRightNeighborhood ends m j k l zero p S).card + 1 =
          S.card ∧
        ∃ c d : ↑S, c ≠ d ∧ ∃ σ : Equiv.Perm ↑S,
          σ c = d ∧
            ∀ x : ↑S, ∃ a b : leftMaskFiber ends m j k l zero p,
              RowSupportDisconnects ends m
                  (canonicalTranslatedRow
                    ends m k zero a.1.1 x.1.1.1) k zero ∧
                canonicalTranslatedRow ends m k zero a.1.1 x.1.1.1 =
                  canonicalTranslatedRow
                    ends m k zero b.1.1 (σ x).1.1.1 := by
  classical
  obtain ⟨S, hSne, htight, -, hproper, -, hadj⟩ :=
    exists_tight_canonicalMaskRightHall_obstruction
      ends m j k l zero hloop hjk hkl hk0 p hfail
  obtain ⟨c, hc⟩ := hSne
  obtain ⟨d, hd, hdc, hcd⟩ := hadj c hc
  obtain ⟨σ, hσcd, hσrows⟩ := exists_canonicalTranslatedRowPerm
    ends m j k l zero hloop hjk hkl p S htight hproper c d hc hd hcd
  refine ⟨S, htight, ⟨c, hc⟩, ⟨d, hd⟩, ?_, σ, hσcd, hσrows⟩
  intro h
  apply hdc
  exact (congrArg Subtype.val h).symm





theorem exists_canonicalTransferFoldCycle_obstruction
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ S : Finset (leftMaskFiber ends m j k l zero p),
      ∃ σ : Equiv.Perm ↑S,
        σ ≠ Equiv.refl ↑S ∧
          ∃ a b : ↑S -> leftMaskFiber ends m j k l zero p,
            (∀ x, RowSupportDisconnects ends m
              (canonicalTranslatedRow
                ends m k zero (a x).1.1 x.1.1.1) k zero) ∧
            (∀ x, canonicalTranslatedRow
                ends m k zero (a x).1.1 x.1.1.1 =
              canonicalTranslatedRow
                ends m k zero (b x).1.1 (σ x).1.1.1) ∧
            symmDiffFold Finset.univ (fun x =>
                canonicalTransferUnion ends m k zero (a x).1.1) =
              symmDiffFold Finset.univ (fun x =>
                canonicalTransferUnion ends m k zero (b x).1.1) := by
  classical
  obtain ⟨S, -, c, d, hcd, σ, hσcd, hrows⟩ :=
    exists_canonicalTranslatedRowCycle_obstruction
      ends m j k l zero hloop hjk hkl hk0 p hfail
  obtain ⟨a, b, hdisc, heq, hfold⟩ :=
    exists_referenceTransferFold_eq_of_translatedRowPerm
      ends m j k l zero p S σ hrows
  refine ⟨S, σ, ?_, a, b, hdisc, heq, hfold⟩
  intro hσ
  apply hcd
  rw [hσ] at hσcd
  simpa using hσcd

end StatMech.GrahamGHS.FourColor
