/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamCanonicalTransferOrbitPropagation










open Finset

namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]

private theorem finset_pair_eq_of_union_eq_of_subsets_disjoint
    {A B C D M O : Finset I}
    (hAM : A ⊆ M) (hBO : B ⊆ O)
    (hCM : C ⊆ M) (hDO : D ⊆ O)
    (hMO : Disjoint M O) (hunion : A ∪ B = C ∪ D) :
    A = C ∧ B = D := by
  constructor
  · apply Finset.Subset.antisymm
    · intro i hiA
      have hi : i ∈ C ∪ D := hunion ▸ Finset.mem_union_left B hiA
      rcases Finset.mem_union.mp hi with hiC | hiD
      · exact hiC
      · exact False.elim
          ((Finset.disjoint_left.mp hMO) (hAM hiA) (hDO hiD))
    · intro i hiC
      have hi : i ∈ A ∪ B := hunion.symm ▸ Finset.mem_union_left D hiC
      rcases Finset.mem_union.mp hi with hiA | hiB
      · exact hiA
      · exact False.elim
          ((Finset.disjoint_left.mp hMO) (hCM hiC) (hBO hiB))
  · apply Finset.Subset.antisymm
    · intro i hiB
      have hi : i ∈ C ∪ D := hunion ▸ Finset.mem_union_right A hiB
      rcases Finset.mem_union.mp hi with hiC | hiD
      · exact False.elim
          ((Finset.disjoint_left.mp hMO) (hCM hiC) (hBO hiB))
      · exact hiD
    · intro i hiD
      have hi : i ∈ A ∪ B := hunion.symm ▸ Finset.mem_union_right C hiD
      rcases Finset.mem_union.mp hi with hiA | hiB
      · exact False.elim
          ((Finset.disjoint_left.mp hMO) (hAM hiA) (hDO hiD))
      · exact hiB



theorem canonicalTransfers_eq_of_union_eq_sameMask
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (c d : leftMaskFiber ends m j k l zero p)
    (hunion : canonicalTransferUnion ends m k zero c.1.1 =
      canonicalTransferUnion ends m k zero d.1.1) :
    canonicalMiddleTransfer ends m c.1.1 k zero =
        canonicalMiddleTransfer ends m d.1.1 k zero ∧
      canonicalOuterTransfer ends m c.1.1 k zero =
        canonicalOuterTransfer ends m d.1.1 k zero := by
  have hvc := canonicalTransfers_valid hloop hjk hkl c.1.2
  have hvd := canonicalTransfers_valid hloop hjk hkl d.1.2
  have hprofile :
      fourColorMaskProfile m c.1.1 = fourColorMaskProfile m d.1.1 :=
    c.2.trans d.2.symm
  have hmid : middleMask m c.1.1 = middleMask m d.1.1 :=
    congrArg Prod.fst hprofile
  have hout : outerMask m c.1.1 = outerMask m d.1.1 :=
    congrArg Prod.snd hprofile
  have hcX : canonicalMiddleTransfer ends m c.1.1 k zero ⊆
      middleMask m c.1.1 := by
    simpa only [middleMask] using hvc.1
  have hcY : canonicalOuterTransfer ends m c.1.1 k zero ⊆
      outerMask m c.1.1 := by
    simpa only [outerMask] using hvc.2.1
  have hdX : canonicalMiddleTransfer ends m d.1.1 k zero ⊆
      middleMask m c.1.1 := by
    have hdX' : canonicalMiddleTransfer ends m d.1.1 k zero ⊆
        middleMask m d.1.1 := by
      simpa only [middleMask] using hvd.1
    rwa [← hmid] at hdX'
  have hdY : canonicalOuterTransfer ends m d.1.1 k zero ⊆
      outerMask m c.1.1 := by
    have hdY' : canonicalOuterTransfer ends m d.1.1 k zero ⊆
        outerMask m d.1.1 := by
      simpa only [outerMask] using hvd.2.1
    rwa [← hout] at hdY'
  exact finset_pair_eq_of_union_eq_of_subsets_disjoint
    hcX hcY hdX hdY (middleMask_disjoint_outerMask m c.1.1) hunion



def CanonicalMaskAdjacentComponentNesting
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ r c d : leftMaskFiber ends m j k l zero p,
    CanonicalMaskTransferAdjacent ends m j k l zero p c d ->
    RowsDisconnect ends m
        (balancedSwap m
          (canonicalMiddleTransfer ends m r.1.1 k zero)
          (canonicalOuterTransfer ends m r.1.1 k zero)
          c.1.1) k zero ->
    ¬ RowsDisconnect ends m
        (balancedSwap m
          (canonicalMiddleTransfer ends m r.1.1 k zero)
          (canonicalOuterTransfer ends m r.1.1 k zero)
          d.1.1) k zero ->
      edgeComponent ends (rowClass m d.1.1 0) zero ∪
          edgeComponent ends (rowClass m d.1.1 1) k ⊆
        edgeComponent ends (rowClass m r.1.1 0) zero ∪
          edgeComponent ends (rowClass m r.1.1 1) k


theorem canonicalTransferUnion_subset_of_adjacentComponentNesting
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hnest : CanonicalMaskAdjacentComponentNesting
      ends m j k l zero p)
    (r c d : leftMaskFiber ends m j k l zero p)
    (hcd : CanonicalMaskTransferAdjacent ends m j k l zero p c d)
    (hgood : RowsDisconnect ends m
      (balancedSwap m
        (canonicalMiddleTransfer ends m r.1.1 k zero)
        (canonicalOuterTransfer ends m r.1.1 k zero)
        c.1.1) k zero)
    (hbad : ¬ RowsDisconnect ends m
      (balancedSwap m
        (canonicalMiddleTransfer ends m r.1.1 k zero)
        (canonicalOuterTransfer ends m r.1.1 k zero)
        d.1.1) k zero) :
    canonicalTransferUnion ends m k zero d.1.1 ⊆
      canonicalTransferUnion ends m k zero r.1.1 := by
  rw [canonicalTransferUnion, canonicalTransfers_union,
    canonicalTransferUnion, canonicalTransfers_union]
  exact hnest r c d hcd hgood hbad




theorem canonicalMaskAdjacentStrictDescent_of_componentNesting
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hnest : CanonicalMaskAdjacentComponentNesting
      ends m j k l zero p) :
    CanonicalMaskAdjacentStrictDescent ends m j k l zero p := by
  intro r c d hcd hgood hbad
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨canonicalTransferUnion_subset_of_adjacentComponentNesting
    ends m j k l zero p hnest r c d hcd hgood hbad, ?_⟩
  intro heq
  have hpairs := canonicalTransfers_eq_of_union_eq_sameMask
    hloop hjk hkl d r heq
  apply hbad
  simpa only [hpairs.1, hpairs.2] using
    canonicalBalancedSwap_disconnects hloop hjk hkl hk0 d.1.2


theorem GrahamFiberMinor_of_canonicalMaskAdjacentComponentNesting
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hnest : ∀ p : Finset I × Finset I,
      CanonicalMaskAdjacentComponentNesting ends m j k l zero p) :
    GrahamFiberMinor ends m j k l zero :=
  GrahamFiberMinor_of_canonicalMaskAdjacentStrictDescent
    ends m j k l zero hloop hjk hkl hk0
    (fun p => canonicalMaskAdjacentStrictDescent_of_componentNesting
      ends m j k l zero hloop hjk hkl hk0 p (hnest p))

end StatMech.GrahamGHS.FourColor
