/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamCanonicalTransferOrbit











open Finset

namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def CanonicalMaskAdjacentStrictDescent
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
      canonicalTransferUnion ends m k zero d.1.1 ⊂
        canonicalTransferUnion ends m k zero r.1.1



theorem canonicalMaskOrbitMinimumReference_disconnects_of_adjacentStrictDescent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hlocal : CanonicalMaskAdjacentStrictDescent
      ends m j k l zero p)
    (d : leftMaskFiber ends m j k l zero p) :
    RowsDisconnect ends m
      (balancedSwap m
        (canonicalMiddleTransfer ends m
          (canonicalMaskOrbitMinimumReference
            ends m j k l zero p d).1.1 k zero)
        (canonicalOuterTransfer ends m
          (canonicalMaskOrbitMinimumReference
            ends m j k l zero p d).1.1 k zero)
        d.1.1) k zero := by
  let r := canonicalMaskOrbitMinimumReference ends m j k l zero p d
  have hdr : CanonicalMaskTransferOrbit ends m j k l zero p d r :=
    canonicalMaskOrbitMinimumReference_mem ends m j k l zero p d
  have hrd : CanonicalMaskTransferOrbit ends m j k l zero p r d :=
    canonicalMaskTransferOrbit_symm ends m j k l zero p hdr
  have propagate : ∀ e : leftMaskFiber ends m j k l zero p,
      CanonicalMaskTransferOrbit ends m j k l zero p r e ->
        RowsDisconnect ends m
          (balancedSwap m
            (canonicalMiddleTransfer ends m r.1.1 k zero)
            (canonicalOuterTransfer ends m r.1.1 k zero)
            e.1.1) k zero := by
    intro e hre
    induction hre with
    | refl =>
        exact canonicalBalancedSwap_disconnects
          hloop hjk hkl hk0 r.1.2
    | @tail c e hrc hce ih =>
        by_contra hbad
        have hproper := hlocal r c e hce ih hbad
        have hlt : canonicalTransferSize ends m k zero e.1.1 <
            canonicalTransferSize ends m k zero r.1.1 := by
          rw [canonicalTransferSize_eq_card_union hloop hjk hkl e.1.2,
            canonicalTransferSize_eq_card_union hloop hjk hkl r.1.2]
          exact Finset.card_lt_card hproper
        have hde : CanonicalMaskTransferOrbit ends m j k l zero p d e :=
          hdr.trans (hrc.tail hce)
        have hle : canonicalTransferSize ends m k zero r.1.1 ≤
            canonicalTransferSize ends m k zero e.1.1 := by
          simpa only [r] using canonicalMaskOrbitMinimumReference_size_le
            ends m j k l zero p d e hde
        exact (not_lt_of_ge hle) hlt
  exact propagate d hrd



noncomputable def canonicalMaskAdjacentDescentEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hlocal : CanonicalMaskAdjacentStrictDescent
      ends m j k l zero p) :
    leftMaskFiber ends m j k l zero p ↪
      rightMaskFiber ends m j k l zero p :=
  canonicalOrbitSelectorMaskFiberEmbedding
    ends m j k l zero hloop hjk hkl p
    (canonicalMaskOrbitMinimumReference ends m j k l zero p)
    (canonicalMaskOrbitMinimumReference_selector ends m j k l zero p)
    (canonicalMaskOrbitMinimumReference_disconnects_of_adjacentStrictDescent
      ends m j k l zero hloop hjk hkl hk0 p hlocal)


theorem GrahamFiberMinor_of_canonicalMaskAdjacentStrictDescent
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hlocal : ∀ p : Finset I × Finset I,
      CanonicalMaskAdjacentStrictDescent ends m j k l zero p) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_maskwise
  intro p
  exact Fintype.card_le_of_injective
    (canonicalMaskAdjacentDescentEmbedding
      ends m j k l zero hloop hjk hkl hk0 p (hlocal p))
    (canonicalMaskAdjacentDescentEmbedding
      ends m j k l zero hloop hjk hkl hk0 p (hlocal p)).injective

end StatMech.GrahamGHS.FourColor
