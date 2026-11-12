/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamFourColorAdmissibleRepair












open Finset
open Classical

namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]



noncomputable def canonicalTransferSize (ends : ι -> Sym2 W)
    (m : Finset ι) (k zero : W) (c : ↑m -> Fin 4) : Nat :=
  #(canonicalMiddleTransfer ends m c k zero) +
    #(canonicalOuterTransfer ends m c k zero)

noncomputable def canonicalTransferUnion (ends : ι -> Sym2 W)
    (m : Finset ι) (k zero : W) (c : ↑m -> Fin 4) : Finset ι :=
  canonicalMiddleTransfer ends m c k zero ∪
    canonicalOuterTransfer ends m c k zero

theorem middleMask_disjoint_outerMask (m : Finset ι) (c : ↑m -> Fin 4) :
    Disjoint (middleMask m c) (outerMask m c) := by
  rw [Finset.disjoint_left]
  intro i hiM hiO
  rcases Finset.mem_union.mp hiM with hi1 | hi2 <;>
    rcases Finset.mem_union.mp hiO with hi0 | hi3
  · exact (Finset.disjoint_left.mp
      (colorClass_disjoint m c (show (1 : Fin 4) ≠ 0 by decide))) hi1 hi0
  · exact (Finset.disjoint_left.mp
      (colorClass_disjoint m c (show (1 : Fin 4) ≠ 3 by decide))) hi1 hi3
  · exact (Finset.disjoint_left.mp
      (colorClass_disjoint m c (show (2 : Fin 4) ≠ 0 by decide))) hi2 hi0
  · exact (Finset.disjoint_left.mp
      (colorClass_disjoint m c (show (2 : Fin 4) ≠ 3 by decide))) hi2 hi3

theorem canonicalTransferSize_eq_card_union
    {ends : ι -> Sym2 W} {m : Finset ι} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {c : ↑m -> Fin 4}
    (hc : LeftPattern ends m {j, k} {k, l} k zero c) :
    canonicalTransferSize ends m k zero c =
      #(canonicalTransferUnion ends m k zero c) := by
  have hv := canonicalTransfers_valid hloop hjk hkl hc
  have hdisj : Disjoint
      (canonicalMiddleTransfer ends m c k zero)
      (canonicalOuterTransfer ends m c k zero) :=
    (middleMask_disjoint_outerMask m c).mono hv.1 hv.2.1
  unfold canonicalTransferSize canonicalTransferUnion
  rw [Finset.card_union_of_disjoint hdisj]

private def IsLeftMaskCandidate (ends : ι -> Sym2 W) (m : Finset ι)
    (j k l zero : W) (p : Finset ι × Finset ι)
    (c : ↑m -> Fin 4) : Prop :=
  LeftPattern ends m {j, k} {k, l} k zero c ∧
    fourColorMaskProfile m c = p

private theorem exists_minimal_leftMaskCandidate
    (ends : ι -> Sym2 W) (m : Finset ι) (j k l zero : W)
    (p : Finset ι × Finset ι)
    (h : ∃ c : ↑m -> Fin 4,
      IsLeftMaskCandidate ends m j k l zero p c) :
    ∃ c : ↑m -> Fin 4,
      IsLeftMaskCandidate ends m j k l zero p c ∧
        ∀ d : ↑m -> Fin 4,
          IsLeftMaskCandidate ends m j k l zero p d ->
            canonicalTransferSize ends m k zero c <=
              canonicalTransferSize ends m k zero d := by
  let S : Finset (↑m -> Fin 4) :=
    Finset.univ.filter (IsLeftMaskCandidate ends m j k l zero p)
  obtain ⟨c, hc⟩ := h
  have hcS : c ∈ S := by simp [S, hc]
  obtain ⟨r, hrS, hrmin⟩ := S.exists_min_image
    (canonicalTransferSize ends m k zero) ⟨c, hcS⟩
  have hr : IsLeftMaskCandidate ends m j k l zero p r := by
    simpa [S] using hrS
  refine ⟨r, hr, ?_⟩
  intro d hd
  apply hrmin d
  simp [S, hd]




noncomputable def leftMaskReference (ends : ι -> Sym2 W) (m : Finset ι)
    (j k l zero : W) (p : Finset ι × Finset ι) : ↑m -> Fin 4 :=
  if h : ∃ c : ↑m -> Fin 4,
      IsLeftMaskCandidate ends m j k l zero p c then
    Classical.choose
      (exists_minimal_leftMaskCandidate ends m j k l zero p h)
  else
    fun _ => 0

theorem leftMaskReference_spec
    (ends : ι -> Sym2 W) (m : Finset ι) (j k l zero : W)
    (p : Finset ι × Finset ι)
    (h : ∃ c : ↑m -> Fin 4,
      LeftPattern ends m {j, k} {k, l} k zero c ∧
        fourColorMaskProfile m c = p) :
    LeftPattern ends m {j, k} {k, l} k zero
        (leftMaskReference ends m j k l zero p) ∧
      fourColorMaskProfile m (leftMaskReference ends m j k l zero p) = p := by
  have h' : ∃ c : ↑m -> Fin 4,
      IsLeftMaskCandidate ends m j k l zero p c := h
  rw [leftMaskReference, dif_pos h']
  exact (Classical.choose_spec
    (exists_minimal_leftMaskCandidate ends m j k l zero p h')).1

theorem leftMaskReference_minimal
    (ends : ι -> Sym2 W) (m : Finset ι) (j k l zero : W)
    (p : Finset ι × Finset ι)
    (h : ∃ c : ↑m -> Fin 4,
      LeftPattern ends m {j, k} {k, l} k zero c ∧
        fourColorMaskProfile m c = p)
    (d : ↑m -> Fin 4)
    (hd : LeftPattern ends m {j, k} {k, l} k zero d)
    (hdp : fourColorMaskProfile m d = p) :
    canonicalTransferSize ends m k zero
        (leftMaskReference ends m j k l zero p) <=
      canonicalTransferSize ends m k zero d := by
  have h' : ∃ c : ↑m -> Fin 4,
      IsLeftMaskCandidate ends m j k l zero p c := h
  rw [leftMaskReference, dif_pos h']
  exact (Classical.choose_spec
    (exists_minimal_leftMaskCandidate ends m j k l zero p h')).2 d ⟨hd, hdp⟩

@[simp] theorem fourColorMaskProfile_balancedSwap
    (m X Y : Finset ι) (c : ↑m -> Fin 4) :
    fourColorMaskProfile m (balancedSwap m X Y c) =
      fourColorMaskProfile m c := by
  simp [fourColorMaskProfile, middleMask_balancedSwap,
    outerMask_balancedSwap]



noncomputable def uniformMaskCanonicalSelector
    (ends : ι -> Sym2 W) (m : Finset ι) (j k l zero : W)
    (c : ↑m -> Fin 4) : Finset ι × Finset ι :=
  let r := leftMaskReference ends m j k l zero
    (fourColorMaskProfile m c)
  (canonicalMiddleTransfer ends m r k zero,
    canonicalOuterTransfer ends m r k zero)

@[simp] theorem uniformMaskCanonicalSelector_balancedSwap
    (ends : ι -> Sym2 W) (m X Y : Finset ι) (j k l zero : W)
    (c : ↑m -> Fin 4) :
    uniformMaskCanonicalSelector ends m j k l zero
        (balancedSwap m X Y c) =
      uniformMaskCanonicalSelector ends m j k l zero c := by
  simp [uniformMaskCanonicalSelector]




theorem uniformMaskCanonicalSelector_valid_sources
    {ends : ι -> Sym2 W} {m : Finset ι} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {c : ↑m -> Fin 4}
    (hc : LeftPattern ends m {j, k} {k, l} k zero c) :
    let s := uniformMaskCanonicalSelector ends m j k l zero c
    s.1 ⊆ colorClass m c 1 ∪ colorClass m c 2 ∧
      s.2 ⊆ colorClass m c 0 ∪ colorClass m c 3 ∧
      sources ends s.1 = {k, l} ∧
      sources ends s.2 = ∅ := by
  let p := fourColorMaskProfile m c
  let r := leftMaskReference ends m j k l zero p
  have hex : ∃ d : ↑m -> Fin 4,
      LeftPattern ends m {j, k} {k, l} k zero d ∧
        fourColorMaskProfile m d = p := ⟨c, hc, rfl⟩
  have hr := leftMaskReference_spec ends m j k l zero p hex
  have hv := canonicalTransfers_valid hloop hjk hkl hr.1
  have hprofile : fourColorMaskProfile m r = fourColorMaskProfile m c := by
    exact hr.2
  have hmid : middleMask m r = middleMask m c :=
    congrArg Prod.fst hprofile
  have hout : outerMask m r = outerMask m c :=
    congrArg Prod.snd hprofile
  have hX : canonicalMiddleTransfer ends m r k zero ⊆
      colorClass m c 1 ∪ colorClass m c 2 := by
    have : canonicalMiddleTransfer ends m r k zero ⊆ middleMask m r := by
      simpa only [middleMask] using hv.1
    rw [hmid] at this
    simpa only [middleMask] using this
  have hY : canonicalOuterTransfer ends m r k zero ⊆
      colorClass m c 0 ∪ colorClass m c 3 := by
    have : canonicalOuterTransfer ends m r k zero ⊆ outerMask m r := by
      simpa only [outerMask] using hv.2.1
    rw [hout] at this
    simpa only [outerMask] using this
  change
    (uniformMaskCanonicalSelector ends m j k l zero c).1 ⊆
        colorClass m c 1 ∪ colorClass m c 2 ∧
      (uniformMaskCanonicalSelector ends m j k l zero c).2 ⊆
        colorClass m c 0 ∪ colorClass m c 3 ∧
      sources ends
          (uniformMaskCanonicalSelector ends m j k l zero c).1 = {k, l} ∧
      sources ends
          (uniformMaskCanonicalSelector ends m j k l zero c).2 = ∅
  simpa only [uniformMaskCanonicalSelector, p, r] using
    And.intro hX (And.intro hY (And.intro hv.2.2.1 hv.2.2.2))



theorem GrahamFiberMinor_of_uniformMaskCanonicalTransfer
    (ends : ι -> Sym2 W) (m : Finset ι) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (hdisconnect : ∀ c : ↑m -> Fin 4,
      LeftPattern ends m {j, k} {k, l} k zero c ->
        let s := uniformMaskCanonicalSelector ends m j k l zero c
        RowsDisconnect ends m (balancedSwap m s.1 s.2 c) k zero) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_balancedSelector ends m j k l zero
    (uniformMaskCanonicalSelector ends m j k l zero)
  · intro c hc
    have hv := uniformMaskCanonicalSelector_valid_sources
      hloop hjk hkl hc
    exact ⟨hv.1, hv.2.1, hv.2.2.1, hv.2.2.2, hdisconnect c hc⟩
  · intro c
    exact uniformMaskCanonicalSelector_balancedSwap
      ends m _ _ j k l zero c





theorem GrahamFiberMinor_of_canonicalTransferDescent
    (ends : ι -> Sym2 W) (m : Finset ι) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (hdescent : ∀ c d : ↑m -> Fin 4,
      LeftPattern ends m {j, k} {k, l} k zero c ->
      LeftPattern ends m {j, k} {k, l} k zero d ->
      fourColorMaskProfile m c = fourColorMaskProfile m d ->
      ¬ RowsDisconnect ends m
          (balancedSwap m
            (canonicalMiddleTransfer ends m c k zero)
            (canonicalOuterTransfer ends m c k zero) d) k zero ->
      canonicalTransferSize ends m k zero d <
        canonicalTransferSize ends m k zero c) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_uniformMaskCanonicalTransfer
    ends m j k l zero hloop hjk hkl
  intro d hd
  let p := fourColorMaskProfile m d
  let r := leftMaskReference ends m j k l zero p
  have hex : ∃ c : ↑m -> Fin 4,
      LeftPattern ends m {j, k} {k, l} k zero c ∧
        fourColorMaskProfile m c = p := ⟨d, hd, rfl⟩
  have hr := leftMaskReference_spec ends m j k l zero p hex
  have hmin := leftMaskReference_minimal ends m j k l zero p
    hex d hd rfl
  change RowsDisconnect ends m
    (balancedSwap m
      (canonicalMiddleTransfer ends m r k zero)
      (canonicalOuterTransfer ends m r k zero) d) k zero
  by_contra hbad
  have hlt := hdescent r d hr.1 hd (by simpa [p] using hr.2) hbad
  exact (not_lt_of_ge hmin) hlt




theorem GrahamFiberMinor_of_canonicalTransferStrictSubset
    (ends : ι -> Sym2 W) (m : Finset ι) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (hproper : ∀ c d : ↑m -> Fin 4,
      LeftPattern ends m {j, k} {k, l} k zero c ->
      LeftPattern ends m {j, k} {k, l} k zero d ->
      fourColorMaskProfile m c = fourColorMaskProfile m d ->
      ¬ RowsDisconnect ends m
          (balancedSwap m
            (canonicalMiddleTransfer ends m c k zero)
            (canonicalOuterTransfer ends m c k zero) d) k zero ->
      canonicalTransferUnion ends m k zero d ⊂
        canonicalTransferUnion ends m k zero c) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_canonicalTransferDescent
    ends m j k l zero hloop hjk hkl
  intro c d hc hd hprofile hbad
  rw [canonicalTransferSize_eq_card_union hloop hjk hkl hc,
    canonicalTransferSize_eq_card_union hloop hjk hkl hd]
  exact Finset.card_lt_card (hproper c d hc hd hprofile hbad)

end StatMech.GrahamGHS.FourColor
