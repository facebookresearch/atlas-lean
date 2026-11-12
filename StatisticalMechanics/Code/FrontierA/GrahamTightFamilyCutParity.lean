/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamTightFamilyRootCollision
import Code.FrontierA.GrahamCanonicalCollisionSquare










open Finset
open scoped symmDiff

namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def CanonicalRowSupportRootComponentCut
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (K : Finset I) : Prop :=
  (StatMech.Sharpness.RandomCurrent.connK ends K k zero ∧
      edgeComponent ends K zero = edgeComponent ends K k) ∨
    (StatMech.Sharpness.RandomCurrent.connK ends (m \ K) k zero ∧
      edgeComponent ends (m \ K) zero = edgeComponent ends (m \ K) k)


def canonicalCollisionOppositeRow
    (m : Finset I) (q c d : ↑m -> Fin 4) : Finset I :=
  rowClass m q 0 ∆ rowClass m c 0 ∆ rowClass m d 0



theorem canonicalCollisionOppositeRow_consecutive_symmDiff
    (m : Finset I) (q r c d e : ↑m -> Fin 4) :
    canonicalCollisionOppositeRow m q c d ∆
        canonicalCollisionOppositeRow m r d e =
      rowClass m q 0 ∆ rowClass m r 0 ∆
        rowClass m c 0 ∆ rowClass m e 0 := by
  unfold canonicalCollisionOppositeRow
  calc
    (rowClass m q 0 ∆ rowClass m c 0 ∆ rowClass m d 0) ∆
          (rowClass m r 0 ∆ rowClass m d 0 ∆ rowClass m e 0) =
        (rowClass m d 0 ∆ rowClass m d 0) ∆
          (rowClass m q 0 ∆ rowClass m r 0 ∆
            rowClass m c 0 ∆ rowClass m e 0) := by ac_rfl
    _ = _ := by simp



theorem sources_consecutive_canonicalCollisionOppositeRows
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (q r : rightMaskFiber ends m j k l zero p)
    (c d e : leftMaskFiber ends m j k l zero p) :
    StatMech.Sharpness.RandomCurrent.sources ends
        (canonicalCollisionOppositeRow m q.1.1 c.1.1 d.1.1 ∆
          canonicalCollisionOppositeRow m r.1.1 d.1.1 e.1.1) = ∅ := by
  rw [canonicalCollisionOppositeRow_consecutive_symmDiff,
    StatMech.Sharpness.RandomCurrent.sources_symmDiff,
    StatMech.Sharpness.RandomCurrent.sources_symmDiff,
    StatMech.Sharpness.RandomCurrent.sources_symmDiff]
  rw [(rightPattern_rowBoundaries q.1.2).1,
    (rightPattern_rowBoundaries r.1.2).1,
    (leftPattern_rowBoundaries c.1.2).1,
    (leftPattern_rowBoundaries e.1.2).1]
  simp




abbrev CanonicalOpposingRootCutsAtRight
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p)
    (q : rightMaskFiber ends m j k l zero p) : Prop :=
  ∃ a b : leftMaskFiber ends m j k l zero p,
    CanonicalTransferWorks ends m k zero a.1.1 c.1.1 ∧
    CanonicalTransferWorks ends m k zero b.1.1 d.1.1 ∧
    q.1.1 = balancedSwap m
      (canonicalMiddleTransfer ends m a.1.1 k zero)
      (canonicalOuterTransfer ends m a.1.1 k zero) c.1.1 ∧
    q.1.1 = balancedSwap m
      (canonicalMiddleTransfer ends m b.1.1 k zero)
      (canonicalOuterTransfer ends m b.1.1 k zero) d.1.1 ∧
    ¬ CanonicalTransferWorks ends m k zero b.1.1 c.1.1 ∧
    ¬ CanonicalTransferWorks ends m k zero a.1.1 d.1.1 ∧
    CanonicalTranslatedRowRootComponentCut
      ends m k zero b.1.1 c.1.1 ∧
    CanonicalTranslatedRowRootComponentCut
      ends m k zero a.1.1 d.1.1

set_option maxHeartbeats 1000000 in




theorem canonicalOpposingRootCutsAtRight_crossTranslatedRows
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (c d : leftMaskFiber ends m j k l zero p)
    (q : rightMaskFiber ends m j k l zero p)
    (hcuts : CanonicalOpposingRootCutsAtRight
      ends m j k l zero p c d q) :
    ∃ a b : leftMaskFiber ends m j k l zero p,
      canonicalCollisionOppositeRow m q.1.1 c.1.1 d.1.1 =
          canonicalTranslatedRow ends m k zero b.1.1 c.1.1 ∧
      canonicalCollisionOppositeRow m q.1.1 c.1.1 d.1.1 =
          canonicalTranslatedRow ends m k zero a.1.1 d.1.1 ∧
      CanonicalTranslatedRowRootComponentCut
          ends m k zero b.1.1 c.1.1 ∧
      CanonicalTranslatedRowRootComponentCut
          ends m k zero a.1.1 d.1.1 := by
  obtain ⟨a, b, hac, hbd, hqa, hqb, -, -, hcutbc, hcutad⟩ := hcuts
  have hqrowa : rowClass m q.1.1 0 =
      canonicalTranslatedRow ends m k zero a.1.1 c.1.1 := by
    rw [hqa]
    have hv := canonicalTransfers_valid_on_sameMask hloop hjk hkl a c
    rw [rowClass_balancedSwap_zero hv.1 hv.2.1]
    rfl
  have hqrowb : rowClass m q.1.1 0 =
      canonicalTranslatedRow ends m k zero b.1.1 d.1.1 := by
    rw [hqb]
    have hv := canonicalTransfers_valid_on_sameMask hloop hjk hkl b d
    rw [rowClass_balancedSwap_zero hv.1 hv.2.1]
    rfl
  have htrans : canonicalTranslatedRow ends m k zero a.1.1 c.1.1 =
      canonicalTranslatedRow ends m k zero b.1.1 d.1.1 :=
    hqrowa.symm.trans hqrowb
  have hopp := canonicalTranslatedRow_opposite_eq_of_eq
    ends m k zero a.1.1 b.1.1 c.1.1 d.1.1 htrans
  have hexp : canonicalTranslatedRow ends m k zero b.1.1 c.1.1 =
      canonicalCollisionOppositeRow m q.1.1 c.1.1 d.1.1 := by
    rw [hopp, canonicalCollisionOppositeRow, hqrowa]
    unfold canonicalTranslatedRow
    calc
      rowClass m d.1.1 0 ∆ canonicalTransferUnion ends m k zero a.1.1 =
          canonicalTransferUnion ends m k zero a.1.1 ∆
            rowClass m d.1.1 0 := symmDiff_comm _ _
      _ = (rowClass m c.1.1 0 ∆ rowClass m c.1.1 0) ∆
            canonicalTransferUnion ends m k zero a.1.1 ∆
              rowClass m d.1.1 0 := by
        rw [symmDiff_self, bot_symmDiff]
      _ = (rowClass m c.1.1 0 ∆
            canonicalTransferUnion ends m k zero a.1.1) ∆
          rowClass m c.1.1 0 ∆ rowClass m d.1.1 0 := by ac_rfl
  exact ⟨a, b, hexp.symm, hexp.symm.trans hopp, hcutbc, hcutad⟩

set_option maxHeartbeats 1000000 in



theorem canonicalCommonImage_opposingAtRight_or_twoCommon
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (c d : leftMaskFiber ends m j k l zero p) (hcd : c ≠ d)
    (q : rightMaskFiber ends m j k l zero p)
    (hqc : q ∈ canonicalMaskRightImages ends m j k l zero p c)
    (hqd : q ∈ canonicalMaskRightImages ends m j k l zero p d) :
    CanonicalOpposingRootCutsAtRight
        ends m j k l zero p c d q ∨
      CanonicalTightTwoRowCollision ends m j k l zero p c d := by
  obtain ⟨a, hac, hqa⟩ := (mem_canonicalMaskRightImages_iff
    ends m j k l zero p c q).mp hqc
  obtain ⟨b, hbd, hqb⟩ := (mem_canonicalMaskRightImages_iff
    ends m j k l zero p d q).mp hqd
  have hqrowa : rowClass m q.1.1 0 =
      canonicalTranslatedRow ends m k zero a.1.1 c.1.1 := by
    rw [hqa]
    have hv := canonicalTransfers_valid_on_sameMask hloop hjk hkl a c
    rw [rowClass_balancedSwap_zero hv.1 hv.2.1]
    rfl
  have hqrowb : rowClass m q.1.1 0 =
      canonicalTranslatedRow ends m k zero b.1.1 d.1.1 := by
    rw [hqb]
    have hv := canonicalTransfers_valid_on_sameMask hloop hjk hkl b d
    rw [rowClass_balancedSwap_zero hv.1 hv.2.1]
    rfl
  have htrans : canonicalTranslatedRow ends m k zero a.1.1 c.1.1 =
      canonicalTranslatedRow ends m k zero b.1.1 d.1.1 :=
    hqrowa.symm.trans hqrowb
  have hopp := canonicalTransferWorks_opposite_iff_of_translatedRow_eq
    hloop hjk hkl a b c d htrans
  by_cases hbc : CanonicalTransferWorks ends m k zero b.1.1 c.1.1
  · exact Or.inr
      (exists_two_common_canonicalMaskRightImages_of_collisionSquare
        hloop hjk hkl a b c d hcd hac htrans hbc)
  · have had : ¬ CanonicalTransferWorks
        ends m k zero a.1.1 d.1.1 := fun had => hbc (hopp.mpr had)
    exact Or.inl ⟨a, b, hac, hbd, hqa, hqb, hbc, had,
      canonicalTransferWorks_failed_rootComponentCut
        hloop hjk hkl b c hbc,
      canonicalTransferWorks_failed_rootComponentCut
        hloop hjk hkl a d had⟩

set_option maxHeartbeats 1000000 in




theorem canonicalSelfImage_owner_rootComponentCut_or_works_twoCommon
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    {p : Finset I × Finset I}
    (c d : leftMaskFiber ends m j k l zero p) (hcd : c ≠ d)
    (howner : canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p c c
          (canonicalTransferWorks_self hloop hjk hkl hk0 c) ∈
      canonicalMaskRightImages ends m j k l zero p d) :
    CanonicalTranslatedRowRootComponentCut
        ends m k zero c.1.1 d.1.1 ∨
      (CanonicalTransferWorks ends m k zero c.1.1 d.1.1 ∧
        CanonicalTightTwoRowCollision ends m j k l zero p c d) := by
  let q := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p c c
      (canonicalTransferWorks_self hloop hjk hkl hk0 c)
  obtain ⟨b, hbd, hqb⟩ := (mem_canonicalMaskRightImages_iff
    ends m j k l zero p d q).mp howner
  have hqrowc : rowClass m q.1.1 0 =
      canonicalTranslatedRow ends m k zero c.1.1 c.1.1 :=
    rowClass_zero_canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p c c
        (canonicalTransferWorks_self hloop hjk hkl hk0 c)
  have hqrowb : rowClass m q.1.1 0 =
      canonicalTranslatedRow ends m k zero b.1.1 d.1.1 := by
    rw [hqb]
    have hv := canonicalTransfers_valid_on_sameMask hloop hjk hkl b d
    rw [rowClass_balancedSwap_zero hv.1 hv.2.1]
    rfl
  have htrans : canonicalTranslatedRow ends m k zero c.1.1 c.1.1 =
      canonicalTranslatedRow ends m k zero b.1.1 d.1.1 :=
    hqrowc.symm.trans hqrowb
  have hopp := canonicalTransferWorks_opposite_iff_of_translatedRow_eq
    hloop hjk hkl c b c d htrans
  by_cases hbc : CanonicalTransferWorks ends m k zero b.1.1 c.1.1
  · exact Or.inr ⟨hopp.mp hbc,
      exists_two_common_canonicalMaskRightImages_of_collisionSquare
        hloop hjk hkl c b c d hcd
          (canonicalTransferWorks_self hloop hjk hkl hk0 c)
          htrans hbc⟩
  · have hcdBad : ¬ CanonicalTransferWorks
        ends m k zero c.1.1 d.1.1 := fun hcdWorks =>
      hbc (hopp.mpr hcdWorks)
    exact Or.inl (canonicalTransferWorks_failed_rootComponentCut
      hloop hjk hkl c d hcdBad)



theorem canonicalSelfImage_owner_rootComponentCut_or_twoCommon
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    {p : Finset I × Finset I}
    (c d : leftMaskFiber ends m j k l zero p) (hcd : c ≠ d)
    (howner : canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p c c
          (canonicalTransferWorks_self hloop hjk hkl hk0 c) ∈
      canonicalMaskRightImages ends m j k l zero p d) :
    CanonicalTranslatedRowRootComponentCut
        ends m k zero c.1.1 d.1.1 ∨
      CanonicalTightTwoRowCollision ends m j k l zero p c d := by
  rcases canonicalSelfImage_owner_rootComponentCut_or_works_twoCommon
      hloop hjk hkl hk0 c d hcd howner with hcut | ⟨-, hsquare⟩
  · exact Or.inl hcut
  · exact Or.inr hsquare

set_option maxHeartbeats 1000000 in




theorem canonicalReferenceImage_owner_rootComponentCut_or_works_twoCommon
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r c d : leftMaskFiber ends m j k l zero p)
    (hrc : CanonicalTransferWorks ends m k zero r.1.1 c.1.1)
    (hcd : c ≠ d)
    (howner : canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p r c hrc ∈
      canonicalMaskRightImages ends m j k l zero p d) :
    CanonicalTranslatedRowRootComponentCut
        ends m k zero r.1.1 d.1.1 ∨
      (CanonicalTransferWorks ends m k zero r.1.1 d.1.1 ∧
        CanonicalTightTwoRowCollision ends m j k l zero p c d) := by
  let q := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p r c hrc
  obtain ⟨b, hbd, hqb⟩ := (mem_canonicalMaskRightImages_iff
    ends m j k l zero p d q).mp howner
  have hqrowr : rowClass m q.1.1 0 =
      canonicalTranslatedRow ends m k zero r.1.1 c.1.1 :=
    rowClass_zero_canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p r c hrc
  have hqrowb : rowClass m q.1.1 0 =
      canonicalTranslatedRow ends m k zero b.1.1 d.1.1 := by
    rw [hqb]
    have hv := canonicalTransfers_valid_on_sameMask hloop hjk hkl b d
    rw [rowClass_balancedSwap_zero hv.1 hv.2.1]
    rfl
  have htrans : canonicalTranslatedRow ends m k zero r.1.1 c.1.1 =
      canonicalTranslatedRow ends m k zero b.1.1 d.1.1 :=
    hqrowr.symm.trans hqrowb
  have hopp := canonicalTransferWorks_opposite_iff_of_translatedRow_eq
    hloop hjk hkl r b c d htrans
  by_cases hbc : CanonicalTransferWorks ends m k zero b.1.1 c.1.1
  · exact Or.inr ⟨hopp.mp hbc,
      exists_two_common_canonicalMaskRightImages_of_collisionSquare
        hloop hjk hkl r b c d hcd hrc htrans hbc⟩
  · have hrdBad : ¬ CanonicalTransferWorks
        ends m k zero r.1.1 d.1.1 := fun hrd => hbc (hopp.mpr hrd)
    exact Or.inl (canonicalTransferWorks_failed_rootComponentCut
      hloop hjk hkl r d hrdBad)





theorem tightFamily_referenceImage_internalCut_or_coverageGrowth
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (r c : leftMaskFiber ends m j k l zero p)
    (hrS : r ∈ S) (hcS : c ∈ S)
    (herase : canonicalMaskRightNeighborhood
        ends m j k l zero p (S.erase c) =
      canonicalMaskRightNeighborhood ends m j k l zero p S)
    (hrc : CanonicalTransferWorks ends m k zero r.1.1 c.1.1) :
    ∃ d ∈ S, d ≠ c ∧
      (CanonicalTranslatedRowRootComponentCut
          ends m k zero r.1.1 d.1.1 ∨
        (CanonicalTransferWorks ends m k zero r.1.1 d.1.1 ∧
          CanonicalTightTwoRowCollision ends m j k l zero p c d)) := by
  have _hrS : r ∈ S := hrS
  let q := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p r c hrc
  have hqc : q ∈ canonicalMaskRightImages
      ends m j k l zero p c :=
    (mem_canonicalMaskRightImages_iff
      ends m j k l zero p c q).mpr ⟨r, hrc, rfl⟩
  obtain ⟨d, hdS, hdc, hqd⟩ :=
    exists_other_of_erase_canonicalMaskRightNeighborhood_eq
      ends m j k l zero p S c hcS herase q hqc
  exact ⟨d, hdS, hdc,
    canonicalReferenceImage_owner_rootComponentCut_or_works_twoCommon
      hloop hjk hkl r c d hrc hdc.symm hqd⟩




theorem tightFamily_referenceCoverageGrowth_of_no_internalCut
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (r c : leftMaskFiber ends m j k l zero p)
    (hrS : r ∈ S) (hcS : c ∈ S)
    (herase : canonicalMaskRightNeighborhood
        ends m j k l zero p (S.erase c) =
      canonicalMaskRightNeighborhood ends m j k l zero p S)
    (hrc : CanonicalTransferWorks ends m k zero r.1.1 c.1.1)
    (hno : ∀ a ∈ S, ∀ b ∈ S,
      ¬ CanonicalTranslatedRowRootComponentCut
        ends m k zero a.1.1 b.1.1) :
    ∃ d ∈ S, d ≠ c ∧
      CanonicalTransferWorks ends m k zero r.1.1 d.1.1 ∧
      CanonicalTightTwoRowCollision ends m j k l zero p c d := by
  obtain ⟨d, hdS, hdc, hcut | hgrow⟩ :=
    tightFamily_referenceImage_internalCut_or_coverageGrowth
      ends m j k l zero hloop hjk hkl p S r c hrS hcS herase hrc
  · exact False.elim (hno r hrS d hdS hcut)
  · exact ⟨d, hdS, hdc, hgrow⟩




theorem tightFamily_selfImage_internalCut_or_twoCommon
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : leftMaskFiber ends m j k l zero p) (hc : c ∈ S)
    (herase : canonicalMaskRightNeighborhood
        ends m j k l zero p (S.erase c) =
      canonicalMaskRightNeighborhood ends m j k l zero p S) :
    ∃ d ∈ S, d ≠ c ∧
      (CanonicalTranslatedRowRootComponentCut
          ends m k zero c.1.1 d.1.1 ∨
        CanonicalTightTwoRowCollision ends m j k l zero p c d) := by
  let q := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p c c
      (canonicalTransferWorks_self hloop hjk hkl hk0 c)
  have hqc : q ∈ canonicalMaskRightImages
      ends m j k l zero p c :=
    (mem_canonicalMaskRightImages_iff
      ends m j k l zero p c q).mpr ⟨c,
        canonicalTransferWorks_self hloop hjk hkl hk0 c, rfl⟩
  obtain ⟨d, hdS, hdc, hqd⟩ :=
    exists_other_of_erase_canonicalMaskRightNeighborhood_eq
      ends m j k l zero p S c hc herase q hqc
  exact ⟨d, hdS, hdc,
    canonicalSelfImage_owner_rootComponentCut_or_twoCommon
      hloop hjk hkl hk0 c d hdc.symm hqd⟩

set_option maxHeartbeats 1000000 in




theorem exists_tightFamily_allSelfImage_internalCut_or_twoCommon_of_not_hall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ S : Finset (leftMaskFiber ends m j k l zero p),
      S.Nonempty ∧
      (canonicalMaskRightNeighborhood
          ends m j k l zero p S).card + 1 = S.card ∧
      ∀ c ∈ S, ∃ d ∈ S, d ≠ c ∧
        (CanonicalTranslatedRowRootComponentCut
            ends m k zero c.1.1 d.1.1 ∨
          CanonicalTightTwoRowCollision ends m j k l zero p c d) := by
  obtain ⟨S, hSne, htight, herase, -, -, -⟩ :=
    exists_tight_canonicalMaskRightHall_obstruction
      ends m j k l zero hloop hjk hkl hk0 p hfail
  refine ⟨S, hSne, htight, ?_⟩
  intro c hc
  exact tightFamily_selfImage_internalCut_or_twoCommon
    ends m j k l zero hloop hjk hkl hk0 p S c hc (herase c hc)



def CanonicalMaskRightTightRootCutCoverageComparable
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ S : Finset (leftMaskFiber ends m j k l zero p),
    S.Nonempty ->
    (canonicalMaskRightNeighborhood
      ends m j k l zero p S).card + 1 = S.card ->
    ∀ r ∈ S, ∀ c ∈ S,
      CanonicalTranslatedRowRootComponentCut
          ends m k zero r.1.1 c.1.1 ->
        canonicalMaskRightRestrictedCoverage
            ends m j k l zero p S r ⊆
              canonicalMaskRightRestrictedCoverage
                ends m j k l zero p S c ∨
          canonicalMaskRightRestrictedCoverage
              ends m j k l zero p S c ⊆
                canonicalMaskRightRestrictedCoverage
                  ends m j k l zero p S r



theorem canonicalMaskRightTightRootCutCoverageMerge_of_comparable
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hcomp : CanonicalMaskRightTightRootCutCoverageComparable
      ends m j k l zero p) :
    CanonicalMaskRightTightRootCutCoverageMerge
      ends m j k l zero p := by
  intro S hSne htight r hrS c hcS hcut
  rcases hcomp S hSne htight r hrS c hcS hcut with hrc | hcr
  · refine ⟨c, hcS, ?_⟩
    intro d hdS hworks
    rcases hworks with hrd | hcd
    · have hd := hrc ((mem_canonicalMaskRightRestrictedCoverage_iff
          ends m j k l zero p S r d).mpr ⟨hdS, hrd⟩)
      exact ((mem_canonicalMaskRightRestrictedCoverage_iff
        ends m j k l zero p S c d).mp hd).2
    · exact hcd
  · refine ⟨r, hrS, ?_⟩
    intro d hdS hworks
    rcases hworks with hrd | hcd
    · exact hrd
    · have hd := hcr ((mem_canonicalMaskRightRestrictedCoverage_iff
          ends m j k l zero p S c d).mpr ⟨hdS, hcd⟩)
      exact ((mem_canonicalMaskRightRestrictedCoverage_iff
        ends m j k l zero p S r d).mp hd).2



theorem canonicalMaskRightHall_of_tightRootCutCoverageComparable
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hcomp : CanonicalMaskRightTightRootCutCoverageComparable
      ends m j k l zero p) :
    CanonicalMaskRightHall ends m j k l zero p :=
  canonicalMaskRightHall_of_tightRootCutCoverageMerge
    ends m j k l zero hloop hjk hkl hk0 p
      (canonicalMaskRightTightRootCutCoverageMerge_of_comparable
        ends m j k l zero p hcomp)



def CanonicalMaskRightTightRootCutIncomparableThirdMerge
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ S : Finset (leftMaskFiber ends m j k l zero p),
    S.Nonempty ->
    (canonicalMaskRightNeighborhood
      ends m j k l zero p S).card + 1 = S.card ->
    ∀ r ∈ S, ∀ c ∈ S,
      CanonicalTranslatedRowRootComponentCut
          ends m k zero r.1.1 c.1.1 ->
      ¬ canonicalMaskRightRestrictedCoverage
          ends m j k l zero p S r ⊆
        canonicalMaskRightRestrictedCoverage
          ends m j k l zero p S c ->
      ¬ canonicalMaskRightRestrictedCoverage
          ends m j k l zero p S c ⊆
        canonicalMaskRightRestrictedCoverage
          ends m j k l zero p S r ->
      ∃ t ∈ S, ∀ d ∈ S,
        (CanonicalTransferWorks ends m k zero r.1.1 d.1.1 ∨
          CanonicalTransferWorks ends m k zero c.1.1 d.1.1) ->
        CanonicalTransferWorks ends m k zero t.1.1 d.1.1



theorem canonicalMaskRightTightRootCutCoverageMerge_of_incomparableThird
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hthird : CanonicalMaskRightTightRootCutIncomparableThirdMerge
      ends m j k l zero p) :
    CanonicalMaskRightTightRootCutCoverageMerge
      ends m j k l zero p := by
  intro S hSne htight r hrS c hcS hcut
  by_cases hrc : canonicalMaskRightRestrictedCoverage
      ends m j k l zero p S r ⊆
        canonicalMaskRightRestrictedCoverage ends m j k l zero p S c
  · refine ⟨c, hcS, ?_⟩
    intro d hdS hworks
    rcases hworks with hrd | hcd
    · have hd := hrc ((mem_canonicalMaskRightRestrictedCoverage_iff
          ends m j k l zero p S r d).mpr ⟨hdS, hrd⟩)
      exact ((mem_canonicalMaskRightRestrictedCoverage_iff
        ends m j k l zero p S c d).mp hd).2
    · exact hcd
  · by_cases hcr : canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S c ⊆
          canonicalMaskRightRestrictedCoverage ends m j k l zero p S r
    · refine ⟨r, hrS, ?_⟩
      intro d hdS hworks
      rcases hworks with hrd | hcd
      · exact hrd
      · have hd := hcr ((mem_canonicalMaskRightRestrictedCoverage_iff
            ends m j k l zero p S c d).mpr ⟨hdS, hcd⟩)
        exact ((mem_canonicalMaskRightRestrictedCoverage_iff
          ends m j k l zero p S r d).mp hd).2
    · exact hthird S hSne htight r hrS c hcS hcut hrc hcr



theorem canonicalMaskRightHall_of_tightRootCutIncomparableThird
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hthird : CanonicalMaskRightTightRootCutIncomparableThirdMerge
      ends m j k l zero p) :
    CanonicalMaskRightHall ends m j k l zero p :=
  canonicalMaskRightHall_of_tightRootCutCoverageMerge
    ends m j k l zero hloop hjk hkl hk0 p
      (canonicalMaskRightTightRootCutCoverageMerge_of_incomparableThird
        ends m j k l zero p hthird)




theorem exists_restrictedCoverage_exclusiveWitnesses_of_incomparable
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (r c : leftMaskFiber ends m j k l zero p)
    (hrc : ¬ canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S r ⊆
      canonicalMaskRightRestrictedCoverage ends m j k l zero p S c)
    (hcr : ¬ canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S c ⊆
      canonicalMaskRightRestrictedCoverage ends m j k l zero p S r) :
    (∃ d ∈ S,
      CanonicalTransferWorks ends m k zero r.1.1 d.1.1 ∧
      ¬ CanonicalTransferWorks ends m k zero c.1.1 d.1.1) ∧
    ∃ e ∈ S,
      CanonicalTransferWorks ends m k zero c.1.1 e.1.1 ∧
      ¬ CanonicalTransferWorks ends m k zero r.1.1 e.1.1 := by
  obtain ⟨d, hdR, hdC⟩ := Finset.not_subset.mp hrc
  obtain ⟨e, heC, heR⟩ := Finset.not_subset.mp hcr
  have hdR' := (mem_canonicalMaskRightRestrictedCoverage_iff
    ends m j k l zero p S r d).mp hdR
  have heC' := (mem_canonicalMaskRightRestrictedCoverage_iff
    ends m j k l zero p S c e).mp heC
  refine ⟨⟨d, hdR'.1, hdR'.2, ?_⟩, ⟨e, heC'.1, heC'.2, ?_⟩⟩
  · intro hcd
    exact hdC ((mem_canonicalMaskRightRestrictedCoverage_iff
      ends m j k l zero p S c d).mpr ⟨hdR'.1, hcd⟩)
  · intro hre
    exact heR ((mem_canonicalMaskRightRestrictedCoverage_iff
      ends m j k l zero p S r e).mpr ⟨heC'.1, hre⟩)

set_option maxHeartbeats 1000000 in





theorem restrictedExclusiveWitness_quadrangleExchange_or_badCertificate
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r c d : leftMaskFiber ends m j k l zero p)
    (hrcOrbit : CanonicalMaskTransferOrbit ends m j k l zero p r c)
    (hrdOrbit : CanonicalMaskTransferOrbit ends m j k l zero p r d)
    (hrd : CanonicalTransferWorks ends m k zero r.1.1 d.1.1)
    (hcd : ¬ CanonicalTransferWorks ends m k zero c.1.1 d.1.1) :
    (∃ t : leftMaskFiber ends m j k l zero p,
      t ∈ canonicalMaskOrbitCoverage ends m j k l zero p c ∧
      t ∉ canonicalMaskOrbitCoverage ends m j k l zero p r) ∨
      (d ∈ canonicalCoverageExclusiveBadQuadrangles
          ends m j k l zero p r c ∧
        CanonicalCoverageExclusiveBoundaryCertificate
          ends m j k l zero p r c d) := by
  have hdR : d ∈ canonicalMaskOrbitCoverage
      ends m j k l zero p r :=
    (mem_canonicalMaskOrbitCoverage_iff
      ends m j k l zero p r d).mpr ⟨hrdOrbit, hrd⟩
  have hdNotC : d ∉ canonicalMaskOrbitCoverage
      ends m j k l zero p c := by
    intro hdC
    exact hcd ((mem_canonicalMaskOrbitCoverage_iff
      ends m j k l zero p c d).mp hdC).2
  by_cases hdisc : RowsDisconnect ends m
      (canonicalQuadrangleCompletion ends m k zero
        r.1.1 c.1.1 d.1.1) k zero
  · let t := canonicalQuadrangleCompletionMemOfDisconnects
      ends m j k l zero hloop hjk hkl p r c d hdisc
    have ht := quadrangleCompletion_mem_coverage_sdiff
      hloop hjk hkl r c d hrcOrbit hdR hdNotC hdisc
    exact Or.inl ⟨t, ht.1, ht.2⟩
  · have hdBad : d ∈ canonicalCoverageExclusiveBadQuadrangles
        ends m j k l zero p r c := by
      rw [mem_canonicalCoverageExclusiveBadQuadrangles_iff]
      exact ⟨hdR, hdNotC, hdisc⟩
    exact Or.inr ⟨hdBad,
      canonicalCoverageExclusiveBadQuadrangle_boundaryCertificate
        hloop hjk hkl r c d hrcOrbit hdBad⟩





theorem canonicalCoverageExclusiveBoundaryCertificate_zeroRootNormalized
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p)
    (hcert : CanonicalCoverageExclusiveBoundaryCertificate
      ends m j k l zero p a b c) :
    let d := canonicalQuadrangleCompletion ends m k zero
      a.1.1 b.1.1 c.1.1
    ((StatMech.Sharpness.RandomCurrent.connK
          ends (rowClass m d 0) k zero ∧
        StatMech.Sharpness.RandomCurrent.sources
          ends (edgeComponent ends (rowClass m d 0) zero) = {j, k} ∧
        StatMech.Sharpness.RandomCurrent.sources ends (rowClass m d 0 \
          edgeComponent ends (rowClass m d 0) zero) = ∅ ∧
        Disjoint (canonicalTransferUnion ends m k zero d)
          (rowClass m d 0 \ edgeComponent ends (rowClass m d 0) zero)) ∨
      (StatMech.Sharpness.RandomCurrent.connK
          ends (rowClass m d 1) k zero ∧
        StatMech.Sharpness.RandomCurrent.sources
          ends (edgeComponent ends (rowClass m d 1) zero) = {k, l} ∧
        StatMech.Sharpness.RandomCurrent.sources ends (rowClass m d 1 \
          edgeComponent ends (rowClass m d 1) zero) = ∅ ∧
        Disjoint (canonicalTransferUnion ends m k zero d)
          (rowClass m d 1 \ edgeComponent ends (rowClass m d 1) zero))) := by
  dsimp only
  rcases hcert with hzero | hone
  · exact Or.inl hzero
  · right
    have heq : edgeComponent ends
        (rowClass m
          (canonicalQuadrangleCompletion ends m k zero
            a.1.1 b.1.1 c.1.1) 1) k =
      edgeComponent ends
        (rowClass m
          (canonicalQuadrangleCompletion ends m k zero
            a.1.1 b.1.1 c.1.1) 1) zero :=
      edgeComponent_eq_of_conn ends _ k zero hone.1
    rw [← heq]
    exact hone



theorem canonicalCoverageExclusiveBoundaryCertificate_component_ne_complement
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p)
    (hcert : CanonicalCoverageExclusiveBoundaryCertificate
      ends m j k l zero p a b c) :
    let d := canonicalQuadrangleCompletion ends m k zero
      a.1.1 b.1.1 c.1.1
    ((StatMech.Sharpness.RandomCurrent.connK
          ends (rowClass m d 0) k zero ∧
        edgeComponent ends (rowClass m d 0) zero ≠
          rowClass m d 0 \ edgeComponent ends (rowClass m d 0) zero) ∨
      (StatMech.Sharpness.RandomCurrent.connK
          ends (rowClass m d 1) k zero ∧
        edgeComponent ends (rowClass m d 1) zero ≠
          rowClass m d 1 \ edgeComponent ends (rowClass m d 1) zero)) := by
  dsimp only
  rcases canonicalCoverageExclusiveBoundaryCertificate_zeroRootNormalized
      a b c hcert with hzero | hone
  · left
    refine ⟨hzero.1, ?_⟩
    intro heq
    have hs := congrArg (StatMech.Sharpness.RandomCurrent.sources ends) heq
    rw [hzero.2.1, hzero.2.2.1] at hs
    have hj : j ∈ ({j, k} : Finset W) := by simp
    rw [hs] at hj
    simp at hj
  · right
    refine ⟨hone.1, ?_⟩
    intro heq
    have hs := congrArg (StatMech.Sharpness.RandomCurrent.sources ends) heq
    rw [hone.2.1, hone.2.2.1] at hs
    have hk : k ∈ ({k, l} : Finset W) := by simp
    rw [hs] at hk
    simp at hk



def CanonicalCoverageNormalizedBoundaryRow
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (d : ↑m -> Fin 4) (rho : Fin 2) : Prop :=
  StatMech.Sharpness.RandomCurrent.connK
      ends (rowClass m d rho) k zero ∧
    StatMech.Sharpness.RandomCurrent.sources
        ends (edgeComponent ends (rowClass m d rho) zero) =
      (if rho = 0 then ({j, k} : Finset W) else ({k, l} : Finset W)) ∧
    StatMech.Sharpness.RandomCurrent.sources ends
        (rowClass m d rho \ edgeComponent ends (rowClass m d rho) zero) = ∅ ∧
    Disjoint (canonicalTransferUnion ends m k zero d)
      (rowClass m d rho \ edgeComponent ends (rowClass m d rho) zero)


theorem exists_normalizedBoundaryRow_of_exclusiveBoundaryCertificate
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    {p : Finset I × Finset I}
    (a b c : leftMaskFiber ends m j k l zero p)
    (hcert : CanonicalCoverageExclusiveBoundaryCertificate
      ends m j k l zero p a b c) :
    ∃ rho : Fin 2, CanonicalCoverageNormalizedBoundaryRow
      ends m j k l zero
        (canonicalQuadrangleCompletion ends m k zero
          a.1.1 b.1.1 c.1.1) rho := by
  rcases canonicalCoverageExclusiveBoundaryCertificate_zeroRootNormalized
      a b c hcert with hzero | hone
  · exact ⟨0, by simpa [CanonicalCoverageNormalizedBoundaryRow] using hzero⟩
  · exact ⟨1, by simpa [CanonicalCoverageNormalizedBoundaryRow] using hone⟩



theorem normalizedBoundaryRow_component_ne_other_complement
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (d e : ↑m -> Fin 4) (rho sigma : Fin 2)
    (hd : CanonicalCoverageNormalizedBoundaryRow
      ends m j k l zero d rho)
    (he : CanonicalCoverageNormalizedBoundaryRow
      ends m j k l zero e sigma) :
    edgeComponent ends (rowClass m d rho) zero ≠
      rowClass m e sigma \
        edgeComponent ends (rowClass m e sigma) zero := by
  intro heq
  have hs := congrArg (StatMech.Sharpness.RandomCurrent.sources ends) heq
  rw [hd.2.1, he.2.2.1] at hs
  fin_cases rho <;> simp at hs





theorem opposingQuadrangle_rowClass_eq_iff
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c d : leftMaskFiber ends m j k l zero p) (rho : Fin 2) :
    rowClass m
        (canonicalQuadrangleCompletion ends m k zero
          a.1.1 b.1.1 c.1.1) rho =
        rowClass m
          (canonicalQuadrangleCompletion ends m k zero
            b.1.1 a.1.1 d.1.1) rho ↔
      rowClass m c.1.1 rho = rowClass m d.1.1 rho := by
  rw [rowClass_canonicalQuadrangleCompletion hloop hjk hkl a b c rho,
    rowClass_canonicalQuadrangleCompletion hloop hjk hkl b a d rho]
  have hreorder :
      rowClass m d.1.1 rho ∆
          canonicalTransferUnion ends m k zero b.1.1 ∆
          canonicalTransferUnion ends m k zero a.1.1 =
        rowClass m d.1.1 rho ∆
          canonicalTransferUnion ends m k zero a.1.1 ∆
          canonicalTransferUnion ends m k zero b.1.1 := by
    ac_rfl
  rw [hreorder, symmDiff_left_inj, symmDiff_left_inj]





theorem opposingExclusiveBadQuadrangles_rowZero_ne
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r y d : leftMaskFiber ends m j k l zero p)
    (hy : y ∈ canonicalCoverageExclusiveBadQuadrangles
      ends m j k l zero p y r)
    (hd : d ∈ canonicalCoverageExclusiveBadQuadrangles
      ends m j k l zero p r y) :
    rowClass m
        (canonicalQuadrangleCompletion ends m k zero
          y.1.1 r.1.1 y.1.1) 0 ≠
      rowClass m
        (canonicalQuadrangleCompletion ends m k zero
          r.1.1 y.1.1 d.1.1) 0 := by
  have hy' := (mem_canonicalCoverageExclusiveBadQuadrangles_iff
    ends m j k l zero p y r y).mp hy
  have hd' := (mem_canonicalCoverageExclusiveBadQuadrangles_iff
    ends m j k l zero p r y d).mp hd
  intro hrow
  have hydRow : rowClass m y.1.1 0 = rowClass m d.1.1 0 :=
    (opposingQuadrangle_rowClass_eq_iff
      hloop hjk hkl y r y d 0).mp hrow
  have hyd : y = d := leftMaskFiber_rowClass_zero_injective
    ends m j k l zero p hydRow
  subst d
  exact hy'.2.1 hd'.1

set_option maxHeartbeats 1000000 in





theorem incomparableRestrictedCoverage_controlledOwnerDichotomies
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (herase : ∀ x ∈ S, canonicalMaskRightNeighborhood
        ends m j k l zero p (S.erase x) =
      canonicalMaskRightNeighborhood ends m j k l zero p S)
    (r c : leftMaskFiber ends m j k l zero p)
    (hrS : r ∈ S) (hcS : c ∈ S)
    (hrc : ¬ canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S r ⊆
      canonicalMaskRightRestrictedCoverage ends m j k l zero p S c)
    (hcr : ¬ canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S c ⊆
      canonicalMaskRightRestrictedCoverage ends m j k l zero p S r) :
    ∃ d ∈ S, ∃ e ∈ S,
      CanonicalTransferWorks ends m k zero r.1.1 d.1.1 ∧
      ¬ CanonicalTransferWorks ends m k zero c.1.1 d.1.1 ∧
      CanonicalTransferWorks ends m k zero c.1.1 e.1.1 ∧
      ¬ CanonicalTransferWorks ends m k zero r.1.1 e.1.1 ∧
      (∃ u ∈ S, u ≠ d ∧
        (CanonicalTranslatedRowRootComponentCut
            ends m k zero r.1.1 u.1.1 ∨
          (CanonicalTransferWorks ends m k zero r.1.1 u.1.1 ∧
            CanonicalTightTwoRowCollision ends m j k l zero p d u))) ∧
      ∃ v ∈ S, v ≠ e ∧
        (CanonicalTranslatedRowRootComponentCut
            ends m k zero c.1.1 v.1.1 ∨
          (CanonicalTransferWorks ends m k zero c.1.1 v.1.1 ∧
            CanonicalTightTwoRowCollision ends m j k l zero p e v)) := by
  obtain ⟨⟨d, hdS, hrd, hcd⟩, ⟨e, heS, hce, hre⟩⟩ :=
    exists_restrictedCoverage_exclusiveWitnesses_of_incomparable
      ends m j k l zero p S r c hrc hcr
  obtain ⟨u, huS, hud, hu⟩ :=
    tightFamily_referenceImage_internalCut_or_coverageGrowth
      ends m j k l zero hloop hjk hkl p S r d hrS hdS
        (herase d hdS) hrd
  obtain ⟨v, hvS, hve, hv⟩ :=
    tightFamily_referenceImage_internalCut_or_coverageGrowth
      ends m j k l zero hloop hjk hkl p S c e hcS heS
        (herase e heS) hce
  exact ⟨d, hdS, e, heS, hrd, hcd, hce, hre,
    ⟨u, huS, hud, hu⟩, v, hvS, hve, hv⟩

set_option maxHeartbeats 1000000 in





theorem exists_tightFamily_incomparableRootCut_of_not_hall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ S : Finset (leftMaskFiber ends m j k l zero p),
      S.Nonempty ∧
      (canonicalMaskRightNeighborhood
          ends m j k l zero p S).card + 1 = S.card ∧
      (∀ x ∈ S, canonicalMaskRightNeighborhood
          ends m j k l zero p (S.erase x) =
        canonicalMaskRightNeighborhood ends m j k l zero p S) ∧
      (∀ x ∈ S, ∀ y ∈ S,
        CanonicalMaskTransferOrbit ends m j k l zero p x y) ∧
      ∃ r ∈ S, ∃ c ∈ S,
        CanonicalTranslatedRowRootComponentCut
            ends m k zero r.1.1 c.1.1 ∧
        ¬ canonicalMaskRightRestrictedCoverage
            ends m j k l zero p S r ⊆
          canonicalMaskRightRestrictedCoverage
            ends m j k l zero p S c ∧
        ¬ canonicalMaskRightRestrictedCoverage
            ends m j k l zero p S c ⊆
          canonicalMaskRightRestrictedCoverage
            ends m j k l zero p S r := by
  classical
  obtain ⟨S, hSne, htight, herase, -, horbit, -⟩ :=
    exists_tight_canonicalMaskRightHall_obstruction
      ends m j k l zero hloop hjk hkl hk0 p hfail
  obtain ⟨r, hrS, hrMax⟩ := S.exists_max_image
    (fun x => (canonicalMaskRightRestrictedCoverage
      ends m j k l zero p S x).card) hSne
  by_cases hworks : ∀ d ∈ S,
      CanonicalTransferWorks ends m k zero r.1.1 d.1.1
  · have hle := card_le_canonicalMaskRightNeighborhood_of_reference
      ends m j k l zero hloop hjk hkl p S r hworks
    omega
  · push Not at hworks
    obtain ⟨c, hcS, hrcBad⟩ := hworks
    have hcut := canonicalTransferWorks_failed_rootComponentCut
      hloop hjk hkl r c hrcBad
    have hcNotR : c ∉ canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S r := by
      rw [mem_canonicalMaskRightRestrictedCoverage_iff]
      exact fun hc => hrcBad hc.2
    have hcInC : c ∈ canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S c := by
      rw [mem_canonicalMaskRightRestrictedCoverage_iff]
      exact ⟨hcS, canonicalTransferWorks_self hloop hjk hkl hk0 c⟩
    have hCR : ¬ canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S c ⊆
      canonicalMaskRightRestrictedCoverage ends m j k l zero p S r :=
      fun hsub => hcNotR (hsub hcInC)
    have hRC : ¬ canonicalMaskRightRestrictedCoverage
        ends m j k l zero p S r ⊆
      canonicalMaskRightRestrictedCoverage ends m j k l zero p S c := by
      intro hsub
      have hins : insert c (canonicalMaskRightRestrictedCoverage
          ends m j k l zero p S r) ⊆
          canonicalMaskRightRestrictedCoverage
            ends m j k l zero p S c := by
        intro d hd
        rw [Finset.mem_insert] at hd
        rcases hd with rfl | hd
        · exact hcInC
        · exact hsub hd
      have hcard := Finset.card_le_card hins
      rw [Finset.card_insert_of_notMem hcNotR] at hcard
      have hmax := hrMax c hcS
      omega
    exact ⟨S, hSne, htight, herase, horbit,
      r, hrS, c, hcS, hcut, hRC, hCR⟩



theorem exists_secondCommonImage_iff_canonicalTightTwoRowCollision
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p)
    (q : rightMaskFiber ends m j k l zero p)
    (hqc : q ∈ canonicalMaskRightImages ends m j k l zero p c)
    (hqd : q ∈ canonicalMaskRightImages ends m j k l zero p d) :
    (∃ r : rightMaskFiber ends m j k l zero p,
        r ≠ q ∧
        r ∈ canonicalMaskRightImages ends m j k l zero p c ∧
        r ∈ canonicalMaskRightImages ends m j k l zero p d) ↔
      CanonicalTightTwoRowCollision ends m j k l zero p c d := by
  constructor
  · rintro ⟨r, hrq, hrc, hrd⟩
    exact ⟨q, r, hrq.symm, hqc, hqd, hrc, hrd⟩
  · rintro ⟨q1, q2, hq12, hq1c, hq1d, hq2c, hq2d⟩
    by_cases hq1q : q1 = q
    · refine ⟨q2, ?_, hq2c, hq2d⟩
      intro hq2q
      exact hq12 (hq1q.trans hq2q.symm)
    · exact ⟨q1, hq1q, hq1c, hq1d⟩



theorem common_canonicalMaskRightImage_eq_of_not_twoRowCollision
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p)
    (hno : ¬ CanonicalTightTwoRowCollision ends m j k l zero p c d)
    (q r : rightMaskFiber ends m j k l zero p)
    (hqc : q ∈ canonicalMaskRightImages ends m j k l zero p c)
    (hqd : q ∈ canonicalMaskRightImages ends m j k l zero p d)
    (hrc : r ∈ canonicalMaskRightImages ends m j k l zero p c)
    (hrd : r ∈ canonicalMaskRightImages ends m j k l zero p d) :
    r = q := by
  by_contra hrq
  exact hno ((exists_secondCommonImage_iff_canonicalTightTwoRowCollision
    ends m j k l zero p c d q hqc hqd).mp ⟨r, hrq, hrc, hrd⟩)

set_option maxHeartbeats 1000000 in





theorem canonicalMaskRightAugmentedRootCollision_opposingAtRight_or_reroute
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType
      ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f)
    (q : ↑(canonicalMaskRightNeighborhood ends m j k l zero p S))
    (hqc : q.1 ∈ canonicalMaskRightImages
      ends m j k l zero p c.1) :
    (∃ d : ↑S, d ≠ c ∧ f d = some q ∧
      CanonicalOpposingRootCutsAtRight
        ends m j k l zero p c.1 d.1 q.1) ∨
      ∃ e : ↑S, e ≠ c ∧
        ∃ g : canonicalMaskRightAugmentedEquivType
            ends m j k l zero p S,
          CanonicalMaskRightAugmentedMatching
            ends m j k l zero p S e g := by
  classical
  let d : ↑S := f.symm (some q)
  have hfd : f d = some q := by simp [d]
  have hdc : d ≠ c := by
    intro h
    have hnone : f d = none := (congrArg f h).trans hf.1
    rw [hnone] at hfd
    cases hfd
  obtain ⟨s, hfs, hsd⟩ := hf.2 d hdc
  have hsq : s = q := Option.some.inj (hfs.symm.trans hfd)
  have hqd : q.1 ∈ canonicalMaskRightImages
      ends m j k l zero p d.1 := by
    simpa only [hsq] using hsd
  have hcd : c.1 ≠ d.1 := by
    intro h
    exact hdc (Subtype.ext h.symm)
  rcases canonicalCommonImage_opposingAtRight_or_twoCommon
      hloop hjk hkl c.1 d.1 hcd q.1 hqc hqd with hcuts | hsquare
  · exact Or.inl ⟨d, hdc, hfd, hcuts⟩
  · obtain ⟨r, hrq, hrc, hrd⟩ :=
      (exists_secondCommonImage_iff_canonicalTightTwoRowCollision
        ends m j k l zero p c.1 d.1 q.1 hqc hqd).mpr hsquare
    have hrS : r ∈ canonicalMaskRightNeighborhood
        ends m j k l zero p S :=
      (mem_canonicalMaskRightNeighborhood_iff
        ends m j k l zero p S r).mpr ⟨c.1, c.2, hrc⟩
    let rS : ↑(canonicalMaskRightNeighborhood
        ends m j k l zero p S) := ⟨r, hrS⟩
    have hqrS : q ≠ rS := by
      intro h
      exact hrq (congrArg Subtype.val h).symm
    obtain ⟨e, hec, -, -, g, hg⟩ :=
      canonicalMaskRightAugmentedMatching_rotateAssignedSecondRow
        ends m j k l zero p S c d hdc f hf q rS hfd hqrS hqc hrd
    exact Or.inr ⟨e, hec, g, hg⟩

set_option maxHeartbeats 1000000 in




theorem canonicalMaskRightAugmentedSelfImage_internalCut_or_reroute
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (c : ↑S)
    (f : canonicalMaskRightAugmentedEquivType
      ends m j k l zero p S)
    (hf : CanonicalMaskRightAugmentedMatching
      ends m j k l zero p S c f) :
    (∃ d : ↑S, d ≠ c ∧
      CanonicalTranslatedRowRootComponentCut
        ends m k zero c.1.1.1 d.1.1.1) ∨
      ∃ e : ↑S, e ≠ c ∧
        ∃ g : canonicalMaskRightAugmentedEquivType
            ends m j k l zero p S,
          CanonicalMaskRightAugmentedMatching
            ends m j k l zero p S e g := by
  classical
  let q0 := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p c.1 c.1
      (canonicalTransferWorks_self hloop hjk hkl hk0 c.1)
  have hq0c : q0 ∈ canonicalMaskRightImages
      ends m j k l zero p c.1 :=
    (mem_canonicalMaskRightImages_iff
      ends m j k l zero p c.1 q0).mpr ⟨c.1,
        canonicalTransferWorks_self hloop hjk hkl hk0 c.1, rfl⟩
  have hq0N : q0 ∈ canonicalMaskRightNeighborhood
      ends m j k l zero p S :=
    (mem_canonicalMaskRightNeighborhood_iff
      ends m j k l zero p S q0).mpr ⟨c.1, c.2, hq0c⟩
  let q : ↑(canonicalMaskRightNeighborhood
      ends m j k l zero p S) := ⟨q0, hq0N⟩
  let d : ↑S := f.symm (some q)
  have hfd : f d = some q := by simp [d]
  have hdc : d ≠ c := by
    intro h
    have hnone : f d = none := (congrArg f h).trans hf.1
    rw [hnone] at hfd
    cases hfd
  obtain ⟨s, hfs, hsd⟩ := hf.2 d hdc
  have hsq : s = q := Option.some.inj (hfs.symm.trans hfd)
  have hq0d : q0 ∈ canonicalMaskRightImages
      ends m j k l zero p d.1 := by
    simpa only [q, hsq] using hsd
  have hcd : c.1 ≠ d.1 := by
    intro h
    exact hdc (Subtype.ext h.symm)
  rcases canonicalSelfImage_owner_rootComponentCut_or_twoCommon
      hloop hjk hkl hk0 c.1 d.1 hcd hq0d with hcut | hsquare
  · exact Or.inl ⟨d, hdc, hcut⟩
  · obtain ⟨r, hrq0, hrc, hrd⟩ :=
      (exists_secondCommonImage_iff_canonicalTightTwoRowCollision
        ends m j k l zero p c.1 d.1 q0 hq0c hq0d).mpr hsquare
    have hrN : r ∈ canonicalMaskRightNeighborhood
        ends m j k l zero p S :=
      (mem_canonicalMaskRightNeighborhood_iff
        ends m j k l zero p S r).mpr ⟨c.1, c.2, hrc⟩
    let rN : ↑(canonicalMaskRightNeighborhood
        ends m j k l zero p S) := ⟨r, hrN⟩
    have hqr : q ≠ rN := by
      intro h
      exact hrq0 (congrArg Subtype.val h).symm
    obtain ⟨e, hec, -, -, g, hg⟩ :=
      canonicalMaskRightAugmentedMatching_rotateAssignedSecondRow
        ends m j k l zero p S c d hdc f hf q rN hfd hqr hq0c hrd
    exact Or.inr ⟨e, hec, g, hg⟩

set_option maxHeartbeats 1000000 in





theorem canonicalConsecutiveTriple_twoRow_or_chord_or_escape
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (hproper : ∀ T : Finset (leftMaskFiber ends m j k l zero p),
      T ⊂ S -> T.card ≤
        (canonicalMaskRightNeighborhood ends m j k l zero p T).card)
    (herase : ∀ x ∈ S, canonicalMaskRightNeighborhood
        ends m j k l zero p (S.erase x) =
      canonicalMaskRightNeighborhood ends m j k l zero p S)
    (c d e : leftMaskFiber ends m j k l zero p)
    (hcd : c ≠ d) (hce : c ≠ e) (hde : d ≠ e)
    (htriple : ({c, d, e} : Finset
      (leftMaskFiber ends m j k l zero p)) ⊂ S)
    (q r : rightMaskFiber ends m j k l zero p)
    (hqc : q ∈ canonicalMaskRightImages ends m j k l zero p c)
    (hqd : q ∈ canonicalMaskRightImages ends m j k l zero p d)
    (hrd : r ∈ canonicalMaskRightImages ends m j k l zero p d)
    (hre : r ∈ canonicalMaskRightImages ends m j k l zero p e) :
    CanonicalTightTwoRowCollision ends m j k l zero p c d ∨
      CanonicalTightTwoRowCollision ends m j k l zero p d e ∨
      ∃ x ∈ ({c, d, e} : Finset
          (leftMaskFiber ends m j k l zero p)),
        ∃ y ∈ S, y ≠ x ∧
          ∃ s : rightMaskFiber ends m j k l zero p,
            s ≠ q ∧ s ≠ r ∧
            s ∈ canonicalMaskRightImages ends m j k l zero p x ∧
            s ∈ canonicalMaskRightImages ends m j k l zero p y ∧
            ((x = c ∧ y = e) ∨ (x = e ∧ y = c) ∨
              y ∉ ({c, d, e} : Finset
                (leftMaskFiber ends m j k l zero p))) := by
  classical
  by_cases hCD : CanonicalTightTwoRowCollision
      ends m j k l zero p c d
  · exact Or.inl hCD
  by_cases hDE : CanonicalTightTwoRowCollision
      ends m j k l zero p d e
  · exact Or.inr (Or.inl hDE)
  right
  right
  have hcard : 2 < ({c, d, e} : Finset
      (leftMaskFiber ends m j k l zero p)).card := by
    simp [hcd, hce, hde]
  obtain ⟨x, hxT, s, hsx, hsq, hsr⟩ :=
    exists_canonicalMaskRightNeighbor_ne_pair_of_properHall
      ends m j k l zero p S hproper {c, d, e} htriple hcard q r
  have hxS : x ∈ S := htriple.subset hxT
  obtain ⟨y, hyS, hyx, hsy⟩ :=
    exists_other_of_erase_canonicalMaskRightNeighborhood_eq
      ends m j k l zero p S x hxS (herase x hxS) s hsx
  have hsquareCD
      (hsc : s ∈ canonicalMaskRightImages ends m j k l zero p c)
      (hsd : s ∈ canonicalMaskRightImages ends m j k l zero p d) :
      CanonicalTightTwoRowCollision ends m j k l zero p c d :=
    (exists_secondCommonImage_iff_canonicalTightTwoRowCollision
      ends m j k l zero p c d q hqc hqd).mp ⟨s, hsq, hsc, hsd⟩
  have hsquareDE
      (hsd : s ∈ canonicalMaskRightImages ends m j k l zero p d)
      (hse : s ∈ canonicalMaskRightImages ends m j k l zero p e) :
      CanonicalTightTwoRowCollision ends m j k l zero p d e :=
    (exists_secondCommonImage_iff_canonicalTightTwoRowCollision
      ends m j k l zero p d e r hrd hre).mp ⟨s, hsr, hsd, hse⟩
  simp only [Finset.mem_insert, Finset.mem_singleton] at hxT
  rcases hxT with hxc | hxd | hxe
  · subst x
    by_cases hyT : y ∈ ({c, d, e} : Finset
        (leftMaskFiber ends m j k l zero p))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hyT
      rcases hyT with hyc | hyd | hye
      · exact False.elim (hyx hyc)
      · subst y
        exact False.elim (hCD (hsquareCD hsx hsy))
      · exact ⟨c, by simp, y, hyS, hyx, s, hsq, hsr, hsx, hsy,
          Or.inl ⟨rfl, hye⟩⟩
    · exact ⟨c, by simp, y, hyS, hyx, s, hsq, hsr, hsx, hsy,
        Or.inr (Or.inr hyT)⟩
  · subst x
    by_cases hyT : y ∈ ({c, d, e} : Finset
        (leftMaskFiber ends m j k l zero p))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hyT
      rcases hyT with hyc | hyd | hye
      · subst y
        exact False.elim (hCD (hsquareCD hsy hsx))
      · exact False.elim (hyx hyd)
      · subst y
        exact False.elim (hDE (hsquareDE hsx hsy))
    · exact ⟨d, by simp, y, hyS, hyx, s, hsq, hsr, hsx, hsy,
        Or.inr (Or.inr hyT)⟩
  · subst x
    by_cases hyT : y ∈ ({c, d, e} : Finset
        (leftMaskFiber ends m j k l zero p))
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hyT
      rcases hyT with hyc | hyd | hye
      · exact ⟨e, by simp, y, hyS, hyx, s, hsq, hsr, hsx, hsy,
          Or.inr (Or.inl ⟨rfl, hyc⟩)⟩
      · subst y
        exact False.elim (hDE (hsquareDE hsy hsx))
      · exact False.elim (hyx hye)
    · exact ⟨e, by simp, y, hyS, hyx, s, hsq, hsr, hsx, hsy,
        Or.inr (Or.inr hyT)⟩

set_option maxHeartbeats 1000000 in




theorem exists_twoRowCollision_of_tight_canonicalMaskRightNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (htight : (canonicalMaskRightNeighborhood
        ends m j k l zero p S).card + 1 = S.card) :
    ∃ c ∈ S, ∃ d ∈ S, c ≠ d ∧
      CanonicalTightTwoRowCollision ends m j k l zero p c d := by
  classical
  let selfImage : ↑S ->
      ↑(canonicalMaskRightNeighborhood ends m j k l zero p S) :=
    fun c =>
      let q := canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p c.1 c.1
          (canonicalTransferWorks_self hloop hjk hkl hk0 c.1)
      ⟨q, (mem_canonicalMaskRightNeighborhood_iff
        ends m j k l zero p S q).mpr ⟨c.1, c.2,
          (mem_canonicalMaskRightImages_iff
            ends m j k l zero p c.1 q).mpr
              ⟨c.1, canonicalTransferWorks_self
                hloop hjk hkl hk0 c.1, rfl⟩⟩⟩
  have hnotinj : ¬ Function.Injective selfImage := by
    intro hinj
    have hcard := Fintype.card_le_of_injective selfImage hinj
    simp only [Fintype.card_coe] at hcard
    omega
  obtain ⟨c, d, hself, hcd⟩ := Function.not_injective_iff.mp hnotinj
  have himage :
      (canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p c.1 c.1
          (canonicalTransferWorks_self hloop hjk hkl hk0 c.1)).1.1 =
      (canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p d.1 d.1
          (canonicalTransferWorks_self hloop hjk hkl hk0 d.1)).1.1 := by
    exact congrArg (fun q => q.1.1.1) hself
  exact ⟨c.1, c.2, d.1, d.2, fun h => hcd (Subtype.ext h),
    canonicalSelfTransfer_collision_twoCommonImages
      ends m j k l zero hloop hjk hkl hk0 p c.1 d.1
        (fun h => hcd (Subtype.ext h)) himage⟩

set_option maxHeartbeats 1000000 in



theorem canonicalCollisionPerm_twoCycle_twoRow
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (σ : Equiv.Perm ↑S)
    (Q : ↑S -> rightMaskFiber ends m j k l zero p)
    (hQ : ∀ x,
      Q x ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
      Q x ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1)
    (x : ↑S) (hcycle : σ (σ x) = x)
    (hlabels : Q x ≠ Q (σ x)) :
    CanonicalTightTwoRowCollision
      ends m j k l zero p x.1 (σ x).1 := by
  have hq2x : Q (σ x) ∈
      canonicalMaskRightImages ends m j k l zero p x.1 := by
    have hxval : (σ (σ x)).1 = x.1 := congrArg Subtype.val hcycle
    exact hxval ▸ (hQ (σ x)).2
  exact ⟨Q x, Q (σ x), hlabels, (hQ x).1, (hQ x).2,
    hq2x, (hQ (σ x)).1⟩

set_option maxHeartbeats 1000000 in



theorem canonicalCollisionPerm_secondIterate_ne_of_noTwoRow
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (σ : Equiv.Perm ↑S)
    (Q : ↑S -> rightMaskFiber ends m j k l zero p)
    (hQ : ∀ x,
      Q x ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
      Q x ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1)
    (hQinj : Function.Injective Q)
    (hno : ∀ x, ¬ CanonicalTightTwoRowCollision
      ends m j k l zero p x.1 (σ x).1)
    (x : ↑S) (hx : σ x ≠ x) :
    σ (σ x) ≠ x := by
  intro hcycle
  have hlabels : Q x ≠ Q (σ x) := by
    intro h
    exact hx (hQinj h.symm)
  exact hno x (canonicalCollisionPerm_twoCycle_twoRow
    ends m j k l zero p S σ Q hQ x hcycle hlabels)

set_option maxHeartbeats 1000000 in



theorem canonicalInjectiveCollisionPerm_opposingCuts_and_no_twoCycles
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (σ : Equiv.Perm ↑S) (hσ : ∀ x, σ x ≠ x)
    (Q : ↑S -> rightMaskFiber ends m j k l zero p)
    (hQ : ∀ x,
      Q x ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
      Q x ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1)
    (hQinj : Function.Injective Q)
    (hno : ∀ x, ¬ CanonicalTightTwoRowCollision
      ends m j k l zero p x.1 (σ x).1) :
    (∀ x, CanonicalOpposingRootCutsAtRight
      ends m j k l zero p x.1 (σ x).1 (Q x)) ∧
      ∀ x, σ (σ x) ≠ x := by
  constructor
  · intro x
    have hxne : x.1 ≠ (σ x).1 := by
      intro h
      exact hσ x (Subtype.ext h.symm)
    rcases canonicalCommonImage_opposingAtRight_or_twoCommon
        hloop hjk hkl x.1 (σ x).1 hxne (Q x) (hQ x).1 (hQ x).2 with
      hcuts | hsquare
    · exact hcuts
    · exact False.elim (hno x hsquare)
  · intro x
    exact canonicalCollisionPerm_secondIterate_ne_of_noTwoRow
      ends m j k l zero p S σ Q hQ hQinj hno x (hσ x)

set_option maxHeartbeats 1000000 in



theorem canonicalCollisionIndexPerm_opposingAtRight_or_square
    {A : Type*} [Fintype A]
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (σ : Equiv.Perm A)
    (X : A -> leftMaskFiber ends m j k l zero p)
    (hX : ∀ x, X x ≠ X (σ x))
    (Q : A -> rightMaskFiber ends m j k l zero p)
    (hQ : ∀ x,
      Q x ∈ canonicalMaskRightImages ends m j k l zero p (X x) ∧
      Q x ∈ canonicalMaskRightImages ends m j k l zero p (X (σ x))) :
    (∃ x, CanonicalTightTwoRowCollision
      ends m j k l zero p (X x) (X (σ x))) ∨
      ∀ x, CanonicalOpposingRootCutsAtRight
        ends m j k l zero p (X x) (X (σ x)) (Q x) := by
  by_cases hsquare : ∃ x, CanonicalTightTwoRowCollision
      ends m j k l zero p (X x) (X (σ x))
  · exact Or.inl hsquare
  · right
    intro x
    rcases canonicalCommonImage_opposingAtRight_or_twoCommon
        hloop hjk hkl (X x) (X (σ x)) (hX x)
        (Q x) (hQ x).1 (hQ x).2 with hcuts | hs
    · exact hcuts
    · exact False.elim (hsquare ⟨x, hs⟩)

set_option maxHeartbeats 1000000 in




theorem exists_hallFailure_labelledCollisionPerm
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    [DecidableEq (leftMaskFiber ends m j k l zero p)]
    (hfail : ¬ CanonicalMaskRightHall ends m j k l zero p) :
    ∃ S : Finset (leftMaskFiber ends m j k l zero p),
      ∃ σ : Equiv.Perm ↑S, σ ≠ Equiv.refl ↑S ∧
        ∀ x : ↑S, σ x ≠ x ->
          ∃ q : rightMaskFiber ends m j k l zero p,
            q ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
            q ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1 ∧
            (CanonicalOpposingRootCutsAtRight
                ends m j k l zero p x.1 (σ x).1 q ∨
              CanonicalTightTwoRowCollision
                ends m j k l zero p x.1 (σ x).1) := by
  classical
  obtain ⟨S, hSne, htight, -, hproper, -, hadj⟩ :=
    exists_tight_canonicalMaskRightHall_obstruction
      ends m j k l zero hloop hjk hkl hk0 p hfail
  obtain ⟨c, hc⟩ := hSne
  obtain ⟨d, hd, hdc, hcd⟩ := hadj c hc
  obtain ⟨σ, hσcd, hσadj⟩ := exists_canonicalMaskTransferAdjacentPerm
    ends m j k l zero p S htight hproper c d hc hd hcd
  have hσne : σ ≠ Equiv.refl ↑S := by
    intro h
    have hfix : σ ⟨c, hc⟩ = ⟨c, hc⟩ := by simp [h]
    exact hdc (congrArg Subtype.val (hσcd.symm.trans hfix))
  refine ⟨S, σ, hσne, ?_⟩
  intro x hx
  obtain ⟨q, hqx, hqσ⟩ :=
    (exists_mem_canonicalMaskRightImages_iff_adjacent
      ends m j k l zero p x.1 (σ x).1).mpr (hσadj x)
  have hxne : x.1 ≠ (σ x).1 := by
    intro h
    exact hx (Subtype.ext h.symm)
  exact ⟨q, hqx, hqσ,
    canonicalCommonImage_opposingAtRight_or_twoCommon
      hloop hjk hkl x.1 (σ x).1 hxne q hqx hqσ⟩

set_option maxHeartbeats 1000000 in



theorem canonicalCommonImage_explicitOppositeCut_or_twoCommon
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (c d : leftMaskFiber ends m j k l zero p) (hcd : c ≠ d)
    (q : rightMaskFiber ends m j k l zero p)
    (hqc : q ∈ canonicalMaskRightImages ends m j k l zero p c)
    (hqd : q ∈ canonicalMaskRightImages ends m j k l zero p d) :
    CanonicalRowSupportRootComponentCut ends m k zero
        (canonicalCollisionOppositeRow m q.1.1 c.1.1 d.1.1) ∨
      CanonicalTightTwoRowCollision ends m j k l zero p c d := by
  obtain ⟨a, hac, hqa⟩ := (mem_canonicalMaskRightImages_iff
    ends m j k l zero p c q).mp hqc
  obtain ⟨b, hbd, hqb⟩ := (mem_canonicalMaskRightImages_iff
    ends m j k l zero p d q).mp hqd
  have hqrowa : rowClass m q.1.1 0 =
      canonicalTranslatedRow ends m k zero a.1.1 c.1.1 := by
    rw [hqa]
    have hv := canonicalTransfers_valid_on_sameMask hloop hjk hkl a c
    rw [rowClass_balancedSwap_zero hv.1 hv.2.1]
    rfl
  have hqrowb : rowClass m q.1.1 0 =
      canonicalTranslatedRow ends m k zero b.1.1 d.1.1 := by
    rw [hqb]
    have hv := canonicalTransfers_valid_on_sameMask hloop hjk hkl b d
    rw [rowClass_balancedSwap_zero hv.1 hv.2.1]
    rfl
  have htrans : canonicalTranslatedRow ends m k zero a.1.1 c.1.1 =
      canonicalTranslatedRow ends m k zero b.1.1 d.1.1 :=
    hqrowa.symm.trans hqrowb
  by_cases hbc : CanonicalTransferWorks ends m k zero b.1.1 c.1.1
  · exact Or.inr
      (exists_two_common_canonicalMaskRightImages_of_collisionSquare
        hloop hjk hkl a b c d hcd hac htrans hbc)
  · left
    have hcut := canonicalTransferWorks_failed_rootComponentCut
      hloop hjk hkl b c hbc
    have hopp := canonicalTranslatedRow_opposite_eq_of_eq
      ends m k zero a.1.1 b.1.1 c.1.1 d.1.1 htrans
    have hexp : canonicalTranslatedRow ends m k zero b.1.1 c.1.1 =
        canonicalCollisionOppositeRow m q.1.1 c.1.1 d.1.1 := by
      rw [hopp, canonicalCollisionOppositeRow, hqrowa]
      unfold canonicalTranslatedRow
      calc
        rowClass m d.1.1 0 ∆ canonicalTransferUnion ends m k zero a.1.1 =
            canonicalTransferUnion ends m k zero a.1.1 ∆
              rowClass m d.1.1 0 := symmDiff_comm _ _
        _ = (rowClass m c.1.1 0 ∆ rowClass m c.1.1 0) ∆
              canonicalTransferUnion ends m k zero a.1.1 ∆
                rowClass m d.1.1 0 := by
          rw [symmDiff_self, bot_symmDiff]
        _ = (rowClass m c.1.1 0 ∆
              canonicalTransferUnion ends m k zero a.1.1) ∆
            rowClass m c.1.1 0 ∆ rowClass m d.1.1 0 := by ac_rfl
    unfold CanonicalTranslatedRowRootComponentCut at hcut
    unfold CanonicalRowSupportRootComponentCut
    rw [← hexp]
    exact hcut

set_option maxHeartbeats 1000000 in




theorem canonicalFixedPointFreeCollisionPerm_explicitCuts_or_square
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (σ : Equiv.Perm ↑S) (hσ : ∀ x, σ x ≠ x)
    (Q : ↑S -> rightMaskFiber ends m j k l zero p)
    (hQ : ∀ x,
      Q x ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
      Q x ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1) :
    (∃ x, CanonicalTightTwoRowCollision
      ends m j k l zero p x.1 (σ x).1) ∨
      ((∀ x, CanonicalRowSupportRootComponentCut ends m k zero
        (canonicalCollisionOppositeRow
          m (Q x).1.1 x.1.1.1 (σ x).1.1.1)) ∧
        symmDiffFold Finset.univ (fun x =>
            canonicalCollisionOppositeRow
              m (Q x).1.1 x.1.1.1 (σ x).1.1.1) =
          symmDiffFold Finset.univ
            (fun x => rowClass m (Q x).1.1 0)) := by
  classical
  by_cases hsquare : ∃ x, CanonicalTightTwoRowCollision
      ends m j k l zero p x.1 (σ x).1
  · exact Or.inl hsquare
  · right
    constructor
    · intro x
      have hxne : x.1 ≠ (σ x).1 := by
        intro h
        exact hσ x (Subtype.ext h.symm)
      rcases canonicalCommonImage_explicitOppositeCut_or_twoCommon
          hloop hjk hkl x.1 (σ x).1 hxne (Q x) (hQ x).1 (hQ x).2 with
        hcut | hs
      · exact hcut
      · exact False.elim (hsquare ⟨x, hs⟩)
    · exact symmDiffFold_endpointCancellation
        (fun x => rowClass m (Q x).1.1 0)
        (fun x => rowClass m x.1.1.1 0) σ




theorem canonicalFixedPointFreeCollisionPerm_cutBoundaryParity_or_square
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (σ : Equiv.Perm ↑S) (hσ : ∀ x, σ x ≠ x)
    (Q : ↑S -> rightMaskFiber ends m j k l zero p)
    (hQ : ∀ x,
      Q x ∈ canonicalMaskRightImages ends m j k l zero p x.1 ∧
      Q x ∈ canonicalMaskRightImages ends m j k l zero p (σ x).1) :
    (∃ x, CanonicalTightTwoRowCollision
      ends m j k l zero p x.1 (σ x).1) ∨
      ((∀ x, CanonicalRowSupportRootComponentCut ends m k zero
        (canonicalCollisionOppositeRow
          m (Q x).1.1 x.1.1.1 (σ x).1.1.1)) ∧
        StatMech.Sharpness.RandomCurrent.sources ends
          (symmDiffFold Finset.univ (fun x =>
            canonicalCollisionOppositeRow
              m (Q x).1.1 x.1.1.1 (σ x).1.1.1)) =
          if (Finset.univ : Finset ↑S).card % 2 = 0 then ∅
          else {j, k} ∆ {k, l}) := by
  rcases canonicalFixedPointFreeCollisionPerm_explicitCuts_or_square
      hloop hjk hkl S σ hσ Q hQ with hsquare | ⟨hcuts, hfold⟩
  · exact Or.inl hsquare
  · right
    refine ⟨hcuts, ?_⟩
    rw [hfold]
    exact sources_symmDiffFold_rightMaskRows
      ends m j k l zero p Finset.univ Q




theorem canonicalCollisionIndexPerm_cutBoundaryParity_or_square
    {A : Type*} [Fintype A]
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ e ∈ m, ¬ (ends e).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (σ : Equiv.Perm A)
    (X : A -> leftMaskFiber ends m j k l zero p)
    (hX : ∀ x, X x ≠ X (σ x))
    (Q : A -> rightMaskFiber ends m j k l zero p)
    (hQ : ∀ x,
      Q x ∈ canonicalMaskRightImages ends m j k l zero p (X x) ∧
      Q x ∈ canonicalMaskRightImages ends m j k l zero p (X (σ x))) :
    (∃ x, CanonicalTightTwoRowCollision
      ends m j k l zero p (X x) (X (σ x))) ∨
      ((∀ x, CanonicalRowSupportRootComponentCut ends m k zero
        (canonicalCollisionOppositeRow
          m (Q x).1.1 (X x).1.1 (X (σ x)).1.1)) ∧
        StatMech.Sharpness.RandomCurrent.sources ends
          (symmDiffFold Finset.univ (fun x =>
            canonicalCollisionOppositeRow
              m (Q x).1.1 (X x).1.1 (X (σ x)).1.1)) =
          if (Finset.univ : Finset A).card % 2 = 0 then ∅
          else {j, k} ∆ {k, l}) := by
  classical
  by_cases hsquare : ∃ x, CanonicalTightTwoRowCollision
      ends m j k l zero p (X x) (X (σ x))
  · exact Or.inl hsquare
  · right
    have hcuts : ∀ x, CanonicalRowSupportRootComponentCut ends m k zero
        (canonicalCollisionOppositeRow
          m (Q x).1.1 (X x).1.1 (X (σ x)).1.1) := by
      intro x
      rcases canonicalCommonImage_explicitOppositeCut_or_twoCommon
          hloop hjk hkl (X x) (X (σ x)) (hX x)
          (Q x) (hQ x).1 (hQ x).2 with hcut | hs
      · exact hcut
      · exact False.elim (hsquare ⟨x, hs⟩)
    refine ⟨hcuts, ?_⟩
    have hfold : symmDiffFold Finset.univ (fun x =>
          canonicalCollisionOppositeRow
            m (Q x).1.1 (X x).1.1 (X (σ x)).1.1) =
        symmDiffFold Finset.univ
          (fun x => rowClass m (Q x).1.1 0) := by
      exact symmDiffFold_endpointCancellation
        (fun x => rowClass m (Q x).1.1 0)
        (fun x => rowClass m (X x).1.1 0) σ
    rw [hfold]
    exact sources_symmDiffFold_rightMaskRows
      ends m j k l zero p Finset.univ Q

end StatMech.GrahamGHS.FourColor
