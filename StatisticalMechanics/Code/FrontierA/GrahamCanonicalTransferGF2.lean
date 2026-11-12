/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamCanonicalTransferCoverageJoin










open Finset
open scoped symmDiff

namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]



theorem eq_of_rowClass_zero_of_fourColorMaskProfile_eq
    (m : Finset I) (c d : ↑m -> Fin 4)
    (hprofile : fourColorMaskProfile m c = fourColorMaskProfile m d)
    (hrow : rowClass m c 0 = rowClass m d 0) :
    c = d := by
  funext i
  have hmid := congrArg
    (fun S : Finset I × Finset I => i.1 ∈ S.1) hprofile
  have hout := congrArg
    (fun S : Finset I × Finset I => i.1 ∈ S.2) hprofile
  have hrow' := congrArg (fun S : Finset I => i.1 ∈ S) hrow
  have hc : c i = 0 ∨ c i = 1 ∨ c i = 2 ∨ c i = 3 := by omega
  have hd : d i = 0 ∨ d i = 1 ∨ d i = 2 ∨ d i = 3 := by omega
  rcases hc with hc | hc | hc | hc <;>
    rcases hd with hd | hd | hd | hd <;>
    simp [fourColorMaskProfile, middleMask, outerMask, rowClass,
      mem_colorClass_iff, i.2, hc, hd] at hmid hout hrow' ⊢


noncomputable def canonicalTranslatedRow
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (r c : ↑m -> Fin 4) : Finset I :=
  rowClass m c 0 ∆ canonicalTransferUnion ends m k zero r


def RowSupportDisconnects
    (ends : I -> Sym2 W) (m K : Finset I) (k zero : W) : Prop :=
  ¬ StatMech.Sharpness.RandomCurrent.connK ends K k zero ∧
    ¬ StatMech.Sharpness.RandomCurrent.connK ends (m \ K) k zero



theorem balancedSwap_comp_eq_symmDiff
    (m X₁ Y₁ X₂ Y₂ : Finset I) (c : ↑m -> Fin 4) :
    balancedSwap m X₂ Y₂ (balancedSwap m X₁ Y₁ c) =
      balancedSwap m (X₁ ∆ X₂) (Y₁ ∆ Y₂) c := by
  funext i
  have hc : c i = 0 ∨ c i = 1 ∨ c i = 2 ∨ c i = 3 := by omega
  rcases hc with hc | hc | hc | hc <;>
    by_cases hX₁ : (i : I) ∈ X₁ <;>
    by_cases hY₁ : (i : I) ∈ Y₁ <;>
    by_cases hX₂ : (i : I) ∈ X₂ <;>
    by_cases hY₂ : (i : I) ∈ Y₂ <;>
    simp [balancedSwap, middleSwapOn, outerSwapOn,
      Finset.mem_symmDiff, Equiv.swap_apply_def, hc, hX₁, hY₁, hX₂, hY₂]

theorem canonicalTransferUnion_subset_m
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r : leftMaskFiber ends m j k l zero p) :
    canonicalTransferUnion ends m k zero r.1.1 ⊆ m := by
  have hv := canonicalTransfers_valid hloop hjk hkl r.1.2
  intro i hi
  rcases Finset.mem_union.mp hi with hi | hi
  · rcases Finset.mem_union.mp (hv.1 hi) with hi | hi
    · exact colorClass_subset m r.1.1 1 hi
    · exact colorClass_subset m r.1.1 2 hi
  · rcases Finset.mem_union.mp (hv.2.1 hi) with hi | hi
    · exact colorClass_subset m r.1.1 0 hi
    · exact colorClass_subset m r.1.1 3 hi

private theorem rowClass_one_symmDiff_eq_sdiff_translated
    (m T : Finset I) (c : ↑m -> Fin 4) (hTm : T ⊆ m) :
    rowClass m c 1 ∆ T = m \ (rowClass m c 0 ∆ T) := by
  rw [rowClass_one_eq_sdiff]
  ext i
  by_cases him : i ∈ m
  · simp only [Finset.mem_symmDiff, Finset.mem_sdiff, him, true_and]
    tauto
  · have hiT : i ∉ T := fun hi => him (hTm hi)
    simp [Finset.mem_symmDiff, Finset.mem_sdiff, him, hiT]



theorem canonicalTransferWorks_iff_translatedRowDisconnects
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r c : leftMaskFiber ends m j k l zero p) :
    CanonicalTransferWorks ends m k zero r.1.1 c.1.1 ↔
      RowSupportDisconnects ends m
        (canonicalTranslatedRow ends m k zero r.1.1 c.1.1) k zero := by
  rw [canonicalTransferWorks_iff_rowSymmDiff hloop hjk hkl r c]
  unfold RowSupportDisconnects canonicalTranslatedRow
  rw [rowClass_one_symmDiff_eq_sdiff_translated m
    (canonicalTransferUnion ends m k zero r.1.1) c.1.1
    (canonicalTransferUnion_subset_m hloop hjk hkl r)]



theorem canonicalBalancedSwaps_eq_iff_rowSymmDiff
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (a b c d : leftMaskFiber ends m j k l zero p) :
    balancedSwap m
          (canonicalMiddleTransfer ends m a.1.1 k zero)
          (canonicalOuterTransfer ends m a.1.1 k zero) c.1.1 =
        balancedSwap m
          (canonicalMiddleTransfer ends m b.1.1 k zero)
          (canonicalOuterTransfer ends m b.1.1 k zero) d.1.1 ↔
      rowClass m c.1.1 0 ∆ canonicalTransferUnion ends m k zero a.1.1 =
        rowClass m d.1.1 0 ∆ canonicalTransferUnion ends m k zero b.1.1 := by
  have hva := canonicalTransfers_valid_on_sameMask hloop hjk hkl a c
  have hvb := canonicalTransfers_valid_on_sameMask hloop hjk hkl b d
  constructor
  · intro h
    have hrow := congrArg (fun q => rowClass m q 0) h
    simpa only [rowClass_balancedSwap_zero hva.1 hva.2.1,
      rowClass_balancedSwap_zero hvb.1 hvb.2.1,
      canonicalTransferUnion] using hrow
  · intro hrow
    apply eq_of_rowClass_zero_of_fourColorMaskProfile_eq m
    · simpa only [fourColorMaskProfile_balancedSwap] using c.2.trans d.2.symm
    · simpa only [rowClass_balancedSwap_zero hva.1 hva.2.1,
        rowClass_balancedSwap_zero hvb.1 hvb.2.1,
        canonicalTransferUnion] using hrow



theorem rowSymmDiff_eq_transferSymmDiff_of_translatedRow_eq
    {ends : I -> Sym2 W} {m : Finset I} {k zero : W}
    (a b c d : ↑m -> Fin 4)
    (h : canonicalTranslatedRow ends m k zero a c =
      canonicalTranslatedRow ends m k zero b d) :
    rowClass m c 0 ∆ rowClass m d 0 =
      canonicalTransferUnion ends m k zero a ∆
        canonicalTransferUnion ends m k zero b := by
  unfold canonicalTranslatedRow at h
  let A := canonicalTransferUnion ends m k zero a
  let B := canonicalTransferUnion ends m k zero b
  let C := rowClass m c 0
  let D := rowClass m d 0
  have hC : C = (D ∆ B) ∆ A := by
    calc
      C = (C ∆ A) ∆ A := by simp
      _ = (D ∆ B) ∆ A := congrArg (fun S : Finset I => S ∆ A) h
  change C ∆ D = A ∆ B
  rw [hC]
  calc
    (D ∆ B) ∆ A ∆ D = (D ∆ D) ∆ (B ∆ A) := by ac_rfl
    _ = B ∆ A := by simp
    _ = A ∆ B := symmDiff_comm B A

theorem card_rowSymmDiff_eq_card_transferSymmDiff_of_translatedRow_eq
    {ends : I -> Sym2 W} {m : Finset I} {k zero : W}
    (a b c d : ↑m -> Fin 4)
    (h : canonicalTranslatedRow ends m k zero a c =
      canonicalTranslatedRow ends m k zero b d) :
    #(rowClass m c 0 ∆ rowClass m d 0) =
      #(canonicalTransferUnion ends m k zero a ∆
        canonicalTransferUnion ends m k zero b) := by
  exact congrArg Finset.card
    (rowSymmDiff_eq_transferSymmDiff_of_translatedRow_eq a b c d h)



noncomputable def canonicalTransferMapOfWorks
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (a c : leftMaskFiber ends m j k l zero p)
    (hworks : CanonicalTransferWorks ends m k zero a.1.1 c.1.1) :
    rightMaskFiber ends m j k l zero p := by
  let X := canonicalMiddleTransfer ends m a.1.1 k zero
  let Y := canonicalOuterTransfer ends m a.1.1 k zero
  let q := balancedSwap m X Y c.1.1
  have hv := canonicalTransfers_valid_on_sameMask hloop hjk hkl a c
  have hq : RightPattern ends m {j, k} {k, l} k zero q :=
    rightPattern_of_balancedTransfer c.1.2 hv.1 hv.2.1
      hv.2.2.1 hv.2.2.2 hworks
  refine ⟨⟨q, hq⟩, ?_⟩
  calc
    fourColorMaskProfile m q = fourColorMaskProfile m c.1.1 :=
      fourColorMaskProfile_balancedSwap m X Y c.1.1
    _ = p := c.2



theorem canonicalMaskTransferAdjacent_iff_exists_works_rowSymmDiff
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (c d : leftMaskFiber ends m j k l zero p) :
    CanonicalMaskTransferAdjacent ends m j k l zero p c d ↔
      ∃ a b : leftMaskFiber ends m j k l zero p,
        CanonicalTransferWorks ends m k zero a.1.1 c.1.1 ∧
          CanonicalTransferWorks ends m k zero b.1.1 d.1.1 ∧
          rowClass m c.1.1 0 ∆
              canonicalTransferUnion ends m k zero a.1.1 =
            rowClass m d.1.1 0 ∆
              canonicalTransferUnion ends m k zero b.1.1 := by
  constructor
  · rintro ⟨q, a, b, hqc, hqd⟩
    refine ⟨a, b, ?_, ?_, ?_⟩
    · rw [CanonicalTransferWorks, ← hqc]
      exact q.1.2.2.2.2.2
    · rw [CanonicalTransferWorks, ← hqd]
      exact q.1.2.2.2.2.2
    · apply (canonicalBalancedSwaps_eq_iff_rowSymmDiff
        hloop hjk hkl a b c d).mp
      exact hqc.symm.trans hqd
  · rintro ⟨a, b, hac, hbd, hrow⟩
    let q := canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p a c hac
    refine ⟨q, a, b, rfl, ?_⟩
    change balancedSwap m
        (canonicalMiddleTransfer ends m a.1.1 k zero)
        (canonicalOuterTransfer ends m a.1.1 k zero) c.1.1 =
      balancedSwap m
        (canonicalMiddleTransfer ends m b.1.1 k zero)
        (canonicalOuterTransfer ends m b.1.1 k zero) d.1.1
    exact (canonicalBalancedSwaps_eq_iff_rowSymmDiff
      hloop hjk hkl a b c d).mpr hrow



theorem canonicalMaskTransferAdjacent_iff_exists_translatedRow
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (c d : leftMaskFiber ends m j k l zero p) :
    CanonicalMaskTransferAdjacent ends m j k l zero p c d ↔
      ∃ a b : leftMaskFiber ends m j k l zero p,
        RowSupportDisconnects ends m
            (canonicalTranslatedRow ends m k zero a.1.1 c.1.1) k zero ∧
          canonicalTranslatedRow ends m k zero a.1.1 c.1.1 =
            canonicalTranslatedRow ends m k zero b.1.1 d.1.1 := by
  rw [canonicalMaskTransferAdjacent_iff_exists_works_rowSymmDiff
    hloop hjk hkl c d]
  constructor
  · rintro ⟨a, b, hac, -, heq⟩
    exact ⟨a, b,
      (canonicalTransferWorks_iff_translatedRowDisconnects
        hloop hjk hkl a c).mp hac,
      heq⟩
  · rintro ⟨a, b, hdisc, heq⟩
    have hac := (canonicalTransferWorks_iff_translatedRowDisconnects
      hloop hjk hkl a c).mpr hdisc
    have hbd : CanonicalTransferWorks ends m k zero b.1.1 d.1.1 :=
      (canonicalTransferWorks_iff_translatedRowDisconnects
        hloop hjk hkl b d).mpr (heq ▸ hdisc)
    exact ⟨a, b, hac, hbd, heq⟩


theorem mem_canonicalMaskOrbitCoverage_iff_translatedRow
    {ends : I -> Sym2 W} {m : Finset I} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    {p : Finset I × Finset I}
    (r d : leftMaskFiber ends m j k l zero p) :
    d ∈ canonicalMaskOrbitCoverage ends m j k l zero p r ↔
      CanonicalMaskTransferOrbit ends m j k l zero p r d ∧
        RowSupportDisconnects ends m
          (canonicalTranslatedRow ends m k zero r.1.1 d.1.1) k zero := by
  rw [mem_canonicalMaskOrbitCoverage_iff]
  exact and_congr_right fun _ =>
    canonicalTransferWorks_iff_translatedRowDisconnects
      hloop hjk hkl r d

end StatMech.GrahamGHS.FourColor
