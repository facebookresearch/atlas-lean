/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamCanonicalTransferCoverageExchange









open Finset
open scoped symmDiff

namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def LeftSourcePattern (ends : I -> Sym2 W) (m : Finset I)
    (A B : Finset W) (c : ↑m -> Fin 4) : Prop :=
  sources ends (colorClass m c 0) = A ∧
    sources ends (colorClass m c 1) = ∅ ∧
    sources ends (colorClass m c 2) = B ∧
    sources ends (colorClass m c 3) = ∅



def leftSourceMaskFiber (ends : I -> Sym2 W) (m : Finset I)
    (j k l zero : W) (p : Finset I × Finset I) :=
  {c : ↑m -> Fin 4 //
    LeftSourcePattern ends m {j, k} {k, l} c ∧
      fourColorMaskProfile m c = p}

noncomputable instance instFintypeLeftSourceMaskFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Fintype (leftSourceMaskFiber ends m j k l zero p) := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective


def leftMaskFiberToSourceMaskFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    leftMaskFiber ends m j k l zero p ->
      leftSourceMaskFiber ends m j k l zero p := fun c =>
  ⟨c.1.1, ⟨⟨c.1.2.1, c.1.2.2.1, c.1.2.2.2.1,
    c.1.2.2.2.2.1⟩, c.2⟩⟩

theorem leftMaskFiberToSourceMaskFiber_injective
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Function.Injective
      (leftMaskFiberToSourceMaskFiber ends m j k l zero p) := by
  intro c d h
  apply Subtype.ext
  apply Subtype.ext
  have hv := congrArg
    (fun x : leftSourceMaskFiber ends m j k l zero p => x.1) h
  simpa only [leftMaskFiberToSourceMaskFiber] using hv


theorem leftSourcePattern_of_sourceless_balancedSwap
    {ends : I -> Sym2 W} {m X Y : Finset I}
    {A B : Finset W} {c : ↑m -> Fin 4}
    (hleft : LeftSourcePattern ends m A B c)
    (hX : X ⊆ colorClass m c 1 ∪ colorClass m c 2)
    (hY : Y ⊆ colorClass m c 0 ∪ colorClass m c 3)
    (hsrcX : sources ends X = ∅)
    (hsrcY : sources ends Y = ∅) :
    LeftSourcePattern ends m A B (balancedSwap m X Y c) := by
  rcases hleft with ⟨h0, h1, h2, h3⟩
  have hY' : Y ⊆ colorClass m (middleSwapOn m X c) 0 ∪
      colorClass m (middleSwapOn m X c) 3 := by
    rwa [colorClass_middleSwapOn_zero, colorClass_middleSwapOn_three]
  unfold LeftSourcePattern balancedSwap
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [colorClass_outerSwapOn_zero m Y _ hY', sources_symmDiff,
      colorClass_middleSwapOn_zero, h0, hsrcY]
    simp
  · rw [colorClass_outerSwapOn_one, colorClass_middleSwapOn_one m X c hX,
      sources_symmDiff, h1, hsrcX]
    simp
  · rw [colorClass_outerSwapOn_two, colorClass_middleSwapOn_two m X c hX,
      sources_symmDiff, h2, hsrcX]
    simp
  · rw [colorClass_outerSwapOn_three m Y _ hY', sources_symmDiff,
      colorClass_middleSwapOn_three, h3, hsrcY]
    simp

private theorem symmDiff_subset_of_subsets_ambient
    {A B S : Finset I} (hA : A ⊆ S) (hB : B ⊆ S) : A ∆ B ⊆ S := by
  intro i hi
  rcases Finset.mem_symmDiff.mp hi with hi | hi
  · exact hA hi.1
  · exact hB hi.1



noncomputable def canonicalQuadrangleCompletionSourceMap
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (a b : leftMaskFiber ends m j k l zero p)
    (c : leftSourceMaskFiber ends m j k l zero p) :
    leftSourceMaskFiber ends m j k l zero p := by
  let X := canonicalMiddleTransferDifference ends m k zero a.1.1 b.1.1
  let Y := canonicalOuterTransferDifference ends m k zero a.1.1 b.1.1
  let d := canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1
  have hva := canonicalTransfers_valid hloop hjk hkl a.1.2
  have hvb := canonicalTransfers_valid hloop hjk hkl b.1.2
  have haProfile : fourColorMaskProfile m a.1.1 =
      fourColorMaskProfile m c.1 := a.2.trans c.2.2.symm
  have hbProfile : fourColorMaskProfile m b.1.1 =
      fourColorMaskProfile m c.1 := b.2.trans c.2.2.symm
  have haMid : middleMask m a.1.1 = middleMask m c.1 :=
    congrArg Prod.fst haProfile
  have hbMid : middleMask m b.1.1 = middleMask m c.1 :=
    congrArg Prod.fst hbProfile
  have haOut : outerMask m a.1.1 = outerMask m c.1 :=
    congrArg Prod.snd haProfile
  have hbOut : outerMask m b.1.1 = outerMask m c.1 :=
    congrArg Prod.snd hbProfile
  have haX : canonicalMiddleTransfer ends m a.1.1 k zero ⊆
      middleMask m c.1 := by
    rw [← haMid]
    simpa only [middleMask] using hva.1
  have hbX : canonicalMiddleTransfer ends m b.1.1 k zero ⊆
      middleMask m c.1 := by
    rw [← hbMid]
    simpa only [middleMask] using hvb.1
  have haY : canonicalOuterTransfer ends m a.1.1 k zero ⊆
      outerMask m c.1 := by
    rw [← haOut]
    simpa only [outerMask] using hva.2.1
  have hbY : canonicalOuterTransfer ends m b.1.1 k zero ⊆
      outerMask m c.1 := by
    rw [← hbOut]
    simpa only [outerMask] using hvb.2.1
  have hX : X ⊆ colorClass m c.1 1 ∪ colorClass m c.1 2 := by
    simpa only [X, canonicalMiddleTransferDifference, middleMask] using
      symmDiff_subset_of_subsets_ambient haX hbX
  have hY : Y ⊆ colorClass m c.1 0 ∪ colorClass m c.1 3 := by
    simpa only [Y, canonicalOuterTransferDifference, outerMask] using
      symmDiff_subset_of_subsets_ambient haY hbY
  have hsrcX : sources ends X = ∅ := by
    dsimp only [X, canonicalMiddleTransferDifference]
    rw [sources_symmDiff, hva.2.2.1, hvb.2.2.1]
    exact symmDiff_self _
  have hsrcY : sources ends Y = ∅ := by
    dsimp only [Y, canonicalOuterTransferDifference]
    rw [sources_symmDiff, hva.2.2.2, hvb.2.2.2]
    exact symmDiff_self _
  refine ⟨d, leftSourcePattern_of_sourceless_balancedSwap
    c.2.1 hX hY hsrcX hsrcY, ?_⟩
  calc
    fourColorMaskProfile m d = fourColorMaskProfile m c.1 := by
      simp [d, canonicalQuadrangleCompletion,
        fourColorMaskProfile_balancedSwap]
    _ = p := c.2.2



noncomputable def canonicalQuadrangleCompletionSourceEquiv
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (a b : leftMaskFiber ends m j k l zero p) :
    leftSourceMaskFiber ends m j k l zero p ≃
      leftSourceMaskFiber ends m j k l zero p where
  toFun := canonicalQuadrangleCompletionSourceMap
    ends m j k l zero hloop hjk hkl p a b
  invFun := canonicalQuadrangleCompletionSourceMap
    ends m j k l zero hloop hjk hkl p a b
  left_inv := by
    intro c
    apply Subtype.ext
    exact canonicalQuadrangleCompletion_involutive
      ends m k zero a.1.1 b.1.1 c.1

  right_inv := by
    intro c
    apply Subtype.ext
    exact canonicalQuadrangleCompletion_involutive
      ends m k zero a.1.1 b.1.1 c.1



theorem canonicalQuadrangleCompletionSourceEquiv_commute
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (a b r s : leftMaskFiber ends m j k l zero p)
    (x : leftSourceMaskFiber ends m j k l zero p) :
    canonicalQuadrangleCompletionSourceEquiv
        ends m j k l zero hloop hjk hkl p a b
        (canonicalQuadrangleCompletionSourceEquiv
          ends m j k l zero hloop hjk hkl p r s x) =
      canonicalQuadrangleCompletionSourceEquiv
        ends m j k l zero hloop hjk hkl p r s
        (canonicalQuadrangleCompletionSourceEquiv
          ends m j k l zero hloop hjk hkl p a b x) := by
  apply Subtype.ext
  exact canonicalQuadrangleCompletion_changes_commute
    ends m k zero a.1.1 b.1.1 r.1.1 s.1.1 x.1


noncomputable def canonicalCoverageExclusive
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (a b : leftMaskFiber ends m j k l zero p) :
    Finset (leftMaskFiber ends m j k l zero p) := by
  classical
  exact canonicalMaskOrbitCoverage ends m j k l zero p a \
    canonicalMaskOrbitCoverage ends m j k l zero p b



noncomputable def canonicalCoverageExclusiveGoodQuadrangles
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (a b : leftMaskFiber ends m j k l zero p) :
    Finset (leftMaskFiber ends m j k l zero p) := by
  classical
  exact (canonicalCoverageExclusive ends m j k l zero p a b).filter fun c =>
    RowsDisconnect ends m
      (canonicalQuadrangleCompletion ends m k zero
        a.1.1 b.1.1 c.1.1) k zero

set_option maxHeartbeats 1000000 in
@[simp] theorem mem_canonicalCoverageExclusiveGoodQuadrangles_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (a b c : leftMaskFiber ends m j k l zero p) :
    c ∈ canonicalCoverageExclusiveGoodQuadrangles
        ends m j k l zero p a b ↔
      c ∈ canonicalMaskOrbitCoverage ends m j k l zero p a ∧
        c ∉ canonicalMaskOrbitCoverage ends m j k l zero p b ∧
        RowsDisconnect ends m
          (canonicalQuadrangleCompletion ends m k zero
            a.1.1 b.1.1 c.1.1) k zero := by
  classical
  simp only [canonicalCoverageExclusiveGoodQuadrangles,
    canonicalCoverageExclusive, Finset.mem_filter, Finset.mem_sdiff]
  tauto

set_option maxHeartbeats 1000000 in


noncomputable def canonicalCoverageExclusiveGoodSwap
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (a b : leftMaskFiber ends m j k l zero p)
    (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b) :
    ↥(canonicalCoverageExclusiveGoodQuadrangles
        ends m j k l zero p a b) ->
      ↥(canonicalCoverageExclusiveGoodQuadrangles
        ends m j k l zero p b a) := fun c => by
  have hc := (mem_canonicalCoverageExclusiveGoodQuadrangles_iff
    ends m j k l zero p a b c.1).mp c.2
  let d := canonicalQuadrangleCompletionMemOfDisconnects
    ends m j k l zero hloop hjk hkl p a b c.1 hc.2.2
  have hdExclusive := quadrangleCompletion_mem_coverage_sdiff
    hloop hjk hkl a b c.1 hab hc.1 hc.2.1 hc.2.2
  refine ⟨d, (mem_canonicalCoverageExclusiveGoodQuadrangles_iff
    ends m j k l zero p b a d).mpr ⟨hdExclusive.1, hdExclusive.2, ?_⟩⟩
  change RowsDisconnect ends m
    (canonicalQuadrangleCompletion ends m k zero b.1.1 a.1.1 d.1.1) k zero
  rw [show d.1.1 = canonicalQuadrangleCompletion ends m k zero
    a.1.1 b.1.1 c.1.1.1 from rfl]
  rw [canonicalQuadrangleCompletion_comm ends m k zero b.1.1 a.1.1]
  rw [canonicalQuadrangleCompletion_involutive]
  exact c.1.1.2.2.2.2.2

theorem canonicalCoverageExclusiveGoodSwap_injective
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (a b : leftMaskFiber ends m j k l zero p)
    (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b) :
    Function.Injective (canonicalCoverageExclusiveGoodSwap
      ends m j k l zero hloop hjk hkl p a b hab) := by
  intro c e hce
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  have hraw := congrArg
    (fun x : ↥(canonicalCoverageExclusiveGoodQuadrangles
        ends m j k l zero p b a) => x.1.1.1) hce
  change canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 c.1.1.1 =
    canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1 e.1.1.1 at hraw
  have hinv := congrArg
    (canonicalQuadrangleCompletion ends m k zero a.1.1 b.1.1) hraw
  simpa only [canonicalQuadrangleCompletion_involutive] using hinv



theorem card_canonicalCoverageExclusiveGoodQuadrangles_comm
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (a b : leftMaskFiber ends m j k l zero p)
    (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b) :
    #(canonicalCoverageExclusiveGoodQuadrangles
        ends m j k l zero p a b) =
      #(canonicalCoverageExclusiveGoodQuadrangles
        ends m j k l zero p b a) := by
  apply le_antisymm
  · exact Finset.card_le_card_of_injective
      (canonicalCoverageExclusiveGoodSwap_injective
        ends m j k l zero hloop hjk hkl p a b hab)
  · exact Finset.card_le_card_of_injective
      (canonicalCoverageExclusiveGoodSwap_injective
        ends m j k l zero hloop hjk hkl p b a
          (canonicalMaskTransferOrbit_symm ends m j k l zero p hab))



noncomputable def canonicalCoverageExclusiveBadQuadrangles
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (a b : leftMaskFiber ends m j k l zero p) :
    Finset (leftMaskFiber ends m j k l zero p) := by
  classical
  exact (canonicalCoverageExclusive ends m j k l zero p a b).filter fun c =>
    ¬ RowsDisconnect ends m
      (canonicalQuadrangleCompletion ends m k zero
        a.1.1 b.1.1 c.1.1) k zero

set_option maxHeartbeats 1000000 in
@[simp] theorem mem_canonicalCoverageExclusiveBadQuadrangles_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (a b c : leftMaskFiber ends m j k l zero p) :
    c ∈ canonicalCoverageExclusiveBadQuadrangles
        ends m j k l zero p a b ↔
      c ∈ canonicalMaskOrbitCoverage ends m j k l zero p a ∧
        c ∉ canonicalMaskOrbitCoverage ends m j k l zero p b ∧
        ¬ RowsDisconnect ends m
          (canonicalQuadrangleCompletion ends m k zero
            a.1.1 b.1.1 c.1.1) k zero := by
  classical
  simp only [canonicalCoverageExclusiveBadQuadrangles,
    canonicalCoverageExclusive, Finset.mem_filter, Finset.mem_sdiff]
  tauto



theorem card_good_add_bad_eq_card_coverage_sdiff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (a b : leftMaskFiber ends m j k l zero p) :
    #(canonicalCoverageExclusiveGoodQuadrangles
        ends m j k l zero p a b) +
      #(canonicalCoverageExclusiveBadQuadrangles
        ends m j k l zero p a b) =
      #(canonicalCoverageExclusive ends m j k l zero p a b) := by
  classical
  exact Finset.card_filter_add_card_filter_not
    (fun c : leftMaskFiber ends m j k l zero p =>
      RowsDisconnect ends m
        (canonicalQuadrangleCompletion ends m k zero
          a.1.1 b.1.1 c.1.1) k zero)




theorem coverage_card_add_bad_swap
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (a b : leftMaskFiber ends m j k l zero p)
    (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b) :
    #(canonicalMaskOrbitCoverage ends m j k l zero p a) +
        #(canonicalCoverageExclusiveBadQuadrangles
          ends m j k l zero p b a) =
      #(canonicalMaskOrbitCoverage ends m j k l zero p b) +
        #(canonicalCoverageExclusiveBadQuadrangles
          ends m j k l zero p a b) := by
  classical
  let A := canonicalMaskOrbitCoverage ends m j k l zero p a
  let B := canonicalMaskOrbitCoverage ends m j k l zero p b
  let GAB := canonicalCoverageExclusiveGoodQuadrangles
    ends m j k l zero p a b
  let GBA := canonicalCoverageExclusiveGoodQuadrangles
    ends m j k l zero p b a
  let DAB := canonicalCoverageExclusiveBadQuadrangles
    ends m j k l zero p a b
  let DBA := canonicalCoverageExclusiveBadQuadrangles
    ends m j k l zero p b a
  have hgood : #GAB = #GBA :=
    card_canonicalCoverageExclusiveGoodQuadrangles_comm
      ends m j k l zero hloop hjk hkl p a b hab
  have hAB : #GAB + #DAB = #(A \ B) := by
    simpa only [canonicalCoverageExclusive] using
      card_good_add_bad_eq_card_coverage_sdiff
        ends m j k l zero p a b
  have hBA : #GBA + #DBA = #(B \ A) := by
    simpa only [canonicalCoverageExclusive] using
      card_good_add_bad_eq_card_coverage_sdiff
        ends m j k l zero p b a
  have hA := Finset.card_sdiff_add_card_inter A B
  have hB := Finset.card_sdiff_add_card_inter B A
  have hinter : #(A ∩ B) = #(B ∩ A) := by rw [Finset.inter_comm]
  change #A + #DBA = #B + #DAB
  omega



theorem coverage_card_lt_of_mem_bad_of_opposite_bad_eq_empty
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l)
    (p : Finset I × Finset I)
    (a b c : leftMaskFiber ends m j k l zero p)
    (hab : CanonicalMaskTransferOrbit ends m j k l zero p a b)
    (hc : c ∈ canonicalCoverageExclusiveBadQuadrangles
      ends m j k l zero p a b)
    (hopposite : canonicalCoverageExclusiveBadQuadrangles
      ends m j k l zero p b a = ∅) :
    #(canonicalMaskOrbitCoverage ends m j k l zero p b) <
      #(canonicalMaskOrbitCoverage ends m j k l zero p a) := by
  have hbalance := coverage_card_add_bad_swap
    ends m j k l zero hloop hjk hkl p a b hab
  have hbadPos : 0 < #(canonicalCoverageExclusiveBadQuadrangles
      ends m j k l zero p a b) :=
    Finset.card_pos.mpr ⟨c, hc⟩
  rw [hopposite, Finset.card_empty, Nat.add_zero] at hbalance
  omega

end StatMech.GrahamGHS.FourColor
