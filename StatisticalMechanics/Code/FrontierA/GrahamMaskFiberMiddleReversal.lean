/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamCanonicalTransferAmbientQuadrangle
import Code.FrontierA.GrahamCanonicalCollisionSquare
import Code.FrontierA.GrahamCanonicalEdgeDegreeHall
import Code.FrontierA.GrahamCanonicalTransferMatching
import Code.FrontierA.GrahamGateDiscrepancy










open Finset
open scoped symmDiff

namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


def RightSourcePattern (ends : I -> Sym2 W) (m : Finset I)
    (A B : Finset W) (c : ↑m -> Fin 4) : Prop :=
  sources ends (colorClass m c 0) = A ∧
    sources ends (colorClass m c 1) = B ∧
    sources ends (colorClass m c 2) = ∅ ∧
    sources ends (colorClass m c 3) = ∅



def rightSourceMaskFiber (ends : I -> Sym2 W) (m : Finset I)
    (j k l zero : W) (p : Finset I × Finset I) :=
  {c : ↑m -> Fin 4 //
    RightSourcePattern ends m {j, k} {k, l} c ∧
      fourColorMaskProfile m c = p}

noncomputable instance instFintypeRightSourceMaskFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Fintype (rightSourceMaskFiber ends m j k l zero p) := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective


theorem fourColorMaskProfile_middleSwap
    (m : Finset I) (c : ↑m -> Fin 4) :
    fourColorMaskProfile m (middleSwap m c) =
      fourColorMaskProfile m c := by
  apply Prod.ext
  · simp [fourColorMaskProfile, middleMask, colorClass_middleSwap,
      Equiv.swap_apply_def, Finset.union_comm]
  · simp [fourColorMaskProfile, outerMask, colorClass_middleSwap,
      Equiv.swap_apply_def]



theorem rowClass_middleSwap_zero_eq_symmDiff_middleMask
    (m : Finset I) (c : ↑m -> Fin 4) :
    rowClass m (middleSwap m c) 0 =
      rowClass m c 0 ∆ middleMask m c := by
  ext i
  by_cases hi : i ∈ m
  · obtain ⟨a, ha⟩ : ∃ a : ↑m, (a : I) = i :=
      ⟨⟨i, hi⟩, rfl⟩
    subst i
    have hc : c a = 0 ∨ c a = 1 ∨ c a = 2 ∨ c a = 3 := by omega
    rcases hc with hc | hc | hc | hc <;>
      simp [rowClass_zero, middleMask, colorClass_middleSwap,
        Equiv.swap_apply_def, subtype_mem_colorClass_iff, hc,
        Finset.mem_symmDiff]
  · have hclasses : ∀ b : Fin 4, i ∉ colorClass m c b := by
      intro b hib
      exact hi (colorClass_subset m c b hib)
    have hswapclasses : ∀ b : Fin 4,
        i ∉ colorClass m (middleSwap m c) b := by
      intro b hib
      exact hi (colorClass_subset m (middleSwap m c) b hib)
    simp [rowClass_zero, middleMask, hclasses, hswapclasses,
      Finset.mem_symmDiff]



theorem rightSourcePattern_middleSwap_iff_leftSourcePattern
    (ends : I -> Sym2 W) (m : Finset I) (A B : Finset W)
    (c : ↑m -> Fin 4) :
    RightSourcePattern ends m A B (middleSwap m c) ↔
      LeftSourcePattern ends m A B c := by
  simp [RightSourcePattern, LeftSourcePattern, colorClass_middleSwap,
    Equiv.swap_apply_def] <;> tauto



theorem leftSourcePattern_middleSwap_iff_rightSourcePattern
    (ends : I -> Sym2 W) (m : Finset I) (A B : Finset W)
    (c : ↑m -> Fin 4) :
    LeftSourcePattern ends m A B (middleSwap m c) ↔
      RightSourcePattern ends m A B c := by
  simp [RightSourcePattern, LeftSourcePattern, colorClass_middleSwap,
    Equiv.swap_apply_def] <;> tauto


noncomputable def sourceMaskMiddleReversalEquiv
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    leftSourceMaskFiber ends m j k l zero p ≃
      rightSourceMaskFiber ends m j k l zero p where
  toFun c := ⟨middleSwap m c.1, ⟨
    (rightSourcePattern_middleSwap_iff_leftSourcePattern
      ends m {j, k} {k, l} c.1).2 c.2.1,
    (fourColorMaskProfile_middleSwap m c.1).trans c.2.2⟩⟩
  invFun c := ⟨middleSwap m c.1, ⟨
    (leftSourcePattern_middleSwap_iff_rightSourcePattern
      ends m {j, k} {k, l} c.1).2 c.2.1,
    (fourColorMaskProfile_middleSwap m c.1).trans c.2.2⟩⟩
  left_inv c := by
    apply Subtype.ext
    exact middleSwap_involutive m c.1
  right_inv c := by
    apply Subtype.ext
    exact middleSwap_involutive m c.1



theorem card_leftSourceMaskFiber_eq_rightSourceMaskFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Fintype.card (leftSourceMaskFiber ends m j k l zero p) =
      Fintype.card (rightSourceMaskFiber ends m j k l zero p) :=
  Fintype.card_congr
    (sourceMaskMiddleReversalEquiv ends m j k l zero p)


def leftSourceMaskGateFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :=
  {c : leftSourceMaskFiber ends m j k l zero p //
    RowsDisconnect ends m c.1 k zero}



def reversedRightSourceMaskGateFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :=
  {c : leftSourceMaskFiber ends m j k l zero p //
    RowsDisconnect ends m (middleSwap m c.1) k zero}

noncomputable instance instFintypeLeftSourceMaskGateFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Fintype (leftSourceMaskGateFiber ends m j k l zero p) := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable instance instFintypeReversedRightSourceMaskGateFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Fintype (reversedRightSourceMaskGateFiber ends m j k l zero p) := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective



noncomputable def reversalGateBalance
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p) : ℤ :=
  by
    classical
    exact
      (if RowsDisconnect ends m (middleSwap m c.1) k zero then 1 else 0) -
        if RowsDisconnect ends m c.1 k zero then 1 else 0


def BipartitionDisconnects
    (ends : I -> Sym2 W) (m E : Finset I) (u v : W) : Prop :=
  ¬ connK ends E u v ∧ ¬ connK ends (m \ E) u v


noncomputable def bipartitionDisconnectIndicator
    (ends : I -> Sym2 W) (m E : Finset I) (u v : W) : ℤ := by
  classical
  exact if BipartitionDisconnects ends m E u v then 1 else 0

theorem rowsDisconnect_iff_bipartitionDisconnects
    (ends : I -> Sym2 W) (m : Finset I) (c : ↑m -> Fin 4)
    (u v : W) :
    RowsDisconnect ends m c u v ↔
      BipartitionDisconnects ends m (rowClass m c 0) u v := by
  rw [RowsDisconnect, BipartitionDisconnects, rowClass_one_eq_sdiff]



theorem reversalGateBalance_eq_bipartitionIndicators
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p) :
    reversalGateBalance ends m j k l zero p c =
      bipartitionDisconnectIndicator ends m
          (rowClass m c.1 0 ∆ p.1) k zero -
        bipartitionDisconnectIndicator ends m (rowClass m c.1 0) k zero := by
  classical
  unfold reversalGateBalance bipartitionDisconnectIndicator
  rw [rowsDisconnect_iff_bipartitionDisconnects,
    rowsDisconnect_iff_bipartitionDisconnects,
    rowClass_middleSwap_zero_eq_symmDiff_middleMask,
    show middleMask m c.1 = p.1 from congrArg Prod.fst c.2.2]



noncomputable def sourceMaskCycleTranslationEquiv
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) (X Y : Finset I)
    (hX : X ⊆ p.1) (hY : Y ⊆ p.2)
    (hsrcX : sources ends X = ∅) (hsrcY : sources ends Y = ∅) :
    leftSourceMaskFiber ends m j k l zero p ≃
      leftSourceMaskFiber ends m j k l zero p where
  toFun c := by
    have hmiddle : middleMask m c.1 = p.1 :=
      congrArg Prod.fst c.2.2
    have houter : outerMask m c.1 = p.2 :=
      congrArg Prod.snd c.2.2
    have hXc : X ⊆ colorClass m c.1 1 ∪ colorClass m c.1 2 := by
      change X ⊆ middleMask m c.1
      rw [hmiddle]
      exact hX
    have hYc : Y ⊆ colorClass m c.1 0 ∪ colorClass m c.1 3 := by
      change Y ⊆ outerMask m c.1
      rw [houter]
      exact hY
    exact ⟨balancedSwap m X Y c.1, ⟨
      leftSourcePattern_of_sourceless_balancedSwap c.2.1
        hXc hYc hsrcX hsrcY,
      (fourColorMaskProfile_balancedSwap m X Y c.1).trans c.2.2⟩⟩
  invFun c := by
    have hmiddle : middleMask m c.1 = p.1 :=
      congrArg Prod.fst c.2.2
    have houter : outerMask m c.1 = p.2 :=
      congrArg Prod.snd c.2.2
    have hXc : X ⊆ colorClass m c.1 1 ∪ colorClass m c.1 2 := by
      change X ⊆ middleMask m c.1
      rw [hmiddle]
      exact hX
    have hYc : Y ⊆ colorClass m c.1 0 ∪ colorClass m c.1 3 := by
      change Y ⊆ outerMask m c.1
      rw [houter]
      exact hY
    exact ⟨balancedSwap m X Y c.1, ⟨
      leftSourcePattern_of_sourceless_balancedSwap c.2.1
        hXc hYc hsrcX hsrcY,
      (fourColorMaskProfile_balancedSwap m X Y c.1).trans c.2.2⟩⟩
  left_inv c := by
    apply Subtype.ext
    exact balancedSwap_involutive m X Y c.1
  right_inv c := by
    apply Subtype.ext
    exact balancedSwap_involutive m X Y c.1


noncomputable def outerCycleSourceMaskEquiv
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) (Y : Finset I)
    (hY : Y ⊆ p.2) (hsrcY : sources ends Y = ∅) :
    leftSourceMaskFiber ends m j k l zero p ≃
      leftSourceMaskFiber ends m j k l zero p :=
  sourceMaskCycleTranslationEquiv ends m j k l zero p ∅ Y
    (by simp) hY (by simp [sources, degK]) hsrcY


abbrev sourceMaskCycleSpace
    (ends : I -> Sym2 W) (p : Finset I × Finset I) :=
  boundarySector ends p.1 ∅ × boundarySector ends p.2 ∅


noncomputable def sourceMaskCycleAction
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p)
    (z : sourceMaskCycleSpace ends p) :
    leftSourceMaskFiber ends m j k l zero p :=
  sourceMaskCycleTranslationEquiv ends m j k l zero p z.1.1 z.2.1
    z.1.2.1 z.2.2.1 z.1.2.2 z.2.2.2 c



theorem exists_sourceMaskCycleAction_eq
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftSourceMaskFiber ends m j k l zero p) :
    ∃ z : sourceMaskCycleSpace ends p,
      sourceMaskCycleAction ends m j k l zero p c z = d := by
  let X := balancedMiddleDifference m c.1 d.1
  let Y := balancedOuterDifference m c.1 d.1
  have hprofile : fourColorMaskProfile m c.1 =
      fourColorMaskProfile m d.1 := c.2.2.trans d.2.2.symm
  have hmid : middleMask m c.1 = middleMask m d.1 :=
    congrArg Prod.fst hprofile
  have hout : outerMask m c.1 = outerMask m d.1 :=
    congrArg Prod.snd hprofile
  have hXsub : X ⊆ p.1 := by
    have h := balancedMiddleDifference_subset m c.1 d.1 hmid
    rw [show middleMask m c.1 = p.1 from congrArg Prod.fst c.2.2] at h
    exact h
  have hYsub : Y ⊆ p.2 := by
    have h := balancedOuterDifference_subset m c.1 d.1 hout
    rw [show outerMask m c.1 = p.2 from congrArg Prod.snd c.2.2] at h
    exact h
  have hXsrc : sources ends X = ∅ := by
    dsimp only [X]
    rw [balancedMiddleDifference, sources_symmDiff,
      c.2.1.2.1, d.2.1.2.1, symmDiff_self]
    simp
  have hYsrc : sources ends Y = ∅ := by
    dsimp only [Y]
    rw [balancedOuterDifference, sources_symmDiff,
      c.2.1.1, d.2.1.1, symmDiff_self]
    simp
  let z : sourceMaskCycleSpace ends p :=
    (⟨X, hXsub, hXsrc⟩, ⟨Y, hYsub, hYsrc⟩)
  refine ⟨z, ?_⟩
  apply Subtype.ext
  exact balancedSwap_difference m c.1 d.1 hmid hout


noncomputable def sourceMaskCycleDifference
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftSourceMaskFiber ends m j k l zero p) :
    sourceMaskCycleSpace ends p := by
  let X := balancedMiddleDifference m c.1 d.1
  let Y := balancedOuterDifference m c.1 d.1
  have hprofile : fourColorMaskProfile m c.1 =
      fourColorMaskProfile m d.1 := c.2.2.trans d.2.2.symm
  have hmid : middleMask m c.1 = middleMask m d.1 :=
    congrArg Prod.fst hprofile
  have hout : outerMask m c.1 = outerMask m d.1 :=
    congrArg Prod.snd hprofile
  have hXsub : X ⊆ p.1 := by
    have h := balancedMiddleDifference_subset m c.1 d.1 hmid
    rw [show middleMask m c.1 = p.1 from congrArg Prod.fst c.2.2] at h
    exact h
  have hYsub : Y ⊆ p.2 := by
    have h := balancedOuterDifference_subset m c.1 d.1 hout
    rw [show outerMask m c.1 = p.2 from congrArg Prod.snd c.2.2] at h
    exact h
  have hXsrc : sources ends X = ∅ := by
    dsimp only [X]
    rw [balancedMiddleDifference, sources_symmDiff,
      c.2.1.2.1, d.2.1.2.1, symmDiff_self]
    simp
  have hYsrc : sources ends Y = ∅ := by
    dsimp only [Y]
    rw [balancedOuterDifference, sources_symmDiff,
      c.2.1.1, d.2.1.1, symmDiff_self]
    simp
  exact (⟨X, hXsub, hXsrc⟩, ⟨Y, hYsub, hYsrc⟩)

theorem sourceMaskCycleAction_difference
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftSourceMaskFiber ends m j k l zero p) :
    sourceMaskCycleAction ends m j k l zero p c
      (sourceMaskCycleDifference ends m j k l zero p c d) = d := by
  apply Subtype.ext
  exact balancedSwap_difference m c.1 d.1
    (congrArg Prod.fst (c.2.2.trans d.2.2.symm))
    (congrArg Prod.snd (c.2.2.trans d.2.2.symm))


theorem sourceMaskCycleAction_injective
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p) :
    Function.Injective (sourceMaskCycleAction ends m j k l zero p c) := by
  intro z z' hzz'
  have hfun := congrArg Subtype.val hzz'
  have hmidc : middleMask m c.1 = p.1 := congrArg Prod.fst c.2.2
  have houtc : outerMask m c.1 = p.2 := congrArg Prod.snd c.2.2
  have hXc : z.1.1 ⊆ colorClass m c.1 1 ∪ colorClass m c.1 2 := by
    change z.1.1 ⊆ middleMask m c.1
    rw [hmidc]
    exact z.1.2.1
  have hXc' : z'.1.1 ⊆ colorClass m c.1 1 ∪ colorClass m c.1 2 := by
    change z'.1.1 ⊆ middleMask m c.1
    rw [hmidc]
    exact z'.1.2.1
  have hYc : z.2.1 ⊆ colorClass m c.1 0 ∪ colorClass m c.1 3 := by
    change z.2.1 ⊆ outerMask m c.1
    rw [houtc]
    exact z.2.2.1
  have hYc' : z'.2.1 ⊆ colorClass m c.1 0 ∪ colorClass m c.1 3 := by
    change z'.2.1 ⊆ outerMask m c.1
    rw [houtc]
    exact z'.2.2.1
  have hYafter : z.2.1 ⊆
      colorClass m (middleSwapOn m z.1.1 c.1) 0 ∪
        colorClass m (middleSwapOn m z.1.1 c.1) 3 := by
    rwa [colorClass_middleSwapOn_zero, colorClass_middleSwapOn_three]
  have hYafter' : z'.2.1 ⊆
      colorClass m (middleSwapOn m z'.1.1 c.1) 0 ∪
        colorClass m (middleSwapOn m z'.1.1 c.1) 3 := by
    rwa [colorClass_middleSwapOn_zero, colorClass_middleSwapOn_three]
  have htwo := congrArg (fun q => colorClass m q 2) hfun
  have hzero := congrArg (fun q => colorClass m q 0) hfun
  change balancedSwap m z.1.1 z.2.1 c.1 =
    balancedSwap m z'.1.1 z'.2.1 c.1 at hfun
  change colorClass m (balancedSwap m z.1.1 z.2.1 c.1) 2 =
    colorClass m (balancedSwap m z'.1.1 z'.2.1 c.1) 2 at htwo
  change colorClass m (balancedSwap m z.1.1 z.2.1 c.1) 0 =
    colorClass m (balancedSwap m z'.1.1 z'.2.1 c.1) 0 at hzero
  unfold balancedSwap at htwo hzero
  rw [colorClass_outerSwapOn_two,
    colorClass_middleSwapOn_two m z.1.1 c.1 hXc,
    colorClass_outerSwapOn_two,
    colorClass_middleSwapOn_two m z'.1.1 c.1 hXc'] at htwo
  rw [colorClass_outerSwapOn_zero m z.2.1 _ hYafter,
    colorClass_middleSwapOn_zero,
    colorClass_outerSwapOn_zero m z'.2.1 _ hYafter',
    colorClass_middleSwapOn_zero] at hzero
  apply Prod.ext
  · apply Subtype.ext
    exact (symmDiff_right_injective (colorClass m c.1 2)) htwo
  · apply Subtype.ext
    exact (symmDiff_right_injective (colorClass m c.1 0)) hzero



noncomputable def sourceMaskCycleTorsorEquiv
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p) :
    sourceMaskCycleSpace ends p ≃
      leftSourceMaskFiber ends m j k l zero p :=
  Equiv.ofBijective (sourceMaskCycleAction ends m j k l zero p c)
    ⟨sourceMaskCycleAction_injective ends m j k l zero p c,
      fun d => exists_sourceMaskCycleAction_eq ends m j k l zero p c d⟩



theorem rowClass_sourceMaskCycleAction_zero
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p)
    (z : sourceMaskCycleSpace ends p) :
    rowClass m (sourceMaskCycleAction ends m j k l zero p c z).1 0 =
      rowClass m c.1 0 ∆ (z.1.1 ∪ z.2.1) := by
  have hmidc : middleMask m c.1 = p.1 := congrArg Prod.fst c.2.2
  have houtc : outerMask m c.1 = p.2 := congrArg Prod.snd c.2.2
  have hXc : z.1.1 ⊆ colorClass m c.1 1 ∪ colorClass m c.1 2 := by
    change z.1.1 ⊆ middleMask m c.1
    rw [hmidc]
    exact z.1.2.1
  have hYc : z.2.1 ⊆ colorClass m c.1 0 ∪ colorClass m c.1 3 := by
    change z.2.1 ⊆ outerMask m c.1
    rw [houtc]
    exact z.2.2.1
  change rowClass m (balancedSwap m z.1.1 z.2.1 c.1) 0 = _
  exact rowClass_balancedSwap_zero hXc hYc



theorem sourceMaskCycleAction_involutive
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (z : sourceMaskCycleSpace ends p)
    (c : leftSourceMaskFiber ends m j k l zero p) :
    sourceMaskCycleAction ends m j k l zero p
        (sourceMaskCycleAction ends m j k l zero p c z) z = c := by
  apply Subtype.ext
  exact balancedSwap_involutive m z.1.1 z.2.1 c.1


def ReversalGateNegative
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p) : Prop :=
  RowsDisconnect ends m c.1 k zero ∧
    ¬ RowsDisconnect ends m (middleSwap m c.1) k zero


def ReversalGatePositive
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p) : Prop :=
  ¬ RowsDisconnect ends m c.1 k zero ∧
    RowsDisconnect ends m (middleSwap m c.1) k zero



def CycleTranslationCoversNegative
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) (z : sourceMaskCycleSpace ends p) : Prop :=
  ∀ c : leftSourceMaskFiber ends m j k l zero p,
    ReversalGateNegative ends m j k l zero p c ->
      ReversalGatePositive ends m j k l zero p
        (sourceMaskCycleAction ends m j k l zero p c z)



theorem cycleTranslation_pairBalance_nonneg_of_coversNegative
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) (z : sourceMaskCycleSpace ends p)
    (hcovers : CycleTranslationCoversNegative ends m j k l zero p z)
    (c : leftSourceMaskFiber ends m j k l zero p) :
    0 ≤ reversalGateBalance ends m j k l zero p c +
      reversalGateBalance ends m j k l zero p
        (sourceMaskCycleAction ends m j k l zero p c z) := by
  let d := sourceMaskCycleAction ends m j k l zero p c z
  have hdc : sourceMaskCycleAction ends m j k l zero p d z = c :=
    sourceMaskCycleAction_involutive ends m j k l zero p z c
  change 0 ≤ reversalGateBalance ends m j k l zero p c +
    reversalGateBalance ends m j k l zero p d
  have nonneg_of_not_negative : ∀ q :
      leftSourceMaskFiber ends m j k l zero p,
      ¬ ReversalGateNegative ends m j k l zero p q ->
        0 ≤ reversalGateBalance ends m j k l zero p q := by
    intro q hq
    classical
    by_cases hL : RowsDisconnect ends m q.1 k zero
    · by_cases hR : RowsDisconnect ends m (middleSwap m q.1) k zero
      · simp [reversalGateBalance, hL, hR]
      · exact (hq ⟨hL, hR⟩).elim
    · by_cases hR : RowsDisconnect ends m (middleSwap m q.1) k zero <;>
        simp [reversalGateBalance, hL, hR]
  by_cases hcn : ReversalGateNegative ends m j k l zero p c
  · have hdp := hcovers c hcn
    rcases hcn with ⟨hLc, hRc⟩
    rcases hdp with ⟨hLd, hRd⟩
    change ¬ RowsDisconnect ends m d.1 k zero at hLd
    change RowsDisconnect ends m (middleSwap m d.1) k zero at hRd
    simp [reversalGateBalance, hLc, hRc, hLd, hRd]
  · by_cases hdn : ReversalGateNegative ends m j k l zero p d
    · have hcp := hcovers d hdn
      rw [hdc] at hcp
      rcases hdn with ⟨hLd, hRd⟩
      rcases hcp with ⟨hLc, hRc⟩
      simp [reversalGateBalance, hLc, hRc, hLd, hRd]
    · exact add_nonneg
        (nonneg_of_not_negative c hcn)
        (nonneg_of_not_negative d hdn)


theorem sum_reversalGateBalance_eq_cycleCutCorrelation
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c₀ : leftSourceMaskFiber ends m j k l zero p) :
    (∑ c : leftSourceMaskFiber ends m j k l zero p,
        reversalGateBalance ends m j k l zero p c) =
      ∑ z : sourceMaskCycleSpace ends p,
        (bipartitionDisconnectIndicator ends m
            ((rowClass m c₀.1 0 ∆ (z.1.1 ∪ z.2.1)) ∆ p.1) k zero -
          bipartitionDisconnectIndicator ends m
            (rowClass m c₀.1 0 ∆ (z.1.1 ∪ z.2.1)) k zero) := by
  let e := sourceMaskCycleTorsorEquiv ends m j k l zero p c₀
  calc
    _ = ∑ z : sourceMaskCycleSpace ends p,
        reversalGateBalance ends m j k l zero p (e z) := by
      symm
      apply Fintype.sum_equiv e
      intro z
      rfl
    _ = _ := by
      apply Finset.sum_congr rfl
      intro z _
      rw [reversalGateBalance_eq_bipartitionIndicators]
      have he : e z =
          sourceMaskCycleAction ends m j k l zero p c₀ z := by rfl
      rw [he,
        rowClass_sourceMaskCycleAction_zero]

private theorem sum_prop_indicator_eq_card_subtype
    {X : Type*} [Fintype X] (P : X -> Prop) [DecidablePred P]
    [Fintype {x : X // P x}] :
    (∑ x : X, if P x then (1 : ℤ) else 0) =
      Fintype.card {x : X // P x} := by
  rw [Fintype.card_subtype]
  simp



theorem sum_reversalGateBalance_eq_card_sub
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    (∑ c : leftSourceMaskFiber ends m j k l zero p,
        reversalGateBalance ends m j k l zero p c) =
      (Fintype.card
          (reversedRightSourceMaskGateFiber ends m j k l zero p) : ℤ) -
        Fintype.card (leftSourceMaskGateFiber ends m j k l zero p) := by
  classical
  rw [show (∑ c : leftSourceMaskFiber ends m j k l zero p,
        reversalGateBalance ends m j k l zero p c) =
      (∑ c : leftSourceMaskFiber ends m j k l zero p,
        if RowsDisconnect ends m (middleSwap m c.1) k zero
          then (1 : ℤ) else 0) -
        ∑ c : leftSourceMaskFiber ends m j k l zero p,
          if RowsDisconnect ends m c.1 k zero then (1 : ℤ) else 0 by
      simp [reversalGateBalance, Finset.sum_sub_distrib]]
  rw [sum_prop_indicator_eq_card_subtype,
    sum_prop_indicator_eq_card_subtype]
  have hright :
      Fintype.card
          {c : leftSourceMaskFiber ends m j k l zero p //
            RowsDisconnect ends m (middleSwap m c.1) k zero} =
        Fintype.card
          (reversedRightSourceMaskGateFiber ends m j k l zero p) :=
    Fintype.card_congr (Equiv.refl _)
  have hleft :
      Fintype.card
          {c : leftSourceMaskFiber ends m j k l zero p //
            RowsDisconnect ends m c.1 k zero} =
        Fintype.card (leftSourceMaskGateFiber ends m j k l zero p) :=
    Fintype.card_congr (Equiv.refl _)
  rw [hright, hleft]



theorem sum_reversalGateBalance_nonneg_of_equivPairs
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (e : leftSourceMaskFiber ends m j k l zero p ≃
      leftSourceMaskFiber ends m j k l zero p)
    (hpairs : ∀ c : leftSourceMaskFiber ends m j k l zero p,
      0 ≤ reversalGateBalance ends m j k l zero p c +
        reversalGateBalance ends m j k l zero p
          (e c)) :
    0 ≤ ∑ c : leftSourceMaskFiber ends m j k l zero p,
      reversalGateBalance ends m j k l zero p c := by
  have hreindex :
      (∑ c : leftSourceMaskFiber ends m j k l zero p,
        reversalGateBalance ends m j k l zero p (e c)) =
      ∑ c : leftSourceMaskFiber ends m j k l zero p,
        reversalGateBalance ends m j k l zero p c := by
    apply Fintype.sum_equiv e
    intro c
    rfl
  have hsum :
      0 ≤ ∑ c : leftSourceMaskFiber ends m j k l zero p,
        (reversalGateBalance ends m j k l zero p c +
          reversalGateBalance ends m j k l zero p (e c)) :=
    Finset.sum_nonneg fun c _ => hpairs c
  rw [Finset.sum_add_distrib, hreindex] at hsum
  omega



theorem sum_reversalGateBalance_nonneg_of_cycleTranslationPairs
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) (X Y : Finset I)
    (hX : X ⊆ p.1) (hY : Y ⊆ p.2)
    (hsrcX : sources ends X = ∅) (hsrcY : sources ends Y = ∅)
    (hpairs : ∀ c : leftSourceMaskFiber ends m j k l zero p,
      0 ≤ reversalGateBalance ends m j k l zero p c +
        reversalGateBalance ends m j k l zero p
          (sourceMaskCycleTranslationEquiv ends m j k l zero p X Y
            hX hY hsrcX hsrcY c)) :
    0 ≤ ∑ c : leftSourceMaskFiber ends m j k l zero p,
      reversalGateBalance ends m j k l zero p c :=
  sum_reversalGateBalance_nonneg_of_equivPairs ends m j k l zero p
    (sourceMaskCycleTranslationEquiv ends m j k l zero p X Y
      hX hY hsrcX hsrcY) hpairs



theorem sum_reversalGateBalance_nonneg_of_exists_cycleTranslationCover
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hcover : ∃ z : sourceMaskCycleSpace ends p,
      CycleTranslationCoversNegative ends m j k l zero p z) :
    0 ≤ ∑ c : leftSourceMaskFiber ends m j k l zero p,
      reversalGateBalance ends m j k l zero p c := by
  obtain ⟨z, hz⟩ := hcover
  apply sum_reversalGateBalance_nonneg_of_cycleTranslationPairs
    ends m j k l zero p z.1.1 z.2.1
    z.1.2.1 z.2.2.1 z.1.2.2 z.2.2.2
  intro c
  simpa only [sourceMaskCycleAction] using
    cycleTranslation_pairBalance_nonneg_of_coversNegative
      ends m j k l zero p z hz c


theorem sum_reversalGateBalance_nonneg_of_outerCyclePairs
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) (Y : Finset I)
    (hY : Y ⊆ p.2) (hsrcY : sources ends Y = ∅)
    (hpairs : ∀ c : leftSourceMaskFiber ends m j k l zero p,
      0 ≤ reversalGateBalance ends m j k l zero p c +
        reversalGateBalance ends m j k l zero p
          (outerCycleSourceMaskEquiv ends m j k l zero p Y hY hsrcY c)) :
    0 ≤ ∑ c : leftSourceMaskFiber ends m j k l zero p,
      reversalGateBalance ends m j k l zero p c :=
  sum_reversalGateBalance_nonneg_of_equivPairs ends m j k l zero p
    (outerCycleSourceMaskEquiv ends m j k l zero p Y hY hsrcY) hpairs



noncomputable def leftMaskFiberEquivSourceMaskGateFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    leftMaskFiber ends m j k l zero p ≃
      leftSourceMaskGateFiber ends m j k l zero p where
  toFun c := ⟨leftMaskFiberToSourceMaskFiber
      ends m j k l zero p c, c.1.2.2.2.2.2⟩
  invFun c := ⟨⟨c.1.1, ⟨c.1.2.1.1, c.1.2.1.2.1,
      c.1.2.1.2.2.1, c.1.2.1.2.2.2, c.2⟩⟩, c.1.2.2⟩
  left_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  right_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    rfl



noncomputable def rightMaskFiberEquivReversedSourceMaskGateFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    rightMaskFiber ends m j k l zero p ≃
      reversedRightSourceMaskGateFiber ends m j k l zero p where
  toFun q := ⟨⟨middleSwap m q.1.1, ⟨
      (leftSourcePattern_middleSwap_iff_rightSourcePattern
        ends m {j, k} {k, l} q.1.1).2
          ⟨q.1.2.1, q.1.2.2.1, q.1.2.2.2.1, q.1.2.2.2.2.1⟩,
      (fourColorMaskProfile_middleSwap m q.1.1).trans q.2⟩⟩, by
    simpa only [middleSwap_involutive] using q.1.2.2.2.2.2⟩
  invFun c := by
    have hs : RightSourcePattern ends m {j, k} {k, l}
        (middleSwap m c.1.1) :=
      (rightSourcePattern_middleSwap_iff_leftSourcePattern
        ends m {j, k} {k, l} c.1.1).2 c.1.2.1
    exact ⟨⟨middleSwap m c.1.1,
      ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, c.2⟩⟩,
      (fourColorMaskProfile_middleSwap m c.1.1).trans c.1.2.2⟩
  left_inv q := by
    apply Subtype.ext
    apply Subtype.ext
    exact middleSwap_involutive m q.1.1
  right_inv c := by
    apply Subtype.ext
    apply Subtype.ext
    exact middleSwap_involutive m c.1.1


def sourceMaskGatePointToLeftMaskFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p)
    (hdisc : RowsDisconnect ends m c.1 k zero) :
    leftMaskFiber ends m j k l zero p :=
  ⟨⟨c.1, ⟨c.2.1.1, c.2.1.2.1, c.2.1.2.2.1,
    c.2.1.2.2.2, hdisc⟩⟩, c.2.2⟩




noncomputable def canonicalReferenceReturnRaw
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (r c : ↑m -> Fin 4) : ↑m -> Fin 4 :=
  middleSwap m
    (balancedSwap m
      (canonicalMiddleTransfer ends m r k zero)
      (canonicalOuterTransfer ends m r k zero) c)


theorem canonicalReferenceReturnRaw_involutive
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (r c : ↑m -> Fin 4) :
    canonicalReferenceReturnRaw ends m k zero r
        (canonicalReferenceReturnRaw ends m k zero r c) = c := by
  unfold canonicalReferenceReturnRaw
  rw [canonicalTransfer_oppositeReturn_eq_middleSwap]
  exact middleSwap_involutive m c



theorem canonicalReferenceReturnRaw_eq_iff
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (r c d : ↑m -> Fin 4) :
    canonicalReferenceReturnRaw ends m k zero r c = d ↔
      canonicalReferenceReturnRaw ends m k zero r d = c := by
  constructor <;> intro h
  · rw [← h, canonicalReferenceReturnRaw_involutive]
  · rw [← h, canonicalReferenceReturnRaw_involutive]


noncomputable def canonicalSelfRightPointOfSourceGate
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p)
    (hdisc : RowsDisconnect ends m c.1 k zero) :
    rightMaskFiber ends m j k l zero p := by
  let a := sourceMaskGatePointToLeftMaskFiber ends m j k l zero p c hdisc
  exact canonicalTransferMapOfWorks ends m j k l zero
    hloop hjk hkl p a a
      (canonicalTransferWorks_self hloop hjk hkl hk0 a)



noncomputable def canonicalSelfPulledSourcePoint
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p)
    (hdisc : RowsDisconnect ends m c.1 k zero) :
    leftSourceMaskFiber ends m j k l zero p :=
  (rightMaskFiberEquivReversedSourceMaskGateFiber ends m j k l zero p
    (canonicalSelfRightPointOfSourceGate ends m j k l zero
      hloop hjk hkl hk0 p c hdisc)).1

theorem canonicalSelfPulledSourcePoint_val_eq_referenceReturn
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p)
    (hdisc : RowsDisconnect ends m c.1 k zero) :
    (canonicalSelfPulledSourcePoint ends m j k l zero
        hloop hjk hkl hk0 p c hdisc).1 =
      canonicalReferenceReturnRaw ends m k zero c.1 c.1 := by
  rfl




theorem canonicalSelfPulledSourcePoint_reference_fails_of_negative
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p)
    (hneg : ReversalGateNegative ends m j k l zero p c) :
    ¬ CanonicalTransferWorks ends m k zero c.1
      (canonicalSelfPulledSourcePoint ends m j k l zero
        hloop hjk hkl hk0 p c hneg.1).1 := by
  rw [canonicalSelfPulledSourcePoint_val_eq_referenceReturn]
  unfold canonicalReferenceReturnRaw
  exact ((canonicalTransferWorks_oppositeReturn_iff
    ends m k zero c.1 c.1).not.mpr hneg.2)


theorem canonicalSelfPulledSourcePoint_rightGate
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p)
    (hdisc : RowsDisconnect ends m c.1 k zero) :
    RowsDisconnect ends m
      (middleSwap m (canonicalSelfPulledSourcePoint ends m j k l zero
        hloop hjk hkl hk0 p c hdisc).1) k zero :=
  (rightMaskFiberEquivReversedSourceMaskGateFiber ends m j k l zero p
    (canonicalSelfRightPointOfSourceGate ends m j k l zero
      hloop hjk hkl hk0 p c hdisc)).2



noncomputable def canonicalSelfPullbackCycleCandidate
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p)
    (hdisc : RowsDisconnect ends m c.1 k zero) :
    sourceMaskCycleSpace ends p :=
  sourceMaskCycleDifference ends m j k l zero p c
    (canonicalSelfPulledSourcePoint ends m j k l zero
      hloop hjk hkl hk0 p c hdisc)

theorem canonicalSelfPullbackCycleCandidate_maps_base
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p)
    (hdisc : RowsDisconnect ends m c.1 k zero) :
    sourceMaskCycleAction ends m j k l zero p c
        (canonicalSelfPullbackCycleCandidate ends m j k l zero
          hloop hjk hkl hk0 p c hdisc) =
      canonicalSelfPulledSourcePoint ends m j k l zero
        hloop hjk hkl hk0 p c hdisc :=
  sourceMaskCycleAction_difference ends m j k l zero p c _


def negativeReversalGateFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :=
  {c : leftSourceMaskFiber ends m j k l zero p //
    ReversalGateNegative ends m j k l zero p c}


def positiveReversalGateFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :=
  {c : leftSourceMaskFiber ends m j k l zero p //
    ReversalGatePositive ends m j k l zero p c}

noncomputable instance instFintypeNegativeReversalGateFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Fintype (negativeReversalGateFiber ends m j k l zero p) := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable instance instFintypePositiveReversalGateFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Fintype (positiveReversalGateFiber ends m j k l zero p) := by
  classical
  exact Fintype.ofInjective Subtype.val Subtype.val_injective


def negativeReversalGateToLeftMaskFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    negativeReversalGateFiber ends m j k l zero p ->
      leftMaskFiber ends m j k l zero p := fun c =>
  sourceMaskGatePointToLeftMaskFiber ends m j k l zero p c.1 c.2.1



noncomputable def positiveReversalGateToRightMaskFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    positiveReversalGateFiber ends m j k l zero p ->
      rightMaskFiber ends m j k l zero p := fun c =>
  (rightMaskFiberEquivReversedSourceMaskGateFiber
    ends m j k l zero p).symm ⟨c.1, c.2.2⟩




def CanonicalRawGateRelated
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftSourceMaskFiber ends m j k l zero p) : Prop :=
  ∃ (hc : RowsDisconnect ends m c.1 k zero)
      (hd : RowsDisconnect ends m (middleSwap m d.1) k zero),
    (rightMaskFiberEquivReversedSourceMaskGateFiber
      ends m j k l zero p).symm ⟨d, hd⟩ ∈
      canonicalMaskRightImages ends m j k l zero p
        (sourceMaskGatePointToLeftMaskFiber
          ends m j k l zero p c hc)



noncomputable def canonicalRawNegativeGateFinset
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Finset (leftSourceMaskFiber ends m j k l zero p) := by
  classical
  exact Finset.univ.filter fun c =>
    ReversalGateNegative ends m j k l zero p c

noncomputable def canonicalRawCommonClosureIter
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Nat ->
      Finset (leftSourceMaskFiber ends m j k l zero p) :=
  StatMech.FrontierA.finiteCommonClosureIter
    (fun c => RowsDisconnect ends m c.1 k zero)
    (fun c => RowsDisconnect ends m (middleSwap m c.1) k zero)
    (CanonicalRawGateRelated ends m j k l zero p)
    (canonicalRawNegativeGateFinset ends m j k l zero p)

theorem canonicalRawCommonClosureIter_subset_succ
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) (n : Nat) :
    canonicalRawCommonClosureIter ends m j k l zero p n ⊆
      canonicalRawCommonClosureIter ends m j k l zero p (n + 1) :=
  StatMech.FrontierA.finiteCommonClosureIter_subset_succ _ _ _ _ n

theorem exists_canonicalRawCommonClosureIter_fixed
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    ∃ n ≤ Fintype.card (leftSourceMaskFiber ends m j k l zero p) -
        (canonicalRawNegativeGateFinset ends m j k l zero p).card,
      canonicalRawCommonClosureIter ends m j k l zero p (n + 1) =
        canonicalRawCommonClosureIter ends m j k l zero p n :=
  StatMech.FrontierA.exists_finiteCommonClosureIter_fixed _ _ _ _

noncomputable def canonicalRawCommonClosureIndex
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Nat :=
  Classical.choose
    (exists_canonicalRawCommonClosureIter_fixed ends m j k l zero p)

noncomputable def canonicalRawCommonClosure
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Finset (leftSourceMaskFiber ends m j k l zero p) :=
  canonicalRawCommonClosureIter ends m j k l zero p
    (canonicalRawCommonClosureIndex ends m j k l zero p)

theorem canonicalRawCommonClosure_fixed
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    StatMech.FrontierA.finiteCommonClosureStep
        (fun c : leftSourceMaskFiber ends m j k l zero p =>
          RowsDisconnect ends m c.1 k zero)
        (fun c => RowsDisconnect ends m (middleSwap m c.1) k zero)
        (CanonicalRawGateRelated ends m j k l zero p)
        (canonicalRawCommonClosure ends m j k l zero p) =
      canonicalRawCommonClosure ends m j k l zero p := by
  have hfixed := (Classical.choose_spec
    (exists_canonicalRawCommonClosureIter_fixed ends m j k l zero p)).2
  change canonicalRawCommonClosureIter ends m j k l zero p
      (canonicalRawCommonClosureIndex ends m j k l zero p + 1) =
    canonicalRawCommonClosureIter ends m j k l zero p
      (canonicalRawCommonClosureIndex ends m j k l zero p)
  exact hfixed

theorem canonicalRawNegativeGateFinset_subset_commonClosure
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    canonicalRawNegativeGateFinset ends m j k l zero p ⊆
      canonicalRawCommonClosure ends m j k l zero p :=
  StatMech.FrontierA.finiteCommonClosureIter_zero_subset _ _ _ _ _

theorem canonicalRawCommonClosure_leftGate
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    ∀ c ∈ canonicalRawCommonClosure ends m j k l zero p,
      RowsDisconnect ends m c.1 k zero := by
  classical
  apply StatMech.FrontierA.finiteCommonClosureIter_preserves_left
  intro c hc
  have hneg : ReversalGateNegative ends m j k l zero p c := by
    simpa only [canonicalRawNegativeGateFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] using hc
  exact hneg.1



theorem canonicalRawCommonClosure_common_mem_neighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p)
    (hc : c ∈ canonicalRawCommonClosure ends m j k l zero p)
    (hcRight : RowsDisconnect ends m (middleSwap m c.1) k zero) :
    c ∈ StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p) := by
  classical
  apply StatMech.FrontierA.finiteCommonClosureIter_common_mem_neighborhood
    (fun c : leftSourceMaskFiber ends m j k l zero p =>
      RowsDisconnect ends m c.1 k zero)
    (fun c => RowsDisconnect ends m (middleSwap m c.1) k zero)
    (CanonicalRawGateRelated ends m j k l zero p)
    (canonicalRawNegativeGateFinset ends m j k l zero p)
    ?_ (canonicalRawCommonClosureIndex ends m j k l zero p) c hc hcRight
  intro x hx
  have hnegative : ReversalGateNegative ends m j k l zero p x := by
    simpa only [canonicalRawNegativeGateFinset, Finset.mem_filter,
      Finset.mem_univ, true_and] using hx
  exact hnegative.2




theorem canonicalRawCommonClosure_right_iff_neighborhood_left
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftSourceMaskFiber ends m j k l zero p) :
    (c ∈ canonicalRawCommonClosure ends m j k l zero p ∧
        RowsDisconnect ends m (middleSwap m c.1) k zero) ↔
      (c ∈ StatMech.FrontierA.finiteRelationNeighborhood
        (CanonicalRawGateRelated ends m j k l zero p)
        (canonicalRawCommonClosure ends m j k l zero p) ∧
          RowsDisconnect ends m c.1 k zero) := by
  classical
  constructor
  · intro hc
    rcases hc with ⟨hcClosure, hcRight⟩
    exact ⟨
      canonicalRawCommonClosure_common_mem_neighborhood
        ends m j k l zero p c hcClosure hcRight,
      canonicalRawCommonClosure_leftGate
        ends m j k l zero p c hcClosure⟩
  · intro hc
    rcases hc with ⟨hcNeighborhood, hcLeft⟩
    obtain ⟨source, hsource, hrelated⟩ :=
      (Finset.mem_filter.mp hcNeighborhood).2
    obtain ⟨_, hcRight, _⟩ := hrelated
    have hcStep : c ∈ StatMech.FrontierA.finiteCommonClosureStep
        (fun c : leftSourceMaskFiber ends m j k l zero p =>
          RowsDisconnect ends m c.1 k zero)
        (fun c => RowsDisconnect ends m (middleSwap m c.1) k zero)
        (CanonicalRawGateRelated ends m j k l zero p)
        (canonicalRawCommonClosure ends m j k l zero p) :=
      (StatMech.FrontierA.mem_finiteCommonClosureStep _ _ _ _ c).mpr
        (Or.inr ⟨hcNeighborhood, hcLeft, hcRight⟩)
    rw [canonicalRawCommonClosure_fixed ends m j k l zero p] at hcStep
    exact ⟨hcStep, hcRight⟩



def CanonicalDiscrepancyRelated
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : negativeReversalGateFiber ends m j k l zero p)
    (q : positiveReversalGateFiber ends m j k l zero p) : Prop :=
  positiveReversalGateToRightMaskFiber ends m j k l zero p q ∈
    canonicalMaskRightImages ends m j k l zero p
      (negativeReversalGateToLeftMaskFiber ends m j k l zero p c)



noncomputable def canonicalDiscrepancyNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (negativeReversalGateFiber ends m j k l zero p)) :
    Finset (positiveReversalGateFiber ends m j k l zero p) := by
  classical
  exact Finset.univ.filter fun q =>
    ∃ c ∈ S, CanonicalDiscrepancyRelated ends m j k l zero p c q



noncomputable def liftedNegativeReversalGateFamily
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (negativeReversalGateFiber ends m j k l zero p)) :
    Finset (leftMaskFiber ends m j k l zero p) := by
  classical
  exact S.image
    (negativeReversalGateToLeftMaskFiber ends m j k l zero p)


noncomputable def canonicalNegativeFullNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (negativeReversalGateFiber ends m j k l zero p)) :
    Finset (rightMaskFiber ends m j k l zero p) :=
  canonicalMaskRightNeighborhood ends m j k l zero p
    (liftedNegativeReversalGateFamily ends m j k l zero p S)


noncomputable def canonicalNegativePositiveNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (negativeReversalGateFiber ends m j k l zero p)) :
    Finset (rightMaskFiber ends m j k l zero p) := by
  classical
  exact (canonicalNegativeFullNeighborhood ends m j k l zero p S).filter
    fun q => ¬ RowsDisconnect ends m
      (rightMaskFiberEquivReversedSourceMaskGateFiber
        ends m j k l zero p q).1.1 k zero


noncomputable def canonicalNegativeCommonNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (negativeReversalGateFiber ends m j k l zero p)) :
    Finset (rightMaskFiber ends m j k l zero p) := by
  classical
  exact (canonicalNegativeFullNeighborhood ends m j k l zero p S).filter
    fun q => RowsDisconnect ends m
      (rightMaskFiberEquivReversedSourceMaskGateFiber
        ends m j k l zero p q).1.1 k zero



theorem card_canonicalNegativeFullNeighborhood_eq_parts
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (negativeReversalGateFiber ends m j k l zero p)) :
    (canonicalNegativeFullNeighborhood ends m j k l zero p S).card =
      (canonicalNegativePositiveNeighborhood
        ends m j k l zero p S).card +
      (canonicalNegativeCommonNeighborhood
        ends m j k l zero p S).card := by
  classical
  let U := canonicalNegativeFullNeighborhood ends m j k l zero p S
  let common := fun q : rightMaskFiber ends m j k l zero p =>
    RowsDisconnect ends m
      (rightMaskFiberEquivReversedSourceMaskGateFiber
        ends m j k l zero p q).1.1 k zero
  have hsplit := U.card_filter_add_card_filter_not common
  simpa only [canonicalNegativePositiveNeighborhood,
    canonicalNegativeCommonNeighborhood, U, common, add_comm] using hsplit.symm




theorem positiveReversalGate_mem_canonicalNegativePositiveNeighborhood_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (negativeReversalGateFiber ends m j k l zero p))
    (q : positiveReversalGateFiber ends m j k l zero p) :
    positiveReversalGateToRightMaskFiber ends m j k l zero p q ∈
        canonicalNegativePositiveNeighborhood ends m j k l zero p S ↔
      ∃ c ∈ S,
        CanonicalDiscrepancyRelated ends m j k l zero p c q := by
  classical
  simp only [canonicalNegativePositiveNeighborhood, Finset.mem_filter,
    canonicalNegativeFullNeighborhood,
    mem_canonicalMaskRightNeighborhood_iff,
    liftedNegativeReversalGateFamily, Finset.mem_image]
  constructor
  · rintro ⟨⟨a, ⟨c, hc, rfl⟩, ha⟩, -⟩
    exact ⟨c, hc, ha⟩
  · rintro ⟨c, hc, hq⟩
    refine ⟨⟨negativeReversalGateToLeftMaskFiber
      ends m j k l zero p c, ⟨c, hc, rfl⟩, hq⟩, ?_⟩
    simpa [positiveReversalGateToRightMaskFiber] using q.2.1

noncomputable def transportedCanonicalDiscrepancyNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (negativeReversalGateFiber ends m j k l zero p)) :
    Finset (rightMaskFiber ends m j k l zero p) := by
  classical
  exact (canonicalDiscrepancyNeighborhood ends m j k l zero p S).image
    (positiveReversalGateToRightMaskFiber ends m j k l zero p)



theorem image_canonicalDiscrepancyNeighborhood_eq_positiveNeighborhood
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (negativeReversalGateFiber ends m j k l zero p)) :
    transportedCanonicalDiscrepancyNeighborhood
        ends m j k l zero p S =
      canonicalNegativePositiveNeighborhood ends m j k l zero p S := by
  classical
  unfold transportedCanonicalDiscrepancyNeighborhood
  ext q
  constructor
  · intro hq
    obtain ⟨qpos, hqpos, rfl⟩ := Finset.mem_image.mp hq
    apply (positiveReversalGate_mem_canonicalNegativePositiveNeighborhood_iff
      ends m j k l zero p S qpos).mpr
    simpa only [canonicalDiscrepancyNeighborhood, Finset.mem_filter,
      Finset.mem_univ, true_and] using hqpos
  · intro hq
    let pulled := rightMaskFiberEquivReversedSourceMaskGateFiber
      ends m j k l zero p q
    have hnot : ¬ RowsDisconnect ends m pulled.1.1 k zero :=
      (Finset.mem_filter.mp hq).2
    let qpos : positiveReversalGateFiber ends m j k l zero p :=
      ⟨pulled.1, hnot, pulled.2⟩
    have heq : positiveReversalGateToRightMaskFiber
        ends m j k l zero p qpos = q := by
      dsimp only [qpos, pulled, positiveReversalGateToRightMaskFiber]
      exact (rightMaskFiberEquivReversedSourceMaskGateFiber
        ends m j k l zero p).symm_apply_apply q
    have hrelated : ∃ c ∈ S,
        CanonicalDiscrepancyRelated ends m j k l zero p c qpos :=
      (positiveReversalGate_mem_canonicalNegativePositiveNeighborhood_iff
        ends m j k l zero p S qpos).mp (heq ▸ hq)
    apply Finset.mem_image.mpr
    refine ⟨qpos, ?_, heq⟩
    simpa only [canonicalDiscrepancyNeighborhood, Finset.mem_filter,
      Finset.mem_univ, true_and] using hrelated

theorem card_canonicalNegativePositiveNeighborhood_eq_discrepancy
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (negativeReversalGateFiber ends m j k l zero p)) :
    (canonicalNegativePositiveNeighborhood ends m j k l zero p S).card =
      (canonicalDiscrepancyNeighborhood ends m j k l zero p S).card := by
  classical
  rw [← image_canonicalDiscrepancyNeighborhood_eq_positiveNeighborhood]
  unfold transportedCanonicalDiscrepancyNeighborhood
  apply Finset.card_image_of_injective
  intro q r hqr
  apply Subtype.ext
  have h := congrArg
    (rightMaskFiberEquivReversedSourceMaskGateFiber
      ends m j k l zero p) hqr
  have hval := congrArg Subtype.val h
  simpa [positiveReversalGateToRightMaskFiber] using hval




theorem card_canonicalNegativeFullNeighborhood_eq_discrepancy_add_common
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (S : Finset (negativeReversalGateFiber ends m j k l zero p)) :
    (canonicalNegativeFullNeighborhood ends m j k l zero p S).card =
      (canonicalDiscrepancyNeighborhood ends m j k l zero p S).card +
      (canonicalNegativeCommonNeighborhood ends m j k l zero p S).card := by
  rw [card_canonicalNegativeFullNeighborhood_eq_parts,
    card_canonicalNegativePositiveNeighborhood_eq_discrepancy]



def CanonicalDiscrepancyHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ S : Finset (negativeReversalGateFiber ends m j k l zero p),
    S.card ≤
      (canonicalDiscrepancyNeighborhood ends m j k l zero p S).card




def CanonicalDiscrepancyCommonCompensatedExpansion
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ S : Finset (negativeReversalGateFiber ends m j k l zero p),
    S.card +
        (canonicalNegativeCommonNeighborhood
          ends m j k l zero p S).card ≤
      (canonicalNegativeFullNeighborhood ends m j k l zero p S).card



theorem canonicalDiscrepancyCommonCompensatedExpansion_iff_hall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    CanonicalDiscrepancyCommonCompensatedExpansion
        ends m j k l zero p ↔
      CanonicalDiscrepancyHall ends m j k l zero p := by
  constructor <;> intro h S
  · have hS := h S
    rw [card_canonicalNegativeFullNeighborhood_eq_discrepancy_add_common]
      at hS
    omega
  · have hS := h S
    rw [card_canonicalNegativeFullNeighborhood_eq_discrepancy_add_common]
    omega




def CanonicalDiscrepancySingletonExpansion
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop :=
  ∀ c : negativeReversalGateFiber ends m j k l zero p,
    ∃ q : positiveReversalGateFiber ends m j k l zero p,
      CanonicalDiscrepancyRelated ends m j k l zero p c q

noncomputable def canonicalDiscrepancyTargetSelector
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hsingle : CanonicalDiscrepancySingletonExpansion
      ends m j k l zero p) :
    negativeReversalGateFiber ends m j k l zero p ->
      positiveReversalGateFiber ends m j k l zero p := fun c =>
  Classical.choose (hsingle c)

theorem canonicalDiscrepancyTargetSelector_related
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hsingle : CanonicalDiscrepancySingletonExpansion
      ends m j k l zero p)
    (c : negativeReversalGateFiber ends m j k l zero p) :
    CanonicalDiscrepancyRelated ends m j k l zero p c
      (canonicalDiscrepancyTargetSelector
        ends m j k l zero p hsingle c) :=
  Classical.choose_spec (hsingle c)



noncomputable def canonicalDiscrepancyReferenceSelector
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hsingle : CanonicalDiscrepancySingletonExpansion
      ends m j k l zero p)
    (c : negativeReversalGateFiber ends m j k l zero p) :
    leftMaskFiber ends m j k l zero p :=
  Classical.choose ((mem_canonicalMaskRightImages_iff
    ends m j k l zero p
      (negativeReversalGateToLeftMaskFiber ends m j k l zero p c)
      (positiveReversalGateToRightMaskFiber ends m j k l zero p
        (canonicalDiscrepancyTargetSelector
          ends m j k l zero p hsingle c))).mp
    (canonicalDiscrepancyTargetSelector_related
      ends m j k l zero p hsingle c))

theorem canonicalDiscrepancyReferenceSelector_works
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hsingle : CanonicalDiscrepancySingletonExpansion
      ends m j k l zero p)
    (c : negativeReversalGateFiber ends m j k l zero p) :
    CanonicalTransferWorks ends m k zero
      (canonicalDiscrepancyReferenceSelector
        ends m j k l zero p hsingle c).1.1
      (negativeReversalGateToLeftMaskFiber
        ends m j k l zero p c).1.1 :=
  (Classical.choose_spec ((mem_canonicalMaskRightImages_iff
    ends m j k l zero p
      (negativeReversalGateToLeftMaskFiber ends m j k l zero p c)
      (positiveReversalGateToRightMaskFiber ends m j k l zero p
        (canonicalDiscrepancyTargetSelector
          ends m j k l zero p hsingle c))).mp
    (canonicalDiscrepancyTargetSelector_related
      ends m j k l zero p hsingle c))).1


theorem card_le_canonicalDiscrepancyNeighborhood_of_card_le_one
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hsingle : CanonicalDiscrepancySingletonExpansion
      ends m j k l zero p)
    (S : Finset (negativeReversalGateFiber ends m j k l zero p))
    (hcard : S.card ≤ 1) :
    S.card ≤
      (canonicalDiscrepancyNeighborhood ends m j k l zero p S).card := by
  classical
  by_cases hS : S.Nonempty
  · obtain ⟨c, hc⟩ := hS
    have hSeq : S = {c} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hc, ?_⟩
      intro d hd
      exact (Finset.card_le_one.mp hcard) d hd c hc
    subst S
    let q := canonicalDiscrepancyTargetSelector
      ends m j k l zero p hsingle c
    have hq : q ∈ canonicalDiscrepancyNeighborhood
        ends m j k l zero p {c} := by
      simp only [canonicalDiscrepancyNeighborhood, Finset.mem_filter,
        Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨c, rfl,
        canonicalDiscrepancyTargetSelector_related
          ends m j k l zero p hsingle c⟩
    simpa using (Finset.card_pos.mpr ⟨q, hq⟩)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hS]
    simp



theorem canonicalDiscrepancyHall_iff_exists_matching
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    CanonicalDiscrepancyHall ends m j k l zero p ↔
      ∃ f : negativeReversalGateFiber ends m j k l zero p ↪
          positiveReversalGateFiber ends m j k l zero p,
        ∀ c, CanonicalDiscrepancyRelated ends m j k l zero p c (f c) := by
  classical
  let rel := CanonicalDiscrepancyRelated ends m j k l zero p
  have hhall := Fintype.all_card_le_filter_rel_iff_exists_injective rel
  constructor
  · intro h
    have h' : ∀ S : Finset
        (negativeReversalGateFiber ends m j k l zero p),
        S.card ≤ (Finset.univ.filter fun q =>
          ∃ c ∈ S, rel c q).card := by
      simpa only [CanonicalDiscrepancyHall,
        canonicalDiscrepancyNeighborhood] using h
    obtain ⟨f, hf, himage⟩ := hhall.mp h'
    exact ⟨⟨f, hf⟩, himage⟩
  · rintro ⟨f, himage⟩
    have h' : ∀ S : Finset
        (negativeReversalGateFiber ends m j k l zero p),
        S.card ≤ (Finset.univ.filter fun q =>
          ∃ c ∈ S, rel c q).card :=
      hhall.mpr ⟨f, f.injective, himage⟩
    simpa only [CanonicalDiscrepancyHall,
      canonicalDiscrepancyNeighborhood] using h'



theorem card_leftMaskFiber_le_rightMaskFiber_iff_reversalGates
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
        Fintype.card (rightMaskFiber ends m j k l zero p) ↔
      Fintype.card (leftSourceMaskGateFiber ends m j k l zero p) ≤
        Fintype.card
          (reversedRightSourceMaskGateFiber ends m j k l zero p) := by
  rw [Fintype.card_congr
      (leftMaskFiberEquivSourceMaskGateFiber ends m j k l zero p),
    Fintype.card_congr
      (rightMaskFiberEquivReversedSourceMaskGateFiber
        ends m j k l zero p)]




theorem card_leftMaskFiber_le_rightMaskFiber_iff_discrepancies
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
        Fintype.card (rightMaskFiber ends m j k l zero p) ↔
      Fintype.card (negativeReversalGateFiber ends m j k l zero p) ≤
        Fintype.card (positiveReversalGateFiber ends m j k l zero p) := by
  classical
  rw [card_leftMaskFiber_le_rightMaskFiber_iff_reversalGates]
  unfold leftSourceMaskGateFiber reversedRightSourceMaskGateFiber
    negativeReversalGateFiber positiveReversalGateFiber
    ReversalGateNegative ReversalGatePositive
  rw [Fintype.card_subtype, Fintype.card_subtype,
    Fintype.card_subtype, Fintype.card_subtype]
  let leftGate := Finset.univ.filter fun
    c : leftSourceMaskFiber ends m j k l zero p =>
      RowsDisconnect ends m c.1 k zero
  let rightGate := Finset.univ.filter fun
    c : leftSourceMaskFiber ends m j k l zero p =>
      RowsDisconnect ends m (middleSwap m c.1) k zero
  have hnegative : Finset.univ.filter (fun
      c : leftSourceMaskFiber ends m j k l zero p =>
        RowsDisconnect ends m c.1 k zero ∧
          ¬ RowsDisconnect ends m (middleSwap m c.1) k zero) =
      leftGate \ rightGate := by
    ext c
    simp [leftGate, rightGate]
  have hpositive : Finset.univ.filter (fun
      c : leftSourceMaskFiber ends m j k l zero p =>
        ¬ RowsDisconnect ends m c.1 k zero ∧
          RowsDisconnect ends m (middleSwap m c.1) k zero) =
      rightGate \ leftGate := by
    ext c
    simp [leftGate, rightGate, and_comm]
  rw [hnegative, hpositive]
  change leftGate.card ≤ rightGate.card ↔
    (leftGate \ rightGate).card ≤ (rightGate \ leftGate).card
  have hleft := Finset.card_sdiff_add_card leftGate rightGate
  have hright := Finset.card_sdiff_add_card rightGate leftGate
  rw [Finset.union_comm rightGate leftGate] at hright
  omega




theorem card_leftMaskFiber_le_rightMaskFiber_of_commonClosedRawExpansion
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (T : Finset (leftSourceMaskFiber ends m j k l zero p))
    (hnegative : canonicalRawNegativeGateFinset
      ends m j k l zero p ⊆ T)
    (hleft : ∀ c ∈ T, RowsDisconnect ends m c.1 k zero)
    (hclosed : StatMech.FrontierA.finiteCommonClosureStep
        (fun c : leftSourceMaskFiber ends m j k l zero p =>
          RowsDisconnect ends m c.1 k zero)
        (fun c => RowsDisconnect ends m (middleSwap m c.1) k zero)
        (CanonicalRawGateRelated ends m j k l zero p) T = T)
    (hexpand : T.card ≤
      (StatMech.FrontierA.finiteRelationNeighborhood
        (CanonicalRawGateRelated ends m j k l zero p) T).card) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
      Fintype.card (rightMaskFiber ends m j k l zero p) := by
  classical
  let P := fun c : leftSourceMaskFiber ends m j k l zero p =>
    RowsDisconnect ends m c.1 k zero
  let Q := fun c : leftSourceMaskFiber ends m j k l zero p =>
    RowsDisconnect ends m (middleSwap m c.1) k zero
  let R := CanonicalRawGateRelated ends m j k l zero p
  have hrel : ∀ {c d}, R c d -> P c ∧ Q d := by
    rintro c d ⟨hc, hd, -⟩
    exact ⟨hc, hd⟩
  have hcount :=
    StatMech.FrontierA.card_leftOnly_le_rightOnly_of_commonClosed_expansion
      P Q R T hrel (by
        simpa only [P, Q, canonicalRawNegativeGateFinset,
          ReversalGateNegative] using hnegative) (by
        simpa only [P] using hleft) (by
        simpa only [P, Q, R] using hclosed) (by
        simpa only [R] using hexpand)
  apply (card_leftMaskFiber_le_rightMaskFiber_iff_discrepancies
    ends m j k l zero p).mpr
  unfold negativeReversalGateFiber positiveReversalGateFiber
    ReversalGateNegative ReversalGatePositive
  rw [Fintype.card_subtype, Fintype.card_subtype]
  simpa only [P, Q] using hcount



theorem card_leftMaskFiber_le_rightMaskFiber_of_stableRawClosureExpansion
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hexpand :
      (canonicalRawCommonClosure ends m j k l zero p).card ≤
        (StatMech.FrontierA.finiteRelationNeighborhood
          (CanonicalRawGateRelated ends m j k l zero p)
          (canonicalRawCommonClosure ends m j k l zero p)).card) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
      Fintype.card (rightMaskFiber ends m j k l zero p) :=
  card_leftMaskFiber_le_rightMaskFiber_of_commonClosedRawExpansion
    ends m j k l zero p
      (canonicalRawCommonClosure ends m j k l zero p)
      (canonicalRawNegativeGateFinset_subset_commonClosure
        ends m j k l zero p)
      (canonicalRawCommonClosure_leftGate ends m j k l zero p)
      (canonicalRawCommonClosure_fixed ends m j k l zero p) hexpand




noncomputable def CanonicalStableRawCollisionSurplus
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) : Prop := by
  classical
  let T := canonicalRawCommonClosure ends m j k l zero p
  let R := CanonicalRawGateRelated ends m j k l zero p
  let U := StatMech.FrontierA.finiteRelationNeighborhood R T
  exact
    (∑ d ∈ U, ((T.filter fun c => R c d).card : ℤ)) - U.card ≤
      (∑ c ∈ T, ((Finset.univ.filter (R c)).card : ℤ)) - T.card





theorem canonicalStableRawCollisionSurplus_iff_expands
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    CanonicalStableRawCollisionSurplus ends m j k l zero p ↔
      (canonicalRawCommonClosure ends m j k l zero p).card ≤
        (StatMech.FrontierA.finiteRelationNeighborhood
          (CanonicalRawGateRelated ends m j k l zero p)
          (canonicalRawCommonClosure ends m j k l zero p)).card := by
  classical
  let T := canonicalRawCommonClosure ends m j k l zero p
  let R := CanonicalRawGateRelated ends m j k l zero p
  let U := StatMech.FrontierA.finiteRelationNeighborhood R T
  have hiff :=
    StatMech.FrontierA.bipartiteNeighborhood_collisionSurplus_iff_card_le
      R T U (by
        simp only [U, StatMech.FrontierA.finiteRelationNeighborhood])
  simpa only [CanonicalStableRawCollisionSurplus, T, R, U] using hiff




noncomputable def canonicalStableRawSelfBase
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I) :
    ↑(canonicalRawCommonClosure ends m j k l zero p) ->
      leftSourceMaskFiber ends m j k l zero p := fun c =>
  canonicalSelfPulledSourcePoint ends m j k l zero
    hloop hjk hkl hk0 p c.1
      (canonicalRawCommonClosure_leftGate ends m j k l zero p c.1 c.2)

theorem canonicalStableRawSelfBase_related
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : ↑(canonicalRawCommonClosure ends m j k l zero p)) :
    CanonicalRawGateRelated ends m j k l zero p c.1
      (canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p c) := by
  let hc := canonicalRawCommonClosure_leftGate
    ends m j k l zero p c.1 c.2
  let a := sourceMaskGatePointToLeftMaskFiber
    ends m j k l zero p c.1 hc
  let q := canonicalSelfRightPointOfSourceGate ends m j k l zero
    hloop hjk hkl hk0 p c.1 hc
  have hright : RowsDisconnect ends m
      (middleSwap m
        (canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p c).1) k zero := by
    exact canonicalSelfPulledSourcePoint_rightGate ends m j k l zero
      hloop hjk hkl hk0 p c.1 hc
  refine ⟨hc, hright, ?_⟩
  have hqmem : q ∈ canonicalMaskRightImages
      ends m j k l zero p a := by
    rw [mem_canonicalMaskRightImages_iff]
    refine ⟨a, canonicalTransferWorks_self hloop hjk hkl hk0 a, ?_⟩
    rfl
  have heq :
      (rightMaskFiberEquivReversedSourceMaskGateFiber
        ends m j k l zero p).symm
          ⟨canonicalStableRawSelfBase ends m j k l zero
            hloop hjk hkl hk0 p c, hright⟩ = q := by
    let e := rightMaskFiberEquivReversedSourceMaskGateFiber
      ends m j k l zero p
    calc
      e.symm ⟨canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p c, hright⟩ = e.symm (e q) := by
        congr 1
      _ = q := e.symm_apply_apply q
  simpa only [a, q, heq] using hqmem


noncomputable def canonicalStableRawRightBase
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)) ->
      leftSourceMaskFiber ends m j k l zero p := by
  classical
  intro d
  exact Classical.choose (Finset.mem_filter.mp d.2).2

theorem canonicalStableRawRightBase_mem
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p))) :
    canonicalStableRawRightBase ends m j k l zero p d ∈
      canonicalRawCommonClosure ends m j k l zero p := by
  classical
  exact (Classical.choose_spec (Finset.mem_filter.mp d.2).2).1

theorem canonicalStableRawRightBase_related
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p))) :
    CanonicalRawGateRelated ends m j k l zero p
      (canonicalStableRawRightBase ends m j k l zero p d) d.1 := by
  classical
  exact (Classical.choose_spec (Finset.mem_filter.mp d.2).2).2




noncomputable def canonicalStableRawSourceRank
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : ↑(canonicalRawCommonClosure ends m j k l zero p)) : Nat :=
  (Fintype.equivFin
    (↑(canonicalRawCommonClosure ends m j k l zero p)) c).1


noncomputable def canonicalStableRawSelfPreimageFinset
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p))) :
    Finset ↑(canonicalRawCommonClosure ends m j k l zero p) := by
  classical
  exact Finset.univ.filter fun c =>
    canonicalStableRawSelfBase ends m j k l zero
      hloop hjk hkl hk0 p c = d.1

theorem canonicalStableRawSelfPreimageFinset_nonempty
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (hself : ∃ c : ↑(canonicalRawCommonClosure ends m j k l zero p),
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p c = d.1) :
    (canonicalStableRawSelfPreimageFinset ends m j k l zero
      hloop hjk hkl hk0 p d).Nonempty := by
  classical
  obtain ⟨c, hc⟩ := hself
  refine ⟨c, ?_⟩
  simp only [canonicalStableRawSelfPreimageFinset, Finset.mem_filter,
    Finset.mem_univ, true_and]
  exact hc



noncomputable def canonicalStableRawPreferredSelfPreimage
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (hself : ∃ c : ↑(canonicalRawCommonClosure ends m j k l zero p),
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p c = d.1) :
    ↑(canonicalRawCommonClosure ends m j k l zero p) :=
  Classical.choose
    ((canonicalStableRawSelfPreimageFinset ends m j k l zero
      hloop hjk hkl hk0 p d).exists_min_image
        (canonicalStableRawSourceRank ends m j k l zero p)
        (canonicalStableRawSelfPreimageFinset_nonempty
          ends m j k l zero hloop hjk hkl hk0 p d hself))

theorem canonicalStableRawPreferredSelfPreimage_spec
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (hself : ∃ c : ↑(canonicalRawCommonClosure ends m j k l zero p),
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p c = d.1) :
    canonicalStableRawPreferredSelfPreimage ends m j k l zero
          hloop hjk hkl hk0 p d hself ∈
        canonicalStableRawSelfPreimageFinset ends m j k l zero
          hloop hjk hkl hk0 p d ∧
      ∀ c ∈ canonicalStableRawSelfPreimageFinset ends m j k l zero
          hloop hjk hkl hk0 p d,
        canonicalStableRawSourceRank ends m j k l zero p
            (canonicalStableRawPreferredSelfPreimage ends m j k l zero
              hloop hjk hkl hk0 p d hself) ≤
          canonicalStableRawSourceRank ends m j k l zero p c :=
  Classical.choose_spec
    ((canonicalStableRawSelfPreimageFinset ends m j k l zero
      hloop hjk hkl hk0 p d).exists_min_image
        (canonicalStableRawSourceRank ends m j k l zero p)
        (canonicalStableRawSelfPreimageFinset_nonempty
          ends m j k l zero hloop hjk hkl hk0 p d hself))




noncomputable def canonicalStableRawPreferredRightBase
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p))) :
    leftSourceMaskFiber ends m j k l zero p := by
  classical
  by_cases hself : ∃ c :
      ↑(canonicalRawCommonClosure ends m j k l zero p),
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p c = d.1
  · exact (canonicalStableRawPreferredSelfPreimage
      ends m j k l zero hloop hjk hkl hk0 p d hself).1
  · exact canonicalStableRawRightBase ends m j k l zero p d

theorem canonicalStableRawPreferredRightBase_mem
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p))) :
    canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p d ∈
      canonicalRawCommonClosure ends m j k l zero p := by
  classical
  unfold canonicalStableRawPreferredRightBase
  split
  next hself =>
    exact (canonicalStableRawPreferredSelfPreimage
      ends m j k l zero hloop hjk hkl hk0 p d hself).2
  next => exact canonicalStableRawRightBase_mem ends m j k l zero p d

theorem canonicalStableRawPreferredRightBase_related
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p))) :
    CanonicalRawGateRelated ends m j k l zero p
      (canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p d) d.1 := by
  classical
  unfold canonicalStableRawPreferredRightBase
  split
  next hself =>
    let preferred := canonicalStableRawPreferredSelfPreimage
      ends m j k l zero hloop hjk hkl hk0 p d hself
    have hpreferred := (canonicalStableRawPreferredSelfPreimage_spec
      ends m j k l zero hloop hjk hkl hk0 p d hself).1
    have hpreferredSelf : canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p preferred = d.1 := by
      simpa only [canonicalStableRawSelfPreimageFinset,
        Finset.mem_filter, Finset.mem_univ, true_and] using hpreferred
    have hr := canonicalStableRawSelfBase_related ends m j k l zero
      hloop hjk hkl hk0 p preferred
    simpa only [hpreferredSelf, preferred] using hr
  next =>
    exact canonicalStableRawRightBase_related ends m j k l zero p d

theorem canonicalStableRawPreferredRightBase_self_eq_of_exists
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (hself : ∃ c : ↑(canonicalRawCommonClosure ends m j k l zero p),
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p c = d.1) :
    canonicalStableRawSelfBase ends m j k l zero hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p d,
        canonicalStableRawPreferredRightBase_mem ends m j k l zero
          hloop hjk hkl hk0 p d⟩ = d.1 := by
  classical
  let c := Classical.choose hself
  have hpreferred :=
    (canonicalStableRawPreferredSelfPreimage_spec
      ends m j k l zero hloop hjk hkl hk0 p d hself).1
  have hbase : canonicalStableRawSelfBase ends m j k l zero
      hloop hjk hkl hk0 p
        (canonicalStableRawPreferredSelfPreimage ends m j k l zero
          hloop hjk hkl hk0 p d hself) = d.1 := by
    simpa only [canonicalStableRawSelfPreimageFinset,
      Finset.mem_filter, Finset.mem_univ, true_and] using hpreferred
  change canonicalStableRawSelfBase ends m j k l zero
      hloop hjk hkl hk0 p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p d,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p d⟩ = d.1
  simpa only [canonicalStableRawPreferredRightBase, dif_pos hself] using hbase




theorem canonicalStableRawPreferredRightBase_rank_lt_of_self
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (c : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (hself : canonicalStableRawSelfBase ends m j k l zero
      hloop hjk hkl hk0 p c = d.1)
    (hne : c.1 ≠ canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p d) :
    canonicalStableRawSourceRank ends m j k l zero p
        ⟨canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p d,
          canonicalStableRawPreferredRightBase_mem ends m j k l zero
            hloop hjk hkl hk0 p d⟩ <
      canonicalStableRawSourceRank ends m j k l zero p c := by
  classical
  let hExists : ∃ b : ↑(canonicalRawCommonClosure ends m j k l zero p),
      canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p b = d.1 := ⟨c, hself⟩
  let preferred := canonicalStableRawPreferredSelfPreimage
    ends m j k l zero hloop hjk hkl hk0 p d hExists
  have hcMem : c ∈ canonicalStableRawSelfPreimageFinset
      ends m j k l zero hloop hjk hkl hk0 p d := by
    simp only [canonicalStableRawSelfPreimageFinset, Finset.mem_filter,
      Finset.mem_univ, true_and]
    exact hself
  have hle : canonicalStableRawSourceRank ends m j k l zero p preferred ≤
      canonicalStableRawSourceRank ends m j k l zero p c :=
    (canonicalStableRawPreferredSelfPreimage_spec
      ends m j k l zero hloop hjk hkl hk0 p d hExists).2 c hcMem
  have hpreferred :
      (⟨canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p d,
        canonicalStableRawPreferredRightBase_mem ends m j k l zero
          hloop hjk hkl hk0 p d⟩ :
        ↑(canonicalRawCommonClosure ends m j k l zero p)) = preferred := by
    apply Subtype.ext
    simp only [canonicalStableRawPreferredRightBase, dif_pos hExists,
      preferred]
  have hpreferredNe : preferred ≠ c := by
    intro heq
    apply hne
    calc
      c.1 = preferred.1 := congrArg Subtype.val heq.symm
      _ = canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p d := (congrArg Subtype.val hpreferred).symm
  have hrankNe : canonicalStableRawSourceRank ends m j k l zero p preferred ≠
      canonicalStableRawSourceRank ends m j k l zero p c := by
    intro heq
    apply hpreferredNe
    apply (Fintype.equivFin
      (↑(canonicalRawCommonClosure ends m j k l zero p))).injective
    apply Fin.ext
    exact heq
  rw [hpreferred]
  omega




theorem exists_canonicalRawGateRelated_ne_self_of_exceptionalSelfToken
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (c : ↑(canonicalRawCommonClosure ends m j k l zero p))
    (d : ↑(StatMech.FrontierA.finiteRelationNeighborhood
      (CanonicalRawGateRelated ends m j k l zero p)
      (canonicalRawCommonClosure ends m j k l zero p)))
    (hself : canonicalStableRawSelfBase ends m j k l zero
      hloop hjk hkl hk0 p c = d.1)
    (hne : c.1 ≠ canonicalStableRawPreferredRightBase
      ends m j k l zero hloop hjk hkl hk0 p d) :
    ∃ e : leftSourceMaskFiber ends m j k l zero p,
      CanonicalRawGateRelated ends m j k l zero p c.1 e ∧
        e ≠ canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p c := by
  classical
  let hc := canonicalRawCommonClosure_leftGate
    ends m j k l zero p c.1 c.2
  let b : ↑(canonicalRawCommonClosure ends m j k l zero p) :=
    ⟨canonicalStableRawPreferredRightBase ends m j k l zero
      hloop hjk hkl hk0 p d,
    canonicalStableRawPreferredRightBase_mem ends m j k l zero
      hloop hjk hkl hk0 p d⟩
  let hb := canonicalRawCommonClosure_leftGate
    ends m j k l zero p b.1 b.2
  have hcb : c ≠ b := by
    intro h
    exact hne (congrArg (fun x => x.1) h)
  let a := sourceMaskGatePointToLeftMaskFiber
    ends m j k l zero p c.1 hc
  let r := sourceMaskGatePointToLeftMaskFiber
    ends m j k l zero p b.1 hb
  have har : a ≠ r := by
    intro h
    apply hcb
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun x => x.1.1) h
  have hbself : canonicalStableRawSelfBase ends m j k l zero
      hloop hjk hkl hk0 p b = d.1 :=
    canonicalStableRawPreferredRightBase_self_eq_of_exists
      ends m j k l zero hloop hjk hkl hk0 p d ⟨c, hself⟩
  let qa := canonicalSelfRightPointOfSourceGate ends m j k l zero
    hloop hjk hkl hk0 p c.1 hc
  let qr := canonicalSelfRightPointOfSourceGate ends m j k l zero
    hloop hjk hkl hk0 p b.1 hb
  let e := rightMaskFiberEquivReversedSourceMaskGateFiber
    ends m j k l zero p
  have heqa : (e qa).1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p c := by
    rfl
  have heqr : (e qr).1 = canonicalStableRawSelfBase
      ends m j k l zero hloop hjk hkl hk0 p b := by
    rfl
  have heq : qa = qr := by
    apply e.injective
    apply Subtype.ext
    exact heqa.trans (hself.trans (hbself.symm.trans heqr.symm))
  have himage :
      (canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p a a
          (canonicalTransferWorks_self hloop hjk hkl hk0 a)).1.1 =
        (canonicalTransferMapOfWorks
          ends m j k l zero hloop hjk hkl p r r
            (canonicalTransferWorks_self hloop hjk hkl hk0 r)).1.1 := by
    exact congrArg (fun q => q.1.1) heq
  obtain ⟨qalt, hqalt, hqaltne⟩ :=
    exists_canonicalMaskRightImage_ne_self_of_selfImage_collision
      ends m j k l zero hloop hjk hkl hk0 p a r har himage
  let raw := (e qalt).1
  have hrawRight : RowsDisconnect ends m (middleSwap m raw.1) k zero :=
    (e qalt).2
  refine ⟨raw, ⟨hc, hrawRight, ?_⟩, ?_⟩
  · have hback : e.symm ⟨raw, hrawRight⟩ = qalt := by
      exact e.symm_apply_apply qalt
    rw [hback]
    exact hqalt
  · intro hraw
    apply hqaltne
    apply e.injective
    apply Subtype.ext
    exact hraw





noncomputable def CanonicalStableRawCollisionTokenEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I) : Prop := by
  classical
  exact Nonempty
    (StatMech.FrontierA.bipartiteRightCollisionToken
        (CanonicalRawGateRelated ends m j k l zero p)
        (canonicalRawCommonClosure ends m j k l zero p)
        (StatMech.FrontierA.finiteRelationNeighborhood
          (CanonicalRawGateRelated ends m j k l zero p)
          (canonicalRawCommonClosure ends m j k l zero p))
        (canonicalStableRawPreferredRightBase ends m j k l zero
          hloop hjk hkl hk0 p) ↪
      StatMech.FrontierA.bipartiteLeftSurplusToken
        (CanonicalRawGateRelated ends m j k l zero p)
        (canonicalRawCommonClosure ends m j k l zero p)
        (canonicalStableRawSelfBase ends m j k l zero
          hloop hjk hkl hk0 p))

theorem canonicalRawCommonClosure_expands_of_collisionTokenEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hemb : CanonicalStableRawCollisionTokenEmbedding
      ends m j k l zero hloop hjk hkl hk0 p) :
    (canonicalRawCommonClosure ends m j k l zero p).card ≤
      (StatMech.FrontierA.finiteRelationNeighborhood
        (CanonicalRawGateRelated ends m j k l zero p)
        (canonicalRawCommonClosure ends m j k l zero p)).card := by
  classical
  let T := canonicalRawCommonClosure ends m j k l zero p
  let R := CanonicalRawGateRelated ends m j k l zero p
  let U := StatMech.FrontierA.finiteRelationNeighborhood R T
  apply StatMech.FrontierA.card_le_bipartiteNeighbors_of_collisionTokenEmbedding
    R T U
  · simp only [U, StatMech.FrontierA.finiteRelationNeighborhood]
  · refine ⟨canonicalStableRawSelfBase ends m j k l zero
        hloop hjk hkl hk0 p,
      canonicalStableRawPreferredRightBase ends m j k l zero
        hloop hjk hkl hk0 p, ?_, ?_, ?_⟩
    · exact canonicalStableRawSelfBase_related ends m j k l zero
        hloop hjk hkl hk0 p
    · intro d
      exact ⟨canonicalStableRawPreferredRightBase_mem ends m j k l zero
          hloop hjk hkl hk0 p d,
        canonicalStableRawPreferredRightBase_related ends m j k l zero
          hloop hjk hkl hk0 p d⟩
    · simpa only [CanonicalStableRawCollisionTokenEmbedding,
        T, R, U] using hemb

theorem card_leftMaskFiber_le_rightMaskFiber_of_stableCollisionTokenEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (hemb : CanonicalStableRawCollisionTokenEmbedding
      ends m j k l zero hloop hjk hkl hk0 p) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
      Fintype.card (rightMaskFiber ends m j k l zero p) :=
  card_leftMaskFiber_le_rightMaskFiber_of_stableRawClosureExpansion
    ends m j k l zero p
      (canonicalRawCommonClosure_expands_of_collisionTokenEmbedding
        ends m j k l zero hloop hjk hkl hk0 p hemb)

theorem canonicalRawCommonClosure_expands_of_collisionSurplus
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hsurplus : CanonicalStableRawCollisionSurplus
      ends m j k l zero p) :
    (canonicalRawCommonClosure ends m j k l zero p).card ≤
      (StatMech.FrontierA.finiteRelationNeighborhood
        (CanonicalRawGateRelated ends m j k l zero p)
        (canonicalRawCommonClosure ends m j k l zero p)).card := by
  classical
  let T := canonicalRawCommonClosure ends m j k l zero p
  let R := CanonicalRawGateRelated ends m j k l zero p
  let U := StatMech.FrontierA.finiteRelationNeighborhood R T
  apply StatMech.FrontierA.card_le_bipartiteNeighbors_of_collisionSurplus
    R T U
  · simp only [U, StatMech.FrontierA.finiteRelationNeighborhood]
  · simpa only [CanonicalStableRawCollisionSurplus, T, R, U] using hsurplus

theorem card_leftMaskFiber_le_rightMaskFiber_of_stableCollisionSurplus
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hsurplus : CanonicalStableRawCollisionSurplus
      ends m j k l zero p) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
      Fintype.card (rightMaskFiber ends m j k l zero p) :=
  card_leftMaskFiber_le_rightMaskFiber_of_stableRawClosureExpansion
    ends m j k l zero p
      (canonicalRawCommonClosure_expands_of_collisionSurplus
        ends m j k l zero p hsurplus)


theorem card_leftMaskFiber_le_rightMaskFiber_iff_sum_reversalGateBalance
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
        Fintype.card (rightMaskFiber ends m j k l zero p) ↔
      0 ≤ ∑ c : leftSourceMaskFiber ends m j k l zero p,
        reversalGateBalance ends m j k l zero p c := by
  rw [card_leftMaskFiber_le_rightMaskFiber_iff_reversalGates,
    sum_reversalGateBalance_eq_card_sub]
  omega



theorem card_leftMaskFiber_le_rightMaskFiber_of_canonicalDiscrepancyHall
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hhall : CanonicalDiscrepancyHall ends m j k l zero p) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
      Fintype.card (rightMaskFiber ends m j k l zero p) := by
  classical
  obtain ⟨f, -⟩ :=
    (canonicalDiscrepancyHall_iff_exists_matching
      ends m j k l zero p).mp hhall
  have hdisc :
      Fintype.card (negativeReversalGateFiber ends m j k l zero p) ≤
        Fintype.card (positiveReversalGateFiber ends m j k l zero p) :=
    Fintype.card_le_of_embedding f
  have hraw :
      Fintype.card
          {c : leftSourceMaskFiber ends m j k l zero p //
            RowsDisconnect ends m c.1 k zero} ≤
        Fintype.card
          {c : leftSourceMaskFiber ends m j k l zero p //
            RowsDisconnect ends m (middleSwap m c.1) k zero} := by
    rw [StatMech.FrontierA.card_subtype_le_iff_card_leftOnly_le_card_rightOnly]
    calc
      Fintype.card
          {c : leftSourceMaskFiber ends m j k l zero p //
            RowsDisconnect ends m c.1 k zero ∧
              ¬ RowsDisconnect ends m (middleSwap m c.1) k zero} =
          Fintype.card
            (negativeReversalGateFiber ends m j k l zero p) :=
        Fintype.card_congr (Equiv.refl _)
      _ ≤ Fintype.card
          (positiveReversalGateFiber ends m j k l zero p) := hdisc
      _ = Fintype.card
          {c : leftSourceMaskFiber ends m j k l zero p //
            ¬ RowsDisconnect ends m c.1 k zero ∧
              RowsDisconnect ends m (middleSwap m c.1) k zero} :=
        Fintype.card_congr (Equiv.refl _)
  apply (card_leftMaskFiber_le_rightMaskFiber_iff_reversalGates
    ends m j k l zero p).2
  calc
    Fintype.card (leftSourceMaskGateFiber ends m j k l zero p) =
        Fintype.card
          {c : leftSourceMaskFiber ends m j k l zero p //
            RowsDisconnect ends m c.1 k zero} :=
      Fintype.card_congr (Equiv.refl _)
    _ ≤ Fintype.card
          {c : leftSourceMaskFiber ends m j k l zero p //
            RowsDisconnect ends m (middleSwap m c.1) k zero} := hraw
    _ = Fintype.card
          (reversedRightSourceMaskGateFiber ends m j k l zero p) :=
      Fintype.card_congr (Equiv.refl _)



theorem card_leftMaskFiber_le_rightMaskFiber_of_cycleTranslationPairs
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) (X Y : Finset I)
    (hX : X ⊆ p.1) (hY : Y ⊆ p.2)
    (hsrcX : sources ends X = ∅) (hsrcY : sources ends Y = ∅)
    (hpairs : ∀ c : leftSourceMaskFiber ends m j k l zero p,
      0 ≤ reversalGateBalance ends m j k l zero p c +
        reversalGateBalance ends m j k l zero p
          (sourceMaskCycleTranslationEquiv ends m j k l zero p X Y
            hX hY hsrcX hsrcY c)) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
      Fintype.card (rightMaskFiber ends m j k l zero p) :=
  (card_leftMaskFiber_le_rightMaskFiber_iff_sum_reversalGateBalance
    ends m j k l zero p).2
      (sum_reversalGateBalance_nonneg_of_cycleTranslationPairs
        ends m j k l zero p X Y hX hY hsrcX hsrcY hpairs)



theorem card_leftMaskFiber_le_rightMaskFiber_of_exists_cycleTranslationCover
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hcover : ∃ z : sourceMaskCycleSpace ends p,
      CycleTranslationCoversNegative ends m j k l zero p z) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
      Fintype.card (rightMaskFiber ends m j k l zero p) :=
  (card_leftMaskFiber_le_rightMaskFiber_iff_sum_reversalGateBalance
    ends m j k l zero p).2
      (sum_reversalGateBalance_nonneg_of_exists_cycleTranslationCover
        ends m j k l zero p hcover)



theorem card_leftMaskFiber_le_rightMaskFiber_of_outerCyclePairs
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) (Y : Finset I)
    (hY : Y ⊆ p.2) (hsrcY : sources ends Y = ∅)
    (hpairs : ∀ c : leftSourceMaskFiber ends m j k l zero p,
      0 ≤ reversalGateBalance ends m j k l zero p c +
        reversalGateBalance ends m j k l zero p
          (outerCycleSourceMaskEquiv ends m j k l zero p Y hY hsrcY c)) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
      Fintype.card (rightMaskFiber ends m j k l zero p) :=
  (card_leftMaskFiber_le_rightMaskFiber_iff_sum_reversalGateBalance
    ends m j k l zero p).2
      (sum_reversalGateBalance_nonneg_of_outerCyclePairs
        ends m j k l zero p Y hY hsrcY hpairs)

end StatMech.GrahamGHS.FourColor
