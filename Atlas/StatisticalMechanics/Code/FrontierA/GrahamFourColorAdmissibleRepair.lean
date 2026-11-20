/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamFourColorInvariantMasks










open Finset
open Classical
open scoped symmDiff

namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {ι W : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype W] [DecidableEq W]




def BalancedRepairAdmissible (ends : ι -> Sym2 W) (m X : Finset ι)
    (k zero : W) (c : ↑m -> Fin 4) (Y : Finset ι) : Prop :=
  Y ⊆ outerMask m c ∧
    sources ends Y = ∅ ∧
    RowsDisconnect ends m c k zero ∧
    RowsDisconnect ends m (balancedSwap m X Y c) k zero


noncomputable def balancedRepairs (ends : ι -> Sym2 W) (m X : Finset ι)
    (k zero : W) (c : ↑m -> Fin 4) : Finset (Finset ι) :=
  (outerMask m c).powerset.filter
    (fun Y => sources ends Y = ∅ ∧
      RowsDisconnect ends m c k zero ∧
      RowsDisconnect ends m (balancedSwap m X Y c) k zero)

@[simp] theorem mem_balancedRepairs_iff
    (ends : ι -> Sym2 W) (m X : Finset ι) (k zero : W)
    (c : ↑m -> Fin 4) (Y : Finset ι) :
    Y ∈ balancedRepairs ends m X k zero c ↔
      BalancedRepairAdmissible ends m X k zero c Y := by
  simp [balancedRepairs, BalancedRepairAdmissible]



theorem balancedRepairAdmissible_swap
    (ends : ι -> Sym2 W) (m X : Finset ι) (k zero : W)
    (c : ↑m -> Fin 4) (Y : Finset ι)
    (hY : BalancedRepairAdmissible ends m X k zero c Y) :
    BalancedRepairAdmissible ends m X k zero
      (balancedSwap m X Y c) Y := by
  refine ⟨?_, hY.2.1, hY.2.2.2, ?_⟩
  · rw [outerMask_balancedSwap]
    exact hY.1
  · rw [balancedSwap_involutive]
    exact hY.2.2.1


theorem balancedRepairAdmissible_swap_iff
    (ends : ι -> Sym2 W) (m X : Finset ι) (k zero : W)
    (c : ↑m -> Fin 4) (Y : Finset ι) :
    BalancedRepairAdmissible ends m X k zero
        (balancedSwap m X Y c) Y ↔
      BalancedRepairAdmissible ends m X k zero c Y := by
  constructor
  · intro h
    have hs := balancedRepairAdmissible_swap ends m X k zero
      (balancedSwap m X Y c) Y h
    simpa only [balancedSwap_involutive] using hs
  · exact balancedRepairAdmissible_swap ends m X k zero c Y


theorem mem_balancedRepairs_swap_iff
    (ends : ι -> Sym2 W) (m X : Finset ι) (k zero : W)
    (c : ↑m -> Fin 4) (Y : Finset ι) :
    Y ∈ balancedRepairs ends m X k zero (balancedSwap m X Y c) ↔
      Y ∈ balancedRepairs ends m X k zero c := by
  simp only [mem_balancedRepairs_iff, balancedRepairAdmissible_swap_iff]


def BalancedRepairRelated (ends : ι -> Sym2 W) (m X : Finset ι)
    (k zero : W) (c d : ↑m -> Fin 4) : Prop :=
  ∃ Y, BalancedRepairAdmissible ends m X k zero c Y ∧
    d = balancedSwap m X Y c


theorem balancedRepairRelated_symm
    (ends : ι -> Sym2 W) (m X : Finset ι) (k zero : W)
    {c d : ↑m -> Fin 4}
    (h : BalancedRepairRelated ends m X k zero c d) :
    BalancedRepairRelated ends m X k zero d c := by
  rcases h with ⟨Y, hY, rfl⟩
  refine ⟨Y, balancedRepairAdmissible_swap ends m X k zero c Y hY, ?_⟩
  exact (balancedSwap_involutive m X Y c).symm




def balancedMiddleDifference (m : Finset ι) (c d : ↑m -> Fin 4) : Finset ι :=
  colorClass m c 1 ∆ colorClass m d 1


def balancedOuterDifference (m : Finset ι) (c d : ↑m -> Fin 4) : Finset ι :=
  colorClass m c 0 ∆ colorClass m d 0

@[simp] theorem subtype_mem_colorClass_iff
    (m : Finset ι) (c : ↑m -> Fin 4) (i : ↑m) (a : Fin 4) :
    (i : ι) ∈ colorClass m c a ↔ c i = a := by
  rw [mem_colorClass_iff]
  constructor
  · rintro ⟨hi, hci⟩
    have heq : (⟨i, hi⟩ : ↑m) = i := Subtype.ext rfl
    simpa only [heq] using hci
  · intro hci
    exact ⟨i.2, hci⟩




theorem balancedSwap_difference
    (m : Finset ι) (c d : ↑m -> Fin 4)
    (hmid : middleMask m c = middleMask m d)
    (hout : outerMask m c = outerMask m d) :
    balancedSwap m (balancedMiddleDifference m c d)
      (balancedOuterDifference m c d) c = d := by
  funext i
  have hi : (i : ι) ∈ m := i.2
  have hmidi : (i : ι) ∈ middleMask m c ↔ (i : ι) ∈ middleMask m d := by
    rw [hmid]
  have houti : (i : ι) ∈ outerMask m c ↔ (i : ι) ∈ outerMask m d := by
    rw [hout]
  have hmidi' : (c i = 1 ∨ c i = 2) ↔ (d i = 1 ∨ d i = 2) := by
    simpa [middleMask] using hmidi
  have houti' : (c i = 0 ∨ c i = 3) ↔ (d i = 0 ∨ d i = 3) := by
    simpa [outerMask] using houti
  have hc : c i = 0 ∨ c i = 1 ∨ c i = 2 ∨ c i = 3 := by omega
  have hd : d i = 0 ∨ d i = 1 ∨ d i = 2 ∨ d i = 3 := by omega
  rcases hc with hc | hc | hc | hc <;>
    rcases hd with hd | hd | hd | hd <;>
      simp [balancedMiddleDifference, balancedOuterDifference,
        Finset.mem_symmDiff, balancedSwap, middleSwapOn, outerSwapOn,
        Equiv.swap_apply_def, hc, hd] at hmidi' houti' ⊢

theorem balancedMiddleDifference_subset
    (m : Finset ι) (c d : ↑m -> Fin 4)
    (hmid : middleMask m c = middleMask m d) :
    balancedMiddleDifference m c d ⊆ middleMask m c := by
  intro i hi
  rw [balancedMiddleDifference, Finset.mem_symmDiff] at hi
  rcases hi with hi | hi
  · exact Finset.mem_union_left _ hi.1
  · rw [hmid]
    exact Finset.mem_union_left _ hi.1

theorem balancedOuterDifference_subset
    (m : Finset ι) (c d : ↑m -> Fin 4)
    (hout : outerMask m c = outerMask m d) :
    balancedOuterDifference m c d ⊆ outerMask m c := by
  intro i hi
  rw [balancedOuterDifference, Finset.mem_symmDiff] at hi
  rcases hi with hi | hi
  · exact Finset.mem_union_left _ hi.1
  · rw [hout]
    exact Finset.mem_union_left _ hi.1



theorem left_right_sameMasks_admissible
    {ends : ι -> Sym2 W} {m : Finset ι} {j k l zero : W}
    {c d : ↑m -> Fin 4}
    (hc : LeftPattern ends m {j, k} {k, l} k zero c)
    (hd : RightPattern ends m {j, k} {k, l} k zero d)
    (hmid : middleMask m c = middleMask m d)
    (hout : outerMask m c = outerMask m d) :
    let X := balancedMiddleDifference m c d
    let Y := balancedOuterDifference m c d
    X ⊆ middleMask m c ∧
      Y ⊆ outerMask m c ∧
      sources ends X = {k, l} ∧
      sources ends Y = ∅ ∧
      BalancedRepairAdmissible ends m X k zero c Y ∧
      balancedSwap m X Y c = d := by
  dsimp only
  have hX := balancedMiddleDifference_subset m c d hmid
  have hY := balancedOuterDifference_subset m c d hout
  have hsrcX : sources ends (balancedMiddleDifference m c d) = {k, l} := by
    rw [balancedMiddleDifference, sources_symmDiff, hc.2.1, hd.2.1]
    simp
  have hsrcY : sources ends (balancedOuterDifference m c d) = ∅ := by
    rw [balancedOuterDifference, sources_symmDiff, hc.1, hd.1]
    exact symmDiff_self ({j, k} : Finset W)
  have hswap := balancedSwap_difference m c d hmid hout
  refine ⟨hX, hY, hsrcX, hsrcY, ?_, hswap⟩
  refine ⟨hY, hsrcY, hc.2.2.2.2, ?_⟩
  rw [hswap]
  exact hd.2.2.2.2



def fourColorMaskProfile (m : Finset ι) (c : ↑m -> Fin 4) :
    Finset ι × Finset ι :=
  (middleMask m c, outerMask m c)

def leftMaskFiber (ends : ι -> Sym2 W) (m : Finset ι)
    (j k l zero : W) (p : Finset ι × Finset ι) :=
  {c : leftFiber ends m {j, k} {k, l} k zero //
    fourColorMaskProfile m c.1 = p}

def rightMaskFiber (ends : ι -> Sym2 W) (m : Finset ι)
    (j k l zero : W) (p : Finset ι × Finset ι) :=
  {c : rightFiber ends m {j, k} {k, l} k zero //
    fourColorMaskProfile m c.1 = p}

noncomputable instance instFintypeLeftMaskFiber
    (ends : ι -> Sym2 W) (m : Finset ι) (j k l zero : W)
    (p : Finset ι × Finset ι) :
    Fintype (leftMaskFiber ends m j k l zero p) := by
  classical
  unfold leftMaskFiber
  infer_instance

noncomputable instance instFintypeRightMaskFiber
    (ends : ι -> Sym2 W) (m : Finset ι) (j k l zero : W)
    (p : Finset ι × Finset ι) :
    Fintype (rightMaskFiber ends m j k l zero p) := by
  classical
  unfold rightMaskFiber
  infer_instance

theorem leftFiber_card_eq_sum_maskFibers
    (ends : ι -> Sym2 W) (m : Finset ι) (j k l zero : W) :
    Fintype.card (leftFiber ends m {j, k} {k, l} k zero) =
      ∑ p : Finset ι × Finset ι,
        Fintype.card (leftMaskFiber ends m j k l zero p) := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr
    (Equiv.sigmaFiberEquiv
      (fun c : leftFiber ends m {j, k} {k, l} k zero =>
        fourColorMaskProfile m c.1)).symm

theorem rightFiber_card_eq_sum_maskFibers
    (ends : ι -> Sym2 W) (m : Finset ι) (j k l zero : W) :
    Fintype.card (rightFiber ends m {j, k} {k, l} k zero) =
      ∑ p : Finset ι × Finset ι,
        Fintype.card (rightMaskFiber ends m j k l zero p) := by
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr
    (Equiv.sigmaFiberEquiv
      (fun c : rightFiber ends m {j, k} {k, l} k zero =>
        fourColorMaskProfile m c.1)).symm



theorem GrahamFiberMinor_of_maskwise
    (ends : ι -> Sym2 W) (m : Finset ι) (j k l zero : W)
    (hmask : ∀ p : Finset ι × Finset ι,
      Fintype.card (leftMaskFiber ends m j k l zero p) <=
        Fintype.card (rightMaskFiber ends m j k l zero p)) :
    GrahamFiberMinor ends m j k l zero := by
  rw [GrahamFiberMinor, leftFiber_card_eq_sum_maskFibers,
    rightFiber_card_eq_sum_maskFibers]
  exact Finset.sum_le_sum fun p _ => hmask p




theorem rightMaskFiber_nonempty_of_left
    {ends : ι -> Sym2 W} {m : Finset ι} {j k l zero : W}
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset ι × Finset ι)
    (c : leftMaskFiber ends m j k l zero p) :
    Nonempty (rightMaskFiber ends m j k l zero p) := by
  let X := canonicalMiddleTransfer ends m c.1.1 k zero
  let Y := canonicalOuterTransfer ends m c.1.1 k zero
  let d := balancedSwap m X Y c.1.1
  have hv := canonicalTransfers_valid hloop hjk hkl c.1.2
  have hdisc := canonicalBalancedSwap_disconnects
    hloop hjk hkl hk0 c.1.2
  have hd : RightPattern ends m {j, k} {k, l} k zero d :=
    rightPattern_of_balancedTransfer c.1.2 hv.1 hv.2.1
      hv.2.2.1 hv.2.2.2 hdisc
  have hprofile : fourColorMaskProfile m d = p := by
    calc
      fourColorMaskProfile m d = fourColorMaskProfile m c.1.1 := by
        simp [fourColorMaskProfile, d, X, Y,
          middleMask_balancedSwap, outerMask_balancedSwap]
      _ = p := c.2
  exact ⟨⟨⟨d, hd⟩, hprofile⟩⟩

end StatMech.GrahamGHS.FourColor
