/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamRankOneGate









open Finset
open Classical

namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]



theorem rowsDisconnect_of_total_disconnected
    (ends : I → Sym2 W) (m : Finset I) (k zero : W)
    (hdisc : ¬ connK ends m k zero) (c : ↑m → Fin 4) :
    RowsDisconnect ends m c k zero := by
  constructor
  · intro h
    exact hdisc (connK_mono
      (Finset.union_subset (colorClass_subset m c 0)
        (colorClass_subset m c 1)) h)
  · intro h
    exact hdisc (connK_mono
      (Finset.union_subset (colorClass_subset m c 2)
        (colorClass_subset m c 3)) h)



noncomputable def totalDisconnectedMaskFiberMap
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hdisc : ¬ connK ends m k zero)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    rightMaskFiber ends m j k l zero p := by
  let q := balancedSwap m p.1 ∅ c.1.1
  have hmid : middleMask m c.1.1 = p.1 := congrArg Prod.fst c.2
  have hX : p.1 ⊆ colorClass m c.1.1 1 ∪ colorClass m c.1.1 2 := by
    rw [← middleMask, hmid]
  have hXsrc : sources ends p.1 = {k, l} := by
    rw [← hmid]
    exact leftPattern_middleMask_sources c.1.2
  have hq : RightPattern ends m {j, k} {k, l} k zero q := by
    apply rightPattern_of_balancedTransfer c.1.2 hX (Finset.empty_subset _)
      hXsrc
    · simp [sources, degK]
    · exact rowsDisconnect_of_total_disconnected ends m k zero hdisc q
  refine ⟨⟨q, hq⟩, ?_⟩
  calc
    fourColorMaskProfile m q = fourColorMaskProfile m c.1.1 := by
      simp [q, fourColorMaskProfile, middleMask_balancedSwap,
        outerMask_balancedSwap]
    _ = p := c.2



noncomputable def totalDisconnectedMaskFiberEmbedding
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hdisc : ¬ connK ends m k zero)
    (p : Finset I × Finset I) :
    leftMaskFiber ends m j k l zero p ↪
      rightMaskFiber ends m j k l zero p where
  toFun := totalDisconnectedMaskFiberMap ends m j k l zero hdisc p
  inj' := by
    intro c d hcd
    apply Subtype.ext
    apply Subtype.ext
    have hval := congrArg
      (fun z : rightMaskFiber ends m j k l zero p => z.1.1) hcd
    change balancedSwap m p.1 ∅ c.1.1 =
      balancedSwap m p.1 ∅ d.1.1 at hval
    have hinv := congrArg (balancedSwap m p.1 ∅) hval
    simpa only [balancedSwap_involutive] using hinv


theorem rowDataRepairHall_of_total_disconnected
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (hdisc : ¬ connK ends m k zero) :
    RowDataRepairHall ends m j k l zero := by
  apply rowDataRepairHall_of_maskFiberEmbeddings
  intro p
  exact totalDisconnectedMaskFiberEmbedding
    ends m j k l zero hdisc p

end StatMech.GrahamGHS.FourColor
