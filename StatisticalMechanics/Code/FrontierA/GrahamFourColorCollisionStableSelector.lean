/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamTotalDisconnectedHall










open Finset

namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]



theorem GrahamFiberMinor_of_collisionStableBalancedSelector
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (sigma : (↑m -> Fin 4) -> Finset I × Finset I)
    (hvalid : forall c,
      LeftPattern ends m {j, k} {k, l} k zero c ->
        let X := (sigma c).1
        let Y := (sigma c).2
        X ⊆ colorClass m c 1 ∪ colorClass m c 2 ∧
          Y ⊆ colorClass m c 0 ∪ colorClass m c 3 ∧
          sources ends X = {k, l} ∧
          sources ends Y = ∅ ∧
          RowsDisconnect ends m (balancedSwap m X Y c) k zero)
    (hstable : forall c d,
      LeftPattern ends m {j, k} {k, l} k zero c ->
      LeftPattern ends m {j, k} {k, l} k zero d ->
      balancedSwap m (sigma c).1 (sigma c).2 c =
          balancedSwap m (sigma d).1 (sigma d).2 d ->
        sigma c = sigma d) :
    GrahamFiberMinor ends m j k l zero := by
  classical
  let f : leftFiber ends m {j, k} {k, l} k zero ->
      rightFiber ends m {j, k} {k, l} k zero := fun c =>
    ⟨balancedSwap m (sigma c.1).1 (sigma c.1).2 c.1, by
      rcases hvalid c.1 c.2 with ⟨hX, hY, hsrcX, hsrcY, hdisc⟩
      exact rightPattern_of_balancedTransfer
        c.2 hX hY hsrcX hsrcY hdisc⟩
  apply Fintype.card_le_of_injective f
  intro c d hcd
  apply Subtype.ext
  have himage :
      balancedSwap m (sigma c.1).1 (sigma c.1).2 c.1 =
        balancedSwap m (sigma d.1).1 (sigma d.1).2 d.1 :=
    congrArg Subtype.val hcd
  have hsigma : sigma c.1 = sigma d.1 :=
    hstable c.1 d.1 c.2 d.2 himage
  calc
    c.1 = balancedSwap m (sigma c.1).1 (sigma c.1).2
        (balancedSwap m (sigma c.1).1 (sigma c.1).2 c.1) :=
      (balancedSwap_involutive m
        (sigma c.1).1 (sigma c.1).2 c.1).symm
    _ = balancedSwap m (sigma d.1).1 (sigma d.1).2
        (balancedSwap m (sigma d.1).1 (sigma d.1).2 d.1) := by
      have himage' := congrArg
        (balancedSwap m (sigma d.1).1 (sigma d.1).2) himage
      simpa only [hsigma] using himage'
    _ = d.1 := balancedSwap_involutive m
      (sigma d.1).1 (sigma d.1).2 d.1

end StatMech.GrahamGHS.FourColor
