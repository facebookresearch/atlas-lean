/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamCanonicalTransferMatching










open Finset
open scoped symmDiff

namespace StatMech.GrahamGHS.FourColor

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]


theorem canonicalBalancedSwap_injective
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (r : ↑m -> Fin 4) :
    Function.Injective fun c : ↑m -> Fin 4 =>
      balancedSwap m
        (canonicalMiddleTransfer ends m r k zero)
        (canonicalOuterTransfer ends m r k zero) c := by
  intro c d h
  have h' := congrArg
    (balancedSwap m
      (canonicalMiddleTransfer ends m r k zero)
      (canonicalOuterTransfer ends m r k zero)) h
  simpa only [balancedSwap_involutive] using h'



theorem canonicalOppositeReturn_injective
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (r : ↑m -> Fin 4) :
    Function.Injective fun c : ↑m -> Fin 4 =>
      middleSwap m
        (balancedSwap m
          (canonicalMiddleTransfer ends m r k zero)
          (canonicalOuterTransfer ends m r k zero) c) := by
  intro c d h
  have h' := congrArg (middleSwap m) h
  simp only [middleSwap_involutive] at h'
  exact canonicalBalancedSwap_injective ends m k zero r h'

omit [Fintype I] in


theorem canonicalTransfer_oppositeReturn_eq_middleSwap
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (r c : ↑m -> Fin 4) :
    balancedSwap m
        (canonicalMiddleTransfer ends m r k zero)
        (canonicalOuterTransfer ends m r k zero)
        (middleSwap m
          (balancedSwap m
            (canonicalMiddleTransfer ends m r k zero)
            (canonicalOuterTransfer ends m r k zero) c)) =
      middleSwap m c := by
  funext i
  have hv : c i = 0 ∨ c i = 1 ∨ c i = 2 ∨ c i = 3 := by omega
  rcases hv with hv | hv | hv | hv <;>
    by_cases hM : (i : I) ∈ canonicalMiddleTransfer ends m r k zero <;>
    by_cases hO : (i : I) ∈ canonicalOuterTransfer ends m r k zero <;>
    simp [middleSwap, balancedSwap, middleSwapOn, outerSwapOn,
      hM, hO, hv] <;> decide

omit [Fintype I] in


theorem canonicalTransferWorks_oppositeReturn_iff
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (r c : ↑m -> Fin 4) :
    CanonicalTransferWorks ends m k zero r
        (middleSwap m
          (balancedSwap m
            (canonicalMiddleTransfer ends m r k zero)
            (canonicalOuterTransfer ends m r k zero) c)) ↔
      RowsDisconnect ends m (middleSwap m c) k zero := by
  unfold CanonicalTransferWorks
  rw [canonicalTransfer_oppositeReturn_eq_middleSwap]




theorem canonicalCollision_oppositeCorner_ne
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (q r : ↑m -> Fin 4)
    (hqr : q ≠ r)
    (hcollision :
      middleSwap m
          (balancedSwap m
            (canonicalMiddleTransfer ends m q k zero)
            (canonicalOuterTransfer ends m q k zero) q) =
        middleSwap m
          (balancedSwap m
            (canonicalMiddleTransfer ends m r k zero)
            (canonicalOuterTransfer ends m r k zero) r)) :
    middleSwap m
        (balancedSwap m
          (canonicalMiddleTransfer ends m r k zero)
          (canonicalOuterTransfer ends m r k zero) q) ≠
      middleSwap m
        (balancedSwap m
          (canonicalMiddleTransfer ends m q k zero)
          (canonicalOuterTransfer ends m q k zero) q) := by
  intro hopposite
  have hcollision' := congrArg (middleSwap m) hcollision
  have hopposite' := congrArg (middleSwap m) hopposite
  simp only [middleSwap_involutive] at hcollision' hopposite'
  apply hqr
  apply canonicalBalancedSwap_injective ends m k zero r
  exact hopposite'.trans hcollision'

omit [Fintype I] in


theorem middleSwap_canonicalQuadrangleCompletion_selfReturn
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (q r : ↑m -> Fin 4) :
    middleSwap m
        (canonicalQuadrangleCompletion ends m k zero q r
          (middleSwap m
            (balancedSwap m
              (canonicalMiddleTransfer ends m q k zero)
              (canonicalOuterTransfer ends m q k zero) q))) =
      balancedSwap m
        (canonicalMiddleTransfer ends m r k zero)
        (canonicalOuterTransfer ends m r k zero) q := by
  rw [canonicalQuadrangleCompletion]
  funext i
  have hv : q i = 0 ∨ q i = 1 ∨ q i = 2 ∨ q i = 3 := by omega
  rcases hv with hv | hv | hv | hv <;>
    by_cases hqM : (i : I) ∈ canonicalMiddleTransfer ends m q k zero <;>
    by_cases hrM : (i : I) ∈ canonicalMiddleTransfer ends m r k zero <;>
    by_cases hqO : (i : I) ∈ canonicalOuterTransfer ends m q k zero <;>
    by_cases hrO : (i : I) ∈ canonicalOuterTransfer ends m r k zero <;>
    simp [middleSwap, balancedSwap, middleSwapOn, outerSwapOn,
      canonicalMiddleTransferDifference, canonicalOuterTransferDifference,
      Finset.mem_symmDiff, hqM, hrM, hqO, hrO, hv] <;> decide



theorem canonicalCollision_referenceDifference_ne
    (ends : I -> Sym2 W) (m : Finset I) (k zero : W)
    (q r : ↑m -> Fin 4)
    (hqr : q ≠ r)
    (hcollision :
      middleSwap m
          (balancedSwap m
            (canonicalMiddleTransfer ends m q k zero)
            (canonicalOuterTransfer ends m q k zero) q) =
        middleSwap m
          (balancedSwap m
            (canonicalMiddleTransfer ends m r k zero)
            (canonicalOuterTransfer ends m r k zero) r)) :
    canonicalQuadrangleCompletion ends m k zero q r
        (middleSwap m
          (balancedSwap m
            (canonicalMiddleTransfer ends m q k zero)
            (canonicalOuterTransfer ends m q k zero) q)) ≠
      middleSwap m
        (balancedSwap m
          (canonicalMiddleTransfer ends m q k zero)
          (canonicalOuterTransfer ends m q k zero) q) := by
  intro heq
  have heq' := congrArg (middleSwap m) heq
  rw [middleSwap_canonicalQuadrangleCompletion_selfReturn] at heq'
  simp only [middleSwap_involutive] at heq'
  exact canonicalCollision_oppositeCorner_ne
    ends m k zero q r hqr hcollision
      (congrArg (middleSwap m) heq')




theorem canonicalSelfTransfer_collision_oppositeWorks
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (q r : leftMaskFiber ends m j k l zero p)
    (himage :
      (canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p q q
          (canonicalTransferWorks_self hloop hjk hkl hk0 q)).1.1 =
        (canonicalTransferMapOfWorks
          ends m j k l zero hloop hjk hkl p r r
            (canonicalTransferWorks_self hloop hjk hkl hk0 r)).1.1) :
    CanonicalTransferWorks ends m k zero r.1.1 q.1.1 ∧
      CanonicalTransferWorks ends m k zero q.1.1 r.1.1 := by
  have hrow := congrArg (fun c => rowClass m c 0) himage
  have hqnormal : rowClass m
        (canonicalTransferMapOfWorks
          ends m j k l zero hloop hjk hkl p q q
            (canonicalTransferWorks_self hloop hjk hkl hk0 q)).1.1 0 =
      canonicalNormalRow ends m k zero q.1.1 := by
    simpa only [canonicalTranslatedRow, canonicalNormalRow] using
      (rowClass_zero_canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p q q
          (canonicalTransferWorks_self hloop hjk hkl hk0 q))
  have hrnormal : rowClass m
        (canonicalTransferMapOfWorks
          ends m j k l zero hloop hjk hkl p r r
            (canonicalTransferWorks_self hloop hjk hkl hk0 r)).1.1 0 =
      canonicalNormalRow ends m k zero r.1.1 := by
    simpa only [canonicalTranslatedRow, canonicalNormalRow] using
      (rowClass_zero_canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p r r
          (canonicalTransferWorks_self hloop hjk hkl hk0 r))
  have hnormal : canonicalNormalRow ends m k zero q.1.1 =
      canonicalNormalRow ends m k zero r.1.1 :=
    hqnormal.symm.trans (hrow.trans hrnormal)
  have hcomplete := canonicalMaskNormalFiberComplete
    ends m j k l zero hloop hjk hkl p
  exact ⟨hcomplete r q hnormal.symm, hcomplete q r hnormal⟩




theorem canonicalSelfTransfer_collision_twoCommonImages
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (q r : leftMaskFiber ends m j k l zero p)
    (hqr : q ≠ r)
    (himage :
      (canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p q q
          (canonicalTransferWorks_self hloop hjk hkl hk0 q)).1.1 =
        (canonicalTransferMapOfWorks
          ends m j k l zero hloop hjk hkl p r r
            (canonicalTransferWorks_self hloop hjk hkl hk0 r)).1.1) :
    ∃ q₁ q₂ : rightMaskFiber ends m j k l zero p,
      q₁ ≠ q₂ ∧
        q₁ ∈ canonicalMaskRightImages ends m j k l zero p q ∧
        q₁ ∈ canonicalMaskRightImages ends m j k l zero p r ∧
        q₂ ∈ canonicalMaskRightImages ends m j k l zero p q ∧
        q₂ ∈ canonicalMaskRightImages ends m j k l zero p r := by
  have hrow := congrArg (fun c => rowClass m c 0) himage
  have hqrow : rowClass m
        (canonicalTransferMapOfWorks
          ends m j k l zero hloop hjk hkl p q q
            (canonicalTransferWorks_self hloop hjk hkl hk0 q)).1.1 0 =
      canonicalTranslatedRow ends m k zero q.1.1 q.1.1 :=
    rowClass_zero_canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p q q
        (canonicalTransferWorks_self hloop hjk hkl hk0 q)
  have hrrow : rowClass m
        (canonicalTransferMapOfWorks
          ends m j k l zero hloop hjk hkl p r r
            (canonicalTransferWorks_self hloop hjk hkl hk0 r)).1.1 0 =
      canonicalTranslatedRow ends m k zero r.1.1 r.1.1 :=
    rowClass_zero_canonicalTransferMapOfWorks
      ends m j k l zero hloop hjk hkl p r r
        (canonicalTransferWorks_self hloop hjk hkl hk0 r)
  have htranslated :
      canonicalTranslatedRow ends m k zero q.1.1 q.1.1 =
        canonicalTranslatedRow ends m k zero r.1.1 r.1.1 :=
    hqrow.symm.trans (hrow.trans hrrow)
  have hopposite :=
    (canonicalSelfTransfer_collision_oppositeWorks
      ends m j k l zero hloop hjk hkl hk0 p q r himage).1
  exact exists_two_common_canonicalMaskRightImages_of_collisionSquare
    hloop hjk hkl q r q r hqr
      (canonicalTransferWorks_self hloop hjk hkl hk0 q)
      htranslated hopposite




theorem exists_canonicalMaskRightImage_ne_self_of_selfImage_collision
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (q r : leftMaskFiber ends m j k l zero p)
    (hqr : q ≠ r)
    (himage :
      (canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p q q
          (canonicalTransferWorks_self hloop hjk hkl hk0 q)).1.1 =
        (canonicalTransferMapOfWorks
          ends m j k l zero hloop hjk hkl p r r
            (canonicalTransferWorks_self hloop hjk hkl hk0 r)).1.1) :
    ∃ s : rightMaskFiber ends m j k l zero p,
      s ∈ canonicalMaskRightImages ends m j k l zero p q ∧
        s ≠ canonicalTransferMapOfWorks
          ends m j k l zero hloop hjk hkl p q q
            (canonicalTransferWorks_self hloop hjk hkl hk0 q) := by
  obtain ⟨q₁, q₂, hne, hq₁q, -, hq₂q, -⟩ :=
    canonicalSelfTransfer_collision_twoCommonImages
      ends m j k l zero hloop hjk hkl hk0 p q r hqr himage
  let self := canonicalTransferMapOfWorks
    ends m j k l zero hloop hjk hkl p q q
      (canonicalTransferWorks_self hloop hjk hkl hk0 q)
  by_cases hq₁ : q₁ = self
  · exact ⟨q₂, hq₂q, fun hq₂ => hne (hq₁.trans hq₂.symm)⟩
  · exact ⟨q₁, hq₁q, hq₁⟩




theorem card_le_canonicalMaskRightNeighborhood_of_selfImageFiber
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (p : Finset I × Finset I)
    (S : Finset (leftMaskFiber ends m j k l zero p))
    (r : leftMaskFiber ends m j k l zero p)
    (himage : ∀ c ∈ S,
      (canonicalTransferMapOfWorks
        ends m j k l zero hloop hjk hkl p r r
          (canonicalTransferWorks_self hloop hjk hkl hk0 r)).1.1 =
        (canonicalTransferMapOfWorks
          ends m j k l zero hloop hjk hkl p c c
            (canonicalTransferWorks_self hloop hjk hkl hk0 c)).1.1) :
    S.card ≤
      (canonicalMaskRightNeighborhood ends m j k l zero p S).card := by
  apply card_le_canonicalMaskRightNeighborhood_of_reference
    ends m j k l zero hloop hjk hkl p S r
  intro c hc
  exact (canonicalSelfTransfer_collision_oppositeWorks
    ends m j k l zero hloop hjk hkl hk0 p c r
      (himage c hc).symm).1

end StatMech.GrahamGHS.FourColor
