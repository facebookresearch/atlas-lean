/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamFourColorAdmissibleRepair










open Finset

namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]




abbrev MaskFiberEmbeddings (ends : I -> Sym2 W) (m : Finset I)
    (j k l zero : W) :=
  forall p : Finset I × Finset I,
    leftMaskFiber ends m j k l zero p ↪
      rightMaskFiber ends m j k l zero p





theorem nonempty_maskFiberEmbeddings_iff
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W) :
    Nonempty (MaskFiberEmbeddings ends m j k l zero) ↔
      forall p : Finset I × Finset I,
        Fintype.card (leftMaskFiber ends m j k l zero p) <=
          Fintype.card (rightMaskFiber ends m j k l zero p) := by
  classical
  constructor
  · rintro ⟨f⟩ p
    exact Fintype.card_le_of_injective (f p) (f p).injective
  · intro h
    exact ⟨fun p => Classical.choice
      (Function.Embedding.nonempty_iff_card_le.mpr (h p))⟩



theorem GrahamFiberMinor_of_maskFiberEmbeddings
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (f : MaskFiberEmbeddings ends m j k l zero) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_maskwise
  intro p
  exact Fintype.card_le_of_injective (f p) (f p).injective


noncomputable def maskFiberMatchedRight
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (f : MaskFiberEmbeddings ends m j k l zero)
    {p : Finset I × Finset I}
    (c : leftMaskFiber ends m j k l zero p) : ↑m -> Fin 4 :=
  (f p c).1.1







theorem maskFiberEmbedding_differenceTransfer
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (f : MaskFiberEmbeddings ends m j k l zero)
    {p : Finset I × Finset I}
    (c : leftMaskFiber ends m j k l zero p) :
    let d := (f p c).1.1
    let X := balancedMiddleDifference m c.1.1 d
    let Y := balancedOuterDifference m c.1.1 d
    X ⊆ middleMask m c.1.1 ∧
      Y ⊆ outerMask m c.1.1 ∧
      sources ends X = {k, l} ∧
      sources ends Y = ∅ ∧
      BalancedRepairAdmissible ends m X k zero c.1.1 Y ∧
      balancedSwap m X Y c.1.1 = d := by
  let d := (f p c).1.1
  have hc : LeftPattern ends m {j, k} {k, l} k zero c.1.1 := c.1.2
  have hd : RightPattern ends m {j, k} {k, l} k zero d := (f p c).1.2
  have hprofile : fourColorMaskProfile m c.1.1 =
      fourColorMaskProfile m d := c.2.trans (f p c).2.symm
  have hmid : middleMask m c.1.1 = middleMask m d :=
    congrArg Prod.fst hprofile
  have hout : outerMask m c.1.1 = outerMask m d :=
    congrArg Prod.snd hprofile
  simpa only [d] using left_right_sameMasks_admissible hc hd hmid hout



theorem eq_of_middle_outer_colorClass_one_three
    (m : Finset I) (c d : ↑m -> Fin 4)
    (hmid : middleMask m c = middleMask m d)
    (hout : outerMask m c = outerMask m d)
    (hone : colorClass m c 1 = colorClass m d 1)
    (hthree : colorClass m c 3 = colorClass m d 3) : c = d := by
  funext i
  have hmidMem := congrArg (fun S : Finset I => i.1 ∈ S) hmid
  have houtMem := congrArg (fun S : Finset I => i.1 ∈ S) hout
  have honeMem := congrArg (fun S : Finset I => i.1 ∈ S) hone
  have hthreeMem := congrArg (fun S : Finset I => i.1 ∈ S) hthree
  have hc : c i = 0 ∨ c i = 1 ∨ c i = 2 ∨ c i = 3 := by omega
  have hd : d i = 0 ∨ d i = 1 ∨ d i = 2 ∨ d i = 3 := by omega
  rcases hc with hc | hc | hc | hc <;>
    rcases hd with hd | hd | hd | hd <;>
    simp [middleMask, outerMask, mem_colorClass_iff, i.2, hc, hd] at *



theorem subsingleton_leftMaskFiber_of_cycleSectors
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (hmiddle : Subsingleton (boundarySector ends p.1 ∅))
    (houter : Subsingleton (boundarySector ends p.2 ∅)) :
    Subsingleton (leftMaskFiber ends m j k l zero p) := by
  constructor
  intro c d
  apply Subtype.ext
  apply Subtype.ext
  have hcmid : middleMask m c.1.1 = p.1 := congrArg Prod.fst c.2
  have hdmid : middleMask m d.1.1 = p.1 := congrArg Prod.fst d.2
  have hcout : outerMask m c.1.1 = p.2 := congrArg Prod.snd c.2
  have hdout : outerMask m d.1.1 = p.2 := congrArg Prod.snd d.2
  let cMiddle : boundarySector ends p.1 ∅ :=
    ⟨colorClass m c.1.1 1, by
      constructor
      · intro edge hedge
        rw [← hcmid]
        exact Finset.mem_union_left _ hedge
      · exact c.1.2.2.1⟩
  let dMiddle : boundarySector ends p.1 ∅ :=
    ⟨colorClass m d.1.1 1, by
      constructor
      · intro edge hedge
        rw [← hdmid]
        exact Finset.mem_union_left _ hedge
      · exact d.1.2.2.1⟩
  let cOuter : boundarySector ends p.2 ∅ :=
    ⟨colorClass m c.1.1 3, by
      constructor
      · intro edge hedge
        rw [← hcout]
        exact Finset.mem_union_right _ hedge
      · exact c.1.2.2.2.2.1⟩
  let dOuter : boundarySector ends p.2 ∅ :=
    ⟨colorClass m d.1.1 3, by
      constructor
      · intro edge hedge
        rw [← hdout]
        exact Finset.mem_union_right _ hedge
      · exact d.1.2.2.2.2.1⟩
  apply eq_of_middle_outer_colorClass_one_three m c.1.1 d.1.1
  · exact hcmid.trans hdmid.symm
  · exact hcout.trans hdout.symm
  · exact congrArg Subtype.val (hmiddle.allEq cMiddle dMiddle)
  · exact congrArg Subtype.val (houter.allEq cOuter dOuter)




theorem GrahamFiberMinor_of_subsingleton_leftMaskFibers
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hsub : ∀ p : Finset I × Finset I,
      Subsingleton (leftMaskFiber ends m j k l zero p)) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_maskFiberEmbeddings
  intro p
  by_cases hleft : Nonempty (leftMaskFiber ends m j k l zero p)
  · let c := Classical.choice hleft
    let d := Classical.choice
      (rightMaskFiber_nonempty_of_left hloop hjk hkl hk0 p c)
    letI : Subsingleton (leftMaskFiber ends m j k l zero p) := hsub p
    exact
      { toFun := fun _ => d
        inj' := fun a b _ => Subsingleton.elim a b }
  · exact
      { toFun := fun c => False.elim (hleft ⟨c⟩)
        inj' := fun a _ _ => False.elim (hleft ⟨a⟩) }



theorem GrahamFiberMinor_of_subsingleton_cycleSectors
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hcycle : ∀ p : Finset I × Finset I,
      Subsingleton (boundarySector ends p.1 ∅) ∧
        Subsingleton (boundarySector ends p.2 ∅)) :
    GrahamFiberMinor ends m j k l zero := by
  apply GrahamFiberMinor_of_subsingleton_leftMaskFibers
    ends m j k l zero hloop hjk hkl hk0
  intro p
  exact subsingleton_leftMaskFiber_of_cycleSectors
    ends m j k l zero p (hcycle p).1 (hcycle p).2

end StatMech.GrahamGHS.FourColor
