/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamRowDataMaskHall









open Finset
open Classical

namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

variable {I W : Type*} [Fintype I] [DecidableEq I]
  [Fintype W] [DecidableEq W]



theorem embedding_surjective_of_card_le_two_of_ne
    {A B : Type*} [Fintype A] [Fintype B]
    (f : A ↪ B) (a b : A) (hab : a ≠ b)
    (hB : Fintype.card B ≤ 2) : Function.Surjective f := by
  letI : Nontrivial A := ⟨⟨a, b, hab⟩⟩
  have hone : 1 < Fintype.card A := Fintype.one_lt_card
  have hle : Fintype.card A ≤ Fintype.card B :=
    Fintype.card_le_of_embedding f
  have heq : Fintype.card A = Fintype.card B := by omega
  exact ((Fintype.bijective_iff_injective_and_card f).2
    ⟨f.injective, heq⟩).2



noncomputable def emptyBoundarySector
    (ends : I → Sym2 W) (S : Finset I) : boundarySector ends S ∅ := by
  refine ⟨∅, Finset.empty_subset _, ?_⟩
  simp [sources, degK]


noncomputable def emptyMaskCyclePair
    (ends : I → Sym2 W) (p : Finset I × Finset I) :
    boundarySector ends p.1 ∅ × boundarySector ends p.2 ∅ :=
  (emptyBoundarySector ends p.1, emptyBoundarySector ends p.2)



theorem eq_of_middle_outer_colorClass_two_three
    (m : Finset I) (c d : ↑m -> Fin 4)
    (hmid : middleMask m c = middleMask m d)
    (hout : outerMask m c = outerMask m d)
    (htwo : colorClass m c 2 = colorClass m d 2)
    (hthree : colorClass m c 3 = colorClass m d 3) : c = d := by
  funext i
  have hmidMem := congrArg (fun S : Finset I => i.1 ∈ S) hmid
  have houtMem := congrArg (fun S : Finset I => i.1 ∈ S) hout
  have htwoMem := congrArg (fun S : Finset I => i.1 ∈ S) htwo
  have hthreeMem := congrArg (fun S : Finset I => i.1 ∈ S) hthree
  have hc : c i = 0 ∨ c i = 1 ∨ c i = 2 ∨ c i = 3 := by omega
  have hd : d i = 0 ∨ d i = 1 ∨ d i = 2 ∨ d i = 3 := by omega
  rcases hc with hc | hc | hc | hc <;>
    rcases hd with hd | hd | hd | hd <;>
    simp [middleMask, outerMask, mem_colorClass_iff, i.2, hc, hd] at *



noncomputable def leftMaskCyclePair
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p) :
    boundarySector ends p.1 ∅ × boundarySector ends p.2 ∅ := by
  have hmid : middleMask m c.1.1 = p.1 := congrArg Prod.fst c.2
  have hout : outerMask m c.1.1 = p.2 := congrArg Prod.snd c.2
  exact
    (⟨colorClass m c.1.1 1,
      ⟨by
        intro e he
        rw [← hmid]
        exact Finset.mem_union_left _ he,
        c.1.2.2.1⟩⟩,
     ⟨colorClass m c.1.1 3,
      ⟨by
        intro e he
        rw [← hout]
        exact Finset.mem_union_right _ he,
        c.1.2.2.2.2.1⟩⟩)



noncomputable def leftMaskCycleEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    leftMaskFiber ends m j k l zero p ↪
      boundarySector ends p.1 ∅ × boundarySector ends p.2 ∅ where
  toFun := leftMaskCyclePair ends m j k l zero p
  inj' := by
    intro c d hcd
    apply Subtype.ext
    apply Subtype.ext
    apply eq_of_middle_outer_colorClass_one_three m c.1.1 d.1.1
    · exact (congrArg Prod.fst c.2).trans (congrArg Prod.fst d.2).symm
    · exact (congrArg Prod.snd c.2).trans (congrArg Prod.snd d.2).symm
    · exact congrArg (fun z => z.1.1) hcd
    · exact congrArg (fun z => z.2.1) hcd



theorem leftMaskCycleEmbedding_surjective_of_cycleProduct_le_two
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p) (hcd : c ≠ d)
    (hcycle : Fintype.card (boundarySector ends p.1 ∅) *
      Fintype.card (boundarySector ends p.2 ∅) ≤ 2) :
    Function.Surjective
      (leftMaskCycleEmbedding ends m j k l zero p) := by
  apply embedding_surjective_of_card_le_two_of_ne
    (leftMaskCycleEmbedding ends m j k l zero p) c d hcd
  simpa only [Fintype.card_prod] using hcycle



theorem exists_leftMaskFiber_emptyCyclePair_of_cycleProduct_le_two
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p) (hcd : c ≠ d)
    (hcycle : Fintype.card (boundarySector ends p.1 ∅) *
      Fintype.card (boundarySector ends p.2 ∅) ≤ 2) :
    ∃ e : leftMaskFiber ends m j k l zero p,
      leftMaskCyclePair ends m j k l zero p e =
        emptyMaskCyclePair ends p :=
  leftMaskCycleEmbedding_surjective_of_cycleProduct_le_two
    ends m j k l zero p c d hcd hcycle (emptyMaskCyclePair ends p)



theorem cycleProduct_le_two_factor_card_eq_one
    (ends : I → Sym2 W) (p : Finset I × Finset I)
    (hcycle : Fintype.card (boundarySector ends p.1 ∅) *
      Fintype.card (boundarySector ends p.2 ∅) ≤ 2) :
    Fintype.card (boundarySector ends p.1 ∅) = 1 ∨
      Fintype.card (boundarySector ends p.2 ∅) = 1 := by
  have hpos1 : 0 < Fintype.card (boundarySector ends p.1 ∅) :=
    Fintype.card_pos_iff.mpr ⟨emptyBoundarySector ends p.1⟩
  have hpos2 : 0 < Fintype.card (boundarySector ends p.2 ∅) :=
    Fintype.card_pos_iff.mpr ⟨emptyBoundarySector ends p.2⟩
  by_contra h
  push Not at h
  have htwo1 : 2 ≤ Fintype.card (boundarySector ends p.1 ∅) := by omega
  have htwo2 : 2 ≤ Fintype.card (boundarySector ends p.2 ∅) := by omega
  nlinarith



theorem colorClass_zero_eq_outerMask_sdiff_three
    (m : Finset I) (c : ↑m → Fin 4) :
    colorClass m c 0 = outerMask m c \ colorClass m c 3 := by
  rw [outerMask]
  ext i
  have hd := Finset.disjoint_left.mp
    (colorClass_disjoint m c (show (0 : Fin 4) ≠ 3 by decide))
  simp only [Finset.mem_sdiff, Finset.mem_union]
  aesop



theorem leftMaskCycleDifference_empty_side_of_cycleProduct_le_two
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p)
    (hcycle : Fintype.card (boundarySector ends p.1 ∅) *
      Fintype.card (boundarySector ends p.2 ∅) ≤ 2) :
    balancedMiddleDifference m c.1.1 d.1.1 = ∅ ∨
      balancedOuterDifference m c.1.1 d.1.1 = ∅ := by
  rcases cycleProduct_le_two_factor_card_eq_one ends p hcycle with hmid | hout
  · left
    have hsub : Subsingleton (boundarySector ends p.1 ∅) :=
      Fintype.card_le_one_iff_subsingleton.mp (by omega)
    have hp := hsub.elim
      (leftMaskCyclePair ends m j k l zero p c).1
      (leftMaskCyclePair ends m j k l zero p d).1
    have hone : colorClass m c.1.1 1 = colorClass m d.1.1 1 :=
      congrArg Subtype.val hp
    rw [balancedMiddleDifference, hone, symmDiff_self]
    rfl
  · right
    have hsub : Subsingleton (boundarySector ends p.2 ∅) :=
      Fintype.card_le_one_iff_subsingleton.mp (by omega)
    have hp := hsub.elim
      (leftMaskCyclePair ends m j k l zero p c).2
      (leftMaskCyclePair ends m j k l zero p d).2
    have hthree : colorClass m c.1.1 3 = colorClass m d.1.1 3 :=
      congrArg Subtype.val hp
    have houter : outerMask m c.1.1 = outerMask m d.1.1 :=
      (congrArg Prod.snd c.2).trans (congrArg Prod.snd d.2).symm
    have hzero : colorClass m c.1.1 0 = colorClass m d.1.1 0 := by
      rw [colorClass_zero_eq_outerMask_sdiff_three,
        colorClass_zero_eq_outerMask_sdiff_three, houter, hthree]
    rw [balancedOuterDifference, hzero, symmDiff_self]
    rfl



theorem rows_eq_masks_of_leftMaskCyclePair_eq_empty
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : leftMaskFiber ends m j k l zero p)
    (hc : leftMaskCyclePair ends m j k l zero p c =
      emptyMaskCyclePair ends p) :
    rowClass m c.1.1 0 = p.2 ∧ rowClass m c.1.1 1 = p.1 := by
  have hone : colorClass m c.1.1 1 = ∅ := by
    have h := congrArg (fun z => z.1.1) hc
    simpa [leftMaskCyclePair, emptyMaskCyclePair,
      emptyBoundarySector] using h
  have hthree : colorClass m c.1.1 3 = ∅ := by
    have h := congrArg (fun z => z.2.1) hc
    simpa [leftMaskCyclePair, emptyMaskCyclePair,
      emptyBoundarySector] using h
  have hmid : middleMask m c.1.1 = p.1 := congrArg Prod.fst c.2
  have hout : outerMask m c.1.1 = p.2 := congrArg Prod.snd c.2
  constructor
  · calc
      rowClass m c.1.1 0 = colorClass m c.1.1 0 := by
        simp [rowClass_zero, hone]
      _ = outerMask m c.1.1 := by simp [outerMask, hthree]
      _ = p.2 := hout
  · calc
      rowClass m c.1.1 1 = colorClass m c.1.1 2 := by
        simp [rowClass_one, hthree]
      _ = middleMask m c.1.1 := by simp [middleMask, hone]
      _ = p.1 := hmid



theorem exists_leftMaskFiber_with_disconnected_masks_of_cycleProduct_le_two
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p) (hcd : c ≠ d)
    (hcycle : Fintype.card (boundarySector ends p.1 ∅) *
      Fintype.card (boundarySector ends p.2 ∅) ≤ 2) :
    ∃ e : leftMaskFiber ends m j k l zero p,
      ¬ connK ends p.1 k zero ∧ ¬ connK ends p.2 k zero := by
  obtain ⟨e, he⟩ := exists_leftMaskFiber_emptyCyclePair_of_cycleProduct_le_two
    ends m j k l zero p c d hcd hcycle
  have hrows := rows_eq_masks_of_leftMaskCyclePair_eq_empty
    ends m j k l zero p e he
  refine ⟨e, ?_, ?_⟩
  · simpa [RowsDisconnect, hrows.2] using e.1.2.2.2.2.2.2
  · simpa [RowsDisconnect, hrows.1] using e.1.2.2.2.2.2.1




theorem rightPattern_of_sourceless_balancedSwap
    {ends : I → Sym2 W} {m X Y : Finset I}
    {A B : Finset W} {u v : W} {c : ↑m → Fin 4}
    (hright : RightPattern ends m A B u v c)
    (hX : X ⊆ colorClass m c 1 ∪ colorClass m c 2)
    (hY : Y ⊆ colorClass m c 0 ∪ colorClass m c 3)
    (hsrcX : sources ends X = ∅)
    (hsrcY : sources ends Y = ∅)
    (hdisc : RowsDisconnect ends m (balancedSwap m X Y c) u v) :
    RightPattern ends m A B u v (balancedSwap m X Y c) := by
  rcases hright with ⟨h0, h1, h2, h3, -⟩
  have hY' : Y ⊆ colorClass m (middleSwapOn m X c) 0 ∪
      colorClass m (middleSwapOn m X c) 3 := by
    rwa [colorClass_middleSwapOn_zero, colorClass_middleSwapOn_three]
  unfold balancedSwap
  refine ⟨?_, ?_, ?_, ?_, hdisc⟩
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



noncomputable def rightMaskCycleTranslate
    (m : Finset I) (c d q : ↑m → Fin 4) : ↑m → Fin 4 :=
  balancedSwap m (balancedMiddleDifference m c d)
    (balancedOuterDifference m c d) q



theorem rightMaskCycleTranslate_ne
    (m : Finset I) (c d q : ↑m → Fin 4)
    (hmidcd : middleMask m c = middleMask m d)
    (houtcd : outerMask m c = outerMask m d)
    (hmidcq : middleMask m c = middleMask m q)
    (houtcq : outerMask m c = outerMask m q)
    (hcd : c ≠ d) : rightMaskCycleTranslate m c d q ≠ q := by
  intro hfixed
  let X := balancedMiddleDifference m c d
  let Y := balancedOuterDifference m c d
  have hXc : X ⊆ middleMask m c :=
    balancedMiddleDifference_subset m c d hmidcd
  have hYc : Y ⊆ outerMask m c :=
    balancedOuterDifference_subset m c d houtcd
  have hXq : X ⊆ colorClass m q 1 ∪ colorClass m q 2 := by
    rw [← middleMask, ← hmidcq]
    exact hXc
  have hYq : Y ⊆ colorClass m q 0 ∪ colorClass m q 3 := by
    rw [← outerMask, ← houtcq]
    exact hYc
  have hYq' : Y ⊆ colorClass m (middleSwapOn m X q) 0 ∪
      colorClass m (middleSwapOn m X q) 3 := by
    rwa [colorClass_middleSwapOn_zero, colorClass_middleSwapOn_three]
  have htwo := congrArg (fun z => colorClass m z 2) hfixed
  have hthree := congrArg (fun z => colorClass m z 3) hfixed
  change balancedSwap m X Y q = q at hfixed
  change colorClass m (balancedSwap m X Y q) 2 = colorClass m q 2 at htwo
  change colorClass m (balancedSwap m X Y q) 3 = colorClass m q 3 at hthree
  unfold balancedSwap at htwo hthree
  rw [colorClass_outerSwapOn_two,
    colorClass_middleSwapOn_two m X q hXq] at htwo
  rw [colorClass_outerSwapOn_three m Y _ hYq',
    colorClass_middleSwapOn_three] at hthree
  have hXempty : X = ∅ := symmDiff_eq_left.mp htwo
  have hYempty : Y = ∅ := symmDiff_eq_left.mp hthree
  apply hcd
  have hswap := balancedSwap_difference m c d hmidcd houtcd
  change balancedSwap m X Y c = d at hswap
  simpa [hXempty, hYempty, balancedSwap, middleSwapOn, outerSwapOn] using hswap




noncomputable def rightMaskCycleTranslateMemOfDisconnects
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p)
    (q : rightMaskFiber ends m j k l zero p)
    (hdisc : RowsDisconnect ends m
      (rightMaskCycleTranslate m c.1.1 d.1.1 q.1.1) k zero) :
    rightMaskFiber ends m j k l zero p := by
  let X := balancedMiddleDifference m c.1.1 d.1.1
  let Y := balancedOuterDifference m c.1.1 d.1.1
  have hprofilecd : fourColorMaskProfile m c.1.1 =
      fourColorMaskProfile m d.1.1 := c.2.trans d.2.symm
  have hprofilecq : fourColorMaskProfile m c.1.1 =
      fourColorMaskProfile m q.1.1 := c.2.trans q.2.symm
  have hmidcd : middleMask m c.1.1 = middleMask m d.1.1 :=
    congrArg Prod.fst hprofilecd
  have houtcd : outerMask m c.1.1 = outerMask m d.1.1 :=
    congrArg Prod.snd hprofilecd
  have hmidcq : middleMask m c.1.1 = middleMask m q.1.1 :=
    congrArg Prod.fst hprofilecq
  have houtcq : outerMask m c.1.1 = outerMask m q.1.1 :=
    congrArg Prod.snd hprofilecq
  have hXc : X ⊆ middleMask m c.1.1 :=
    balancedMiddleDifference_subset m c.1.1 d.1.1 hmidcd
  have hYc : Y ⊆ outerMask m c.1.1 :=
    balancedOuterDifference_subset m c.1.1 d.1.1 houtcd
  have hXq : X ⊆ colorClass m q.1.1 1 ∪ colorClass m q.1.1 2 := by
    rw [← middleMask, ← hmidcq]
    exact hXc
  have hYq : Y ⊆ colorClass m q.1.1 0 ∪ colorClass m q.1.1 3 := by
    rw [← outerMask, ← houtcq]
    exact hYc
  have hsrcX : sources ends X = ∅ := by
    dsimp only [X]
    rw [balancedMiddleDifference, sources_symmDiff,
      c.1.2.2.1, d.1.2.2.1]
    simp
  have hsrcY : sources ends Y = ∅ := by
    dsimp only [Y]
    rw [balancedOuterDifference, sources_symmDiff,
      c.1.2.1, d.1.2.1]
    simp
  have hright : RightPattern ends m {j, k} {k, l} k zero
      (rightMaskCycleTranslate m c.1.1 d.1.1 q.1.1) := by
    apply rightPattern_of_sourceless_balancedSwap q.1.2 hXq hYq
      hsrcX hsrcY
    simpa only [rightMaskCycleTranslate, X, Y] using hdisc
  refine ⟨⟨rightMaskCycleTranslate m c.1.1 d.1.1 q.1.1, hright⟩, ?_⟩
  calc
    fourColorMaskProfile m
        (rightMaskCycleTranslate m c.1.1 d.1.1 q.1.1) =
        fourColorMaskProfile m q.1.1 := by
      simp [fourColorMaskProfile, rightMaskCycleTranslate,
        middleMask_balancedSwap, outerMask_balancedSwap]
    _ = p := q.2



theorem exists_rightMaskFiber_pair_of_cycleTranslate_disconnects
    (ends : I → Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c d : leftMaskFiber ends m j k l zero p) (hcd : c ≠ d)
    (q : rightMaskFiber ends m j k l zero p)
    (hdisc : RowsDisconnect ends m
      (rightMaskCycleTranslate m c.1.1 d.1.1 q.1.1) k zero) :
    ∃ q r : rightMaskFiber ends m j k l zero p, q ≠ r := by
  let r := rightMaskCycleTranslateMemOfDisconnects
    ends m j k l zero p c d q hdisc
  have hcd' : c.1.1 ≠ d.1.1 := by
    intro heq
    apply hcd
    apply Subtype.ext
    apply Subtype.ext
    exact heq
  have hprofilecd : fourColorMaskProfile m c.1.1 =
      fourColorMaskProfile m d.1.1 := c.2.trans d.2.symm
  have hprofilecq : fourColorMaskProfile m c.1.1 =
      fourColorMaskProfile m q.1.1 := c.2.trans q.2.symm
  have hne : rightMaskCycleTranslate m c.1.1 d.1.1 q.1.1 ≠ q.1.1 :=
    rightMaskCycleTranslate_ne m c.1.1 d.1.1 q.1.1
      (congrArg Prod.fst hprofilecd) (congrArg Prod.snd hprofilecd)
      (congrArg Prod.fst hprofilecq) (congrArg Prod.snd hprofilecq) hcd'
  refine ⟨q, r, ?_⟩
  intro hqr
  apply hne
  exact (congrArg (fun z : rightMaskFiber ends m j k l zero p => z.1.1) hqr).symm



noncomputable def rightMaskCyclePair
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I)
    (c : rightMaskFiber ends m j k l zero p) :
    boundarySector ends p.1 ∅ × boundarySector ends p.2 ∅ := by
  have hmid : middleMask m c.1.1 = p.1 := congrArg Prod.fst c.2
  have hout : outerMask m c.1.1 = p.2 := congrArg Prod.snd c.2
  exact
    (⟨colorClass m c.1.1 2,
      ⟨by
        intro e he
        rw [← hmid]
        exact Finset.mem_union_right _ he,
        c.1.2.2.2.1⟩⟩,
     ⟨colorClass m c.1.1 3,
      ⟨by
        intro e he
        rw [← hout]
        exact Finset.mem_union_right _ he,
        c.1.2.2.2.2.1⟩⟩)


noncomputable def rightMaskCycleEmbedding
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    rightMaskFiber ends m j k l zero p ↪
      boundarySector ends p.1 ∅ × boundarySector ends p.2 ∅ where
  toFun := rightMaskCyclePair ends m j k l zero p
  inj' := by
    intro c d hcd
    apply Subtype.ext
    apply Subtype.ext
    apply eq_of_middle_outer_colorClass_two_three m c.1.1 d.1.1
    · exact (congrArg Prod.fst c.2).trans (congrArg Prod.fst d.2).symm
    · exact (congrArg Prod.snd c.2).trans (congrArg Prod.snd d.2).symm
    · exact congrArg (fun z => z.1.1) hcd
    · exact congrArg (fun z => z.2.1) hcd



theorem leftMaskFiber_card_le_cycleProduct
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Fintype.card (leftMaskFiber ends m j k l zero p) ≤
      Fintype.card (boundarySector ends p.1 ∅) *
        Fintype.card (boundarySector ends p.2 ∅) := by
  rw [← Fintype.card_prod]
  exact Fintype.card_le_of_embedding
    (leftMaskCycleEmbedding ends m j k l zero p)


theorem rightMaskFiber_card_le_cycleProduct
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (p : Finset I × Finset I) :
    Fintype.card (rightMaskFiber ends m j k l zero p) ≤
      Fintype.card (boundarySector ends p.1 ∅) *
        Fintype.card (boundarySector ends p.2 ∅) := by
  rw [← Fintype.card_prod]
  exact Fintype.card_le_of_embedding
    (rightMaskCycleEmbedding ends m j k l zero p)



theorem rowDataRepairHall_of_cycleProduct_le_one
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : forall i, i ∈ m -> ¬(ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hcycle : forall p : Finset I × Finset I,
      Fintype.card (boundarySector ends p.1 ∅) *
        Fintype.card (boundarySector ends p.2 ∅) ≤ 1) :
    RowDataRepairHall ends m j k l zero := by
  apply rowDataRepairHall_of_subsingleton_leftMaskFibers
    ends m j k l zero hloop hjk hkl hk0
  intro p
  rw [← Fintype.card_le_one_iff_subsingleton]
  exact (leftMaskFiber_card_le_cycleProduct ends m j k l zero p).trans
    (hcycle p)






theorem rowDataRepairHall_of_cycleProduct_le_two_of_rightPairs
    (ends : I -> Sym2 W) (m : Finset I) (j k l zero : W)
    (hloop : forall i, i ∈ m -> ¬(ends i).IsDiag)
    (hjk : j ≠ k) (hkl : k ≠ l) (hk0 : k ≠ zero)
    (hcycle : forall p : Finset I × Finset I,
      Fintype.card (boundarySector ends p.1 ∅) *
        Fintype.card (boundarySector ends p.2 ∅) ≤ 2)
    (hpair : forall (p : Finset I × Finset I)
        (c d : leftMaskFiber ends m j k l zero p), c ≠ d ->
      ∃ q r : rightMaskFiber ends m j k l zero p, q ≠ r) :
    RowDataRepairHall ends m j k l zero := by
  apply rowDataRepairHall_of_maskwise
  intro p
  have hleft := (leftMaskFiber_card_le_cycleProduct
    ends m j k l zero p).trans (hcycle p)
  by_cases hsmall : Fintype.card (leftMaskFiber ends m j k l zero p) ≤ 1
  · by_cases hempty : Fintype.card (leftMaskFiber ends m j k l zero p) = 0
    · omega
    · have hpos : 0 < Fintype.card (leftMaskFiber ends m j k l zero p) := by
        omega
      let c := Classical.choice (Fintype.card_pos_iff.mp hpos)
      have hright : Nonempty (rightMaskFiber ends m j k l zero p) :=
        rightMaskFiber_nonempty_of_left hloop hjk hkl hk0 p c
      have hrightPos : 0 < Fintype.card (rightMaskFiber ends m j k l zero p) :=
        Fintype.card_pos_iff.mpr hright
      omega
  · have hleftGt : 1 < Fintype.card (leftMaskFiber ends m j k l zero p) := by
      omega
    letI : Nontrivial (leftMaskFiber ends m j k l zero p) :=
      Fintype.one_lt_card_iff_nontrivial.mp hleftGt
    obtain ⟨c, d, hcd⟩ := exists_pair_ne
      (leftMaskFiber ends m j k l zero p)
    obtain ⟨q, r, hqr⟩ := hpair p c d hcd
    letI : Nontrivial (rightMaskFiber ends m j k l zero p) :=
      ⟨⟨q, r, hqr⟩⟩
    have hrightGt : 1 < Fintype.card
        (rightMaskFiber ends m j k l zero p) := Fintype.one_lt_card
    omega

end StatMech.GrahamGHS.FourColor
