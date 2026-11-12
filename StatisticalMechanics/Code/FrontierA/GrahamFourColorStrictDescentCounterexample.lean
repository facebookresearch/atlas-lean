/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamFourColorUniformMaskSelector

open Finset
open scoped symmDiff

namespace StatMech.GrahamGHS.FourColor

private def counterEnds : Fin 7 -> Sym2 (Fin 6)
  | 0 => s(1, 3)
  | 1 => s(0, 2)
  | 2 => s(2, 3)
  | 3 => s(1, 3)
  | 4 => s(2, 3)
  | 5 => s(0, 4)
  | 6 => s(2, 5)

private def counterC : Fin 7 -> Fin 4
  | 0 => 3
  | 1 => 2
  | 2 => 0
  | 3 => 3
  | 4 => 0
  | 5 => 0
  | 6 => 2

private def counterCU : ↑(Finset.univ : Finset (Fin 7)) -> Fin 4 :=
  fun i => counterC i.1

private def counterD : Fin 7 -> Fin 4
  | 0 => 0
  | 1 => 2
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 2

private def counterDU : ↑(Finset.univ : Finset (Fin 7)) -> Fin 4 :=
  fun i => counterD i.1

private theorem counterC_classes :
    colorClass Finset.univ counterCU 0 = {2, 4, 5} /\
      colorClass Finset.univ counterCU 1 = ∅ /\
      colorClass Finset.univ counterCU 2 = {1, 6} /\
      colorClass Finset.univ counterCU 3 = {0, 3} := by
  constructor
  · ext i
    fin_cases i <;> simp [colorClass, counterCU, counterC]
  constructor
  · ext i
    fin_cases i <;> simp [colorClass, counterCU, counterC]
  constructor <;> ext i <;> fin_cases i <;>
    simp [colorClass, counterCU, counterC]

private theorem counterD_classes :
    colorClass Finset.univ counterDU 0 = {0, 2, 3, 4, 5} /\
      colorClass Finset.univ counterDU 1 = ∅ /\
      colorClass Finset.univ counterDU 2 = {1, 6} /\
      colorClass Finset.univ counterDU 3 = ∅ := by
  constructor
  · ext i
    fin_cases i <;> simp [colorClass, counterDU, counterD]
  constructor
  · ext i
    fin_cases i <;> simp [colorClass, counterDU, counterD]
  constructor <;> ext i <;> fin_cases i <;>
    simp [colorClass, counterDU, counterD]

set_option linter.flexible false in
private theorem counter_sources_025 :
    StatMech.Sharpness.RandomCurrent.sources counterEnds {2, 4, 5} = {4, 0} := by
  ext x
  fin_cases x <;>
    simp [StatMech.Sharpness.RandomCurrent.sources,
      StatMech.Sharpness.RandomCurrent.degK, counterEnds] <;> decide

set_option linter.flexible false in
private theorem counter_sources_01345 :
    StatMech.Sharpness.RandomCurrent.sources counterEnds {0, 2, 3, 4, 5} =
      {4, 0} := by
  ext x
  fin_cases x <;>
    simp [StatMech.Sharpness.RandomCurrent.sources,
      StatMech.Sharpness.RandomCurrent.degK, counterEnds] <;> decide

set_option linter.flexible false in
private theorem counter_sources_16 :
    StatMech.Sharpness.RandomCurrent.sources counterEnds {1, 6} = {0, 5} := by
  ext x
  fin_cases x <;>
    simp [StatMech.Sharpness.RandomCurrent.sources,
      StatMech.Sharpness.RandomCurrent.degK, counterEnds] <;> decide

set_option linter.flexible false in
private theorem counter_sources_03 :
    StatMech.Sharpness.RandomCurrent.sources counterEnds {0, 3} = ∅ := by
  ext x
  fin_cases x <;>
    simp [StatMech.Sharpness.RandomCurrent.sources,
      StatMech.Sharpness.RandomCurrent.degK, counterEnds] <;> decide

private theorem counter_sources_empty :
    StatMech.Sharpness.RandomCurrent.sources counterEnds ∅ = ∅ := by
  simp [StatMech.Sharpness.RandomCurrent.sources,
    StatMech.Sharpness.RandomCurrent.degK]

private theorem not_conn_of_noCrossing
    {K : Finset (Fin 7)} {S : Finset (Fin 6)} {u v : Fin 6}
    (hu : u ∈ S) (hv : v ∉ S)
    (hcross : StatMech.Sharpness.RandomCurrent.NoCrossingK counterEnds K S) :
    ¬ StatMech.Sharpness.RandomCurrent.connK counterEnds K u v := by
  intro huv
  have stay : ∀ x, StatMech.Sharpness.RandomCurrent.connK counterEnds K u x ->
      x ∈ S := by
    intro x hx
    induction hx with
    | refl => exact hu
    | tail hab hstep ih =>
        rcases hstep with ⟨i, hi, ha, hb, hne⟩
        rcases hcross i hi with hin | hout
        · exact hin _ hb
        · exact False.elim ((Finset.mem_compl.mp (hout _ ha)) ih)
  exact hv (stay v huv)

private theorem edgeComponent_mem_support
    {I W : Type*} [Fintype W] [DecidableEq W]
    {ends : I -> Sym2 W} {K : Finset I} {u : W} {i : I}
    (hi : i ∈ edgeComponent ends K u) : i ∈ K := by
  classical
  rw [edgeComponent, Finset.mem_filter] at hi
  exact hi.1

private theorem edgeComponent_conn_endpoint
    {I W : Type*} [Fintype W] [DecidableEq W]
    {ends : I -> Sym2 W} {K : Finset I} {u x : W} {i : I}
    (hi : i ∈ edgeComponent ends K u) (hx : x ∈ ends i) :
    StatMech.Sharpness.RandomCurrent.connK ends K u x := by
  classical
  rw [edgeComponent, Finset.mem_filter] at hi
  exact hi.2 x hx

private theorem edgeComponent_mono
    {I W : Type*} [Fintype W] [DecidableEq W]
    {ends : I -> Sym2 W} {K L : Finset I} {u : W}
    (hKL : K ⊆ L) : edgeComponent ends K u ⊆ edgeComponent ends L u := by
  classical
  intro i hi
  rw [edgeComponent, Finset.mem_filter] at hi ⊢
  refine ⟨hKL hi.1, ?_⟩
  intro x hx
  apply Relation.ReflTransGen.mono (fun a b
      (hab : StatMech.Sharpness.RandomCurrent.adjStep ends K a b) => by
      rcases hab with ⟨e, he, ha, hb, hab⟩
      exact ⟨e, hKL he, ha, hb, hab⟩)
  exact hi.2 x hx

private theorem counterC_left :
    LeftPattern counterEnds Finset.univ {4, 0} {0, 5} 0 1 counterCU := by
  have hc := counterC_classes
  unfold LeftPattern
  rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2]
  refine ⟨counter_sources_025, counter_sources_empty,
    counter_sources_16, counter_sources_03, ?_⟩
  unfold RowsDisconnect
  rw [rowClass_zero, rowClass_one, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2]
  simp only [union_empty]
  constructor
  · apply not_conn_of_noCrossing (K := {2, 4, 5}) (S := {0, 4})
      (u := (0 : Fin 6)) (v := (1 : Fin 6)) (by simp) (by simp)
    intro i hi
    fin_cases i <;> simp [StatMech.Sharpness.RandomCurrent.edgeInsideK,
      counterEnds, Sym2.mem_iff] at hi ⊢
  · apply not_conn_of_noCrossing (K := {1, 6} ∪ {0, 3})
      (S := {0, 2, 5}) (u := (0 : Fin 6)) (v := (1 : Fin 6))
      (by simp) (by simp)
    intro i hi
    fin_cases i <;> simp [StatMech.Sharpness.RandomCurrent.edgeInsideK,
      counterEnds, Sym2.mem_iff] at hi ⊢

private theorem counterD_left :
    LeftPattern counterEnds Finset.univ {4, 0} {0, 5} 0 1 counterDU := by
  have hd := counterD_classes
  unfold LeftPattern
  rw [hd.1, hd.2.1, hd.2.2.1, hd.2.2.2]
  refine ⟨counter_sources_01345, counter_sources_empty,
    counter_sources_16, counter_sources_empty, ?_⟩
  unfold RowsDisconnect
  rw [rowClass_zero, rowClass_one, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2]
  simp only [union_empty]
  constructor
  · apply not_conn_of_noCrossing (K := {0, 2, 3, 4, 5}) (S := {0, 4})
      (u := (0 : Fin 6)) (v := (1 : Fin 6)) (by simp) (by simp)
    intro i hi
    fin_cases i <;> simp [StatMech.Sharpness.RandomCurrent.edgeInsideK,
      counterEnds, Sym2.mem_iff] at hi ⊢
  · apply not_conn_of_noCrossing (K := {1, 6}) (S := {0, 2, 5})
      (u := (0 : Fin 6)) (v := (1 : Fin 6)) (by simp) (by simp)
    intro i hi
    fin_cases i <;> simp [StatMech.Sharpness.RandomCurrent.edgeInsideK,
      counterEnds, Sym2.mem_iff] at hi ⊢

private theorem counter_same_profile :
    fourColorMaskProfile Finset.univ counterCU =
      fourColorMaskProfile Finset.univ counterDU := by
  have hc := counterC_classes
  have hd := counterD_classes
  apply Prod.ext <;> ext i <;> fin_cases i <;>
    simp [fourColorMaskProfile, middleMask, outerMask, hc.1, hc.2.1,
      hc.2.2.1, hc.2.2.2, hd.1, hd.2.1, hd.2.2.1, hd.2.2.2]

private theorem counter_loopless :
    ∀ i ∈ (Finset.univ : Finset (Fin 7)), ¬ (counterEnds i).IsDiag := by
  intro i _
  fin_cases i <;> simp [counterEnds, Sym2.mk_isDiag_iff]

private theorem one_mem_counterC_transfer :
    (1 : Fin 7) ∈ canonicalTransferUnion counterEnds Finset.univ 0 1 counterCU := by
  unfold canonicalTransferUnion
  rw [canonicalTransfers_union]
  apply Finset.mem_union_right
  apply mem_edgeComponent_of_endpoint
  · rw [rowClass_one]
    simp [counterC_classes.2.2.1, counterC_classes.2.2.2]
  · simp [counterEnds, Sym2.mem_iff]

private theorem zero_not_mem_counterC_transfer :
    (0 : Fin 7) ∉ canonicalTransferUnion counterEnds Finset.univ 0 1 counterCU := by
  unfold canonicalTransferUnion
  rw [canonicalTransfers_union]
  intro hi
  rcases Finset.mem_union.mp hi with hi | hi
  · have hirow := edgeComponent_mem_support hi
    rw [rowClass_zero, counterC_classes.1, counterC_classes.2.1] at hirow
    simp at hirow
  · have hz : (1 : Fin 6) ∈ counterEnds 0 := by
      simp [counterEnds, Sym2.mem_iff]
    exact counterC_left.2.2.2.2.2 (edgeComponent_conn_endpoint hi hz)

private theorem two_not_mem_counterC_transfer :
    (2 : Fin 7) ∉ canonicalTransferUnion counterEnds Finset.univ 0 1 counterCU := by
  unfold canonicalTransferUnion
  rw [canonicalTransfers_union]
  intro hi
  rcases Finset.mem_union.mp hi with hi | hi
  · have ha : (2 : Fin 6) ∈ counterEnds 2 := by
      simp [counterEnds, Sym2.mem_iff]
    have hconn := edgeComponent_conn_endpoint hi ha
    have hnot : ¬ StatMech.Sharpness.RandomCurrent.connK counterEnds
        (rowClass Finset.univ counterCU 0) 1 2 :=
      not_connK_of_no_incident (ends := counterEnds)
      (K := rowClass Finset.univ counterCU 0)
        (u := (1 : Fin 6)) (v := (2 : Fin 6)) (by decide) (by
          intro e he
          rw [rowClass_zero, counterC_classes.1, counterC_classes.2.1] at he
          fin_cases e <;> simp [counterEnds, Sym2.mem_iff] at he ⊢)
    exact hnot hconn
  · have hirow := edgeComponent_mem_support hi
    rw [rowClass_one, counterC_classes.2.2.1,
      counterC_classes.2.2.2] at hirow
    simp at hirow

private theorem zero_mem_counterD_transfer :
    (0 : Fin 7) ∈ canonicalTransferUnion counterEnds Finset.univ 0 1 counterDU := by
  unfold canonicalTransferUnion
  rw [canonicalTransfers_union]
  apply Finset.mem_union_left
  apply mem_edgeComponent_of_endpoint
  · rw [rowClass_zero]
    simp [counterD_classes.1, counterD_classes.2.1]
  · simp [counterEnds, Sym2.mem_iff]

private theorem counterC_transfer_ssubset_counterD_transfer :
    canonicalTransferUnion counterEnds Finset.univ 0 1 counterCU ⊂
      canonicalTransferUnion counterEnds Finset.univ 0 1 counterDU := by
  have hrow0 : rowClass Finset.univ counterCU 0 ⊆
      rowClass Finset.univ counterDU 0 := by
    rw [rowClass_zero, rowClass_zero, counterC_classes.1,
      counterC_classes.2.1, counterD_classes.1, counterD_classes.2.1]
    intro i hi
    simp at hi ⊢
    aesop
  have hcomp1 : edgeComponent counterEnds
      (rowClass Finset.univ counterCU 1) 0 ⊆
      edgeComponent counterEnds (rowClass Finset.univ counterDU 1) 0 := by
    intro i hi
    have hrowD1 : rowClass Finset.univ counterDU 1 = {1, 6} := by
      rw [rowClass_one, counterD_classes.2.2.1,
        counterD_classes.2.2.2, union_empty]
    have he1 : (1 : Fin 7) ∈ rowClass Finset.univ counterDU 1 := by
      rw [hrowD1]
      simp
    have hka : StatMech.Sharpness.RandomCurrent.connK counterEnds
        (rowClass Finset.univ counterDU 1) 0 2 :=
      Relation.ReflTransGen.single
        ⟨1, he1, by simp [counterEnds, Sym2.mem_iff],
          by simp [counterEnds, Sym2.mem_iff], by decide⟩
    fin_cases i
    · have hz : (1 : Fin 6) ∈ counterEnds 0 := by
        simp [counterEnds, Sym2.mem_iff]
      exact False.elim
        (counterC_left.2.2.2.2.2 (edgeComponent_conn_endpoint hi hz))
    · exact mem_edgeComponent_of_endpoint he1
        (by simp [counterEnds, Sym2.mem_iff])
    · have hirow := edgeComponent_mem_support hi
      rw [rowClass_one, counterC_classes.2.2.1,
        counterC_classes.2.2.2] at hirow
      simp at hirow
    · have hz : (1 : Fin 6) ∈ counterEnds 3 := by
        simp [counterEnds, Sym2.mem_iff]
      exact False.elim
        (counterC_left.2.2.2.2.2 (edgeComponent_conn_endpoint hi hz))
    · have hirow := edgeComponent_mem_support hi
      rw [rowClass_one, counterC_classes.2.2.1,
        counterC_classes.2.2.2] at hirow
      simp at hirow
    · have hirow := edgeComponent_mem_support hi
      rw [rowClass_one, counterC_classes.2.2.1,
        counterC_classes.2.2.2] at hirow
      simp at hirow
    · apply mem_edgeComponent_of_reachable_endpoint hka
      · rw [hrowD1]
        simp
      · simp [counterEnds, Sym2.mem_iff]
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · unfold canonicalTransferUnion
    rw [canonicalTransfers_union, canonicalTransfers_union]
    intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact Finset.mem_union_left _ (edgeComponent_mono hrow0 hi)
    · exact Finset.mem_union_right _ (hcomp1 hi)
  · intro heq
    exact zero_not_mem_counterC_transfer
      (heq.symm ▸ zero_mem_counterD_transfer)

private theorem counter_transfer_fails_on_D :
    ¬ RowsDisconnect counterEnds Finset.univ
      (balancedSwap Finset.univ
        (canonicalMiddleTransfer counterEnds Finset.univ counterCU 0 1)
        (canonicalOuterTransfer counterEnds Finset.univ counterCU 0 1)
        counterDU) 0 1 := by
  let X := canonicalMiddleTransfer counterEnds Finset.univ counterCU 0 1
  let Y := canonicalOuterTransfer counterEnds Finset.univ counterCU 0 1
  let T := canonicalTransferUnion counterEnds Finset.univ 0 1 counterCU
  have hv := canonicalTransfers_valid counter_loopless (by decide) (by decide)
    counterC_left
  have hXd : X ⊆ colorClass Finset.univ counterDU 1 ∪
      colorClass Finset.univ counterDU 2 := by
    intro i hi
    have hi' := hv.1 hi
    rw [counterC_classes.2.1, counterC_classes.2.2.1] at hi'
    rw [counterD_classes.2.1, counterD_classes.2.2.1]
    exact hi'
  have hYd : Y ⊆ colorClass Finset.univ counterDU 0 ∪
      colorClass Finset.univ counterDU 3 := by
    intro i hi
    have hi' := hv.2.1 hi
    rw [counterC_classes.1, counterC_classes.2.2.2] at hi'
    rw [counterD_classes.1, counterD_classes.2.2.2]
    simp at hi' ⊢
    aesop
  have hT : X ∪ Y = T := rfl
  have hrowD0 : rowClass Finset.univ counterDU 0 = {0, 2, 3, 4, 5} := by
    rw [rowClass_zero, counterD_classes.1, counterD_classes.2.1, union_empty]
  have hrow : rowClass Finset.univ (balancedSwap Finset.univ X Y counterDU) 0 =
      rowClass Finset.univ counterDU 0 ∆ T := by
    rw [rowClass_balancedSwap_zero hXd hYd, hT]
  have he0T : (0 : Fin 7) ∉ T := by
    simpa [T] using zero_not_mem_counterC_transfer
  have he1T : (1 : Fin 7) ∈ T := by
    simpa [T] using one_mem_counterC_transfer
  have he2T : (2 : Fin 7) ∉ T := by
    simpa [T] using two_not_mem_counterC_transfer
  have he0 : (0 : Fin 7) ∈
      rowClass Finset.univ (balancedSwap Finset.univ X Y counterDU) 0 := by
    rw [hrow]
    simp [Finset.mem_symmDiff, hrowD0, he0T]
  have he1 : (1 : Fin 7) ∈
      rowClass Finset.univ (balancedSwap Finset.univ X Y counterDU) 0 := by
    rw [hrow]
    simp [Finset.mem_symmDiff, hrowD0, he1T]
  have he2 : (2 : Fin 7) ∈
      rowClass Finset.univ (balancedSwap Finset.univ X Y counterDU) 0 := by
    rw [hrow]
    simp [Finset.mem_symmDiff, hrowD0, he2T]
  have h01 : StatMech.Sharpness.RandomCurrent.adjStep counterEnds
      (rowClass Finset.univ (balancedSwap Finset.univ X Y counterDU) 0) 0 2 :=
    ⟨1, he1, by simp [counterEnds, Sym2.mem_iff],
      by simp [counterEnds, Sym2.mem_iff], by decide⟩
  have h23 : StatMech.Sharpness.RandomCurrent.adjStep counterEnds
      (rowClass Finset.univ (balancedSwap Finset.univ X Y counterDU) 0) 2 3 :=
    ⟨2, he2, by simp [counterEnds, Sym2.mem_iff],
      by simp [counterEnds, Sym2.mem_iff], by decide⟩
  have h31 : StatMech.Sharpness.RandomCurrent.adjStep counterEnds
      (rowClass Finset.univ (balancedSwap Finset.univ X Y counterDU) 0) 3 1 :=
    ⟨0, he0, by simp [counterEnds, Sym2.mem_iff],
      by simp [counterEnds, Sym2.mem_iff], by decide⟩
  have hconn : StatMech.Sharpness.RandomCurrent.connK counterEnds
      (rowClass Finset.univ (balancedSwap Finset.univ X Y counterDU) 0) 0 1 :=
    Relation.ReflTransGen.tail
      (Relation.ReflTransGen.tail (Relation.ReflTransGen.single h01) h23) h31
  intro hdisc
  exact hdisc.1 hconn



theorem exists_canonicalTransferStrictDescent_counterexample :
    ∃ (ends : Fin 7 -> Sym2 (Fin 6))
      (c d : ↑(Finset.univ : Finset (Fin 7)) -> Fin 4),
      LeftPattern ends Finset.univ {4, 0} {0, 5} 0 1 c ∧
      LeftPattern ends Finset.univ {4, 0} {0, 5} 0 1 d ∧
      fourColorMaskProfile Finset.univ c = fourColorMaskProfile Finset.univ d ∧
      ¬ RowsDisconnect ends Finset.univ
        (balancedSwap Finset.univ
          (canonicalMiddleTransfer ends Finset.univ c 0 1)
          (canonicalOuterTransfer ends Finset.univ c 0 1) d) 0 1 ∧
      canonicalTransferUnion ends Finset.univ 0 1 c ⊂
        canonicalTransferUnion ends Finset.univ 0 1 d := by
  refine ⟨counterEnds, counterCU, counterDU, counterC_left, counterD_left,
    counter_same_profile, counter_transfer_fails_on_D,
    counterC_transfer_ssubset_counterD_transfer⟩

end StatMech.GrahamGHS.FourColor
