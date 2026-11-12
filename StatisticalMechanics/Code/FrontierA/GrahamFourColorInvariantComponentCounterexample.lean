/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.GrahamFourColorInvariantComponentSelector










open Finset
open Classical
open scoped symmDiff

namespace StatMech.GrahamGHS.FourColor

open StatMech.Sharpness.RandomCurrent

private def parallelCounterEnds : Fin 6 -> Sym2 (Fin 4)
  | 0 => s(1, 2)
  | 1 => s(1, 2)
  | 2 => s(2, 3)
  | 3 => s(1, 2)
  | 4 => s(0, 1)
  | 5 => s(2, 3)

private def parallelCounterColor : Fin 6 -> Fin 4
  | 0 => 3
  | 1 => 3
  | 2 => 1
  | 3 => 2
  | 4 => 0
  | 5 => 1

private def parallelCounterColorU :
    ↑(Finset.univ : Finset (Fin 6)) -> Fin 4 :=
  fun i => parallelCounterColor i.1

private theorem parallelCounter_classes :
    colorClass Finset.univ parallelCounterColorU 0 = {4} /\
      colorClass Finset.univ parallelCounterColorU 1 = {2, 5} /\
      colorClass Finset.univ parallelCounterColorU 2 = {3} /\
      colorClass Finset.univ parallelCounterColorU 3 = {0, 1} := by
  constructor
  · ext i
    fin_cases i <;> simp [colorClass, parallelCounterColorU,
      parallelCounterColor]
  constructor
  · ext i
    fin_cases i <;> simp [colorClass, parallelCounterColorU,
      parallelCounterColor]
  constructor <;> ext i <;> fin_cases i <;>
    simp [colorClass, parallelCounterColorU, parallelCounterColor]

set_option linter.flexible false in
private theorem parallelCounter_sources_4 :
    sources parallelCounterEnds {4} = {0, 1} := by
  ext x
  fin_cases x <;>
    simp [sources, degK, parallelCounterEnds] <;> decide

set_option linter.flexible false in
private theorem parallelCounter_sources_25 :
    sources parallelCounterEnds {2, 5} = ∅ := by
  ext x
  fin_cases x <;>
    simp [sources, degK, parallelCounterEnds] <;> decide

set_option linter.flexible false in
private theorem parallelCounter_sources_3 :
    sources parallelCounterEnds {3} = {1, 2} := by
  ext x
  fin_cases x <;>
    simp [sources, degK, parallelCounterEnds] <;> decide

set_option linter.flexible false in
private theorem parallelCounter_sources_01 :
    sources parallelCounterEnds {0, 1} = ∅ := by
  ext x
  fin_cases x <;>
    simp [sources, degK, parallelCounterEnds] <;> decide

private theorem parallelCounter_not_conn_of_noCrossing
    {K : Finset (Fin 6)} {S : Finset (Fin 4)} {u v : Fin 4}
    (hu : u ∈ S) (hv : v ∉ S)
    (hcross : NoCrossingK parallelCounterEnds K S) :
    ¬ connK parallelCounterEnds K u v := by
  intro huv
  have stay : ∀ x, connK parallelCounterEnds K u x -> x ∈ S := by
    intro x hx
    induction hx with
    | refl => exact hu
    | tail hab hstep ih =>
        rcases hstep with ⟨i, hi, ha, hb, hne⟩
        rcases hcross i hi with hin | hout
        · exact hin _ hb
        · exact False.elim ((Finset.mem_compl.mp (hout _ ha)) ih)
  exact hv (stay v huv)

private theorem parallel_edgeComponent_mem_support
    {I W : Type*} [Fintype W] [DecidableEq W]
    {ends : I -> Sym2 W} {K : Finset I} {u : W} {i : I}
    (hi : i ∈ edgeComponent ends K u) : i ∈ K := by
  classical
  rw [edgeComponent, Finset.mem_filter] at hi
  exact hi.1

private theorem parallel_edgeComponent_conn_endpoint
    {I W : Type*} [Fintype W] [DecidableEq W]
    {ends : I -> Sym2 W} {K : Finset I} {u x : W} {i : I}
    (hi : i ∈ edgeComponent ends K u) (hx : x ∈ ends i) :
    connK ends K u x := by
  classical
  rw [edgeComponent, Finset.mem_filter] at hi
  exact hi.2 x hx

private theorem parallelCounter_left :
    LeftPattern parallelCounterEnds Finset.univ {0, 1} {1, 2}
      1 3 parallelCounterColorU := by
  have hc := parallelCounter_classes
  unfold LeftPattern
  rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2]
  refine ⟨parallelCounter_sources_4, parallelCounter_sources_25,
    parallelCounter_sources_3, parallelCounter_sources_01, ?_⟩
  unfold RowsDisconnect
  rw [rowClass_zero, rowClass_one, hc.1, hc.2.1, hc.2.2.1,
    hc.2.2.2]
  constructor
  · apply parallelCounter_not_conn_of_noCrossing
      (K := {4} ∪ {2, 5}) (S := {0, 1}) (by simp) (by simp)
    intro i hi
    fin_cases i <;>
      simp [edgeInsideK, parallelCounterEnds,
        Sym2.mem_iff] at hi ⊢
  · apply parallelCounter_not_conn_of_noCrossing
      (K := {3} ∪ {0, 1}) (S := {1, 2}) (by simp) (by simp)
    intro i hi
    fin_cases i <;>
      simp [edgeInsideK, parallelCounterEnds,
        Sym2.mem_iff] at hi ⊢

private theorem parallelCounter_middleMask :
    middleMask Finset.univ parallelCounterColorU = {2, 3, 5} := by
  rw [middleMask, parallelCounter_classes.2.1,
    parallelCounter_classes.2.2.1]
  ext i
  fin_cases i <;> simp

private theorem parallelCounter_outerMask :
    outerMask Finset.univ parallelCounterColorU = {0, 1, 4} := by
  rw [outerMask, parallelCounter_classes.1,
    parallelCounter_classes.2.2.2]
  ext i
  fin_cases i <;> simp

private theorem parallelCounter_middleTransfer :
    invariantMiddleTransfer parallelCounterEnds Finset.univ
      parallelCounterColorU 1 = {2, 3, 5} := by
  rw [invariantMiddleTransfer, parallelCounter_middleMask]
  apply Finset.Subset.antisymm
  · intro i hi
    exact parallel_edgeComponent_mem_support hi
  · intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · have h12 : connK parallelCounterEnds {2, 3, 5} 1 2 :=
        Relation.ReflTransGen.single
          ⟨3, by simp, by simp [parallelCounterEnds, Sym2.mem_iff],
            by simp [parallelCounterEnds, Sym2.mem_iff], by decide⟩
      apply mem_edgeComponent_of_reachable_endpoint h12 (by simp)
      simp [parallelCounterEnds, Sym2.mem_iff]
    · apply mem_edgeComponent_of_endpoint (by simp)
      simp [parallelCounterEnds, Sym2.mem_iff]
    · have h12 : connK parallelCounterEnds {2, 3, 5} 1 2 :=
        Relation.ReflTransGen.single
          ⟨3, by simp, by simp [parallelCounterEnds, Sym2.mem_iff],
            by simp [parallelCounterEnds, Sym2.mem_iff], by decide⟩
      apply mem_edgeComponent_of_reachable_endpoint h12 (by simp)
      simp [parallelCounterEnds, Sym2.mem_iff]

private theorem parallelCounter_outerTransfer :
    invariantOuterTransfer parallelCounterEnds Finset.univ
      parallelCounterColorU 0 3 = ∅ := by
  have hinc : ∀ i ∈ outerMask Finset.univ parallelCounterColorU,
      (3 : Fin 4) ∉ parallelCounterEnds i := by
    intro i hi
    rw [parallelCounter_outerMask] at hi
    fin_cases i <;>
      simp [parallelCounterEnds, Sym2.mem_iff] at hi ⊢
  have h30 : ¬ connK parallelCounterEnds
      (outerMask Finset.univ parallelCounterColorU) 3 0 :=
    not_connK_of_no_incident (by decide) hinc
  rw [invariantOuterTransfer, if_neg h30]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hiK := parallel_edgeComponent_mem_support hi
  let x : Fin 4 := (parallelCounterEnds i).out.1
  have hx : x ∈ parallelCounterEnds i := Sym2.out_fst_mem _
  have hne : (3 : Fin 4) ≠ x := by
    intro h3x
    apply hinc i hiK
    simpa [x, h3x] using hx
  exact (not_connK_of_no_incident hne hinc)
    (parallel_edgeComponent_conn_endpoint hi hx)



theorem exists_invariantComponentSelector_parallel_counterexample :
    ∃ (ends : Fin 6 -> Sym2 (Fin 4))
      (c : ↑(Finset.univ : Finset (Fin 6)) -> Fin 4),
      LeftPattern ends Finset.univ {0, 1} {1, 2} 1 3 c ∧
      ¬ RowsDisconnect ends Finset.univ
        (balancedSwap Finset.univ
          (invariantMiddleTransfer ends Finset.univ c 1)
          (invariantOuterTransfer ends Finset.univ c 0 3) c) 1 3 := by
  refine ⟨parallelCounterEnds, parallelCounterColorU,
    parallelCounter_left, ?_⟩
  let X := invariantMiddleTransfer parallelCounterEnds Finset.univ
    parallelCounterColorU 1
  let Y := invariantOuterTransfer parallelCounterEnds Finset.univ
    parallelCounterColorU 0 3
  have hX : X = {2, 3, 5} := parallelCounter_middleTransfer
  have hY : Y = ∅ := parallelCounter_outerTransfer
  have hXsub : X ⊆ middleMask Finset.univ parallelCounterColorU :=
    invariantMiddleTransfer_subset _ _ _ _
  have hYsub : Y ⊆ outerMask Finset.univ parallelCounterColorU :=
    invariantOuterTransfer_subset _ _ _ _ _
  have hrow : rowClass Finset.univ
      (balancedSwap Finset.univ X Y parallelCounterColorU) 1 =
        rowClass Finset.univ parallelCounterColorU 1 ∆ (X ∪ Y) := by
    exact rowClass_balancedSwap_one hXsub hYsub
  have he0 : (0 : Fin 6) ∈ rowClass Finset.univ
      (balancedSwap Finset.univ X Y parallelCounterColorU) 1 := by
    rw [hrow, rowClass_one, parallelCounter_classes.2.2.1,
      parallelCounter_classes.2.2.2, hX, hY]
    simp [Finset.mem_symmDiff]
  have he2 : (2 : Fin 6) ∈ rowClass Finset.univ
      (balancedSwap Finset.univ X Y parallelCounterColorU) 1 := by
    rw [hrow, rowClass_one, parallelCounter_classes.2.2.1,
      parallelCounter_classes.2.2.2, hX, hY]
    simp [Finset.mem_symmDiff]
  have h12 : adjStep parallelCounterEnds
      (rowClass Finset.univ
        (balancedSwap Finset.univ X Y parallelCounterColorU) 1) 1 2 :=
    ⟨0, he0, by simp [parallelCounterEnds, Sym2.mem_iff],
      by simp [parallelCounterEnds, Sym2.mem_iff], by decide⟩
  have h23 : adjStep parallelCounterEnds
      (rowClass Finset.univ
        (balancedSwap Finset.univ X Y parallelCounterColorU) 1) 2 3 :=
    ⟨2, he2, by simp [parallelCounterEnds, Sym2.mem_iff],
      by simp [parallelCounterEnds, Sym2.mem_iff], by decide⟩
  have hconn : connK parallelCounterEnds
      (rowClass Finset.univ
        (balancedSwap Finset.univ X Y parallelCounterColorU) 1) 1 3 :=
    Relation.ReflTransGen.tail (Relation.ReflTransGen.single h12) h23
  intro hdisc
  exact hdisc.2 hconn

end StatMech.GrahamGHS.FourColor
