/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.SamplingPlanners.MeasurableList
public import Mathlib.Data.Rat.Encodable

@[expose] public section

/-! # Measurable RRT* cost tables and parent helpers

This file proves measurability of the RRT* cost-table lookup, the breadth-first
cost table, parent replacement, the fuel-bounded parent chain and the subtree
cost shift; the RRT* probability lift uses these deterministic facts about list
functions.
-/

open MeasureTheory

namespace Cslib.Planning.MotionPlanning.SamplingPlanners

/-- The cost-table step function is jointly measurable. -/
private theorem measurable_costToCome_cons {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] :
    Measurable (fun q : S × (S × (Int × Nat)) × List (S × (Int × Nat)) ×
      (Int × Nat) => if q.2.1.1 = q.1 then q.2.1.2 else q.2.2.2) := by
  have hFst : Measurable
      (fun q : S × (S × (Int × Nat)) × List (S × (Int × Nat)) × (Int × Nat) =>
        (q.2.1.1, q.1)) :=
    (measurable_fst.comp (measurable_fst.comp measurable_snd)).prodMk
      measurable_fst
  have hEq : Measurable
      (fun q : S × (S × (Int × Nat)) × List (S × (Int × Nat)) × (Int × Nat) =>
        decide (q.2.1.1 = q.1)) :=
    measurable_decide_eq.comp hFst
  have hSet : MeasurableSet
      {q : S × (S × (Int × Nat)) × List (S × (Int × Nat)) × (Int × Nat) |
        q.2.1.1 = q.1} := by
    have hPre : MeasurableSet ((fun q :
        S × (S × (Int × Nat)) × List (S × (Int × Nat)) × (Int × Nat) =>
        decide (q.2.1.1 = q.1)) ⁻¹' {true}) :=
      MeasurableSet.preimage (measurableSet_singleton true) hEq
    have hEqSet : {q :
        S × (S × (Int × Nat)) × List (S × (Int × Nat)) × (Int × Nat) |
        q.2.1.1 = q.1} =
        (fun q : S × (S × (Int × Nat)) × List (S × (Int × Nat)) × (Int × Nat) =>
          decide (q.2.1.1 = q.1)) ⁻¹' {true} := by
      ext q
      simp
    rw [hEqSet]
    exact hPre
  have hThen : Measurable
      (fun q : S × (S × (Int × Nat)) × List (S × (Int × Nat)) × (Int × Nat) =>
        q.2.1.2) :=
    measurable_snd.comp (measurable_fst.comp measurable_snd)
  have hElse : Measurable
      (fun q : S × (S × (Int × Nat)) × List (S × (Int × Nat)) × (Int × Nat) =>
        q.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  exact Measurable.ite hSet hThen hElse

/-- Cost-table lookup is jointly measurable in the table and the queried vertex. -/
theorem measurable_costToCome {S : Type} [DecidableEq S] [MeasurableSpace S]
    [MeasurableEq S] :
    Measurable (fun p : List (S × (Int × Nat)) × S => costToCome p.1 p.2) := by
  have hNil : Measurable (fun _ : S => ((0, 1) : Int × Nat)) := measurable_const
  have hRec : Measurable (fun p : S × List (S × (Int × Nat)) =>
      List.rec (motive := fun _ => Int × Nat)
        ((fun _ : S => ((0, 1) : Int × Nat)) p.1)
        (fun a l ih =>
          (fun q : S × (S × (Int × Nat)) × List (S × (Int × Nat)) ×
            (Int × Nat) => if q.2.1.1 = q.1 then q.2.1.2 else q.2.2.2)
            (p.1, a, l, ih)) p.2) :=
    measurable_list_rec hNil measurable_costToCome_cons
  have hEqRec : ∀ (l : List (S × (Int × Nat))) (w : S),
      List.rec (motive := fun _ => Int × Nat)
        ((fun _ : S => ((0, 1) : Int × Nat)) w)
        (fun a tl ih =>
          (fun q : S × (S × (Int × Nat)) × List (S × (Int × Nat)) ×
            (Int × Nat) => if q.2.1.1 = q.1 then q.2.1.2 else q.2.2.2)
            (w, a, tl, ih)) l =
        costToCome l w := by
    intro l w
    induction l with
    | nil => simp [costToCome]
    | cons hd tl ih => simp [costToCome, ih]
  have hMeas : Measurable (fun p : S × List (S × (Int × Nat)) =>
      costToCome p.2 p.1) := by
    have hEqFun : (fun p : S × List (S × (Int × Nat)) => costToCome p.2 p.1) =
        (fun p : S × List (S × (Int × Nat)) =>
          List.rec (motive := fun _ => Int × Nat)
            ((fun _ : S => ((0, 1) : Int × Nat)) p.1)
            (fun a l ih =>
              (fun q : S × (S × (Int × Nat)) × List (S × (Int × Nat)) ×
                (Int × Nat) => if q.2.1.1 = q.1 then q.2.1.2 else q.2.2.2)
                (p.1, a, l, ih)) p.2) := by
      funext p
      exact (hEqRec p.2 p.1).symm
    rw [hEqFun]
    exact hRec
  have hSwap : Measurable
      (fun p : List (S × (Int × Nat)) × S => (p.2, p.1)) :=
    measurable_snd.prodMk measurable_fst
  have hComp : Measurable
      ((fun p : S × List (S × (Int × Nat)) => costToCome p.2 p.1) ∘
        (fun p : List (S × (Int × Nat)) × S => (p.2, p.1))) :=
    hMeas.comp hSwap
  have hEq : (fun p : List (S × (Int × Nat)) × S => costToCome p.1 p.2) =
      (fun p : S × List (S × (Int × Nat)) => costToCome p.2 p.1) ∘
        (fun p : List (S × (Int × Nat)) × S => (p.2, p.1)) := by
    funext p
    simp
  rw [hEq]
  exact hComp

/-- Cost addition is measurable on discrete pairs. -/
private theorem measurable_ccAdd_pair :
    Measurable (fun r : (Int × Nat) × Rat => ccAdd r.1 r.2) :=
  measurable_of_countable _

/-- Projecting cost tables to vertices is measurable. -/
private theorem measurable_map_fst {S : Type} [MeasurableSpace S] :
    Measurable (fun acc : List (S × (Int × Nat)) => acc.map Prod.fst) := by
  have hF : Measurable (fun r : Unit × (S × (Int × Nat)) => r.2.1) :=
    measurable_fst.comp measurable_snd
  have hMap : Measurable (fun p : Unit × List (S × (Int × Nat)) =>
      p.2.map (fun a => (fun r : Unit × (S × (Int × Nat)) => r.2.1) (p.1, a))) :=
    measurable_list_map hF
  have hPair : Measurable (fun acc : List (S × (Int × Nat)) => ((), acc)) :=
    measurable_const.prodMk measurable_id
  have hComp : Measurable
      ((fun p : Unit × List (S × (Int × Nat)) =>
        p.2.map (fun a => (fun r : Unit × (S × (Int × Nat)) => r.2.1) (p.1, a))) ∘
        (fun acc : List (S × (Int × Nat)) => ((), acc))) :=
    hMap.comp hPair
  have hEq : (fun acc : List (S × (Int × Nat)) => acc.map Prod.fst) =
      (fun p : Unit × List (S × (Int × Nat)) =>
        p.2.map (fun a => (fun r : Unit × (S × (Int × Nat)) => r.2.1) (p.1, a))) ∘
        (fun acc : List (S × (Int × Nat)) => ((), acc)) := by
    funext acc
    simp
  rw [hEq]
  exact hComp

/-- Boolean conjunction is measurable. -/
private theorem measurable_bool_and :
    Measurable (fun r : Bool × Bool => (r.1 && r.2)) :=
  measurable_of_countable _

/-- Boolean negation is measurable. -/
private theorem measurable_bool_not : Measurable (fun b : Bool => (!b)) :=
  measurable_of_countable _

/-- The cost-table child filter predicate is measurable. -/
private theorem measurable_filter_pred {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] :
    Measurable
      (fun q : (S × List (S × (Int × Nat))) × (S × S) =>
        decide (q.2.1 = q.1.1 ∧ q.2.2 ∉ (q.1.2).map Prod.fst)) := by
  have hEqProj : Measurable
      (fun q : (S × List (S × (Int × Nat))) × (S × S) => (q.2.1, q.1.1)) :=
    (measurable_fst.comp measurable_snd).prodMk
      (measurable_fst.comp measurable_fst)
  have hDecEq : Measurable
      (fun q : (S × List (S × (Int × Nat))) × (S × S) =>
        decide (q.2.1 = q.1.1)) :=
    measurable_decide_eq.comp hEqProj
  have hE2 : Measurable
      (fun q : (S × List (S × (Int × Nat))) × (S × S) => q.2.2) :=
    measurable_snd.comp measurable_snd
  have hAccMap : Measurable
      (fun q : (S × List (S × (Int × Nat))) × (S × S) =>
        (q.1.2).map Prod.fst) :=
    measurable_map_fst.comp (measurable_snd.comp measurable_fst)
  have hPairMem : Measurable
      (fun q : (S × List (S × (Int × Nat))) × (S × S) =>
        (q.2.2, (q.1.2).map Prod.fst)) :=
    hE2.prodMk hAccMap
  have hDecMem : Measurable
      (fun q : (S × List (S × (Int × Nat))) × (S × S) =>
        decide (q.2.2 ∈ (q.1.2).map Prod.fst)) :=
    measurable_list_mem.comp hPairMem
  have hNotMem : Measurable
      (fun q : (S × List (S × (Int × Nat))) × (S × S) =>
        (!decide (q.2.2 ∈ (q.1.2).map Prod.fst))) :=
    measurable_bool_not.comp hDecMem
  have hPairAnd : Measurable
      (fun q : (S × List (S × (Int × Nat))) × (S × S) =>
        (decide (q.2.1 = q.1.1), !decide (q.2.2 ∈ (q.1.2).map Prod.fst))) :=
    hDecEq.prodMk hNotMem
  have hAnd : Measurable
      (fun q : (S × List (S × (Int × Nat))) × (S × S) =>
        (decide (q.2.1 = q.1.1) && !decide (q.2.2 ∈ (q.1.2).map Prod.fst))) :=
    measurable_bool_and.comp hPairAnd
  have hEq : (fun q : (S × List (S × (Int × Nat))) × (S × S) =>
      decide (q.2.1 = q.1.1 ∧ q.2.2 ∉ (q.1.2).map Prod.fst)) =
      (fun q : (S × List (S × (Int × Nat))) × (S × S) =>
        (decide (q.2.1 = q.1.1) && !decide (q.2.2 ∈ (q.1.2).map Prod.fst))) := by
    funext q
    simp
  rw [hEq]
  exact hAnd

/-- The cost-table child map function is measurable. -/
private theorem measurable_children_map {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) :
    Measurable (fun q : (S × (Int × Nat)) × (S × S) =>
      (q.2.2, ccAdd q.1.2 (O.cost q.1.1 q.2.2))) := by
  have hE2 : Measurable (fun q : (S × (Int × Nat)) × (S × S) => q.2.2) :=
    measurable_snd.comp measurable_snd
  have hCu : Measurable (fun q : (S × (Int × Nat)) × (S × S) => q.1.2) :=
    measurable_snd.comp measurable_fst
  have hPairCost : Measurable
      (fun q : (S × (Int × Nat)) × (S × S) => (q.1.1, q.2.2)) :=
    (measurable_fst.comp measurable_fst).prodMk
      (measurable_snd.comp measurable_snd)
  have hCost : Measurable
      (fun q : (S × (Int × Nat)) × (S × S) => O.cost q.1.1 q.2.2) :=
    hO.cost.comp hPairCost
  have hPairCC : Measurable
      (fun q : (S × (Int × Nat)) × (S × S) => (q.1.2, O.cost q.1.1 q.2.2)) :=
    hCu.prodMk hCost
  have hCC : Measurable
      (fun q : (S × (Int × Nat)) × (S × S) => ccAdd q.1.2 (O.cost q.1.1 q.2.2)) :=
    measurable_ccAdd_pair.comp hPairCC
  exact hE2.prodMk hCC

/-- Filtering then mapping children equals the filter-map form. -/
private theorem filterMap_eq_filter_map {S : Type} [DecidableEq S] {O : Oracles S}
    (edges : List (S × S)) (u : S) (cu : Int × Nat)
    (acc : List (S × (Int × Nat))) :
    edges.filterMap (fun e =>
      if e.1 = u then
        if e.2 ∈ (acc.map Prod.fst) then none
        else some (e.2, ccAdd cu (O.cost u e.2))
      else none) =
    ((edges.filter (fun e => decide (e.1 = u ∧ e.2 ∉ acc.map Prod.fst))).map
      (fun e => (e.2, ccAdd cu (O.cost u e.2)))) := by
  induction edges with
  | nil => simp
  | cons hd tl ih =>
    simp only [List.filterMap_cons, List.filter_cons]
    by_cases h1 : hd.1 = u
    · simp only [h1, ite_eq_left]
      by_cases h2 : hd.2 ∈ acc.map Prod.fst
      · simp [h2, ih]
      · simp [h2, ih]
    · simp [h1, ih]

/-- The fuel-indexed cost table is jointly measurable for each fuel value. -/
private theorem measurable_treeCostsAux_fuel {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) (n : Nat) :
    Measurable (fun p : List (S × S) × List (S × (Int × Nat)) ×
      List (S × (Int × Nat)) => treeCostsAux O p.1 n p.2.1 p.2.2) := by
  induction n with
  | zero =>
    have hProj : Measurable
        (fun p : List (S × S) × List (S × (Int × Nat)) × List (S × (Int × Nat)) =>
          p.2.2) :=
      measurable_snd.comp measurable_snd
    have hEq : (fun p : List (S × S) × List (S × (Int × Nat)) ×
        List (S × (Int × Nat)) => treeCostsAux O p.1 0 p.2.1 p.2.2) =
        (fun p : List (S × S) × List (S × (Int × Nat)) × List (S × (Int × Nat)) =>
          p.2.2) := by
      funext p
      simp [treeCostsAux]
    rw [hEq]
    exact hProj
  | succ n ih =>
    have hNil : Measurable
        (fun d : List (S × S) × List (S × (Int × Nat)) => d.2) :=
      measurable_snd
    have hCons : Measurable
        (fun q : (List (S × S) × List (S × (Int × Nat))) × (S × (Int × Nat)) ×
          List (S × (Int × Nat)) × List (S × (Int × Nat)) =>
          if q.2.1.1 ∈ (q.1.2).map Prod.fst then
            treeCostsAux O q.1.1 n q.2.2.1 q.1.2
          else treeCostsAux O q.1.1 n
            (q.2.2.1 ++ ((q.1.1.filter (fun e =>
              decide (e.1 = q.2.1.1 ∧ e.2 ∉ ((q.2.1 :: q.1.2).map Prod.fst)))).map
              (fun e => (e.2, ccAdd q.2.1.2 (O.cost q.2.1.1 e.2)))))
            (q.2.1 :: q.1.2)) := by
      have hU : Measurable
          (fun q : (List (S × S) × List (S × (Int × Nat))) × (S × (Int × Nat)) ×
            List (S × (Int × Nat)) × List (S × (Int × Nat)) => q.2.1.1) :=
        measurable_fst.comp (measurable_fst.comp measurable_snd)
      have hAcc : Measurable
          (fun q : (List (S × S) × List (S × (Int × Nat))) × (S × (Int × Nat)) ×
            List (S × (Int × Nat)) × List (S × (Int × Nat)) => q.1.2) :=
        measurable_snd.comp measurable_fst
      have hAccMap : Measurable
          (fun q : (List (S × S) × List (S × (Int × Nat))) × (S × (Int × Nat)) ×
            List (S × (Int × Nat)) × List (S × (Int × Nat)) =>
            (q.1.2).map Prod.fst) :=
        measurable_map_fst.comp hAcc
      have hPairMem : Measurable
          (fun q : (List (S × S) × List (S × (Int × Nat))) × (S × (Int × Nat)) ×
            List (S × (Int × Nat)) × List (S × (Int × Nat)) =>
            (q.2.1.1, (q.1.2).map Prod.fst)) :=
        hU.prodMk hAccMap
      have hDecMem : Measurable
          (fun q : (List (S × S) × List (S × (Int × Nat))) × (S × (Int × Nat)) ×
            List (S × (Int × Nat)) × List (S × (Int × Nat)) =>
            decide (q.2.1.1 ∈ (q.1.2).map Prod.fst)) :=
        measurable_list_mem.comp hPairMem
      have hSet : MeasurableSet
          {q : (List (S × S) × List (S × (Int × Nat))) × (S × (Int × Nat)) ×
            List (S × (Int × Nat)) × List (S × (Int × Nat)) |
            q.2.1.1 ∈ (q.1.2).map Prod.fst} := by
        have hPre : MeasurableSet
            ((fun q : (List (S × S) × List (S × (Int × Nat))) × (S × (Int × Nat)) ×
              List (S × (Int × Nat)) × List (S × (Int × Nat)) =>
              decide (q.2.1.1 ∈ (q.1.2).map Prod.fst)) ⁻¹' {true}) :=
          MeasurableSet.preimage (measurableSet_singleton true) hDecMem
        have hEqSet : {q : (List (S × S) × List (S × (Int × Nat))) ×
              (S × (Int × Nat)) × List (S × (Int × Nat)) × List (S × (Int × Nat)) |
            q.2.1.1 ∈ (q.1.2).map Prod.fst} =
            (fun q : (List (S × S) × List (S × (Int × Nat))) × (S × (Int × Nat)) ×
              List (S × (Int × Nat)) × List (S × (Int × Nat)) =>
              decide (q.2.1.1 ∈ (q.1.2).map Prod.fst)) ⁻¹' {true} := by
          ext q
          simp
        rw [hEqSet]
        exact hPre
      have hEdges : Measurable
          (fun q : (List (S × S) × List (S × (Int × Nat))) × (S × (Int × Nat)) ×
            List (S × (Int × Nat)) × List (S × (Int × Nat)) => q.1.1) :=
        measurable_fst.comp measurable_fst
      have hTail : Measurable
          (fun q : (List (S × S) × List (S × (Int × Nat))) × (S × (Int × Nat)) ×
            List (S × (Int × Nat)) × List (S × (Int × Nat)) => q.2.2.1) :=
        measurable_fst.comp (measurable_snd.comp measurable_snd)
      have hMapThen : Measurable
          (fun q : (List (S × S) × List (S × (Int × Nat))) × (S × (Int × Nat)) ×
            List (S × (Int × Nat)) × List (S × (Int × Nat)) =>
            (q.1.1, q.2.2.1, q.1.2)) :=
        hEdges.prodMk (hTail.prodMk hAcc)
      have hThen : Measurable
          (fun q : (List (S × S) × List (S × (Int × Nat))) × (S × (Int × Nat)) ×
            List (S × (Int × Nat)) × List (S × (Int × Nat)) =>
            treeCostsAux O q.1.1 n q.2.2.1 q.1.2) :=
        ih.comp hMapThen
      have hHead : Measurable
          (fun q : (List (S × S) × List (S × (Int × Nat))) × (S × (Int × Nat)) ×
            List (S × (Int × Nat)) × List (S × (Int × Nat)) => q.2.1) :=
        measurable_fst.comp measurable_snd
      have hPairAcc : Measurable
          (fun q : (List (S × S) × List (S × (Int × Nat))) × (S × (Int × Nat)) ×
            List (S × (Int × Nat)) × List (S × (Int × Nat)) => (q.2.1, q.1.2)) :=
        hHead.prodMk hAcc
      have hAccUp : Measurable
          (fun q : (List (S × S) × List (S × (Int × Nat))) × (S × (Int × Nat)) ×
            List (S × (Int × Nat)) × List (S × (Int × Nat)) => (q.2.1 :: q.1.2)) :=
        measurable_list_cons.comp hPairAcc
      have hPairFilt : Measurable
          (fun q : (List (S × S) × List (S × (Int × Nat))) × (S × (Int × Nat)) ×
            List (S × (Int × Nat)) × List (S × (Int × Nat)) =>
            ((q.2.1.1, (q.2.1 :: q.1.2)), q.1.1)) :=
        (hU.prodMk hAccUp).prodMk hEdges
      have hFiltFunc : Measurable
          (fun p : (S × List (S × (Int × Nat))) × List (S × S) =>
            p.2.filter (fun e =>
              decide (e.1 = p.1.1 ∧ e.2 ∉ (p.1.2).map Prod.fst))) :=
        measurable_list_filter measurable_filter_pred
      have hFilt : Measurable
          (fun q : (List (S × S) × List (S × (Int × Nat))) × (S × (Int × Nat)) ×
            List (S × (Int × Nat)) × List (S × (Int × Nat)) =>
            q.1.1.filter (fun e =>
              decide (e.1 = q.2.1.1 ∧ e.2 ∉ ((q.2.1 :: q.1.2).map Prod.fst)))) :=
        hFiltFunc.comp hPairFilt
      have hMapFunc : Measurable
          (fun p : (S × (Int × Nat)) × List (S × S) =>
            p.2.map (fun e => (e.2, ccAdd p.1.2 (O.cost p.1.1 e.2)))) :=
        measurable_list_map (measurable_children_map hO)
      have hPairMap : Measurable
          (fun q : (List (S × S) × List (S × (Int × Nat))) × (S × (Int × Nat)) ×
            List (S × (Int × Nat)) × List (S × (Int × Nat)) =>
            (q.2.1, q.1.1.filter (fun e =>
              decide (e.1 = q.2.1.1 ∧ e.2 ∉ ((q.2.1 :: q.1.2).map Prod.fst))))) :=
        hHead.prodMk hFilt
      have hChild : Measurable
          (fun q : (List (S × S) × List (S × (Int × Nat))) × (S × (Int × Nat)) ×
            List (S × (Int × Nat)) × List (S × (Int × Nat)) =>
            ((q.1.1.filter (fun e =>
              decide (e.1 = q.2.1.1 ∧ e.2 ∉ ((q.2.1 :: q.1.2).map Prod.fst)))).map
              (fun e => (e.2, ccAdd q.2.1.2 (O.cost q.2.1.1 e.2))))) :=
        hMapFunc.comp hPairMap
      have hPairApp : Measurable
          (fun q : (List (S × S) × List (S × (Int × Nat))) × (S × (Int × Nat)) ×
            List (S × (Int × Nat)) × List (S × (Int × Nat)) =>
            (q.2.2.1, ((q.1.1.filter (fun e =>
              decide (e.1 = q.2.1.1 ∧ e.2 ∉ ((q.2.1 :: q.1.2).map Prod.fst)))).map
              (fun e => (e.2, ccAdd q.2.1.2 (O.cost q.2.1.1 e.2)))))) :=
        hTail.prodMk hChild
      have hApp : Measurable
          (fun q : (List (S × S) × List (S × (Int × Nat))) × (S × (Int × Nat)) ×
            List (S × (Int × Nat)) × List (S × (Int × Nat)) =>
            (q.2.2.1 ++ ((q.1.1.filter (fun e =>
              decide (e.1 = q.2.1.1 ∧ e.2 ∉ ((q.2.1 :: q.1.2).map Prod.fst)))).map
              (fun e => (e.2, ccAdd q.2.1.2 (O.cost q.2.1.1 e.2)))))) :=
        measurable_list_append.comp hPairApp
      have hMapElse : Measurable
          (fun q : (List (S × S) × List (S × (Int × Nat))) × (S × (Int × Nat)) ×
            List (S × (Int × Nat)) × List (S × (Int × Nat)) =>
            (q.1.1, q.2.2.1 ++ ((q.1.1.filter (fun e =>
              decide (e.1 = q.2.1.1 ∧ e.2 ∉ ((q.2.1 :: q.1.2).map Prod.fst)))).map
              (fun e => (e.2, ccAdd q.2.1.2 (O.cost q.2.1.1 e.2)))), q.2.1 :: q.1.2)) :=
        hEdges.prodMk (hApp.prodMk hAccUp)
      have hElse : Measurable
          (fun q : (List (S × S) × List (S × (Int × Nat))) × (S × (Int × Nat)) ×
            List (S × (Int × Nat)) × List (S × (Int × Nat)) =>
            treeCostsAux O q.1.1 n
              (q.2.2.1 ++ ((q.1.1.filter (fun e =>
                decide (e.1 = q.2.1.1 ∧ e.2 ∉ ((q.2.1 :: q.1.2).map Prod.fst)))).map
                (fun e => (e.2, ccAdd q.2.1.2 (O.cost q.2.1.1 e.2)))))
              (q.2.1 :: q.1.2)) :=
        ih.comp hMapElse
      exact Measurable.ite hSet hThen hElse
    have hRec : Measurable
        (fun p : (List (S × S) × List (S × (Int × Nat))) × List (S × (Int × Nat)) =>
          List.rec (motive := fun _ => List (S × (Int × Nat)))
            ((fun d : List (S × S) × List (S × (Int × Nat)) => d.2) p.1)
            (fun a l ihRec =>
              (fun q : (List (S × S) × List (S × (Int × Nat))) ×
                (S × (Int × Nat)) × List (S × (Int × Nat)) × List (S × (Int × Nat)) =>
                if q.2.1.1 ∈ (q.1.2).map Prod.fst then
                  treeCostsAux O q.1.1 n q.2.2.1 q.1.2
                else treeCostsAux O q.1.1 n
                  (q.2.2.1 ++ ((q.1.1.filter (fun e =>
                    decide (e.1 = q.2.1.1 ∧
                      e.2 ∉ ((q.2.1 :: q.1.2).map Prod.fst)))).map
                    (fun e => (e.2, ccAdd q.2.1.2 (O.cost q.2.1.1 e.2)))))
                  (q.2.1 :: q.1.2)) (p.1, a, l, ihRec)) p.2) :=
      measurable_list_rec hNil hCons
    have hEqRec : ∀ (edges : List (S × S)) (queue : List (S × (Int × Nat)))
        (acc : List (S × (Int × Nat))),
        List.rec (motive := fun _ => List (S × (Int × Nat)))
          ((fun d : List (S × S) × List (S × (Int × Nat)) => d.2) (edges, acc))
          (fun a l ihRec =>
            (fun q : (List (S × S) × List (S × (Int × Nat))) ×
              (S × (Int × Nat)) × List (S × (Int × Nat)) × List (S × (Int × Nat)) =>
              if q.2.1.1 ∈ (q.1.2).map Prod.fst then
                treeCostsAux O q.1.1 n q.2.2.1 q.1.2
              else treeCostsAux O q.1.1 n
                (q.2.2.1 ++ ((q.1.1.filter (fun e =>
                  decide (e.1 = q.2.1.1 ∧
                    e.2 ∉ ((q.2.1 :: q.1.2).map Prod.fst)))).map
                  (fun e => (e.2, ccAdd q.2.1.2 (O.cost q.2.1.1 e.2)))))
                (q.2.1 :: q.1.2)) ((edges, acc), a, l, ihRec)) queue =
          treeCostsAux O edges (n + 1) queue acc := by
      intro edges queue acc
      cases queue with
      | nil => simp [treeCostsAux]
      | cons hd tl =>
        have hChildEq := filterMap_eq_filter_map (O := O) edges hd.1 hd.2
          (hd :: acc)
        simp [treeCostsAux, hChildEq]
    have hMeasParams : Measurable
        (fun p : (List (S × S) × List (S × (Int × Nat))) ×
          List (S × (Int × Nat)) => treeCostsAux O p.1.1 (n + 1) p.2 p.1.2) := by
      have hEqFun : (fun p : (List (S × S) × List (S × (Int × Nat))) ×
          List (S × (Int × Nat)) => treeCostsAux O p.1.1 (n + 1) p.2 p.1.2) =
          (fun p : (List (S × S) × List (S × (Int × Nat))) ×
            List (S × (Int × Nat)) =>
            List.rec (motive := fun _ => List (S × (Int × Nat)))
              ((fun d : List (S × S) × List (S × (Int × Nat)) => d.2) p.1)
              (fun a l ihRec =>
                (fun q : (List (S × S) × List (S × (Int × Nat))) ×
                  (S × (Int × Nat)) × List (S × (Int × Nat)) × List (S × (Int × Nat)) =>
                  if q.2.1.1 ∈ (q.1.2).map Prod.fst then
                    treeCostsAux O q.1.1 n q.2.2.1 q.1.2
                  else treeCostsAux O q.1.1 n
                    (q.2.2.1 ++ ((q.1.1.filter (fun e =>
                      decide (e.1 = q.2.1.1 ∧
                        e.2 ∉ ((q.2.1 :: q.1.2).map Prod.fst)))).map
                      (fun e => (e.2, ccAdd q.2.1.2 (O.cost q.2.1.1 e.2)))))
                    (q.2.1 :: q.1.2)) (p.1, a, l, ihRec)) p.2) := by
        funext p
        exact (hEqRec p.1.1 p.2 p.1.2).symm
      rw [hEqFun]
      exact hRec
    have hSwap : Measurable
        (fun p : List (S × S) × List (S × (Int × Nat)) × List (S × (Int × Nat)) =>
          ((p.1, p.2.2), p.2.1)) :=
      (measurable_fst.prodMk
        (measurable_snd.comp measurable_snd)).prodMk
        (measurable_fst.comp measurable_snd)
    have hComp : Measurable
        ((fun p : (List (S × S) × List (S × (Int × Nat))) × List (S × (Int × Nat)) =>
          treeCostsAux O p.1.1 (n + 1) p.2 p.1.2) ∘
          (fun p : List (S × S) × List (S × (Int × Nat)) × List (S × (Int × Nat)) =>
            ((p.1, p.2.2), p.2.1))) :=
      hMeasParams.comp hSwap
    have hEq : (fun p : List (S × S) × List (S × (Int × Nat)) ×
        List (S × (Int × Nat)) => treeCostsAux O p.1 (n + 1) p.2.1 p.2.2) =
        (fun p : (List (S × S) × List (S × (Int × Nat))) × List (S × (Int × Nat)) =>
          treeCostsAux O p.1.1 (n + 1) p.2 p.1.2) ∘
          (fun p : List (S × S) × List (S × (Int × Nat)) × List (S × (Int × Nat)) =>
            ((p.1, p.2.2), p.2.1)) := by
      funext p
      simp
    rw [hEq]
    exact hComp

/-- The fuel-indexed cost table is jointly measurable with its fuel index. -/
private theorem measurable_treeCostsAux_joint {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] {O : Oracles S}
    (hO : OraclesMeasurable O) :
    Measurable
      (fun q : (List (S × S) × List (S × (Int × Nat)) × List (S × (Int × Nat))) ×
        Nat => treeCostsAux O q.1.1 q.2 q.1.2.1 q.1.2.2) :=
  measurable_from_prod_countable_left
    (fun fuel => measurable_treeCostsAux_fuel hO fuel)

/-- Singleton cost lists depend measurably on their entry. -/
private theorem measurable_singleton_pair {S : Type} [MeasurableSpace S] :
    Measurable (fun v : S × (Int × Nat) => [v]) := by
  have hPair : Measurable
      (fun v : S × (Int × Nat) => (v, ([] : List (S × (Int × Nat))))) :=
    measurable_id.prodMk measurable_const
  have hComp : Measurable
      ((fun p : (S × (Int × Nat)) × List (S × (Int × Nat)) => p.1 :: p.2) ∘
        (fun v : S × (Int × Nat) => (v, ([] : List (S × (Int × Nat)))))) :=
    measurable_list_cons.comp hPair
  have hEq : (fun v : S × (Int × Nat) => [v]) =
      (fun p : (S × (Int × Nat)) × List (S × (Int × Nat)) => p.1 :: p.2) ∘
        (fun v : S × (Int × Nat) => (v, ([] : List (S × (Int × Nat))))) := by
    funext v
    simp
  rw [hEq]
  exact hComp

/-- Adding one to a natural is measurable. -/
private theorem measurable_nat_succ : Measurable (fun n : Nat => n + 1) :=
  measurable_of_countable _

/-- The breadth-first cost table is jointly measurable in the vertex list, the edge list
and the root. -/
theorem measurable_recomputeCosts {S : Type} [DecidableEq S] [MeasurableSpace S]
    [MeasurableEq S] {O : Oracles S} (hO : OraclesMeasurable O) :
    Measurable (fun p : List S × List (S × S) × S => recomputeCosts O p.1 p.2.1 p.2.2) := by
  have hEdges : Measurable (fun p : List S × List (S × S) × S => p.2.1) :=
    measurable_fst.comp measurable_snd
  have hLen : Measurable (fun p : List S × List (S × S) × S => p.2.1.length) :=
    measurable_list_length.comp hEdges
  have hFuel : Measurable
      (fun p : List S × List (S × S) × S => p.2.1.length + 1) :=
    measurable_nat_succ.comp hLen
  have hStart : Measurable (fun p : List S × List (S × S) × S => p.2.2) :=
    measurable_snd.comp measurable_snd
  have hPairQ0 : Measurable
      (fun p : List S × List (S × S) × S => (p.2.2, ((0, 1) : Int × Nat))) :=
    hStart.prodMk measurable_const
  have hQueue : Measurable
      (fun p : List S × List (S × S) × S => [(p.2.2, ((0, 1) : Int × Nat))]) :=
    measurable_singleton_pair.comp hPairQ0
  have hAcc : Measurable
      (fun p : List S × List (S × S) × S => ([] : List (S × (Int × Nat)))) :=
    measurable_const
  have hTriple : Measurable
      (fun p : List S × List (S × S) × S =>
        (p.2.1, [(p.2.2, ((0, 1) : Int × Nat))], ([] : List (S × (Int × Nat))))) :=
    hEdges.prodMk (hQueue.prodMk hAcc)
  have hArg : Measurable
      (fun p : List S × List (S × S) × S =>
        ((p.2.1, [(p.2.2, ((0, 1) : Int × Nat))],
          ([] : List (S × (Int × Nat)))), p.2.1.length + 1)) :=
    hTriple.prodMk hFuel
  have hComp : Measurable
      ((fun q : (List (S × S) × List (S × (Int × Nat)) × List (S × (Int × Nat))) ×
        Nat => treeCostsAux O q.1.1 q.2 q.1.2.1 q.1.2.2) ∘
        (fun p : List S × List (S × S) × S =>
          ((p.2.1, [(p.2.2, ((0, 1) : Int × Nat))],
            ([] : List (S × (Int × Nat)))), p.2.1.length + 1))) :=
    (measurable_treeCostsAux_joint hO).comp hArg
  have hEq : (fun p : List S × List (S × S) × S =>
      recomputeCosts O p.1 p.2.1 p.2.2) =
      (fun q : (List (S × S) × List (S × (Int × Nat)) × List (S × (Int × Nat))) ×
        Nat => treeCostsAux O q.1.1 q.2 q.1.2.1 q.1.2.2) ∘
        (fun p : List S × List (S × S) × S =>
          ((p.2.1, [(p.2.2, ((0, 1) : Int × Nat))],
            ([] : List (S × (Int × Nat)))), p.2.1.length + 1)) := by
    funext p
    simp [recomputeCosts]
  rw [hEq]
  exact hComp

/-- The parent-replacement element function is measurable. -/
private theorem measurable_replaceParent_elem {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] :
    Measurable (fun q : (S × S) × (S × S) =>
      if q.2.2 = q.1.2 then q.1 else q.2) := by
  have hProj : Measurable (fun q : (S × S) × (S × S) => (q.2.2, q.1.2)) :=
    (measurable_snd.comp measurable_snd).prodMk
      (measurable_snd.comp measurable_fst)
  have hEq : Measurable (fun q : (S × S) × (S × S) =>
      decide (q.2.2 = q.1.2)) :=
    measurable_decide_eq.comp hProj
  have hSet : MeasurableSet {q : (S × S) × (S × S) | q.2.2 = q.1.2} := by
    have hPre : MeasurableSet
        ((fun q : (S × S) × (S × S) => decide (q.2.2 = q.1.2)) ⁻¹' {true}) :=
      MeasurableSet.preimage (measurableSet_singleton true) hEq
    have hEqSet : {q : (S × S) × (S × S) | q.2.2 = q.1.2} =
        (fun q : (S × S) × (S × S) => decide (q.2.2 = q.1.2)) ⁻¹' {true} := by
      ext q
      simp
    rw [hEqSet]
    exact hPre
  exact Measurable.ite hSet measurable_fst measurable_snd

/-- Parent replacement is jointly measurable. -/
theorem measurable_replaceParent {S : Type} [DecidableEq S] [MeasurableSpace S]
    [MeasurableEq S] :
    Measurable (fun p : List (S × S) × S × S => replaceParent p.1 p.2.1 p.2.2) := by
  have hMap : Measurable (fun q : (S × S) × List (S × S) =>
      q.2.map (fun e => if e.2 = q.1.2 then q.1 else e)) :=
    measurable_list_map measurable_replaceParent_elem
  have hSwap : Measurable (fun p : List (S × S) × S × S => (p.2, p.1)) :=
    measurable_snd.prodMk measurable_fst
  have hComp : Measurable
      ((fun q : (S × S) × List (S × S) =>
          q.2.map (fun e => if e.2 = q.1.2 then q.1 else e)) ∘
        (fun p : List (S × S) × S × S => (p.2, p.1))) :=
    hMap.comp hSwap
  have hEq : (fun p : List (S × S) × S × S => replaceParent p.1 p.2.1 p.2.2) =
      (fun q : (S × S) × List (S × S) =>
          q.2.map (fun e => if e.2 = q.1.2 then q.1 else e)) ∘
        (fun p : List (S × S) × S × S => (p.2, p.1)) := by
    funext p
    simp [replaceParent]
  rw [hEq]
  exact hComp

/-- The parent-search presence step function is measurable. -/
private theorem measurable_findIsSome_cons {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] :
    Measurable (fun q : S × (S × S) × List (S × S) × Bool =>
      if q.2.1.2 = q.1 then true else q.2.2.2) := by
  have hProj : Measurable (fun q : S × (S × S) × List (S × S) × Bool =>
      (q.2.1.2, q.1)) :=
    (measurable_snd.comp (measurable_fst.comp measurable_snd)).prodMk
      measurable_fst
  have hEq : Measurable (fun q : S × (S × S) × List (S × S) × Bool =>
      decide (q.2.1.2 = q.1)) :=
    measurable_decide_eq.comp hProj
  have hSet : MeasurableSet
      {q : S × (S × S) × List (S × S) × Bool | q.2.1.2 = q.1} := by
    have hPre : MeasurableSet ((fun q :
        S × (S × S) × List (S × S) × Bool =>
        decide (q.2.1.2 = q.1)) ⁻¹' {true}) :=
      MeasurableSet.preimage (measurableSet_singleton true) hEq
    have hEqSet : {q : S × (S × S) × List (S × S) × Bool | q.2.1.2 = q.1} =
        (fun q : S × (S × S) × List (S × S) × Bool =>
          decide (q.2.1.2 = q.1)) ⁻¹' {true} := by
      ext q
      simp
    rw [hEqSet]
    exact hPre
  have hThen : Measurable
      (fun _ : S × (S × S) × List (S × S) × Bool => true) :=
    measurable_const
  have hElse : Measurable
      (fun q : S × (S × S) × List (S × S) × Bool => q.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  exact Measurable.ite hSet hThen hElse

/-- The parent-search presence test is jointly measurable. -/
private theorem measurable_findIsSome_aux {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] :
    Measurable (fun p : S × List (S × S) =>
      (findParent p.2 p.1).isSome) := by
  have hNil : Measurable (fun _ : S => false) := measurable_const
  have hRec : Measurable (fun p : S × List (S × S) =>
      List.rec (motive := fun _ => Bool)
        ((fun _ : S => false) p.1)
        (fun a l ih =>
          (fun q : S × (S × S) × List (S × S) × Bool =>
            if q.2.1.2 = q.1 then true else q.2.2.2) (p.1, a, l, ih)) p.2) :=
    measurable_list_rec hNil measurable_findIsSome_cons
  have hEqRec : ∀ (e : List (S × S)) (v : S),
      List.rec (motive := fun _ => Bool)
        ((fun _ : S => false) v)
        (fun a l ih =>
          (fun q : S × (S × S) × List (S × S) × Bool =>
            if q.2.1.2 = q.1 then true else q.2.2.2) (v, a, l, ih)) e =
        (findParent e v).isSome := by
    intro e v
    induction e with
    | nil => simp [findParent]
    | cons hd tl ih =>
      show (if hd.2 = v then true
        else List.rec (motive := fun _ => Bool) false
          (fun a l2 ih2 =>
            (fun q : S × (S × S) × List (S × S) × Bool =>
              if q.2.1.2 = q.1 then true else q.2.2.2) (v, a, l2, ih2))
          tl) = (findParent (hd :: tl) v).isSome
      simp only [findParent]
      by_cases h : hd.2 = v
      · simp only [ite_eq_left h, Option.isSome_some]
      · simp only [ite_eq_right h, ih]
  have hEqFun : (fun p : S × List (S × S) => (findParent p.2 p.1).isSome) =
      (fun p : S × List (S × S) =>
        List.rec (motive := fun _ => Bool)
          ((fun _ : S => false) p.1)
          (fun a l ih =>
            (fun q : S × (S × S) × List (S × S) × Bool =>
              if q.2.1.2 = q.1 then true else q.2.2.2) (p.1, a, l, ih)) p.2) := by
    funext p
    exact (hEqRec p.2 p.1).symm
  rw [hEqFun]
  exact hRec

/-- The parent-search default step function is measurable. -/
private theorem measurable_findGetD_cons {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] :
    Measurable (fun q : S × (S × S) × List (S × S) × S =>
      if q.2.1.2 = q.1 then q.2.1.1 else q.2.2.2) := by
  have hProj : Measurable (fun q : S × (S × S) × List (S × S) × S =>
      (q.2.1.2, q.1)) :=
    (measurable_snd.comp (measurable_fst.comp measurable_snd)).prodMk
      measurable_fst
  have hEq : Measurable (fun q : S × (S × S) × List (S × S) × S =>
      decide (q.2.1.2 = q.1)) :=
    measurable_decide_eq.comp hProj
  have hSet : MeasurableSet
      {q : S × (S × S) × List (S × S) × S | q.2.1.2 = q.1} := by
    have hPre : MeasurableSet ((fun q :
        S × (S × S) × List (S × S) × S =>
        decide (q.2.1.2 = q.1)) ⁻¹' {true}) :=
      MeasurableSet.preimage (measurableSet_singleton true) hEq
    have hEqSet : {q : S × (S × S) × List (S × S) × S | q.2.1.2 = q.1} =
        (fun q : S × (S × S) × List (S × S) × S =>
          decide (q.2.1.2 = q.1)) ⁻¹' {true} := by
      ext q
      simp
    rw [hEqSet]
    exact hPre
  have hThen : Measurable
      (fun q : S × (S × S) × List (S × S) × S => q.2.1.1) :=
    measurable_fst.comp (measurable_fst.comp measurable_snd)
  have hElse : Measurable
      (fun q : S × (S × S) × List (S × S) × S => q.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  exact Measurable.ite hSet hThen hElse

/-- The parent-search default lookup is jointly measurable. -/
private theorem measurable_findGetD_aux {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] :
    Measurable (fun p : S × List (S × S) =>
      (findParent p.2 p.1).getD p.1) := by
  have hNil : Measurable (fun v : S => v) := measurable_id
  have hRec : Measurable (fun p : S × List (S × S) =>
      List.rec (motive := fun _ => S)
        ((fun v : S => v) p.1)
        (fun a l ih =>
          (fun q : S × (S × S) × List (S × S) × S =>
            if q.2.1.2 = q.1 then q.2.1.1 else q.2.2.2) (p.1, a, l, ih))
        p.2) :=
    measurable_list_rec hNil measurable_findGetD_cons
  have hEqRec : ∀ (e : List (S × S)) (v : S),
      List.rec (motive := fun _ => S)
        ((fun v0 : S => v0) v)
        (fun a l ih =>
          (fun q : S × (S × S) × List (S × S) × S =>
            if q.2.1.2 = q.1 then q.2.1.1 else q.2.2.2) (v, a, l, ih)) e =
        (findParent e v).getD v := by
    intro e v
    induction e with
    | nil => simp [findParent]
    | cons hd tl ih => by_cases h : hd.2 = v <;> simp [findParent, h, ih]
  have hEqFun : (fun p : S × List (S × S) => (findParent p.2 p.1).getD p.1) =
      (fun p : S × List (S × S) =>
        List.rec (motive := fun _ => S)
          ((fun v : S => v) p.1)
          (fun a l ih =>
            (fun q : S × (S × S) × List (S × S) × S =>
              if q.2.1.2 = q.1 then q.2.1.1 else q.2.2.2) (p.1, a, l, ih))
          p.2) := by
    funext p
    exact (hEqRec p.2 p.1).symm
  rw [hEqFun]
  exact hRec

/-- Singleton lists depend measurably on their element. -/
private theorem measurable_singleton_list {S : Type} [MeasurableSpace S] :
    Measurable (fun v : S => [v]) := by
  have hPair : Measurable (fun v : S => (v, ([] : List S))) :=
    measurable_id.prodMk measurable_const
  have hComp : Measurable ((fun p : S × List S => p.1 :: p.2) ∘
      (fun v : S => (v, ([] : List S)))) :=
    measurable_list_cons.comp hPair
  have hEq : (fun v : S => [v]) =
      (fun p : S × List S => p.1 :: p.2) ∘ (fun v : S => (v, ([] : List S))) := by
    funext v
    simp
  rw [hEq]
  exact hComp

/-- The fuel-bounded parent chain is jointly measurable in the edges, the root and the
query vertex, for each fuel value. -/
theorem measurable_parentChain {S : Type} [DecidableEq S] [MeasurableSpace S]
    [MeasurableEq S] (n : ℕ) :
    Measurable (fun p : List (S × S) × S × S => parentChain p.1 p.2.1 p.2.2 n) := by
  induction n with
  | zero =>
    have hProj : Measurable (fun p : List (S × S) × S × S => p.2.2) :=
      measurable_snd.comp measurable_snd
    have hSing : Measurable (fun p : List (S × S) × S × S => [p.2.2]) :=
      measurable_singleton_list.comp hProj
    have hEq : (fun p : List (S × S) × S × S => parentChain p.1 p.2.1 p.2.2 0) =
        (fun p : List (S × S) × S × S => [p.2.2]) := by
      funext p
      simp [parentChain]
    rw [hEq]
    exact hSing
  | succ n ih =>
    have hSing : Measurable (fun p : List (S × S) × S × S => [p.2.2]) :=
      measurable_singleton_list.comp (measurable_snd.comp measurable_snd)
    have hSwap : Measurable (fun p : List (S × S) × S × S => (p.2.2, p.1)) :=
      (measurable_snd.comp measurable_snd).prodMk measurable_fst
    have hIsSome : Measurable
        (fun p : List (S × S) × S × S => (findParent p.1 p.2.2).isSome) :=
      measurable_findIsSome_aux.comp hSwap
    have hGetD : Measurable
        (fun p : List (S × S) × S × S =>
          (findParent p.1 p.2.2).getD p.2.2) :=
      measurable_findGetD_aux.comp hSwap
    have hProjEq : Measurable (fun p : List (S × S) × S × S => (p.2.2, p.2.1)) :=
      (measurable_snd.comp measurable_snd).prodMk
        (measurable_fst.comp measurable_snd)
    have hDecEq : Measurable
        (fun p : List (S × S) × S × S => decide (p.2.2 = p.2.1)) :=
      measurable_decide_eq.comp hProjEq
    have hSetEq : MeasurableSet {p : List (S × S) × S × S | p.2.2 = p.2.1} := by
      have hPre : MeasurableSet
          ((fun p : List (S × S) × S × S => decide (p.2.2 = p.2.1)) ⁻¹' {true}) :=
        MeasurableSet.preimage (measurableSet_singleton true) hDecEq
      have hEqSet : {p : List (S × S) × S × S | p.2.2 = p.2.1} =
          (fun p : List (S × S) × S × S => decide (p.2.2 = p.2.1)) ⁻¹' {true} := by
        ext p
        simp
      rw [hEqSet]
      exact hPre
    have hSetSome : MeasurableSet
        {p : List (S × S) × S × S | (findParent p.1 p.2.2).isSome = true} := by
      have hPre : MeasurableSet
          ((fun p : List (S × S) × S × S =>
            (findParent p.1 p.2.2).isSome) ⁻¹' {true}) :=
        MeasurableSet.preimage (measurableSet_singleton true) hIsSome
      have hEqSet : {p : List (S × S) × S × S |
          (findParent p.1 p.2.2).isSome = true} =
          (fun p : List (S × S) × S × S =>
            (findParent p.1 p.2.2).isSome) ⁻¹' {true} := by
        rfl
      rw [hEqSet]
      exact hPre
    have hMapRec : Measurable
        (fun p : List (S × S) × S × S =>
          (p.1, p.2.1, (findParent p.1 p.2.2).getD p.2.2)) :=
      measurable_fst.prodMk ((measurable_fst.comp measurable_snd).prodMk hGetD)
    have hRecCall : Measurable
        (fun p : List (S × S) × S × S =>
          parentChain p.1 p.2.1 ((findParent p.1 p.2.2).getD p.2.2) n) :=
      ih.comp hMapRec
    have hPairCons : Measurable
        (fun p : List (S × S) × S × S =>
          (p.2.2, parentChain p.1 p.2.1 ((findParent p.1 p.2.2).getD p.2.2) n)) :=
      (measurable_snd.comp measurable_snd).prodMk hRecCall
    have hCons : Measurable
        (fun p : List (S × S) × S × S =>
          p.2.2 :: parentChain p.1 p.2.1 ((findParent p.1 p.2.2).getD p.2.2) n) :=
      measurable_list_cons.comp hPairCons
    have hInner : Measurable
        (fun p : List (S × S) × S × S =>
          if (findParent p.1 p.2.2).isSome = true then
            p.2.2 :: parentChain p.1 p.2.1 ((findParent p.1 p.2.2).getD p.2.2) n
          else [p.2.2]) :=
      Measurable.ite hSetSome hCons hSing
    have hOuter : Measurable
        (fun p : List (S × S) × S × S =>
          if p.2.2 = p.2.1 then [p.2.2]
          else if (findParent p.1 p.2.2).isSome = true then
            p.2.2 :: parentChain p.1 p.2.1 ((findParent p.1 p.2.2).getD p.2.2) n
          else [p.2.2]) :=
      Measurable.ite hSetEq hSing hInner
    have hEq : (fun p : List (S × S) × S × S => parentChain p.1 p.2.1 p.2.2 (n + 1)) =
        (fun p : List (S × S) × S × S =>
          if p.2.2 = p.2.1 then [p.2.2]
          else if (findParent p.1 p.2.2).isSome = true then
            p.2.2 :: parentChain p.1 p.2.1 ((findParent p.1 p.2.2).getD p.2.2) n
          else [p.2.2]) := by
      funext p
      simp only [parentChain]
      by_cases hEq : p.2.2 = p.2.1
      · simp only [hEq, ite_eq_left]
      · simp only [hEq]
        cases hF : findParent p.1 p.2.2 with
        | none => simp
        | some u => simp
    rw [hEq]
    exact hOuter

/-- Cost-pair addition is measurable on discrete pairs. -/
private theorem measurable_ccAddPair_pair :
    Measurable (fun r : (Int × Nat) × (Int × Nat) => ccAddPair r.1 r.2) :=
  measurable_of_countable _

/-- The cost-shift element function is measurable for each fuel value. -/
private theorem measurable_shift_elem {S : Type} [DecidableEq S]
    [MeasurableSpace S] [MeasurableEq S] (n : ℕ) :
    Measurable
      (fun q : (List (S × S) × S × S × (Int × Nat)) × (S × (Int × Nat)) =>
        if q.1.2.2.1 ∈ parentChain q.1.1 q.1.2.1 q.2.1 n then
          (q.2.1, ccAddPair q.2.2 q.1.2.2.2)
        else q.2) := by
  have hEdges : Measurable
      (fun q : (List (S × S) × S × S × (Int × Nat)) × (S × (Int × Nat)) =>
        q.1.1) :=
    measurable_fst.comp measurable_fst
  have hStart : Measurable
      (fun q : (List (S × S) × S × S × (Int × Nat)) × (S × (Int × Nat)) =>
        q.1.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_fst)
  have hQuery : Measurable
      (fun q : (List (S × S) × S × S × (Int × Nat)) × (S × (Int × Nat)) =>
        q.2.1) :=
    measurable_fst.comp measurable_snd
  have hMapPar : Measurable
      (fun q : (List (S × S) × S × S × (Int × Nat)) × (S × (Int × Nat)) =>
        (q.1.1, q.1.2.1, q.2.1)) :=
    hEdges.prodMk (hStart.prodMk hQuery)
  have hPar : Measurable
      (fun q : (List (S × S) × S × S × (Int × Nat)) × (S × (Int × Nat)) =>
        parentChain q.1.1 q.1.2.1 q.2.1 n) :=
    (measurable_parentChain n).comp hMapPar
  have hW : Measurable
      (fun q : (List (S × S) × S × S × (Int × Nat)) × (S × (Int × Nat)) =>
        q.1.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hPairMem : Measurable
      (fun q : (List (S × S) × S × S × (Int × Nat)) × (S × (Int × Nat)) =>
        (q.1.2.2.1, parentChain q.1.1 q.1.2.1 q.2.1 n)) :=
    hW.prodMk hPar
  have hDecMem : Measurable
      (fun q : (List (S × S) × S × S × (Int × Nat)) × (S × (Int × Nat)) =>
        decide (q.1.2.2.1 ∈ parentChain q.1.1 q.1.2.1 q.2.1 n)) :=
    measurable_list_mem.comp hPairMem
  have hSet : MeasurableSet
      {q : (List (S × S) × S × S × (Int × Nat)) × (S × (Int × Nat)) |
        q.1.2.2.1 ∈ parentChain q.1.1 q.1.2.1 q.2.1 n} := by
    have hPre : MeasurableSet
        ((fun q : (List (S × S) × S × S × (Int × Nat)) × (S × (Int × Nat)) =>
          decide (q.1.2.2.1 ∈ parentChain q.1.1 q.1.2.1 q.2.1 n)) ⁻¹' {true}) :=
      MeasurableSet.preimage (measurableSet_singleton true) hDecMem
    have hEqSet : {q : (List (S × S) × S × S × (Int × Nat)) × (S × (Int × Nat)) |
        q.1.2.2.1 ∈ parentChain q.1.1 q.1.2.1 q.2.1 n} =
        (fun q : (List (S × S) × S × S × (Int × Nat)) × (S × (Int × Nat)) =>
          decide (q.1.2.2.1 ∈ parentChain q.1.1 q.1.2.1 q.2.1 n)) ⁻¹' {true} := by
      ext q
      simp
    rw [hEqSet]
    exact hPre
  have hE1 : Measurable
      (fun q : (List (S × S) × S × S × (Int × Nat)) × (S × (Int × Nat)) =>
        q.2.1) :=
    measurable_fst.comp measurable_snd
  have hE2 : Measurable
      (fun q : (List (S × S) × S × S × (Int × Nat)) × (S × (Int × Nat)) =>
        q.2.2) :=
    measurable_snd.comp measurable_snd
  have hD : Measurable
      (fun q : (List (S × S) × S × S × (Int × Nat)) × (S × (Int × Nat)) =>
        q.1.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_fst))
  have hPairCC : Measurable
      (fun q : (List (S × S) × S × S × (Int × Nat)) × (S × (Int × Nat)) =>
        (q.2.2, q.1.2.2.2)) :=
    hE2.prodMk hD
  have hCC : Measurable
      (fun q : (List (S × S) × S × S × (Int × Nat)) × (S × (Int × Nat)) =>
        ccAddPair q.2.2 q.1.2.2.2) :=
    measurable_ccAddPair_pair.comp hPairCC
  have hThen : Measurable
      (fun q : (List (S × S) × S × S × (Int × Nat)) × (S × (Int × Nat)) =>
        (q.2.1, ccAddPair q.2.2 q.1.2.2.2)) :=
    hE1.prodMk hCC
  have hElse : Measurable
      (fun q : (List (S × S) × S × S × (Int × Nat)) × (S × (Int × Nat)) =>
        q.2) :=
    measurable_snd
  exact Measurable.ite hSet hThen hElse

/-- The subtree cost shift is jointly measurable in its list, vertex and pair arguments,
for each fuel value. -/
theorem measurable_shiftCostsPair {S : Type} [DecidableEq S] [MeasurableSpace S]
    [MeasurableEq S] (n : ℕ) :
    Measurable (fun p : List (S × S) × S × S × (Int × Nat) × List (S × (Int × Nat)) =>
      shiftCostsPair p.1 p.2.1 p.2.2.1 n p.2.2.2.1 p.2.2.2.2) := by
  have hMap : Measurable
      (fun r : (List (S × S) × S × S × (Int × Nat)) × List (S × (Int × Nat)) =>
        r.2.map (fun e =>
          if r.1.2.2.1 ∈ parentChain r.1.1 r.1.2.1 e.1 n then
            (e.1, ccAddPair e.2 r.1.2.2.2)
          else e)) :=
    measurable_list_map (measurable_shift_elem n)
  have hP1 : Measurable
      (fun p : List (S × S) × S × S × (Int × Nat) × List (S × (Int × Nat)) =>
        p.1) :=
    measurable_fst
  have hP21 : Measurable
      (fun p : List (S × S) × S × S × (Int × Nat) × List (S × (Int × Nat)) =>
        p.2.1) :=
    measurable_fst.comp measurable_snd
  have hP221 : Measurable
      (fun p : List (S × S) × S × S × (Int × Nat) × List (S × (Int × Nat)) =>
        p.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hP2221 : Measurable
      (fun p : List (S × S) × S × S × (Int × Nat) × List (S × (Int × Nat)) =>
        p.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hP2222 : Measurable
      (fun p : List (S × S) × S × S × (Int × Nat) × List (S × (Int × Nat)) =>
        p.2.2.2.2) :=
    measurable_snd.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hInnerWD : Measurable
      (fun p : List (S × S) × S × S × (Int × Nat) × List (S × (Int × Nat)) =>
        (p.2.2.1, p.2.2.2.1)) :=
    hP221.prodMk hP2221
  have hInnerSWD : Measurable
      (fun p : List (S × S) × S × S × (Int × Nat) × List (S × (Int × Nat)) =>
        (p.2.1, p.2.2.1, p.2.2.2.1)) :=
    hP21.prodMk hInnerWD
  have hDelta : Measurable
      (fun p : List (S × S) × S × S × (Int × Nat) × List (S × (Int × Nat)) =>
        (p.1, p.2.1, p.2.2.1, p.2.2.2.1)) :=
    hP1.prodMk hInnerSWD
  have hRearr : Measurable
      (fun p : List (S × S) × S × S × (Int × Nat) × List (S × (Int × Nat)) =>
        ((p.1, p.2.1, p.2.2.1, p.2.2.2.1), p.2.2.2.2)) :=
    hDelta.prodMk hP2222
  have hComp : Measurable
      ((fun r : (List (S × S) × S × S × (Int × Nat)) × List (S × (Int × Nat)) =>
          r.2.map (fun e =>
            if r.1.2.2.1 ∈ parentChain r.1.1 r.1.2.1 e.1 n then
              (e.1, ccAddPair e.2 r.1.2.2.2)
            else e)) ∘
        (fun p : List (S × S) × S × S × (Int × Nat) × List (S × (Int × Nat)) =>
          ((p.1, p.2.1, p.2.2.1, p.2.2.2.1), p.2.2.2.2))) :=
    hMap.comp hRearr
  have hEq : (fun p : List (S × S) × S × S × (Int × Nat) × List (S × (Int × Nat)) =>
      shiftCostsPair p.1 p.2.1 p.2.2.1 n p.2.2.2.1 p.2.2.2.2) =
      (fun r : (List (S × S) × S × S × (Int × Nat)) × List (S × (Int × Nat)) =>
          r.2.map (fun e =>
            if r.1.2.2.1 ∈ parentChain r.1.1 r.1.2.1 e.1 n then
              (e.1, ccAddPair e.2 r.1.2.2.2)
            else e)) ∘
        (fun p : List (S × S) × S × S × (Int × Nat) × List (S × (Int × Nat)) =>
          ((p.1, p.2.1, p.2.2.1, p.2.2.2.1), p.2.2.2.2)) := by
    funext p
    simp [shiftCostsPair]
  rw [hEq]
  exact hComp

end Cslib.Planning.MotionPlanning.SamplingPlanners
