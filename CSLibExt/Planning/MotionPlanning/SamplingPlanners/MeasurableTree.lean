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

/-! # RRT measurability

The RRT tree built from a finite sample list is a measurable function of the
samples, and pre-filtering the collision-free samples does not change it.

The configuration type carries a σ-algebra with measurable diagonal, finite
lists carry the length-stratified σ-algebra, and the oracle bundle tests are
jointly measurable. A planner reads a raw sample prefix and applies its own
collision filter; there is no infinite free-sample subsequence.
-/

open MeasureTheory

namespace Cslib.Planning.MotionPlanning.SamplingPlanners

/-- One step of the nearest-vertex scan, as a function of sample and state. -/
private def nearestStep {C : Type} (O : Oracles C) (t : C × C × C) : C :=
  if O.cost t.2.2 t.1 < O.cost t.2.1 t.1 then t.2.2 else t.2.1

/-- The nearest-vertex scan step is measurable in its inputs. -/
private theorem measurable_nearestStep {C : Type} [MeasurableSpace C]
    {O : Oracles C} (hO : OraclesMeasurable O) :
    Measurable (nearestStep O) := by
  have h1 : Measurable (fun t : C × C × C => O.cost t.2.2 t.1) :=
    hO.cost.comp (measurable_snd.snd.prodMk measurable_fst)
  have h2 : Measurable (fun t : C × C × C => O.cost t.2.1 t.1) :=
    hO.cost.comp (measurable_snd.fst.prodMk measurable_fst)
  have hcount : {p : ℚ × ℚ | p.1 < p.2}.Countable :=
    Set.Countable.mono (Set.subset_univ _) Set.countable_univ
  have hsetT : MeasurableSet {p : ℚ × ℚ | p.1 < p.2} := hcount.measurableSet
  have hset : MeasurableSet
      {t : C × C × C | O.cost t.2.2 t.1 < O.cost t.2.1 t.1} :=
    (h1.prodMk h2) hsetT
  have hbr1 : Measurable (fun t : C × C × C => t.2.2) := measurable_snd.snd
  have hbr2 : Measurable (fun t : C × C × C => t.2.1) := measurable_snd.fst
  exact Measurable.ite hset hbr1 hbr2

/-- `nearest` agrees with the list-recursion form used for measurability. -/
private theorem nearest_eq_rec {C : Type} (O : Oracles C) (verts : List C)
    (dflt s : C) :
    nearest O verts dflt s =
      List.rec (motive := fun _ => C) dflt
        (fun v vs _ => vs.foldl (fun best w => nearestStep O (s, best, w)) v)
        verts := by
  cases verts with
  | nil => rfl
  | cons v vs => rfl

/-- The cons case of the `nearest` recursion is measurable. -/
private theorem measurable_nearest_cons {C : Type} [MeasurableSpace C]
    {O : Oracles C} (hO : OraclesMeasurable O) :
    Measurable (fun q : (C × C) × C × List C × C =>
      q.2.2.1.foldl (fun best w => nearestStep O (q.1.2, best, w)) q.2.1) := by
  have hF : Measurable (fun r : C × C × List C =>
      r.2.2.foldl (fun b a => nearestStep O (r.1, b, a)) r.2.1) :=
    measurable_list_foldl (measurable_nearestStep hO)
  have hreorg : Measurable (fun q : (C × C) × C × List C × C =>
      (q.1.2, q.2.1, q.2.2.1)) :=
    measurable_fst.snd.prodMk
      (measurable_snd.fst.prodMk measurable_snd.snd.fst)
  simpa [Function.comp_def] using hF.comp hreorg

/-- `nearest` is jointly measurable in the vertex list and the query. -/
private theorem measurable_nearest {C : Type} [MeasurableSpace C]
    {O : Oracles C} (hO : OraclesMeasurable O) :
    Measurable (fun p : (C × C) × List C => nearest O p.2 p.1.1 p.1.2) := by
  have heq : (fun p : (C × C) × List C => nearest O p.2 p.1.1 p.1.2)
      = (fun p => List.rec (motive := fun _ => C) p.1.1
          (fun v vs _ =>
            vs.foldl (fun best w => nearestStep O (p.1.2, best, w)) v) p.2) := by
    funext p
    exact nearest_eq_rec O p.2 p.1.1 p.1.2
  rw [heq]
  exact measurable_list_rec measurable_fst (measurable_nearest_cons hO)

/-- Single-sample RRT update of the accumulator and the sample. -/
private def rrtStep {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (p : (List C × List (C × C)) × C) : List C × List (C × C) :=
  let u := nearest O p.1.1 start p.2
  let x := O.steer u p.2
  if O.free p.2 = true ∧ O.free x = true ∧ O.link u x = true ∧ x ∉ p.1.1 then
    (x :: p.1.1, (u, x) :: p.1.2)
  else p.1

/-- `rrtAux` is a left fold of the single-sample update. -/
private theorem rrtAux_eq_foldl {C : Type} [DecidableEq C] (O : Oracles C)
    (start : C) (ss : List C) (verts : List C) (edges : List (C × C)) :
    rrtAux O start ss verts edges =
      ss.foldl (fun b a => rrtStep O start (b, a)) (verts, edges) := by
  induction ss generalizing verts edges with
  | nil => simp [rrtAux]
  | cons s ss ih =>
      simp only [List.foldl_cons, rrtAux, rrtStep]
      split
      · exact ih _ _
      · exact ih _ _

/-- The single-sample RRT update is measurable. -/
private theorem measurable_rrtStep {C : Type} [DecidableEq C] [MeasurableSpace C]
    [MeasurableEq C] {O : Oracles C} (hO : OraclesMeasurable O) (start : C) :
    Measurable (rrtStep O start) := by
  have hU : Measurable (fun p : (List C × List (C × C)) × C =>
      nearest O p.1.1 start p.2) :=
    (measurable_nearest hO).comp
      ((measurable_const.prodMk measurable_snd).prodMk measurable_fst.fst)
  have hX : Measurable (fun p : (List C × List (C × C)) × C =>
      O.steer (nearest O p.1.1 start p.2) p.2) :=
    hO.steer.comp (hU.prodMk measurable_snd)
  have hS1 : MeasurableSet
      {p : (List C × List (C × C)) × C | O.free p.2 = true} :=
    (hO.free.comp measurable_snd) (measurableSet_singleton true)
  have hXfree : Measurable (fun p : (List C × List (C × C)) × C =>
      O.free (O.steer (nearest O p.1.1 start p.2) p.2)) :=
    hO.free.comp hX
  have hS2 : MeasurableSet {p : (List C × List (C × C)) × C |
      O.free (O.steer (nearest O p.1.1 start p.2) p.2) = true} :=
    hXfree (measurableSet_singleton true)
  have hlink : Measurable (fun p : (List C × List (C × C)) × C =>
      O.link (nearest O p.1.1 start p.2)
        (O.steer (nearest O p.1.1 start p.2) p.2)) :=
    hO.link.comp (hU.prodMk hX)
  have hS3 : MeasurableSet {p : (List C × List (C × C)) × C |
      O.link (nearest O p.1.1 start p.2)
          (O.steer (nearest O p.1.1 start p.2) p.2) = true} :=
    hlink (measurableSet_singleton true)
  have hmem : Measurable (fun p : (List C × List (C × C)) × C =>
      decide (O.steer (nearest O p.1.1 start p.2) p.2 ∈ p.1.1)) :=
    measurable_list_mem.comp (hX.prodMk measurable_fst.fst)
  have hS4' : MeasurableSet {p : (List C × List (C × C)) × C |
      decide (O.steer (nearest O p.1.1 start p.2) p.2 ∈ p.1.1) = true} :=
    hmem (measurableSet_singleton true)
  have hS4 : MeasurableSet {p : (List C × List (C × C)) × C |
      O.steer (nearest O p.1.1 start p.2) p.2 ∉ p.1.1} := by
    have heq : {p : (List C × List (C × C)) × C |
          O.steer (nearest O p.1.1 start p.2) p.2 ∉ p.1.1}
        = {p : (List C × List (C × C)) × C |
          decide (O.steer (nearest O p.1.1 start p.2) p.2 ∈ p.1.1) = true}ᶜ := by
      ext p
      simp [decide_eq_true_eq]
    rw [heq]
    exact hS4'.compl
  have hgate : MeasurableSet {p : (List C × List (C × C)) × C |
      O.free p.2 = true ∧
        O.free (O.steer (nearest O p.1.1 start p.2) p.2) = true ∧
        O.link (nearest O p.1.1 start p.2)
            (O.steer (nearest O p.1.1 start p.2) p.2) = true ∧
        O.steer (nearest O p.1.1 start p.2) p.2 ∉ p.1.1} :=
    hS1.inter (hS2.inter (hS3.inter hS4))
  have hthen1 : Measurable (fun p : (List C × List (C × C)) × C =>
      O.steer (nearest O p.1.1 start p.2) p.2 :: p.1.1) :=
    measurable_list_cons.comp (hX.prodMk measurable_fst.fst)
  have hpair : Measurable (fun p : (List C × List (C × C)) × C =>
      (nearest O p.1.1 start p.2,
        O.steer (nearest O p.1.1 start p.2) p.2)) :=
    hU.prodMk hX
  have hthen2 : Measurable (fun p : (List C × List (C × C)) × C =>
      (nearest O p.1.1 start p.2,
          O.steer (nearest O p.1.1 start p.2) p.2) :: p.1.2) :=
    measurable_list_cons.comp (hpair.prodMk measurable_fst.snd)
  have hthen : Measurable (fun p : (List C × List (C × C)) × C =>
      (O.steer (nearest O p.1.1 start p.2) p.2 :: p.1.1,
        (nearest O p.1.1 start p.2,
            O.steer (nearest O p.1.1 start p.2) p.2) :: p.1.2)) :=
    hthen1.prodMk hthen2
  have helse : Measurable (fun p : (List C × List (C × C)) × C => p.1) :=
    measurable_fst
  exact Measurable.ite hgate hthen helse

/-- The RRT output (vertices and edges) is a measurable function of the sample list. -/
theorem measurable_rrt {C : Type} [DecidableEq C] [MeasurableSpace C] [MeasurableEq C]
    {O : Oracles C} (hO : OraclesMeasurable O) (start : C) :
    Measurable (rrt O start) := by
  have hg : Measurable (fun t : Unit × (List C × List (C × C)) × C =>
      rrtStep O start (t.2.1, t.2.2)) :=
    (measurable_rrtStep hO start).comp
      (measurable_snd.fst.prodMk measurable_snd.snd)
  have hfold : Measurable (fun q : Unit × (List C × List (C × C)) × List C =>
      q.2.2.foldl (fun b a => rrtStep O start (b, a)) q.2.1) :=
    measurable_list_foldl hg
  have hinit : Measurable
      (fun ss : List C => ((), (([start], ([] : List (C × C))), ss))) :=
    measurable_const.prodMk (measurable_const.prodMk measurable_id)
  have hmain : Measurable (fun ss : List C =>
      ss.foldl (fun b a => rrtStep O start (b, a)) ([start], [])) :=
    hfold.comp hinit
  have heq : rrt O start = (fun ss : List C =>
      ss.foldl (fun b a => rrtStep O start (b, a)) ([start], [])) := by
    funext ss
    exact rrtAux_eq_foldl O start ss [start] []
  rw [heq]
  exact hmain

/-- Running `rrtAux` on pre-filtered samples matches raw samples, from any state. -/
private theorem rrtAux_filter_free {C : Type} [DecidableEq C] (O : Oracles C)
    (start : C) (samples : List C) (verts : List C) (edges : List (C × C)) :
    rrtAux O start (samples.filter O.free) verts edges =
      rrtAux O start samples verts edges := by
  induction samples generalizing verts edges with
  | nil => simp [rrtAux]
  | cons s ss ih =>
      by_cases h : O.free s = true
      · rw [List.filter_cons_of_pos h]
        simp only [rrtAux, ih]
      · rw [List.filter_cons_of_neg h, ih]
        simp [rrtAux, h]

/-- RRT skips samples that are not collision free. -/
theorem rrt_filter_free {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (samples : List C) : rrt O start (samples.filter O.free) = rrt O start samples := by
  exact rrtAux_filter_free O start samples [start] []

end Cslib.Planning.MotionPlanning.SamplingPlanners
