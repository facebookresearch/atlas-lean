/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.SamplingPlanners.Stream
public import CSLibExt.Planning.MotionPlanning.SamplingPlanners.MeasurableRoadmap
public import CSLibExt.Planning.MotionPlanning.SamplingPlanners.MeasurableTree
public import CSLibExt.Planning.MotionPlanning.SamplingPlanners.MeasurableStar
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

/-! # Probability lift for sampling-based planners

This file assembles the probability lift for the sampling-based planners:
a generic lift of any measurable list function to i.i.d. streams, its six
planner instances, raw-prefix rejection equalities, and vertex, edge and
cost-table events. Streams carry the product law, planners read the first
`N` raw samples and apply their own collision filter. The sampling model
follows that of Karaman and Frazzoli (2011, Section 3.1), with independent
uniform samples, while the lift here holds for an arbitrary probability law
and is specialized to the uniform box elsewhere in the library.
-/

open MeasureTheory

namespace Cslib.Planning.MotionPlanning.SamplingPlanners

/-- Pull an existence event back along a measurable list-valued map. -/
private theorem measurableSet_event_of_measurable {C α : Type*}
    [MeasurableSpace C] [MeasurableSpace α] {X : (ℕ → C) → List α}
    (hX : Measurable X) {S : Set α} (hS : MeasurableSet S) :
    MeasurableSet {ω | ∃ a ∈ X ω, a ∈ S} := by
  exact (measurableSet_list_exists_mem hS).preimage hX

/-- The probability lift of a native planner output `F` at raw sample size `N` under
the i.i.d. stream law `ν^ℕ`: the random output `ω ↦ F (rawPrefix N ω)` is measurable,
and its law is the pushforward of the `N`-fold product law `ν^N` through
`F ∘ List.ofFn`. -/
structure IsSampleLift {C β : Type*} [MeasurableSpace C] [MeasurableSpace β]
    (ν : Measure C) [IsProbabilityMeasure ν] (N : ℕ) (F : List C → β) : Prop where
  /-- The random output is measurable. -/
  measurable : Measurable fun ω : ℕ → C => F (rawPrefix N ω)
  /-- The random output has the pushforward law. -/
  map_eq : (streamLaw ν).map (fun ω => F (rawPrefix N ω)) =
    (Measure.pi fun _ : Fin N => ν).map (fun v : Fin N → C => F (List.ofFn v))

/-- Every measurable function of the sample list lifts. -/
theorem isSampleLift_of_measurable {C β : Type*} [MeasurableSpace C] [MeasurableSpace β]
    (ν : Measure C) [IsProbabilityMeasure ν] (N : ℕ) {F : List C → β} (hF : Measurable F) :
    IsSampleLift ν N F := by
  exact ⟨hF.comp (measurable_rawPrefix N), streamLaw_map_comp_rawPrefix ν hF N⟩

/-- Probability lift of the sPRM vertices. -/
theorem isSampleLift_sprmVertices {C : Type} [DecidableEq C] [MeasurableSpace C]
    [StandardBorelSpace C] {O : Oracles C} (hO : OraclesMeasurable O) (ν : Measure C)
    [IsProbabilityMeasure ν] (start : C) (N : ℕ) :
    IsSampleLift ν N (sprmVertices O start) := by
  exact isSampleLift_of_measurable ν N (measurable_sprmVertices hO start)

/-- Probability lift of the sPRM edges. -/
theorem isSampleLift_sprmEdges {C : Type} [DecidableEq C] [MeasurableSpace C]
    [StandardBorelSpace C] {O : Oracles C} (hO : OraclesMeasurable O) (ν : Measure C)
    [IsProbabilityMeasure ν] (start : C) (N : ℕ) :
    IsSampleLift ν N (sprmEdges O start) := by
  exact isSampleLift_of_measurable ν N (measurable_sprmEdges hO start)

/-- Probability lift of the PRM* vertices. -/
theorem isSampleLift_prmStarVertices {C : Type} [DecidableEq C] [MeasurableSpace C]
    [StandardBorelSpace C] {O : Oracles C} (hO : OraclesMeasurable O) (ν : Measure C)
    [IsProbabilityMeasure ν] (start : C) (N : ℕ) :
    IsSampleLift ν N (prmStarVertices O start) := by
  exact isSampleLift_of_measurable ν N (measurable_prmStarVertices hO start)

/-- Probability lift of the PRM* edges. -/
theorem isSampleLift_prmStarEdges {C : Type} [DecidableEq C] [MeasurableSpace C]
    [StandardBorelSpace C] {O : Oracles C} (hO : OraclesMeasurable O) (ν : Measure C)
    [IsProbabilityMeasure ν] (radiusOf : ℕ → ℚ) (start : C) (N : ℕ) :
    IsSampleLift ν N (prmStarEdges O radiusOf start) := by
  exact isSampleLift_of_measurable ν N (measurable_prmStarEdges hO radiusOf start)

/-- Probability lift of the RRT output. -/
theorem isSampleLift_rrt {C : Type} [DecidableEq C] [MeasurableSpace C]
    [StandardBorelSpace C] {O : Oracles C} (hO : OraclesMeasurable O) (ν : Measure C)
    [IsProbabilityMeasure ν] (start : C) (N : ℕ) :
    IsSampleLift ν N (rrt O start) := by
  exact isSampleLift_of_measurable ν N (measurable_rrt hO start)

/-- Probability lift of the RRT* output, including its cost table. -/
theorem isSampleLift_rrtStar {C : Type} [DecidableEq C] [MeasurableSpace C]
    [StandardBorelSpace C] {O : Oracles C} (hO : OraclesMeasurable O) (ν : Measure C)
    [IsProbabilityMeasure ν] (radiusOf : ℕ → ℚ) (start : C) (N : ℕ) :
    IsSampleLift ν N (rrtStar O radiusOf start) := by
  exact isSampleLift_of_measurable ν N (measurable_rrtStar hO radiusOf start)

/-- sPRM on the raw prefix equals sPRM on its collision-free entries. -/
theorem sprmVertices_rawPrefix {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (N : ℕ) (ω : ℕ → C) :
    sprmVertices O start (rawPrefix N ω) =
      sprmVertices O start ((rawPrefix N ω).filter O.free) := by
  exact (sprmVertices_filter_free O start _).symm

/-- sPRM edges on the raw prefix equal those on its collision-free entries. -/
theorem sprmEdges_rawPrefix {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (N : ℕ) (ω : ℕ → C) :
    sprmEdges O start (rawPrefix N ω) = sprmEdges O start ((rawPrefix N ω).filter O.free) := by
  exact (sprmEdges_filter_free O start _).symm

/-- PRM* vertices on the raw prefix equal those on its collision-free entries. -/
theorem prmStarVertices_rawPrefix {C : Type} [DecidableEq C] (O : Oracles C) (start : C)
    (N : ℕ) (ω : ℕ → C) :
    prmStarVertices O start (rawPrefix N ω) =
      prmStarVertices O start ((rawPrefix N ω).filter O.free) := by
  exact (prmStarVertices_filter_free O start _).symm

/-- PRM* edges on the raw prefix equal those on its collision-free entries. -/
theorem prmStarEdges_rawPrefix {C : Type} [DecidableEq C] (O : Oracles C)
    (radiusOf : ℕ → ℚ) (start : C) (N : ℕ) (ω : ℕ → C) :
    prmStarEdges O radiusOf start (rawPrefix N ω) =
      prmStarEdges O radiusOf start ((rawPrefix N ω).filter O.free) := by
  exact (prmStarEdges_filter_free O radiusOf start _).symm

/-- RRT on the raw prefix equals RRT on its collision-free entries. -/
theorem rrt_rawPrefix {C : Type} [DecidableEq C] (O : Oracles C) (start : C) (N : ℕ)
    (ω : ℕ → C) : rrt O start (rawPrefix N ω) = rrt O start ((rawPrefix N ω).filter O.free) := by
  exact (rrt_filter_free O start _).symm

/-- RRT* on the raw prefix equals RRT* on its collision-free entries. -/
theorem rrtStar_rawPrefix {C : Type} [DecidableEq C] (O : Oracles C) (radiusOf : ℕ → ℚ)
    (start : C) (N : ℕ) (ω : ℕ → C) :
    rrtStar O radiusOf start (rawPrefix N ω) =
      rrtStar O radiusOf start ((rawPrefix N ω).filter O.free) := by
  exact (rrtStar_filter_free O radiusOf start _).symm

/-- On the raw prefix, the PRM* radius schedule reads the free-sample count, not `N`. -/
theorem prmStarEdges_rawPrefix_eq_freeCount {C : Type} [DecidableEq C] (O : Oracles C)
    (radiusOf : ℕ → ℚ) (start : C) (N : ℕ) (ω : ℕ → C) :
    prmStarEdges O radiusOf start (rawPrefix N ω) =
      withReversals (allPairs { O with radius := radiusOf (freeCount O N ω) }
        (prmStarVertices O start (rawPrefix N ω))) := by
  rfl

/-- The event that some sPRM vertex lies in a measurable set is measurable. -/
theorem measurableSet_sprmVertices_event {C : Type} [DecidableEq C] [MeasurableSpace C]
    [StandardBorelSpace C] {O : Oracles C} (hO : OraclesMeasurable O) (start : C) (N : ℕ)
    {A : Set C} (hA : MeasurableSet A) :
    MeasurableSet {ω : ℕ → C | ∃ v ∈ sprmVertices O start (rawPrefix N ω), v ∈ A} := by
  have hX : Measurable fun ω : ℕ → C => sprmVertices O start (rawPrefix N ω) :=
    (measurable_sprmVertices hO start).comp (measurable_rawPrefix N)
  exact measurableSet_event_of_measurable hX hA

/-- The event that some sPRM edge lies in a measurable set is measurable. -/
theorem measurableSet_sprmEdges_event {C : Type} [DecidableEq C] [MeasurableSpace C]
    [StandardBorelSpace C] {O : Oracles C} (hO : OraclesMeasurable O) (start : C) (N : ℕ)
    {E : Set (C × C)} (hE : MeasurableSet E) :
    MeasurableSet {ω : ℕ → C | ∃ e ∈ sprmEdges O start (rawPrefix N ω), e ∈ E} := by
  have hX : Measurable fun ω : ℕ → C => sprmEdges O start (rawPrefix N ω) :=
    (measurable_sprmEdges hO start).comp (measurable_rawPrefix N)
  exact measurableSet_event_of_measurable hX hE

/-- The event that some PRM* vertex lies in a measurable set is measurable. -/
theorem measurableSet_prmStarVertices_event {C : Type} [DecidableEq C] [MeasurableSpace C]
    [StandardBorelSpace C] {O : Oracles C} (hO : OraclesMeasurable O) (start : C) (N : ℕ)
    {A : Set C} (hA : MeasurableSet A) :
    MeasurableSet {ω : ℕ → C | ∃ v ∈ prmStarVertices O start (rawPrefix N ω), v ∈ A} := by
  have hX : Measurable fun ω : ℕ → C => prmStarVertices O start (rawPrefix N ω) :=
    (measurable_prmStarVertices hO start).comp (measurable_rawPrefix N)
  exact measurableSet_event_of_measurable hX hA

/-- The event that some PRM* edge lies in a measurable set is measurable. -/
theorem measurableSet_prmStarEdges_event {C : Type} [DecidableEq C] [MeasurableSpace C]
    [StandardBorelSpace C] {O : Oracles C} (hO : OraclesMeasurable O) (radiusOf : ℕ → ℚ)
    (start : C) (N : ℕ) {E : Set (C × C)} (hE : MeasurableSet E) :
    MeasurableSet {ω : ℕ → C | ∃ e ∈ prmStarEdges O radiusOf start (rawPrefix N ω), e ∈ E} := by
  have hX : Measurable fun ω : ℕ → C => prmStarEdges O radiusOf start (rawPrefix N ω) :=
    (measurable_prmStarEdges hO radiusOf start).comp (measurable_rawPrefix N)
  exact measurableSet_event_of_measurable hX hE

/-- The event that some RRT vertex lies in a measurable set is measurable. -/
theorem measurableSet_rrt_vertex_event {C : Type} [DecidableEq C] [MeasurableSpace C]
    [StandardBorelSpace C] {O : Oracles C} (hO : OraclesMeasurable O) (start : C) (N : ℕ)
    {A : Set C} (hA : MeasurableSet A) :
    MeasurableSet {ω : ℕ → C | ∃ v ∈ (rrt O start (rawPrefix N ω)).1, v ∈ A} := by
  have hbase : Measurable fun ω : ℕ → C => rrt O start (rawPrefix N ω) :=
    (measurable_rrt hO start).comp (measurable_rawPrefix N)
  have hX : Measurable fun ω : ℕ → C => (rrt O start (rawPrefix N ω)).1 :=
    measurable_fst.comp hbase
  exact measurableSet_event_of_measurable hX hA

/-- The event that some RRT edge lies in a measurable set is measurable. -/
theorem measurableSet_rrt_edge_event {C : Type} [DecidableEq C] [MeasurableSpace C]
    [StandardBorelSpace C] {O : Oracles C} (hO : OraclesMeasurable O) (start : C) (N : ℕ)
    {E : Set (C × C)} (hE : MeasurableSet E) :
    MeasurableSet {ω : ℕ → C | ∃ e ∈ (rrt O start (rawPrefix N ω)).2, e ∈ E} := by
  have hbase : Measurable fun ω : ℕ → C => rrt O start (rawPrefix N ω) :=
    (measurable_rrt hO start).comp (measurable_rawPrefix N)
  have hX : Measurable fun ω : ℕ → C => (rrt O start (rawPrefix N ω)).2 :=
    measurable_snd.comp hbase
  exact measurableSet_event_of_measurable hX hE

/-- The event that some RRT* vertex lies in a measurable set is measurable. -/
theorem measurableSet_rrtStar_vertex_event {C : Type} [DecidableEq C] [MeasurableSpace C]
    [StandardBorelSpace C] {O : Oracles C} (hO : OraclesMeasurable O) (radiusOf : ℕ → ℚ)
    (start : C) (N : ℕ) {A : Set C} (hA : MeasurableSet A) :
    MeasurableSet {ω : ℕ → C | ∃ v ∈ (rrtStar O radiusOf start (rawPrefix N ω)).1, v ∈ A} := by
  have hbase : Measurable fun ω : ℕ → C => rrtStar O radiusOf start (rawPrefix N ω) :=
    (measurable_rrtStar hO radiusOf start).comp (measurable_rawPrefix N)
  have hX : Measurable fun ω : ℕ → C => (rrtStar O radiusOf start (rawPrefix N ω)).1 :=
    measurable_fst.comp hbase
  exact measurableSet_event_of_measurable hX hA

/-- The event that some RRT* edge lies in a measurable set is measurable. -/
theorem measurableSet_rrtStar_edge_event {C : Type} [DecidableEq C] [MeasurableSpace C]
    [StandardBorelSpace C] {O : Oracles C} (hO : OraclesMeasurable O) (radiusOf : ℕ → ℚ)
    (start : C) (N : ℕ) {E : Set (C × C)} (hE : MeasurableSet E) :
    MeasurableSet {ω : ℕ → C | ∃ e ∈ (rrtStar O radiusOf start (rawPrefix N ω)).2.1, e ∈ E} := by
  have hbase : Measurable fun ω : ℕ → C => rrtStar O radiusOf start (rawPrefix N ω) :=
    (measurable_rrtStar hO radiusOf start).comp (measurable_rawPrefix N)
  have hsnd : Measurable fun ω : ℕ → C => (rrtStar O radiusOf start (rawPrefix N ω)).2 :=
    measurable_snd.comp hbase
  have hX : Measurable fun ω : ℕ → C => (rrtStar O radiusOf start (rawPrefix N ω)).2.1 :=
    measurable_fst.comp hsnd
  exact measurableSet_event_of_measurable hX hE

/-- The event that some RRT* cost-table entry lies in a measurable set is measurable. -/
theorem measurableSet_rrtStar_cost_event {C : Type} [DecidableEq C] [MeasurableSpace C]
    [StandardBorelSpace C] {O : Oracles C} (hO : OraclesMeasurable O) (radiusOf : ℕ → ℚ)
    (start : C) (N : ℕ) {E : Set (C × (Int × Nat))} (hE : MeasurableSet E) :
    MeasurableSet
      {ω : ℕ → C | ∃ e ∈ (rrtStar O radiusOf start (rawPrefix N ω)).2.2, e ∈ E} := by
  have hbase : Measurable fun ω : ℕ → C => rrtStar O radiusOf start (rawPrefix N ω) :=
    (measurable_rrtStar hO radiusOf start).comp (measurable_rawPrefix N)
  have hsnd : Measurable fun ω : ℕ → C => (rrtStar O radiusOf start (rawPrefix N ω)).2 :=
    measurable_snd.comp hbase
  have hX : Measurable fun ω : ℕ → C => (rrtStar O radiusOf start (rawPrefix N ω)).2.2 :=
    measurable_snd.comp hsnd
  exact measurableSet_event_of_measurable hX hE

end Cslib.Planning.MotionPlanning.SamplingPlanners
