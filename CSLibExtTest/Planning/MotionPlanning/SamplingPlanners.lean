/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Planning.MotionPlanning.SamplingPlanners
public meta import CSLibExt.Planning.MotionPlanning.SamplingPlanners


namespace Cslib.Planning.MotionPlanning.SamplingPlanners

/-!
# Tests for deterministic sampling-based motion planners

Concrete checks over configurations `Rat × Rat` with a squared-distance cost
proxy: sPRM vertices and edges on four samples, RRT growth on three samples
(one a duplicate, exercising the skip), the tree property instance, the RRT
nearest tie-break, PRM* edges under a vertex-count radius schedule, RRT*
choose-parent and rewiring, and axiom probes on the main lemmas.
-/

/-- Squared Euclidean distance on `Rat × Rat`, as the RRT/sPRM cost proxy,
computed on numerators and cast back: kernel `decide` evaluation gets stuck on
`Rat` arithmetic, which normalizes fractions, while `Int`/`Nat` arithmetic
reduces. On integer-coordinate points this equals squared Euclidean distance. -/
def sqDist (p q : Rat × Rat) : Rat :=
  ((((p.1.num - q.1.num) ^ 2 + (p.2.num - q.2.num) ^ 2).toNat : Nat) : Rat)

/-- Oracles with no obstacles: everything is free and links. -/
def testOracles : Oracles (Rat × Rat) :=
  { free := fun _ => true
    link := fun _ _ => true
    cost := sqDist
    radius := 2 }

/-- Oracles with an obstacle: points with x-coordinate at least 5 are blocked. -/
def testOraclesObs : Oracles (Rat × Rat) :=
  { free := fun p => decide (p.1 < 5)
    link := fun _ _ => true
    cost := sqDist
    radius := 2 }

/-- Oracles with a large connection radius, for RRT* tests. -/
def testOraclesBig : Oracles (Rat × Rat) :=
  { free := fun _ => true
    link := fun _ _ => true
    cost := sqDist
    radius := 100 }

/-- Sanity check on the cost proxy: 3-4-5 triangle. -/
theorem testSqDist_val : sqDist (0, 0) (3, 4) = 25 := by decide

/-- sPRM vertices on four free samples. -/
theorem testSprmVertices_allFree :
    sprmVertices testOracles [(0, 0), (1, 0), (0, 1), (10, 10)] =
      [(0, 0), (1, 0), (0, 1), (10, 10)] := by decide

/-- sPRM edges on four samples: three pairs within radius 2. -/
theorem testSprmEdges_basic :
    sprmEdges testOracles [(0, 0), (1, 0), (0, 1), (10, 10)] =
      [((0, 0), (1, 0)), ((0, 0), (0, 1)), ((1, 0), (0, 1))] := by decide

/-- sPRM vertices drop the blocked sample. -/
theorem testSprmVertices_obstacle :
    sprmVertices testOraclesObs [(0, 0), (1, 0), (0, 1), (10, 10)] =
      [(0, 0), (1, 0), (0, 1)] := by decide

/-- sPRM vertices deduplicate samples. -/
theorem testSprmVertices_dedup :
    sprmVertices testOracles [(0, 0), (1, 0), (0, 0)] =
      [(1, 0), (0, 0)] := by decide

/-- RRT growth on three samples; the repeated sample is skipped. -/
theorem testRrt_basic :
    rrt testOracles (0, 0) [(1, 0), (2, 0), (1, 0)] =
      ([(2, 0), (1, 0), (0, 0)], [((1, 0), (2, 0)), ((0, 0), (1, 0))]) := by
  decide

/-- Tree property instance, via the general lemma. -/
theorem testRrt_tree :
    ((rrt testOracles (0, 0) [(1, 0), (2, 0), (1, 0)]).2.map Prod.snd).Nodup :=
  rrt_tree _ _ _

/-- Tree property instance, checked computationally. -/
theorem testRrt_tree_decide :
    ((rrt testOracles (0, 0) [(1, 0), (2, 0), (1, 0)]).2.map Prod.snd).Nodup := by
  decide

/-- Vertex-subset instance, via the general lemma. -/
theorem testRrt_subset :
    ∀ v ∈ (rrt testOracles (0, 0) [(1, 0), (2, 0), (1, 0)]).1,
      v ∈ (0, 0) :: [(1, 0), (2, 0), (1, 0)] :=
  fun v hv => rrt_verts_subset _ _ _ v hv

/-- Edge-count instance, via the general lemma. -/
theorem testRrt_length :
    (rrt testOracles (0, 0) [(1, 0), (2, 0), (1, 0)]).2.length ≤
      [(1, 0), (2, 0), (1, 0)].length :=
  rrt_edges_length _ _ _

/-- Symmetry instance: the swapped pair satisfies the edge predicate. -/
theorem testSprm_symmetric : IsSprmEdge testOracles (1, 0) (0, 0) := by
  have h : ((0, 0), (1, 0)) ∈
      sprmEdges testOracles [(0, 0), (1, 0), (0, 1), (10, 10)] := by decide
  exact sprmEdges_symmetric _ _ _ _ h

/-- RRT nearest tie-break: with tree vertices `[(2, 0), (0, 0)]` and sample
`(1, 0)`, both at squared distance 1, the first vertex in list order wins, so
the second edge is `((2, 0), (1, 0))`. -/
theorem testRrt_tiebreak :
    rrt testOracles (0, 0) [(2, 0), (1, 0)] =
      ([(1, 0), (2, 0), (0, 0)], [((2, 0), (1, 0)), ((0, 0), (2, 0))]) := by
  decide

/-- `nearest` returns the first minimizer in list order on ties. -/
theorem testNearest_firstMinimizer :
    nearest testOracles [(2, 0), (0, 0)] (0, 0) (1, 0) = (2, 0) := by decide

/-- Edge-existence instance, via the general lemma. -/
theorem testRrt_edge_of_mem :
    (1, 0) ∈ (rrt testOracles (0, 0) [(1, 0), (2, 0), (1, 0)]).2.map Prod.snd := by
  have h : (1, 0) ∈ (rrt testOracles (0, 0) [(1, 0), (2, 0), (1, 0)]).1 := by
    decide
  exact rrt_edge_of_mem _ _ _ _ h (by decide)

/-- PRM* with a vertex-count radius schedule connects all six pairs, unlike the
fixed radius 2 which gives three edges (`testSprmEdges_basic`). -/
theorem testPrmStar_edges :
    prmStarEdges testOracles (fun n => if n ≤ 3 then 2 else 200)
        [(0, 0), (1, 0), (0, 1), (10, 10)] =
      [((0, 0), (1, 0)), ((0, 0), (0, 1)), ((0, 0), (10, 10)),
       ((1, 0), (0, 1)), ((1, 0), (10, 10)), ((0, 1), (10, 10))] := by decide

/-- PRM* with a constant schedule agrees with sPRM, via the general lemma. -/
theorem testPrmStar_const :
    prmStarEdges testOracles (fun _ => 2) [(0, 0), (1, 0), (0, 1), (10, 10)] =
      sprmEdges testOracles [(0, 0), (1, 0), (0, 1), (10, 10)] :=
  prmStarEdges_const_radius _ _

/-- RRT* rewiring: `(10, 0)` first attaches to `(0, 0)` with cost `(100, 1)`;
after `(9, 0)` joins with cost `(81, 1)`, `(10, 0)` rewires through it with
cost `(82, 1)`. -/
theorem testRrtStar_rewire :
    rrtStar testOraclesBig (0, 0) [(10, 0), (9, 0)] =
      ([(9, 0), (10, 0), (0, 0)],
       [((0, 0), (9, 0)), ((9, 0), (10, 0))],
       [((10, 0), (82, 1)), ((9, 0), (81, 1)), ((10, 0), (100, 1)),
        ((0, 0), (0, 1))]) := by decide

/-- RRT* choose-parent: for sample `(9, 0)` the nearer vertex `(10, 0)` has
cost-to-come `(100, 1)` (total `(101, 1)`) while `(0, 0)` has cost-to-come
`(0, 1)` (total `(81, 1)`), so the non-nearest `(0, 0)` is chosen. -/
theorem testChooseParent_nonNearest :
    chooseParent testOraclesBig [((10, 0), (100, 1)), ((0, 0), (0, 1))]
        [(10, 0), (0, 0)] (9, 0) =
      some (0, 0) := by decide

/-- RRT* tree property instance, via the general lemma. -/
theorem testRrtStar_tree :
    (((rrtStar testOraclesBig (0, 0) [(10, 0), (9, 0)]).2.1.map Prod.snd).Nodup) :=
  rrtStar_tree _ _ _

/-- RRT* start-cost instance, via the general lemma. -/
theorem testRrtStar_cost :
    costToCome (rrtStar testOraclesBig (0, 0) [(10, 0), (9, 0)]).2.2 (0, 0)
      = (0, 1) :=
  rrtStar_cost_start _ _ _

/-- RRT* vertex-subset instance, via the general lemma. -/
theorem testRrtStar_subset :
    ∀ v ∈ (rrtStar testOraclesBig (0, 0) [(10, 0), (9, 0)]).1,
      v ∈ (0, 0) :: [(10, 0), (9, 0)] :=
  fun v hv => rrtStar_verts_subset _ _ _ v hv

#print axioms sprmVertices_all_free
#print axioms sprmEdges_symmetric
#print axioms rrt_verts_subset
#print axioms rrt_edges_length
#print axioms rrt_tree
#print axioms rrt_edge_of_mem
#print axioms prmStarEdges_mem
#print axioms prmStarEdges_const_radius
#print axioms rrtStar_tree
#print axioms rrtStar_cost_start
#print axioms testRrt_basic
#print axioms testSprm_symmetric
#print axioms testRrt_tiebreak
#print axioms testPrmStar_edges
#print axioms testRrtStar_rewire
#print axioms testChooseParent_nonNearest

end Cslib.Planning.MotionPlanning.SamplingPlanners
