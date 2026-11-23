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

Concrete checks over configurations `Int × Int` with a squared-distance cost
proxy: sPRM vertices and edges on four samples, RRT growth on three samples
(one a duplicate, exercising the skip), the tree property instance, the RRT
nearest tie-break, PRM* edges under a vertex-count radius schedule, RRT*
choose-parent and rewiring with recomputed tree costs, descendant cost
freshness, the nearest-vertex candidate fallback, ancestor rejection on
rewire, `rewireAux` forbid-guard isolation with a synthetic cost table, an
RRT* size-dependent radius schedule, and axiom probes on the main lemmas.
-/

/-- Squared Euclidean distance on `Int × Int`, as the RRT/sPRM cost proxy,
cast to `Rat`: kernel `decide` evaluation reduces `Int` arithmetic directly,
while on integer-coordinate points this equals squared Euclidean distance. -/
def sqDist (p q : Int × Int) : Rat :=
  ((((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2).toNat : Nat) : Rat)

/-- The cost proxy is nonnegative. -/
theorem sqDist_nonneg (p q : Int × Int) : 0 ≤ sqDist p q := by
  unfold sqDist
  exact Nat.cast_nonneg _

/-- The cost proxy vanishes on identical configurations. -/
theorem sqDist_self (p : Int × Int) : sqDist p p = 0 := by
  simp [sqDist]

/-- The cost proxy is positive on distinct configurations. -/
theorem sqDist_pos (p q : Int × Int) (h : p ≠ q) : 0 < sqDist p q := by
  have hne : p.1 ≠ q.1 ∨ p.2 ≠ q.2 := by
    by_contra hc
    push Not at hc
    exact h (Prod.ext hc.1 hc.2)
  have hpos : 0 < (p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2 := by
    rcases hne with h1 | h2
    · have hsq1 : 0 < (p.1 - q.1) ^ 2 :=
        sq_pos_of_ne_zero (sub_ne_zero.mpr h1)
      have hsq2 : 0 ≤ (p.2 - q.2) ^ 2 := sq_nonneg _
      linarith
    · have hsq1 : 0 ≤ (p.1 - q.1) ^ 2 := sq_nonneg _
      have hsq2 : 0 < (p.2 - q.2) ^ 2 :=
        sq_pos_of_ne_zero (sub_ne_zero.mpr h2)
      linarith
  have hnat : 0 < (((p.1 - q.1) ^ 2 + (p.2 - q.2) ^ 2).toNat) :=
    Int.pos_iff_toNat_pos.mp hpos
  unfold sqDist
  exact Nat.cast_pos.mpr hnat

/-- Oracles with no obstacles: everything is free and links. -/
def testOracles : Oracles (Int × Int) :=
  { free := fun _ => true
    link := fun _ _ => true
    cost := sqDist
    radius := 2
    cost_nonneg := sqDist_nonneg
    cost_self := sqDist_self
    cost_pos := sqDist_pos }

/-- Oracles with an obstacle: points with x-coordinate at least 5 are blocked. -/
def testOraclesObs : Oracles (Int × Int) :=
  { free := fun p => decide (p.1 < 5)
    link := fun _ _ => true
    cost := sqDist
    radius := 2
    cost_nonneg := sqDist_nonneg
    cost_self := sqDist_self
    cost_pos := sqDist_pos }

/-- Oracles with a large connection radius, for RRT* tests. -/
def testOraclesBig : Oracles (Int × Int) :=
  { free := fun _ => true
    link := fun _ _ => true
    cost := sqDist
    radius := 100
    cost_nonneg := sqDist_nonneg
    cost_self := sqDist_self
    cost_pos := sqDist_pos }

/-- Oracles where only the start links to the far sample, for the
nearest-vertex fallback test. -/
def testOraclesFallback : Oracles (Int × Int) :=
  { free := fun _ => true
    link := fun a b => a == (0, 0) && b == (5, 0)
    cost := sqDist
    radius := 100
    cost_nonneg := sqDist_nonneg
    cost_self := sqDist_self
    cost_pos := sqDist_pos }

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
      ([(2, 0), (1, 0), (0, 0)], [((1, 0), (2, 0)), ((0, 0), (1, 0))]) := by decide

/-- Tree property instance, via the general lemma. -/
theorem testRrt_tree :
    ((rrt testOracles (0, 0) [(1, 0), (2, 0), (1, 0)]).2.map Prod.snd).Nodup :=
  rrt_tree _ _ _

/-- Tree property instance, checked computationally. -/
theorem testRrt_tree_decide :
    ((rrt testOracles (0, 0) [(1, 0), (2, 0), (1, 0)]).2.map Prod.snd).Nodup := by decide

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
      ([(1, 0), (2, 0), (0, 0)], [((2, 0), (1, 0)), ((0, 0), (2, 0))]) := by decide

/-- `nearest` returns the first minimizer in list order on ties. -/
theorem testNearest_firstMinimizer :
    nearest testOracles [(2, 0), (0, 0)] (0, 0) (1, 0) = (2, 0) := by decide

/-- Edge-existence instance, via the general lemma. -/
theorem testRrt_edge_of_mem :
    (1, 0) ∈ (rrt testOracles (0, 0) [(1, 0), (2, 0), (1, 0)]).2.map Prod.snd := by
  have h : (1, 0) ∈ (rrt testOracles (0, 0) [(1, 0), (2, 0), (1, 0)]).1 := by decide
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

/-- Cost table fixture: two entries. -/
def testCosts : List ((Int × Int) × (Int × Nat)) :=
  [((1, 0), (5, 1)), ((0, 0), (0, 1))]

/-- `costToCome` returns the first matching entry. -/
theorem testCostToCome_hit : costToCome testCosts (1, 0) = (5, 1) := by decide

/-- `costToCome` defaults to `(0, 1)` on a miss. -/
theorem testCostToCome_miss : costToCome testCosts (9, 9) = (0, 1) := by decide

/-- RRT* rewiring: vertices, newest first. -/
theorem testRrtStar_rewire_verts :
    (rrtStar testOraclesBig (fun _ => testOraclesBig.radius) (0, 0)
      [(10, 0), (9, 0)]).1 =
      [(9, 0), (10, 0), (0, 0)] := by decide

/-- RRT* rewiring: `(10, 0)` drops its direct edge to the start and attaches
through `(9, 0)`. -/
theorem testRrtStar_rewire_edges :
    ((9, 0), (10, 0)) ∈ (rrtStar testOraclesBig (fun _ => testOraclesBig.radius)
      (0, 0) [(10, 0), (9, 0)]).2.1 ∧
    ((0, 0), (10, 0)) ∉ (rrtStar testOraclesBig (fun _ => testOraclesBig.radius)
      (0, 0) [(10, 0), (9, 0)]).2.1 := by decide

/-- RRT* rewiring: recomputed tree costs with no stale entries: `(10, 0)`
first attaches to `(0, 0)` with cost `(100, 1)`; after `(9, 0)` joins with
cost `(81, 1)`, `(10, 0)` rewires through it with cost `(82, 1)`. -/
theorem testRrtStar_rewire_costs :
    costToCome (rrtStar testOraclesBig (fun _ => testOraclesBig.radius)
      (0, 0) [(10, 0), (9, 0)]).2.2 (10, 0) = (82, 1) ∧
    costToCome (rrtStar testOraclesBig (fun _ => testOraclesBig.radius)
      (0, 0) [(10, 0), (9, 0)]).2.2 (9, 0) = (81, 1) := by decide

/-- RRT* choose-parent: for sample `(9, 0)` the nearer vertex `(10, 0)` has
cost-to-come `(100, 1)` (total `(101, 1)`) while `(0, 0)` has cost-to-come
`(0, 1)` (total `(81, 1)`), so the non-nearest `(0, 0)` is chosen. -/
theorem testChooseParent_nonNearest :
    chooseParent testOraclesBig [(10, 0), (0, 0)]
        [((10, 0), (100, 1)), ((0, 0), (0, 1))]
        (fun _ => testOraclesBig.radius) (0, 0) (9, 0) =
      some (0, 0) := by decide

/-- RRT* tree property instance, via the general lemma. -/
theorem testRrtStar_tree :
    (((rrtStar testOraclesBig (fun _ => testOraclesBig.radius) (0, 0)
      [(10, 0), (9, 0)]).2.1.map Prod.snd).Nodup) :=
  rrtStar_tree _ _ _ _

/-- RRT* start-cost instance, via the general lemma. -/
theorem testRrtStar_cost :
    costToCome (rrtStar testOraclesBig (fun _ => testOraclesBig.radius)
      (0, 0) [(10, 0), (9, 0)]).2.2 (0, 0) = (0, 1) :=
  rrtStar_cost_start _ _ _ _

/-- RRT* vertex-subset instance, via the general lemma. -/
theorem testRrtStar_subset :
    ∀ v ∈ (rrtStar testOraclesBig (fun _ => testOraclesBig.radius)
        (0, 0) [(10, 0), (9, 0)]).1,
      v = (0, 0) ∨ v ∈ [(10, 0), (9, 0)] :=
  fun v hv => rrtStar_verts_subset _ _ _ _ v hv

/-- Descendant cost freshness: vertices, newest first. -/
theorem testRrtStar_freshness_verts :
    (rrtStar testOraclesBig (fun _ => testOraclesBig.radius) (0, 0)
      [(2, 0), (4, 0), (1, 0)]).1 =
      [(1, 0), (4, 0), (2, 0), (0, 0)] := by decide

/-- Descendant cost freshness: in the chain `(0, 0) → (2, 0) → (4, 0)`, the
later sample `(1, 0)` rewires `(2, 0)` to cost `(2, 1)`, and the descendant
`(4, 0)` drops from `(8, 1)` to `(6, 1)` accordingly. -/
theorem testRrtStar_freshness_costs :
    costToCome (rrtStar testOraclesBig (fun _ => testOraclesBig.radius)
      (0, 0) [(2, 0), (4, 0), (1, 0)]).2.2 (2, 0) = (2, 1) ∧
    costToCome (rrtStar testOraclesBig (fun _ => testOraclesBig.radius)
      (0, 0) [(2, 0), (4, 0), (1, 0)]).2.2 (4, 0) = (6, 1) := by decide

/-- Nearest-vertex fallback: with radius schedule `0`, the sample `(5, 0)` is
within radius of nothing, but it is still added through its nearest vertex. -/
theorem testRrtStar_nearestFallback :
    (5, 0) ∈ (rrtStar testOraclesFallback (fun _ => 0) (0, 0)
      [(5, 0)]).1 := by decide

/-- Ancestor rejection setup: the samples build the chain
`(0, 0) → (1, 0) → (2, 0) → (3, 0)`. -/
theorem testRrtStar_ancestorSetup :
    ((0, 0), (1, 0)) ∈ (rrtStar testOraclesBig
      (fun _ => testOraclesBig.radius) (0, 0)
      [(1, 0), (2, 0), (3, 0)]).2.1 ∧
    ((1, 0), (2, 0)) ∈ (rrtStar testOraclesBig
      (fun _ => testOraclesBig.radius) (0, 0)
      [(1, 0), (2, 0), (3, 0)]).2.1 ∧
    ((2, 0), (3, 0)) ∈ (rrtStar testOraclesBig
      (fun _ => testOraclesBig.radius) (0, 0)
      [(1, 0), (2, 0), (3, 0)]).2.1 := by decide

/-- Ancestor rejection: `(1, 0)` does not rewire through its descendant
`(3, 0)`, so the edge `((3, 0), (1, 0))` is absent. -/
theorem testRrtStar_ancestorReject :
    ((3, 0), (1, 0)) ∉ (rrtStar testOraclesBig
      (fun _ => testOraclesBig.radius) (0, 0)
      [(1, 0), (2, 0), (3, 0)]).2.1 := by decide

/-- Why the forbid guard is tested at the `rewireAux` level rather than
end-to-end: with exact `recomputeCosts` tables and positive edge costs, an
ancestor flip can never strictly improve — the cost value strictly increases
along tight parent edges (the acyclicity argument behind `rrtStar_acyclic`) —
so the strict-improvement conjunct already fails for every ancestor and no
end-to-end `rrtStar` example can isolate the `w ∉ forbid` guard. Since
`rewireAux` takes the cost table as a parameter, the synthetic table below
makes flipping `(10, 0)` through `(9, 0)` strictly improving, isolating the
guard: the only difference between the two tests is the forbid list. -/
def testForbidCosts : List ((Int × Int) × (Int × Nat)) :=
  [((9, 0), (0, 1)), ((10, 0), (100, 1)), ((0, 0), (0, 1))]

/-- The synthetic table makes routing `(10, 0)` through `(9, 0)` strictly
improving: `(0, 1)` plus edge cost `1` is `(1, 1)`, below `(100, 1)`. -/
theorem testRewireAux_improvementHolds :
    ccLt (ccAdd (costToCome testForbidCosts (9, 0))
        (testOraclesBig.cost (9, 0) (10, 0)))
      (costToCome testForbidCosts (10, 0)) := by decide

/-- Forbid isolation: with `(10, 0)` forbidden, `rewireAux` leaves the edges
unchanged even though the flip would strictly improve. -/
theorem testRewireAux_forbidBlocks :
    rewireAux testOraclesBig testForbidCosts (fun _ => testOraclesBig.radius)
      3 [(10, 0)] (0, 0) (9, 0) (0, 0) [(10, 0)]
      [((0, 0), (10, 0)), ((0, 0), (9, 0))] =
      [((0, 0), (10, 0)), ((0, 0), (9, 0))] := by decide

/-- Forbid isolation: with an empty forbid list, `rewireAux` rewrites the
parent edge of `(10, 0)` to `((9, 0), (10, 0))`. -/
theorem testRewireAux_forbidAbsentFlips :
    rewireAux testOraclesBig testForbidCosts (fun _ => testOraclesBig.radius)
      3 [] (0, 0) (9, 0) (0, 0) [(10, 0)]
      [((0, 0), (10, 0)), ((0, 0), (9, 0))] =
      [((9, 0), (10, 0)), ((0, 0), (9, 0))] := by decide

/-- Convention: `extendStar` evaluates `radiusOf` at `(s :: verts).length`
(the post-insertion vertex count) for the rewire pass, while `candidates`
uses the pre-insertion `verts.length` (reached via `chooseParent` before `s`
is added). The schedule below is wide (`1000`) at counts `≤ 2` and `0`
afterwards, so the first two insertions choose parents from the full near
set while the third insertion falls back to its nearest vertex. -/
def testRadiusOf (n : Nat) : Rat := if n ≤ 2 then 1000 else 0

/-- RRT* under the nonconstant schedule: vertices, newest first. -/
theorem testRrtStar_schedule_verts :
    (rrtStar testOraclesBig testRadiusOf (0, 0)
      [(10, 0), (9, 0), (8, 0)]).1 =
      [(8, 0), (9, 0), (10, 0), (0, 0)] := by decide

/-- RRT* under the nonconstant schedule: exact edges. `(10, 0)` attaches to
`(0, 0)`; `(9, 0)` takes the cheaper non-nearest parent `(0, 0)` (radius
`1000` at count `2`, but the rewire pass at count `3` already sees radius
`0`, so no flip); `(8, 0)` falls back to its nearest vertex `(9, 0)`. -/
theorem testRrtStar_schedule_edges :
    (rrtStar testOraclesBig testRadiusOf (0, 0)
      [(10, 0), (9, 0), (8, 0)]).2.1 =
      [((9, 0), (8, 0)), ((0, 0), (9, 0)), ((0, 0), (10, 0))] := by decide

/-- The constant-`0` schedule on the same samples: `(9, 0)` takes its nearest
vertex `(10, 0)` as parent instead of `(0, 0)`. -/
theorem testRrtStar_schedule_constLo_edges :
    (rrtStar testOraclesBig (fun _ => 0) (0, 0)
      [(10, 0), (9, 0), (8, 0)]).2.1 =
      [((9, 0), (8, 0)), ((10, 0), (9, 0)), ((0, 0), (10, 0))] := by decide

/-- The constant-`1000` schedule on the same samples: wide-radius rewiring
forms the chain `(0, 0) → (8, 0) → (9, 0) → (10, 0)`. After `(9, 0)` rewires
under `(8, 0)` at cost `65`, routing `(10, 0)` through `(8, 0)` would cost
`68`, worse than `66` through `(9, 0)`, so `(10, 0)` keeps parent `(9, 0)`.
This discriminates the per-flip cost recompute: with a pass-start snapshot
guard, both `(9, 0)` and `(10, 0)` attach through `(8, 0)`. -/
theorem testRrtStar_schedule_constHi_edges :
    (rrtStar testOraclesBig (fun _ => 1000) (0, 0)
      [(10, 0), (9, 0), (8, 0)]).2.1 =
      [((0, 0), (8, 0)), ((8, 0), (9, 0)), ((9, 0), (10, 0))] := by decide

/-- The nonconstant schedule outcome differs from both constant schedules. -/
theorem testRrtStar_schedule_differs :
    (rrtStar testOraclesBig testRadiusOf (0, 0)
      [(10, 0), (9, 0), (8, 0)]).2.1 ≠
      (rrtStar testOraclesBig (fun _ => 0) (0, 0)
        [(10, 0), (9, 0), (8, 0)]).2.1 ∧
    (rrtStar testOraclesBig testRadiusOf (0, 0)
      [(10, 0), (9, 0), (8, 0)]).2.1 ≠
      (rrtStar testOraclesBig (fun _ => 1000) (0, 0)
        [(10, 0), (9, 0), (8, 0)]).2.1 := by decide

/-- Guard table regression: the rewire pass must price the new vertex from the
post-insertion table, not the pre-insertion one (where it has no entry and
reads as the `(0, 1)` lookup default). Here `(4, 9)` joins at cost 97 and
`(0, 10)` joins under the start at 100; routing `(4, 9)` through `(0, 10)`
would cost 117, so the tree is kept. A guard pricing `(0, 10)` at `(0, 1)`
sees 17 < 97 and would flip it, raising its cost to 117. -/
theorem testRrtStar_guardPostInsertion :
    (rrtStar testOraclesBig (fun _ => testOraclesBig.radius) (0, 0)
      [(4, 9), (0, 10)]).2.1 =
      [((0, 0), (0, 10)), ((0, 0), (4, 9))] := by decide


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
#print axioms rrtStar_verts_subset
#print axioms rrtStar_acyclic
#print axioms costToCome_cons_ne
#print axioms sqDist_pos
#print axioms testRrt_basic
#print axioms testSprm_symmetric
#print axioms testRrt_tiebreak
#print axioms testPrmStar_edges
#print axioms testRrtStar_rewire_costs
#print axioms testRrtStar_freshness_costs
#print axioms testRrtStar_nearestFallback
#print axioms testRrtStar_ancestorReject
#print axioms testChooseParent_nonNearest
#print axioms testRewireAux_improvementHolds
#print axioms testRewireAux_forbidBlocks
#print axioms testRewireAux_forbidAbsentFlips
#print axioms testRrtStar_schedule_verts
#print axioms testRrtStar_schedule_edges
#print axioms testRrtStar_schedule_constLo_edges
#print axioms testRrtStar_schedule_constHi_edges
#print axioms testRrtStar_schedule_differs
#print axioms testRrtStar_guardPostInsertion

end Cslib.Planning.MotionPlanning.SamplingPlanners
