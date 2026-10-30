/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.CriticalReduction
public import PhyslibExt.StatisticalMechanics.RandomCluster.TriHex.FKDuality

/-!
# Critical points of the triangular and hexagonal random-cluster models from phase inputs

Two-point connection probabilities of the wired infinite-volume FK measure on a periodic planar
graph, and the reduction of the triangular/hexagonal critical-point identification to explicit
phase inputs.

## i. Overview

`PeriodicGraph.twoPointEvent x y` is the event that `x` and `y` are joined by open edges; it is
measurable (`measurableSet_twoPointEvent`) and `wiredTwoPointProbability` is its probability under
the buffered wired infinite-volume measure (`0` outside `p ∈ (0, 1)`, `q > 0`).
`SubcriticalTwoPointExponentialDecay` says the two-point function decays exponentially in graph
distance for every `p < p_c`. `CriticalSurfacePhaseBoundary surface pc` says that a function of
`p` changes sign exactly at `pc`; for the triangular and hexagonal critical polynomials
(`TriangularCriticalPhaseBoundary`, `HexagonalCriticalPhaseBoundary`) this forces `pc` to be the
root of the cubic, i.e. it assumes that `pc` is the self-dual value. Combining these with the
duality relation `p_c(hex) = dualParam p_c(tri) q` from `PeriodicPlanar.CriticalReduction` gives
the critical polynomials at both thresholds.

Fidelity of the headlines. None of the results computes a critical point from the FK measure:
- `triHexCriticalPolynomials_of_dualThreshold_of_triangularPhase` (and the hexagonal variant) are
  conditional on `TriangularCriticalPhaseBoundary q pcTri` (resp. hexagonal), which is equivalent
  to `triangularFKCriticalPolynomial q (fkEdgeOdds pcTri) = 0` for `q > 0` (the cubic is strictly
  increasing in `p`): the triangular critical value is assumed, and the hexagonal one follows by
  the algebraic duality of `CriticalAlgebra`.
- `triangular_hexagonal_critical_of_phase_inputs` (`q ≥ 1`) is conditional on: both critical
  points in `(0, 1)`, `OffCriticalSharpness` for both lattices, `DualSubcriticalCoverage`,
  `DualNoCoexistence`, `TriangularCriticalPhaseBoundary` (assumes the triangular critical value),
  `SubcriticalTwoPointExponentialDecay` on the triangular lattice, and
  `TriHexSubcriticalDecayTransfer`. Its two decay conclusions are the decay hypothesis itself and
  the transfer hypothesis applied to it (circular); the only derived content is the duality
  relation of the critical points and the hexagonal cubic at `p_c(hex)`.
- `triHexCriticalPolynomials_one_of_starTriangle_of_dualThreshold` (`q = 1`) assumes the
  bond-percolation star–triangle equation at `pcTri`, which is equivalent to its first conclusion.
- `measurableSet_twoPointEvent`, the bounds on `wiredTwoPointProbability` and
  `CriticalSurfacePhaseBoundary.eq_zero` are unconditional.

## ii. Key results

- `PeriodicGraph.measurableSet_twoPointEvent` : connection events are measurable. Unconditional.
- `triHexCriticalPolynomials_of_dualThreshold_of_triangularPhase` : critical cubics at both
  thresholds. Conditional (assumes the triangular critical value, see above).
- `triangular_hexagonal_critical_of_phase_inputs` : the critical-point assembly. Conditional on
  sharpness, coverage, no coexistence, the triangular critical value, triangular decay and decay
  transfer; decay conclusions circular.

## iii. Table of contents

- A. Connection events and the wired two-point function
- B. Phase boundaries of the critical polynomials
- C. Critical points from duality
- D. Bond percolation at `q = 1`

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), §6.6.
- V. Beffara and H. Duminil-Copin, *The self-dual point of the two-dimensional random-cluster
  model is critical for q ≥ 1*, Probab. Theory Related Fields 153 (2012) 511–542.
-/

@[expose] public section

open MeasureTheory Set SimpleGraph

namespace StatMech
namespace FK
namespace PeriodicPlanar

open BeffaraDC FrontierA

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-! ## A. Connection events and the wired two-point function -/

/-- The connection event `{x ↔ y}`: `x` and `y` are joined by a path of open edges of the periodic
graph. -/
def PeriodicGraph.twoPointEvent (P : PeriodicGraph V) (x y : V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | (P.openSubgraph omega).Reachable x y}

private lemma PeriodicGraph.measurableSet_openSubgraphAdj
    (P : PeriodicGraph V) (x y : V) :
    MeasurableSet
      {omega : ConfigSpace (Sym2 V) | (P.openSubgraph omega).Adj x y} := by
  by_cases hxy : P.graph.Adj x y
  · have heq :
        {omega : ConfigSpace (Sym2 V) | (P.openSubgraph omega).Adj x y} =
          {omega | omega s(x, y) = true} := by
      ext omega
      rw [Set.mem_ofPred_eq, P.openSubgraph_adj]
      exact ⟨fun h => h.2, fun h => ⟨hxy, h⟩⟩
    rw [heq]
    exact measurableSet_eq_fun
      (measurable_pi_apply s(x, y)) measurable_const
  · have heq :
        {omega : ConfigSpace (Sym2 V) | (P.openSubgraph omega).Adj x y} = ∅ := by
      ext omega
      rw [Set.mem_ofPred_eq, P.openSubgraph_adj]
      simp only [Set.mem_empty_iff_false, iff_false]
      exact fun h => hxy h.1
    rw [heq]
    exact MeasurableSet.empty

/-- The event that a vertex list is an open path is measurable. -/
lemma PeriodicGraph.measurableSet_openChain
    (P : PeriodicGraph V) (l : List V) :
    MeasurableSet
      {omega : ConfigSpace (Sym2 V) |
        List.IsChain (P.openSubgraph omega).Adj l} := by
  induction l with
  | nil => simp only [List.isChain_nil, Set.ofPred_true, MeasurableSet.univ]
  | cons a l ih =>
      cases l with
      | nil => simp only [List.isChain_singleton, Set.ofPred_true, MeasurableSet.univ]
      | cons b l =>
          have heq :
              {omega : ConfigSpace (Sym2 V) |
                  List.IsChain (P.openSubgraph omega).Adj (a :: b :: l)} =
                {omega | (P.openSubgraph omega).Adj a b} ∩
                  {omega | List.IsChain (P.openSubgraph omega).Adj (b :: l)} := by
            ext omega
            simp only [Set.mem_ofPred_eq, Set.mem_inter_iff,
              List.isChain_cons_cons]
          rw [heq]
          exact (P.measurableSet_openSubgraphAdj a b).inter ih

/-- Open connectivity is the existence of an open path given as a vertex list. -/
lemma PeriodicGraph.reachable_iff_openChain
    (P : PeriodicGraph V) (omega : ConfigSpace (Sym2 V)) (x y : V) :
    (P.openSubgraph omega).Reachable x y ↔
      ∃ l : List V, List.IsChain (P.openSubgraph omega).Adj (x :: l) ∧
        (x :: l).getLast (List.cons_ne_nil _ _) = y := by
  rw [SimpleGraph.reachable_iff_reflTransGen]
  constructor
  · intro h
    obtain ⟨l, hchain, hlast⟩ :=
      List.exists_isChain_cons_of_relationReflTransGen h
    exact ⟨l, hchain, hlast⟩
  · rintro ⟨l, hchain, hlast⟩
    exact List.relationReflTransGen_of_exists_isChain_cons l hchain hlast

lemma PeriodicGraph.measurableSet_twoPointEvent
    [Countable V] (P : PeriodicGraph V) (x y : V) :
    MeasurableSet (P.twoPointEvent x y) := by
  classical
  have heq : P.twoPointEvent x y =
      ⋃ l : List V,
        ({omega | List.IsChain (P.openSubgraph omega).Adj (x :: l)} ∩
          if (x :: l).getLast (List.cons_ne_nil _ _) = y then Set.univ else ∅) := by
    ext omega
    rw [PeriodicGraph.twoPointEvent, Set.mem_ofPred_eq,
      P.reachable_iff_openChain]
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨l, hchain, hlast⟩
      exact ⟨l, hchain, by rw [ite_eq_left hlast]; trivial⟩
    · rintro ⟨l, hchain, hlast⟩
      refine ⟨l, hchain, ?_⟩
      by_cases h : (x :: l).getLast (List.cons_ne_nil _ _) = y
      · exact h
      · rw [ite_eq_right h] at hlast
        exact (Set.notMem_empty _ hlast).elim
  rw [heq]
  apply MeasurableSet.iUnion
  intro l
  apply MeasurableSet.inter (P.measurableSet_openChain (x :: l))
  split <;> simp

/-- The wired two-point function `φ¹_{p,q}(x ↔ y)` under the buffered wired infinite-volume FK
measure, set to `0` outside `p ∈ (0, 1)`, `q > 0`. -/
noncomputable def PeriodicGraph.wiredTwoPointProbability
    [Countable V] (P : PeriodicGraph V) (p q : ℝ) (x y : V) : ℝ :=
  if h : p ∈ Ioo (0 : ℝ) 1 ∧ 0 < q then
    ((P.wiredBufferedInfiniteVolume h.1.1 h.1.2 h.2 :
        ProbabilityMeasure (ConfigSpace (Sym2 V))) :
      Measure (ConfigSpace (Sym2 V))).real (P.twoPointEvent x y)
  else 0

lemma PeriodicGraph.wiredTwoPointProbability_nonneg
    [Countable V] (P : PeriodicGraph V) (p q : ℝ) (x y : V) :
    0 ≤ P.wiredTwoPointProbability p q x y := by
  unfold PeriodicGraph.wiredTwoPointProbability
  split
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

lemma PeriodicGraph.wiredTwoPointProbability_le_one
    [Countable V] (P : PeriodicGraph V) (p q : ℝ) (x y : V) :
    P.wiredTwoPointProbability p q x y ≤ 1 := by
  unfold PeriodicGraph.wiredTwoPointProbability
  split
  · rw [Measure.real]
    refine ENNReal.toReal_le_of_le_ofReal (by norm_num) ?_
    rw [ENNReal.ofReal_one]
    exact prob_le_one
  · norm_num

/-! ## B. Phase boundaries of the critical polynomials -/

/-- Exponential decay of the wired two-point function in graph distance for every `p ∈ (0, p_c)`. -/
def SubcriticalTwoPointExponentialDecay
    [Countable V] (P : PeriodicGraph V) (q pc : ℝ) : Prop :=
  ∀ p ∈ Ioo (0 : ℝ) pc, ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ x y : V,
      P.wiredTwoPointProbability p q x y ≤
        C * Real.exp (-c * (P.graph.dist x y : ℝ))

/-- A function of `p ∈ (0, 1)` is negative exactly below `pc` and positive exactly above it, so `pc`
is its unique sign change. -/
def CriticalSurfacePhaseBoundary (surface : ℝ → ℝ) (pc : ℝ) : Prop :=
  ∀ p ∈ Ioo (0 : ℝ) 1,
    (surface p < 0 ↔ p < pc) ∧ (0 < surface p ↔ pc < p)

lemma CriticalSurfacePhaseBoundary.eq_zero
    {surface : ℝ → ℝ} {pc : ℝ}
    (hpc : pc ∈ Ioo (0 : ℝ) 1)
    (hphase : CriticalSurfacePhaseBoundary surface pc) :
    surface pc = 0 := by
  have hsign := hphase pc hpc
  have hnotNeg : ¬surface pc < 0 := by
    rw [hsign.1]
    exact lt_irrefl pc
  have hnotPos : ¬0 < surface pc := by
    rw [hsign.2]
    exact lt_irrefl pc
  exact le_antisymm (le_of_not_gt hnotPos) (le_of_not_gt hnotNeg)

/-- The triangular critical cubic in the odds of `p` changes sign exactly at `pc`; for `q > 0` this
says `pc` is the triangular self-dual value. -/
def TriangularCriticalPhaseBoundary (q pc : ℝ) : Prop :=
  CriticalSurfacePhaseBoundary
    (fun p => triangularFKCriticalPolynomial q (fkEdgeOdds p)) pc

/-- The hexagonal critical cubic in the odds of `p` changes sign exactly at `pc`; for `q > 0` this
says `pc` is the hexagonal self-dual value. -/
def HexagonalCriticalPhaseBoundary (q pc : ℝ) : Prop :=
  CriticalSurfacePhaseBoundary
    (fun p => hexagonalFKCriticalPolynomial q (fkEdgeOdds p)) pc

lemma triangularFKCriticalPolynomial_eq_zero_of_phaseBoundary
    {q pc : ℝ} (hpc : pc ∈ Ioo (0 : ℝ) 1)
    (hphase : TriangularCriticalPhaseBoundary q pc) :
    triangularFKCriticalPolynomial q (fkEdgeOdds pc) = 0 := by
  exact CriticalSurfacePhaseBoundary.eq_zero
    (surface := fun p => triangularFKCriticalPolynomial q (fkEdgeOdds p))
    (pc := pc) hpc hphase

lemma hexagonalFKCriticalPolynomial_eq_zero_of_phaseBoundary
    {q pc : ℝ} (hpc : pc ∈ Ioo (0 : ℝ) 1)
    (hphase : HexagonalCriticalPhaseBoundary q pc) :
    hexagonalFKCriticalPolynomial q (fkEdgeOdds pc) = 0 := by
  exact CriticalSurfacePhaseBoundary.eq_zero
    (surface := fun p => hexagonalFKCriticalPolynomial q (fkEdgeOdds p))
    (pc := pc) hpc hphase

/-! ## C. Critical points from duality -/

lemma triHexCriticalPolynomials_of_dualThreshold_of_triangularPhase
    {q pcTri pcHex : ℝ}
    (hq : 0 < q)
    (hpcTri : pcTri ∈ Ioo (0 : ℝ) 1)
    (hdual : dualParam pcTri q = pcHex)
    (hphase : TriangularCriticalPhaseBoundary q pcTri) :
    triangularFKCriticalPolynomial q (fkEdgeOdds pcTri) = 0 ∧
      hexagonalFKCriticalPolynomial q (fkEdgeOdds pcHex) = 0 := by
  have htri := triangularFKCriticalPolynomial_eq_zero_of_phaseBoundary
    hpcTri hphase
  have hproduct := fkEdgeOdds_mul_dualParam hpcTri.1 hpcTri.2 hq
  rw [hdual] at hproduct
  have hy : fkEdgeOdds pcTri ≠ 0 :=
    div_ne_zero (ne_of_gt hpcTri.1) (by linarith [hpcTri.2])
  exact ⟨htri,
    hexagonalFKCritical_of_dual_triangular hy hproduct htri⟩

lemma triHexCriticalPolynomials_of_dualThreshold_of_hexagonalPhase
    {q pcTri pcHex : ℝ}
    (hq : 0 < q)
    (hpcTri : pcTri ∈ Ioo (0 : ℝ) 1)
    (hpcHex : pcHex ∈ Ioo (0 : ℝ) 1)
    (hdual : dualParam pcTri q = pcHex)
    (hphase : HexagonalCriticalPhaseBoundary q pcHex) :
    triangularFKCriticalPolynomial q (fkEdgeOdds pcTri) = 0 ∧
      hexagonalFKCriticalPolynomial q (fkEdgeOdds pcHex) = 0 := by
  have hhex := hexagonalFKCriticalPolynomial_eq_zero_of_phaseBoundary
    hpcHex hphase
  have hproduct := fkEdgeOdds_mul_dualParam hpcTri.1 hpcTri.2 hq
  rw [hdual] at hproduct
  have hyHex : fkEdgeOdds pcHex ≠ 0 :=
    div_ne_zero (ne_of_gt hpcHex.1) (by linarith [hpcHex.2])
  exact ⟨triangularFKCritical_of_dual_hexagonal hyHex hproduct hhex,
    hhex⟩

/-- Transfer hypothesis: subcritical exponential decay on the triangular lattice below `pcTri`
implies it on the hexagonal lattice below `pcHex`. -/
def TriHexSubcriticalDecayTransfer (q pcTri pcHex : ℝ) : Prop :=
  SubcriticalTwoPointExponentialDecay triangular q pcTri →
    SubcriticalTwoPointExponentialDecay hexagonal q pcHex

lemma triHexCriticalConclusion_of_exactDualThreshold
    {q pcTri pcHex : ℝ}
    (hq : 0 < q)
    (hpcTri : pcTri ∈ Ioo (0 : ℝ) 1)
    (hdual : dualParam pcTri q = pcHex)
    (hphase : TriangularCriticalPhaseBoundary q pcTri)
    (hdecayTri : SubcriticalTwoPointExponentialDecay triangular q pcTri)
    (hdecayTransfer : TriHexSubcriticalDecayTransfer q pcTri pcHex) :
    (triangularFKCriticalPolynomial q (fkEdgeOdds pcTri) = 0 ∧
      hexagonalFKCriticalPolynomial q (fkEdgeOdds pcHex) = 0) ∧
      SubcriticalTwoPointExponentialDecay triangular q pcTri ∧
      SubcriticalTwoPointExponentialDecay hexagonal q pcHex := by
  exact ⟨triHexCriticalPolynomials_of_dualThreshold_of_triangularPhase
      hq hpcTri hdual hphase,
    hdecayTri, hdecayTransfer hdecayTri⟩

/-- Critical points of the triangular and hexagonal random-cluster models from phase inputs (`q ≥
1`): under off-critical sharpness, dual coverage, no coexistence, the triangular phase boundary,
triangular subcritical decay and decay transfer, both critical cubics vanish and both lattices have
subcritical decay. Conditional: the triangular critical value is assumed (`hphase`) and the decay
conclusions restate hypotheses (Grimmett, *The Random-Cluster Model*, §6.6). -/
theorem triangular_hexagonal_critical_of_phase_inputs
    {q : ℝ}
    (hq : 1 ≤ q)
    (hpcTri : triangular.criticalPoint q ∈ Ioo (0 : ℝ) 1)
    (hpcHex : hexagonal.criticalPoint q ∈ Ioo (0 : ℝ) 1)
    (hsharpTri : OffCriticalSharpness
      (fun p => triangular.wiredPercolates p q)
      (triangular.criticalPoint q))
    (hsharpHex : OffCriticalSharpness
      (fun p => hexagonal.wiredPercolates p q)
      (hexagonal.criticalPoint q))
    (hcoverage : DualSubcriticalCoverage
      (fun p => hexagonal.wiredPercolates p q)
      (triangular.criticalPoint q) q)
    (hnoCoexistence : DualNoCoexistence
      (fun p => triangular.wiredPercolates p q)
      (fun p => hexagonal.wiredPercolates p q) q)
    (hphase : TriangularCriticalPhaseBoundary q
      (triangular.criticalPoint q))
    (hdecayTri : SubcriticalTwoPointExponentialDecay triangular q
      (triangular.criticalPoint q))
    (hdecayTransfer : TriHexSubcriticalDecayTransfer q
      (triangular.criticalPoint q) (hexagonal.criticalPoint q)) :
    (triangularFKCriticalPolynomial q
        (fkEdgeOdds (triangular.criticalPoint q)) = 0 ∧
      hexagonalFKCriticalPolynomial q
        (fkEdgeOdds (hexagonal.criticalPoint q)) = 0) ∧
      SubcriticalTwoPointExponentialDecay triangular q
        (triangular.criticalPoint q) ∧
      SubcriticalTwoPointExponentialDecay hexagonal q
        (hexagonal.criticalPoint q) := by
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hrelation :=
    triangular.dualCritical_relation_of_sharpness_noCoexistence hexagonal
      hpcTri hpcHex hq0 hsharpTri hsharpHex hcoverage hnoCoexistence
  exact triHexCriticalConclusion_of_exactDualThreshold hq0 hpcTri
    hrelation.1 hphase hdecayTri hdecayTransfer

/-! ## D. Bond percolation at `q = 1` -/

lemma triangularFKCriticalPolynomial_one_of_starTriangle
    {p : ℝ} (hp : p ∈ Ioo (0 : ℝ) 1)
    (hstt : Universality.triProb p p p Universality.triPatABC =
      Universality.starProb (1 - p) (1 - p) (1 - p)
        Universality.starPatABC) :
    triangularFKCriticalPolynomial 1 (fkEdgeOdds p) = 0 := by
  have hcritical : Universality.IsCriticalTri p p p :=
    (Universality.starTriangle_iff_isCriticalTri p p p).1 hstt
  have hsurface :=
    (triangularFKCriticalSurface_one_iff_isCriticalTri
      (by linarith [hp.2]) (by linarith [hp.2]) (by linarith [hp.2])).2
      hcritical
  simpa [triangularFKCriticalSurface_diagonal] using hsurface

lemma triHexCriticalPolynomials_one_of_starTriangle_of_dualThreshold
    {pcTri pcHex : ℝ}
    (hpcTri : pcTri ∈ Ioo (0 : ℝ) 1)
    (hdual : dualParam pcTri 1 = pcHex)
    (hstt : Universality.triProb pcTri pcTri pcTri Universality.triPatABC =
      Universality.starProb (1 - pcTri) (1 - pcTri) (1 - pcTri)
        Universality.starPatABC) :
    triangularFKCriticalPolynomial 1 (fkEdgeOdds pcTri) = 0 ∧
      hexagonalFKCriticalPolynomial 1 (fkEdgeOdds pcHex) = 0 := by
  have htri := triangularFKCriticalPolynomial_one_of_starTriangle hpcTri hstt
  have hproduct := fkEdgeOdds_mul_dualParam (q := (1 : ℝ))
    hpcTri.1 hpcTri.2 (by norm_num)
  rw [hdual] at hproduct
  have hy : fkEdgeOdds pcTri ≠ 0 :=
    div_ne_zero (ne_of_gt hpcTri.1) (by linarith [hpcTri.2])
  exact ⟨htri, hexagonalFKCritical_of_dual_triangular hy hproduct htri⟩

end PeriodicPlanar
end FK
end StatMech
