/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















import Code.FK.PeriodicPlanarCriticalReduction
import Code.FrontierA.FKTrihexDuality

open MeasureTheory Set SimpleGraph

namespace StatMech
namespace FK
namespace PeriodicPlanar

open BeffaraDC FrontierA

variable {V W : Type*} [DecidableEq V] [DecidableEq W]




def PeriodicGraph.twoPointEvent (P : PeriodicGraph V) (x y : V) :
    Set (ConfigSpace (Sym2 V)) :=
  {omega | (P.openSubgraph omega).Reachable x y}

private theorem PeriodicGraph.measurableSet_openSubgraphAdj
    (P : PeriodicGraph V) (x y : V) :
    MeasurableSet
      {omega : ConfigSpace (Sym2 V) | (P.openSubgraph omega).Adj x y} := by
  by_cases hxy : P.graph.Adj x y
  · have heq :
        {omega : ConfigSpace (Sym2 V) | (P.openSubgraph omega).Adj x y} =
          {omega | omega s(x, y) = true} := by
      ext omega
      rw [Set.mem_setOf_eq, P.openSubgraph_adj]
      exact ⟨fun h => h.2, fun h => ⟨hxy, h⟩⟩
    rw [heq]
    exact measurableSet_eq_fun
      (ConfigSpace.measurable_eval s(x, y)) measurable_const
  · have heq :
        {omega : ConfigSpace (Sym2 V) | (P.openSubgraph omega).Adj x y} = ∅ := by
      ext omega
      rw [Set.mem_setOf_eq, P.openSubgraph_adj]
      simp only [Set.mem_empty_iff_false, iff_false]
      exact fun h => hxy h.1
    rw [heq]
    exact MeasurableSet.empty

private theorem PeriodicGraph.measurableSet_openChain
    (P : PeriodicGraph V) (l : List V) :
    MeasurableSet
      {omega : ConfigSpace (Sym2 V) |
        List.IsChain (P.openSubgraph omega).Adj l} := by
  induction l with
  | nil => simp only [List.isChain_nil, Set.setOf_true, MeasurableSet.univ]
  | cons a l ih =>
      cases l with
      | nil => simp only [List.isChain_singleton, Set.setOf_true, MeasurableSet.univ]
      | cons b l =>
          have heq :
              {omega : ConfigSpace (Sym2 V) |
                  List.IsChain (P.openSubgraph omega).Adj (a :: b :: l)} =
                {omega | (P.openSubgraph omega).Adj a b} ∩
                  {omega | List.IsChain (P.openSubgraph omega).Adj (b :: l)} := by
            ext omega
            simp only [Set.mem_setOf_eq, Set.mem_inter_iff,
              List.isChain_cons_cons]
          rw [heq]
          exact (P.measurableSet_openSubgraphAdj a b).inter ih

private theorem PeriodicGraph.reachable_iff_openChain
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



theorem PeriodicGraph.measurableSet_twoPointEvent
    [Countable V] (P : PeriodicGraph V) (x y : V) :
    MeasurableSet (P.twoPointEvent x y) := by
  classical
  have heq : P.twoPointEvent x y =
      ⋃ l : List V,
        ({omega | List.IsChain (P.openSubgraph omega).Adj (x :: l)} ∩
          if (x :: l).getLast (List.cons_ne_nil _ _) = y then Set.univ else ∅) := by
    ext omega
    rw [PeriodicGraph.twoPointEvent, Set.mem_setOf_eq,
      P.reachable_iff_openChain]
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨l, hchain, hlast⟩
      exact ⟨l, hchain, by rw [if_pos hlast]; trivial⟩
    · rintro ⟨l, hchain, hlast⟩
      refine ⟨l, hchain, ?_⟩
      by_cases h : (x :: l).getLast (List.cons_ne_nil _ _) = y
      · exact h
      · rw [if_neg h] at hlast
        exact (Set.notMem_empty _ hlast).elim
  rw [heq]
  apply MeasurableSet.iUnion
  intro l
  apply MeasurableSet.inter (P.measurableSet_openChain (x :: l))
  split <;> simp




noncomputable def PeriodicGraph.wiredTwoPointProbability
    [Countable V] (P : PeriodicGraph V) (p q : ℝ) (x y : V) : ℝ :=
  if h : p ∈ Ioo (0 : ℝ) 1 ∧ 0 < q then
    ((P.wiredBufferedInfiniteVolume h.1.1 h.1.2 h.2 :
        ProbabilityMeasure (ConfigSpace (Sym2 V))) :
      Measure (ConfigSpace (Sym2 V))).real (P.twoPointEvent x y)
  else 0

theorem PeriodicGraph.wiredTwoPointProbability_nonneg
    [Countable V] (P : PeriodicGraph V) (p q : ℝ) (x y : V) :
    0 ≤ P.wiredTwoPointProbability p q x y := by
  unfold PeriodicGraph.wiredTwoPointProbability
  split
  · exact ENNReal.toReal_nonneg
  · exact le_rfl

theorem PeriodicGraph.wiredTwoPointProbability_le_one
    [Countable V] (P : PeriodicGraph V) (p q : ℝ) (x y : V) :
    P.wiredTwoPointProbability p q x y ≤ 1 := by
  unfold PeriodicGraph.wiredTwoPointProbability
  split
  · rw [Measure.real]
    refine ENNReal.toReal_le_of_le_ofReal (by norm_num) ?_
    rw [ENNReal.ofReal_one]
    exact prob_le_one
  · norm_num



def SubcriticalTwoPointExponentialDecay
    [Countable V] (P : PeriodicGraph V) (q pc : ℝ) : Prop :=
  ∀ p ∈ Ioo (0 : ℝ) pc, ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ x y : V,
      P.wiredTwoPointProbability p q x y ≤
        C * Real.exp (-c * (P.graph.dist x y : ℝ))





def CriticalSurfacePhaseBoundary (surface : ℝ → ℝ) (pc : ℝ) : Prop :=
  ∀ p ∈ Ioo (0 : ℝ) 1,
    (surface p < 0 ↔ p < pc) ∧ (0 < surface p ↔ pc < p)


theorem CriticalSurfacePhaseBoundary.eq_zero
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




def TriangularCriticalPhaseBoundary (q pc : ℝ) : Prop :=
  CriticalSurfacePhaseBoundary
    (fun p => triangularFKCriticalPolynomial q (fkEdgeOdds p)) pc


def HexagonalCriticalPhaseBoundary (q pc : ℝ) : Prop :=
  CriticalSurfacePhaseBoundary
    (fun p => hexagonalFKCriticalPolynomial q (fkEdgeOdds p)) pc

theorem triangularFKCriticalPolynomial_eq_zero_of_phaseBoundary
    {q pc : ℝ} (hpc : pc ∈ Ioo (0 : ℝ) 1)
    (hphase : TriangularCriticalPhaseBoundary q pc) :
    triangularFKCriticalPolynomial q (fkEdgeOdds pc) = 0 := by
  exact CriticalSurfacePhaseBoundary.eq_zero
    (surface := fun p => triangularFKCriticalPolynomial q (fkEdgeOdds p))
    (pc := pc) hpc hphase

theorem hexagonalFKCriticalPolynomial_eq_zero_of_phaseBoundary
    {q pc : ℝ} (hpc : pc ∈ Ioo (0 : ℝ) 1)
    (hphase : HexagonalCriticalPhaseBoundary q pc) :
    hexagonalFKCriticalPolynomial q (fkEdgeOdds pc) = 0 := by
  exact CriticalSurfacePhaseBoundary.eq_zero
    (surface := fun p => hexagonalFKCriticalPolynomial q (fkEdgeOdds p))
    (pc := pc) hpc hphase






theorem triHexCriticalPolynomials_of_dualThreshold_of_triangularPhase
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


theorem triHexCriticalPolynomials_of_dualThreshold_of_hexagonalPhase
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






def TriHexSubcriticalDecayTransfer (q pcTri pcHex : ℝ) : Prop :=
  SubcriticalTwoPointExponentialDecay triangular q pcTri →
    SubcriticalTwoPointExponentialDecay hexagonal q pcHex




theorem triHexCriticalConclusion_of_exactDualThreshold
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





theorem triangularFKCriticalPolynomial_one_of_starTriangle
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



theorem triHexCriticalPolynomials_one_of_starTriangle_of_dualThreshold
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
