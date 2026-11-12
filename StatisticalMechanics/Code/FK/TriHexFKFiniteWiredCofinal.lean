/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.TriHexFKFiniteWiredWeights
import Code.FK.PeriodicPlanarDiagonalLimit
import Code.FK.BoundaryEdgeAbsorption
import Code.FK.PeriodicPlanarCoverageUpgrade









open Finset Set SimpleGraph Filter MeasureTheory Topology

namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice Universality

noncomputable section


theorem triangular_mem_orbitBox_iff_box (n : Nat) (v : Site 2) :
    v ∈ triangular.orbitBox n ↔ v ∈ box 2 n := by
  rw [triangular.mem_orbitBox_iff]
  simp [triangular, siteTranslate_apply]


theorem hexagonal_mem_orbitBox_iff_box (n : Nat) (v : HexVertex) :
    v ∈ hexagonal.orbitBox n ↔ v.1 ∈ box 2 n := by
  rw [hexagonal.mem_orbitBox_iff]
  rcases v with ⟨v, b⟩
  cases b <;> simp [hexagonal, hexTranslate_apply]

theorem triHexPlanarCellTerminal_mem_box_succ
    (n : Nat) {z : Site 2} (hz : z ∈ box 2 n) (i : Fin 3) :
    triHexPlanarCellTerminal z i ∈ box 2 (n + 1) := by
  intro k
  fin_cases i <;> fin_cases k <;>
    simp [triHexPlanarCellTerminal, hexagonalStep] at hz ⊢ <;> omega

theorem triHexPlanarCellPredecessor_mem_box_succ
    (n : Nat) {v : Site 2} (hv : v ∈ box 2 n) :
    v - hexagonalStep 0 ∈ box 2 (n + 1) := by
  intro k
  fin_cases k <;> simp [hexagonalStep] at hv ⊢ <;> omega



def triHexPlanarFiniteStarVertexEmbedding (n : Nat) :
    TriHexPlanarFiniteStarVertex n ↪ HexVertex where
  toFun
    | Sum.inl z => (z.1, false)
    | Sum.inr v => (v.1, true)
  inj' := by
    intro u v huv
    rcases u with z | x <;> rcases v with w | y
    · apply congrArg Sum.inl
      exact Subtype.ext (congrArg (fun a : HexVertex => a.1) huv)
    · have := congrArg (fun a : HexVertex => a.2) huv
      simp at this
    · have := congrArg (fun a : HexVertex => a.2) huv
      simp at this
    · apply congrArg Sum.inr
      exact Subtype.ext (congrArg (fun a : HexVertex => a.1) huv)

@[simp] theorem triHexPlanarFiniteStarVertexEmbedding_cell
    (n : Nat) (z : TriHexPlanarFiniteCell n) :
    triHexPlanarFiniteStarVertexEmbedding n (Sum.inl z) = (z.1, false) := rfl

@[simp] theorem triHexPlanarFiniteStarVertexEmbedding_terminal
    (n : Nat) (v : TriHexPlanarFiniteTerminal n) :
    triHexPlanarFiniteStarVertexEmbedding n (Sum.inr v) = (v.1, true) := rfl



theorem triHexPlanarFiniteStarGraph_adj_hexagonal
    (n : Nat) {u v : TriHexPlanarFiniteStarVertex n}
    (huv : (triHexPlanarFiniteStarGraph n).Adj u v) :
    hexagonalGraph.Adj
      (triHexPlanarFiniteStarVertexEmbedding n u)
      (triHexPlanarFiniteStarVertexEmbedding n v) := by
  rw [triHexPlanarFiniteStarGraph, SimpleGraph.fromEdgeSet_adj] at huv
  obtain ⟨⟨⟨z, i⟩, hedge⟩, _⟩ := huv
  change s(Sum.inl z,
    Sum.inr (triHexPlanarFiniteTerminalMap n z i)) = s(u, v) at hedge
  rw [Sym2.eq_iff] at hedge
  rcases hedge with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · subst u
    subst v
    simpa [triHexPlanarFiniteTerminalMap, triHexPlanarCellTerminal] using
      hexagonalGraph_adj_triHexPlanarCellTerminal z.1 i
  · subst u
    subst v
    exact (by
      simpa [triHexPlanarFiniteTerminalMap, triHexPlanarCellTerminal] using
        (hexagonalGraph_adj_triHexPlanarCellTerminal z.1 i).symm)



theorem triHexPlanarFiniteStarGraph_adj_of_hexagonal
    (n : Nat) {u v : TriHexPlanarFiniteStarVertex n}
    (huv : hexagonalGraph.Adj
      (triHexPlanarFiniteStarVertexEmbedding n u)
      (triHexPlanarFiniteStarVertexEmbedding n v)) :
    (triHexPlanarFiniteStarGraph n).Adj u v := by
  rcases u with z | x <;> rcases v with w | y
  · simp [hexagonalGraph_adj, hexagonalAdj] at huv
  · rw [hexagonalGraph_adj] at huv
    rcases huv with ⟨_, _, i, hi⟩ | hbad
    · change y.1 - z.1 = hexagonalStep i at hi
      have hxy : y.1 = triHexPlanarCellTerminal z.1 i := by
        rw [triHexPlanarCellTerminal]
        exact eq_add_of_sub_eq' hi
      have hterm : y = triHexPlanarFiniteTerminalMap n z i :=
        Subtype.ext hxy
      subst y
      rw [triHexPlanarFiniteStarGraph, SimpleGraph.fromEdgeSet_adj]
      refine ⟨⟨(z, i), rfl⟩, Sum.inl_ne_inr⟩
    · simp at hbad
  · rw [hexagonalGraph_adj] at huv
    rcases huv with hbad | ⟨_, _, i, hi⟩
    · simp at hbad
    · change x.1 - w.1 = hexagonalStep i at hi
      have hxy : x.1 = triHexPlanarCellTerminal w.1 i := by
        rw [triHexPlanarCellTerminal]
        exact eq_add_of_sub_eq' hi
      have hterm : x = triHexPlanarFiniteTerminalMap n w i :=
        Subtype.ext hxy
      subst x
      rw [triHexPlanarFiniteStarGraph, SimpleGraph.fromEdgeSet_adj]
      refine ⟨⟨(w, i), ?_⟩, Sum.inr_ne_inl⟩
      change s(Sum.inl w,
        Sum.inr (triHexPlanarFiniteTerminalMap n w i)) =
          s(Sum.inr (triHexPlanarFiniteTerminalMap n w i), Sum.inl w)
      rw [Sym2.eq_iff]
      exact Or.inr ⟨rfl, rfl⟩
  · simp [hexagonalGraph_adj, hexagonalAdj] at huv



theorem triHexPlanarFiniteStarGraph_adj_iff_hexagonal
    (n : Nat) (u v : TriHexPlanarFiniteStarVertex n) :
    (triHexPlanarFiniteStarGraph n).Adj u v ↔
      hexagonalGraph.Adj
        (triHexPlanarFiniteStarVertexEmbedding n u)
        (triHexPlanarFiniteStarVertexEmbedding n v) :=
  ⟨triHexPlanarFiniteStarGraph_adj_hexagonal n,
    triHexPlanarFiniteStarGraph_adj_of_hexagonal n⟩



theorem triHexPlanarFiniteStar_adjMatch_hexagonal (n : Nat) :
    ocd_AdjMatch (triHexPlanarFiniteStarGraph n) hexagonalGraph
      (triHexPlanarFiniteStarVertexEmbedding n) :=
  triHexPlanarFiniteStarGraph_adj_iff_hexagonal n



theorem triHexPlanarFiniteStar_cell_not_boundary
    (n : Nat) (z : TriHexPlanarFiniteCell n) :
    ¬ ∃ w : HexVertex,
      hexagonalGraph.Adj
          (triHexPlanarFiniteStarVertexEmbedding n (Sum.inl z)) w ∧
        w ∉ Set.range (triHexPlanarFiniteStarVertexEmbedding n) := by
  rintro ⟨w, hadj, hw⟩
  rw [hexagonalGraph_adj] at hadj
  rcases hadj with ⟨_, hwWhite, i, hi⟩ | hbad
  · have hsite : w.1 = triHexPlanarCellTerminal z.1 i := by
      rw [triHexPlanarCellTerminal]
      change w.1 - z.1 = hexagonalStep i at hi
      exact eq_add_of_sub_eq' hi
    have hwEq : w =
        triHexPlanarFiniteStarVertexEmbedding n
          (Sum.inr (triHexPlanarFiniteTerminalMap n z i)) := by
      apply Prod.ext
      · simpa [triHexPlanarFiniteTerminalMap] using hsite
      · simpa using hwWhite.symm
    exact hw ⟨Sum.inr (triHexPlanarFiniteTerminalMap n z i), hwEq.symm⟩
  · simp at hbad



theorem triHexPlanarFiniteStar_terminal_boundary_iff
    (n : Nat) (v : TriHexPlanarFiniteTerminal n) :
    triHexPlanarFiniteStarBoundary n (Sum.inr v) ↔
      ∃ w : HexVertex,
        hexagonalGraph.Adj
            (triHexPlanarFiniteStarVertexEmbedding n (Sum.inr v)) w ∧
          w ∉ Set.range (triHexPlanarFiniteStarVertexEmbedding n) := by
  constructor
  · rintro ⟨i, hi⟩
    let w : HexVertex := (v.1 - hexagonalStep i, false)
    refine ⟨w, ?_, ?_⟩
    · rw [hexagonalGraph_adj]
      right
      refine ⟨rfl, rfl, i, ?_⟩
      change v.1 - (v.1 - hexagonalStep i) = hexagonalStep i
      abel
    · rintro ⟨u, hu⟩
      rcases u with z | x
      · have hsite := congrArg (fun a : HexVertex => a.1) hu
        apply hi
        change z.1 = v.1 - hexagonalStep i at hsite
        rw [← hsite]
        exact z.2
      · have hlabel := congrArg (fun a : HexVertex => a.2) hu
        simp [w] at hlabel
  · rintro ⟨w, hadj, hw⟩
    rw [hexagonalGraph_adj] at hadj
    rcases hadj with hbad | ⟨hwBlack, _, i, hi⟩
    · simp at hbad
    · refine ⟨i, ?_⟩
      change v.1 - hexagonalStep i ∉ box 2 n
      intro hcenter
      let z : TriHexPlanarFiniteCell n :=
        ⟨v.1 - hexagonalStep i, hcenter⟩
      apply hw
      refine ⟨Sum.inl z, ?_⟩
      apply Prod.ext
      · change z.1 = w.1
        change v.1 - w.1 = hexagonalStep i at hi
        dsimp only [z]
        rw [← hi]
        abel
      · simpa using hwBlack.symm



theorem triHexPlanarFiniteStar_boundary_iff_ambient
    (n : Nat) (u : TriHexPlanarFiniteStarVertex n) :
    triHexPlanarFiniteStarBoundary n u ↔
      ∃ w : HexVertex,
        hexagonalGraph.Adj
            (triHexPlanarFiniteStarVertexEmbedding n u) w ∧
          w ∉ Set.range (triHexPlanarFiniteStarVertexEmbedding n) := by
  rcases u with z | v
  · simp only [triHexPlanarFiniteStarBoundary]
    exact (iff_false_intro
      (triHexPlanarFiniteStar_cell_not_boundary n z)).symm
  · exact triHexPlanarFiniteStar_terminal_boundary_iff n v


theorem triHexPlanarFiniteStar_range_subset_orbitBox_succ (n : Nat) :
    Set.range (triHexPlanarFiniteStarVertexEmbedding n) ⊆
      (hexagonal.orbitBox (n + 1) : Set HexVertex) := by
  rintro v ⟨u, rfl⟩
  change triHexPlanarFiniteStarVertexEmbedding n u ∈
    hexagonal.orbitBox (n + 1)
  rw [hexagonal_mem_orbitBox_iff_box]
  rcases u with z | x
  · exact box_mono 2 (Nat.le_succ n) z.2
  · obtain ⟨zi, hzi, hx⟩ := Finset.mem_image.mp x.2
    obtain ⟨z, i⟩ := zi
    rw [Finset.mem_product] at hzi
    change triHexPlanarCellTerminal z i = x.1 at hx
    change x.1 ∈ box 2 (n + 1)
    rw [← hx]
    exact triHexPlanarCellTerminal_mem_box_succ n (by simpa using hzi.1) i



theorem hexagonal_orbitBox_subset_triHexPlanarFiniteStar_range_succ
    (n : Nat) :
    (hexagonal.orbitBox n : Set HexVertex) ⊆
      Set.range (triHexPlanarFiniteStarVertexEmbedding (n + 1)) := by
  intro v hv
  change v ∈ hexagonal.orbitBox n at hv
  rw [hexagonal_mem_orbitBox_iff_box] at hv
  rcases v with ⟨v, b⟩
  cases b
  · let z : TriHexPlanarFiniteCell (n + 1) :=
      ⟨v, box_mono 2 (Nat.le_succ n) hv⟩
    exact ⟨Sum.inl z, rfl⟩
  · let z : TriHexPlanarFiniteCell (n + 1) :=
      ⟨v - hexagonalStep 0,
        triHexPlanarCellPredecessor_mem_box_succ n hv⟩
    refine ⟨Sum.inr (triHexPlanarFiniteTerminalMap (n + 1) z 0), ?_⟩
    apply Prod.ext
    · change triHexPlanarCellTerminal z.1 0 = v
      dsimp only [z]
      rw [triHexPlanarCellTerminal]
      abel
    · rfl


theorem triHexPlanarFiniteTerminal_subset_triangular_orbitBox_succ
    (n : Nat) (v : TriHexPlanarFiniteTerminal n) :
    v.1 ∈ triangular.orbitBox (n + 1) := by
  rw [triangular_mem_orbitBox_iff_box]
  obtain ⟨zi, hzi, hv⟩ := Finset.mem_image.mp v.2
  obtain ⟨z, i⟩ := zi
  rw [Finset.mem_product] at hzi
  change triHexPlanarCellTerminal z i = v.1 at hv
  rw [← hv]
  exact triHexPlanarCellTerminal_mem_box_succ n (by simpa using hzi.1) i



theorem triangular_orbitBox_subset_triHexPlanarFiniteTerminal_succ
    (n : Nat) {v : Site 2} (hv : v ∈ triangular.orbitBox n) :
    v ∈ triHexPlanarFiniteTerminalFinset (n + 1) := by
  rw [triangular_mem_orbitBox_iff_box] at hv
  let z : TriHexPlanarFiniteCell (n + 1) :=
    ⟨v - hexagonalStep 0,
      triHexPlanarCellPredecessor_mem_box_succ n hv⟩
  apply Finset.mem_image.mpr
  refine ⟨(z.1, 0), ?_, ?_⟩
  · rw [Finset.mem_product]
    exact ⟨by simpa using z.2, Finset.mem_univ 0⟩
  · change triHexPlanarCellTerminal z.1 0 = v
    dsimp only [z]
    rw [triHexPlanarCellTerminal]
    abel





theorem triangularIndexedEdge_rebase_eq_cellEdge
    (z : Site 2) (i : Fin 3) :
    triangularIndexedEdge (triHexPlanarTriangleIndexEquiv (z, i)) =
      s(triHexPlanarCellTerminal z (triHexTriangleEdgeTerminal1 i),
        triHexPlanarCellTerminal z (triHexTriangleEdgeTerminal2 i)) := by
  have hzUnion : z ∈ ⋃ n, box 2 n := by
    rw [iUnion_box]
    trivial
  obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hzUnion
  let z' : TriHexPlanarFiniteCell n := ⟨z, hn⟩
  have h := triHexPlanarFiniteTriangleEdge_val n (z', i)
  simpa [triHexPlanarFiniteTriangleEdge, triHexPlanarFiniteTerminalMap,
    z'] using h.symm



theorem triHexPlanarFiniteTriangle_adj_or_boundary
    (n : Nat) {u v : TriHexPlanarFiniteTerminal n}
    (huv : triangularGraph.Adj u.1 v.1) :
    (triHexPlanarFiniteTriangleGraph n).Adj u v ∨
      (triHexPlanarFiniteBoundary n u ∧
        triHexPlanarFiniteBoundary n v) := by
  let e : triangularGraph.edgeSet := ⟨s(u.1, v.1), by
    rwa [SimpleGraph.mem_edgeSet]⟩
  let a := triangularEdgeChartEquiv.symm e
  rcases hpair : triHexPlanarTriangleIndexEquiv.symm a with ⟨z, i⟩
  have ha : triHexPlanarTriangleIndexEquiv (z, i) = a := by
    rw [← hpair]
    exact triHexPlanarTriangleIndexEquiv.apply_symm_apply a
  have hchart : triangularIndexedEdge a = s(u.1, v.1) := by
    have h := congrArg Subtype.val
      (triangularEdgeChartEquiv.apply_symm_apply e)
    exact h
  have hedge :
      s(triHexPlanarCellTerminal z (triHexTriangleEdgeTerminal1 i),
        triHexPlanarCellTerminal z (triHexTriangleEdgeTerminal2 i)) =
          s(u.1, v.1) := by
    rw [← hchart, ← ha]
    exact (triangularIndexedEdge_rebase_eq_cellEdge z i).symm
  by_cases hz : z ∈ box 2 n
  · left
    let z' : TriHexPlanarFiniteCell n := ⟨z, hz⟩
    rw [triHexPlanarFiniteTriangleGraph, SimpleGraph.fromEdgeSet_adj]
    refine ⟨⟨(z', i), ?_⟩, ?_⟩
    · change s(triHexPlanarFiniteTerminalMap n z'
          (triHexTriangleEdgeTerminal1 i),
        triHexPlanarFiniteTerminalMap n z'
          (triHexTriangleEdgeTerminal2 i)) = s(u, v)
      rw [Sym2.eq_iff] at hedge ⊢
      rcases hedge with h | h
      · exact Or.inl ⟨Subtype.ext h.1, Subtype.ext h.2⟩
      · exact Or.inr ⟨Subtype.ext h.1, Subtype.ext h.2⟩
    · exact fun huvEq => huv.ne (congrArg Subtype.val huvEq)
  · right
    rw [Sym2.eq_iff] at hedge
    rcases hedge with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · constructor
      · refine ⟨triHexTriangleEdgeTerminal1 i, ?_⟩
        change u.1 - hexagonalStep (triHexTriangleEdgeTerminal1 i) ∉ box 2 n
        rw [← hu]
        simp [triHexPlanarCellTerminal, hz]
      · refine ⟨triHexTriangleEdgeTerminal2 i, ?_⟩
        change v.1 - hexagonalStep (triHexTriangleEdgeTerminal2 i) ∉ box 2 n
        rw [← hv]
        simp [triHexPlanarCellTerminal, hz]
    · constructor
      · refine ⟨triHexTriangleEdgeTerminal2 i, ?_⟩
        change u.1 - hexagonalStep (triHexTriangleEdgeTerminal2 i) ∉ box 2 n
        rw [← hu]
        simp [triHexPlanarCellTerminal, hz]
      · refine ⟨triHexTriangleEdgeTerminal1 i, ?_⟩
        change v.1 - hexagonalStep (triHexTriangleEdgeTerminal1 i) ∉ box 2 n
        rw [← hv]
        simp [triHexPlanarCellTerminal, hz]



theorem triHexPlanarFiniteTriangle_induced_le_wiredGraph (n : Nat) :
    SimpleGraph.comap Subtype.val triangularGraph ≤
      triHexPlanarFiniteTriangleGraph n ⊔
        boundaryCliqueGraph (triHexPlanarFiniteBoundary n) := by
  intro u v huv
  rcases triHexPlanarFiniteTriangle_adj_or_boundary n huv with h | ⟨hu, hv⟩
  · exact Or.inl h
  · right
    rw [boundaryCliqueGraph_adj]
    exact ⟨huv.ne, hu, hv⟩


def triHexPlanarFiniteTriangleInducedGraph (n : Nat) :
    SimpleGraph (TriHexPlanarFiniteTerminal n) :=
  SimpleGraph.comap Subtype.val triangularGraph

noncomputable instance triHexPlanarFiniteTriangleInducedGraphDecidable
    (n : Nat) : DecidableRel (triHexPlanarFiniteTriangleInducedGraph n).Adj :=
  Classical.decRel _


theorem triHexPlanarFiniteTriangleGraph_le_induced (n : Nat) :
    triHexPlanarFiniteTriangleGraph n ≤
      triHexPlanarFiniteTriangleInducedGraph n := by
  intro u v huv
  rw [triHexPlanarFiniteTriangleGraph,
    SimpleGraph.fromEdgeSet_adj] at huv
  obtain ⟨⟨⟨z, i⟩, hedge⟩, _⟩ := huv
  change s(triHexPlanarFiniteTerminalMap n z
      (triHexTriangleEdgeTerminal1 i),
    triHexPlanarFiniteTerminalMap n z
      (triHexTriangleEdgeTerminal2 i)) = s(u, v) at hedge
  have hamb := triangularGraph_adj_triHexPlanarCellTerminal z.1
    (triHexTriangleEdgeTerminal1 i)
    (triHexTriangleEdgeTerminal2 i) (by
      fin_cases i <;> decide)
  rw [Sym2.eq_iff] at hedge
  rcases hedge with ⟨hu, hv⟩ | ⟨hv, hu⟩
  · subst u
    subst v
    simpa [triHexPlanarFiniteTriangleInducedGraph,
      triHexPlanarFiniteTerminalMap] using hamb
  · subst u
    subst v
    simpa [triHexPlanarFiniteTriangleInducedGraph,
      triHexPlanarFiniteTerminalMap] using hamb.symm



theorem triHexPlanarFiniteRoot_not_boundary_succ (n : Nat) :
    ¬ triHexPlanarFiniteBoundary (n + 1)
      (triHexPlanarFiniteTerminalMap (n + 1)
        (triHexPlanarFiniteRootCell (n + 1)) 0) := by
  rintro ⟨i, hi⟩
  apply hi
  intro k
  fin_cases i <;> fin_cases k <;>
    simp [triHexPlanarFiniteTerminalMap, triHexPlanarFiniteRootCell,
      triHexPlanarCellTerminal, hexagonalStep]


def triHexPlanarFiniteTriangleInducedBoundaryReachIndicator (n : Nat)
    (eta : ConfigSpace (triHexPlanarFiniteTriangleInducedGraph n).edgeSet) :
    Real :=
  if ∃ y : TriHexPlanarFiniteTerminal n,
      triHexPlanarFiniteBoundary n y ∧
      (openSub (triHexPlanarFiniteTriangleInducedGraph n)
        (extendActive (triHexPlanarFiniteTriangleInducedGraph n) eta)).Reachable
          (triHexPlanarFiniteTerminalMap n
            (triHexPlanarFiniteRootCell n) 0) y then 1 else 0



theorem triHexPlanarFiniteTriangleInducedBoundaryReachIndicator_eq
    (n : Nat)
    (eta : ConfigSpace
      (triHexPlanarFiniteTriangleInducedGraph (n + 1)).edgeSet) :
    triHexPlanarFiniteTriangleInducedBoundaryReachIndicator (n + 1) eta =
      triHexPlanarFiniteTriangleBoundaryReachIndicator (n + 1)
        (activeGraphRestrict
          (triHexPlanarFiniteTriangleGraph (n + 1))
          (triHexPlanarFiniteTriangleInducedGraph (n + 1))
          (triHexPlanarFiniteTriangleGraph_le_induced (n + 1)) eta) := by
  unfold triHexPlanarFiniteTriangleInducedBoundaryReachIndicator
    triHexPlanarFiniteTriangleBoundaryReachIndicator
  congr 1
  apply propext
  exact boundaryReachable_iff_of_le_sup_boundaryClique
    (triHexPlanarFiniteTriangleGraph (n + 1))
    (triHexPlanarFiniteTriangleInducedGraph (n + 1))
    (triHexPlanarFiniteBoundary (n + 1))
    (triHexPlanarFiniteTriangleGraph_le_induced (n + 1))
    (by simpa [triHexPlanarFiniteTriangleInducedGraph] using
      triHexPlanarFiniteTriangle_induced_le_wiredGraph (n + 1))
    (triHexPlanarFiniteRoot_not_boundary_succ n) eta



noncomputable def triHexPlanarFiniteTriangleInducedWiredBoundaryProbability
    (n : Nat) (p q : Real) : Real :=
  ∑ eta : ConfigSpace
      (Sym2 (TriHexPlanarFiniteTerminal n)),
    triHexPlanarFiniteTriangleInducedBoundaryReachIndicator n
        (restrictActive (triHexPlanarFiniteTriangleInducedGraph n) eta) *
      wiredFkProb (triHexPlanarFiniteTriangleInducedGraph n)
        (triHexPlanarFiniteBoundary n) p q eta



theorem triHexPlanarFiniteTriangleInducedWiredBoundaryProbability_eq
    (n : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    triHexPlanarFiniteTriangleInducedWiredBoundaryProbability (n + 1) p q =
      triHexPlanarFiniteTriangleWiredBoundaryProbability (n + 1) p q := by
  rw [triHexPlanarFiniteTriangleInducedWiredBoundaryProbability,
    ← activeBCMean_boundaryClique_eq_wired
      (triHexPlanarFiniteTriangleInducedGraph (n + 1))
      (triHexPlanarFiniteBoundary (n + 1)) hp hp1 hq]
  rw [triHexPlanarFiniteTriangleWiredBoundaryProbability,
    ← wiredActiveRatio_eq_wiredFkProb_lift
      (triHexPlanarFiniteTriangleGraph (n + 1))
      (triHexPlanarFiniteBoundary (n + 1)) hp hp1 hq]
  rw [show triHexPlanarFiniteTriangleInducedBoundaryReachIndicator (n + 1) =
      fun eta => triHexPlanarFiniteTriangleBoundaryReachIndicator (n + 1)
        (activeGraphRestrict
          (triHexPlanarFiniteTriangleGraph (n + 1))
          (triHexPlanarFiniteTriangleInducedGraph (n + 1))
          (triHexPlanarFiniteTriangleGraph_le_induced (n + 1)) eta) by
    funext eta
    exact triHexPlanarFiniteTriangleInducedBoundaryReachIndicator_eq n eta]
  rw [activeBCMean_eq_of_le_sup_boundaryClique
    (triHexPlanarFiniteTriangleGraph (n + 1))
    (triHexPlanarFiniteTriangleInducedGraph (n + 1))
    (triHexPlanarFiniteBoundary (n + 1))
    (triHexPlanarFiniteTriangleGraph_le_induced (n + 1))
    (by simpa [triHexPlanarFiniteTriangleInducedGraph] using
      triHexPlanarFiniteTriangle_induced_le_wiredGraph (n + 1))]
  rw [activeBCMean_eq_div]
  unfold wiredActiveRatio wiredActiveNumer wiredActiveZ wiredActiveWeight
    activeBCNumer activeBCZ activeBCWeight wiredFkWeight
  simp only [numClustersBC_boundaryClique]
  rfl





theorem triHexPlanarFiniteInducedWiredBoundaryProbability_eq_homogeneous
    (n : Nat) {q p : Real} (hq : 0 < q)
    (hp : p ∈ Set.Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0) :
    triHexPlanarFiniteStarWiredBoundaryProbability (n + 1)
        (BeffaraDC.dualParam p q) q =
      triHexPlanarFiniteTriangleInducedWiredBoundaryProbability (n + 1) p q := by
  rw [triHexPlanarFiniteTriangleInducedWiredBoundaryProbability_eq
    n hp.1 hp.2 hq]
  exact triHexPlanarFiniteWiredBoundaryProbability_eq_homogeneous
    (n + 1) hq hp hsurface




def triHexPlanarFiniteStarToHexBuffered (n : Nat) :
    TriHexPlanarFiniteStarVertex n ↪ hexagonal.BufferedVertex (n + 2) where
  toFun v := ⟨triHexPlanarFiniteStarVertexEmbedding n v, by
    apply hexagonal.orbitBox_mono
      ((Nat.succ_le_succ (Nat.le_succ n)).trans
        (hexagonal.id_le_bufferedRadius (n + 2)))
    exact triHexPlanarFiniteStar_range_subset_orbitBox_succ n ⟨v, rfl⟩⟩
  inj' x y h := (triHexPlanarFiniteStarVertexEmbedding n).injective
    (congrArg Subtype.val h)

theorem triHexPlanarFiniteStarToHexBuffered_adjMatch (n : Nat) :
    ocd_AdjMatch (triHexPlanarFiniteStarGraph n)
      (hexagonal.bufferedGraph (n + 2))
      (triHexPlanarFiniteStarToHexBuffered n) := by
  intro x y
  exact triHexPlanarFiniteStarGraph_adj_iff_hexagonal n x y

theorem triHexPlanarFiniteStarToHexBuffered_not_boundary
    (n : Nat) (v : TriHexPlanarFiniteStarVertex n) :
    ¬ hexagonal.bufferedBoundary (n + 2)
      (triHexPlanarFiniteStarToHexBuffered n v) := by
  let vPrev : hexagonal.BufferedVertex (n + 1) :=
    ⟨triHexPlanarFiniteStarVertexEmbedding n v, by
      apply hexagonal.orbitBox_mono (hexagonal.id_le_bufferedRadius (n + 1))
      exact triHexPlanarFiniteStar_range_subset_orbitBox_succ n ⟨v, rfl⟩⟩
  have hnot := hexagonal.not_bufferedBoundary_incl_succ (n + 1) vPrev
  simpa [triHexPlanarFiniteStarToHexBuffered, vPrev, Nat.add_assoc] using hnot

theorem triHexPlanarFiniteStar_boundary_of_outsideGraph_adj
    (n : Nat) (psi : ConfigSpace
      (Sym2 (hexagonal.BufferedVertex (n + 2))))
    (x : TriHexPlanarFiniteStarVertex n)
    {c : hexagonal.BufferedVertex (n + 2)}
    (h : (ocd_outsideGraph (hexagonal.bufferedGraph (n + 2))
      (triHexPlanarFiniteStarToHexBuffered n)
      (hexagonal.bufferedBoundary (n + 2)) psi).Adj
        (triHexPlanarFiniteStarToHexBuffered n x) c) :
    triHexPlanarFiniteStarBoundary n x := by
  rw [ocd_outsideGraph_adj] at h
  rcases h with ⟨hadj, _, hnotRange⟩ | ⟨_, houter, _⟩
  · apply (triHexPlanarFiniteStar_boundary_iff_ambient n x).2
    refine ⟨c.1, hadj, ?_⟩
    rintro ⟨z, hz⟩
    apply hnotRange
    refine ⟨s(x, z), ?_⟩
    rw [ocd_innerEdge_mk]
    congr 1
    exact Subtype.ext hz
  · exact (triHexPlanarFiniteStarToHexBuffered_not_boundary n x houter).elim

theorem triHexPlanarFiniteStar_inducedWiring_le
    (n : Nat) (psi : ConfigSpace
      (Sym2 (hexagonal.BufferedVertex (n + 2)))) :
    ocd_inducedWiring (hexagonal.bufferedGraph (n + 2))
        (triHexPlanarFiniteStarToHexBuffered n)
        (hexagonal.bufferedBoundary (n + 2)) psi ≤
      boundaryCliqueGraph (triHexPlanarFiniteStarBoundary n) := by
  intro x y hxy
  obtain ⟨hne, hreach⟩ := hxy
  rw [boundaryCliqueGraph_adj]
  refine ⟨hne, ?_, ?_⟩
  · have hne' : triHexPlanarFiniteStarToHexBuffered n x ≠
        triHexPlanarFiniteStarToHexBuffered n y :=
      fun h => hne ((triHexPlanarFiniteStarToHexBuffered n).injective h)
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    rcases hreach.cases_head with heq | ⟨c, hadj, _⟩
    · exact (hne' heq).elim
    · exact triHexPlanarFiniteStar_boundary_of_outsideGraph_adj n psi x hadj
  · have hreach' := hreach.symm
    have hne' : triHexPlanarFiniteStarToHexBuffered n y ≠
        triHexPlanarFiniteStarToHexBuffered n x :=
      fun h => hne ((triHexPlanarFiniteStarToHexBuffered n).injective h).symm
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach'
    rcases hreach'.cases_head with heq | ⟨c, hadj, _⟩
    · exact (hne' heq).elim
    · exact triHexPlanarFiniteStar_boundary_of_outsideGraph_adj n psi y hadj



theorem triHexPlanarFiniteStar_outerBuffered_dominated
    (n : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace
      (Sym2 (TriHexPlanarFiniteStarVertex n)))} (hA : IsIncreasing A) :
    (∑ rho,
        (ocd_innerRestrict (triHexPlanarFiniteStarToHexBuffered n) ⁻¹' A).indicator
          (fun _ => (1 : Real)) rho *
        wiredFkProb (hexagonal.bufferedGraph (n + 2))
          (hexagonal.bufferedBoundary (n + 2)) p q rho) ≤
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        wiredFkProb (triHexPlanarFiniteStarGraph n)
          (triHexPlanarFiniteStarBoundary n) p q omega := by
  have h := ocd_wired_inner_dominated_bcProb
    (triHexPlanarFiniteStarToHexBuffered n).injective
    (triHexPlanarFiniteStarToHexBuffered_adjMatch n)
    (triHexPlanarFiniteStarBoundary n) hp hp1 hq
    (triHexPlanarFiniteStar_inducedWiring_le n) hA
  simpa only [bcProb_clique_eq_wiredFkProb] using h



def triHexPlanarHexBufferedOuterStarLevel (n : Nat) : Nat :=
  hexagonal.bufferedRadius (n + 1) + 1



noncomputable def triHexPlanarHexBufferedToFiniteStar (n : Nat) :
    hexagonal.BufferedVertex n ↪
      TriHexPlanarFiniteStarVertex
        (triHexPlanarHexBufferedOuterStarLevel n) where
  toFun v := Classical.choose
    (hexagonal_orbitBox_subset_triHexPlanarFiniteStar_range_succ
      (hexagonal.bufferedRadius (n + 1))
      (hexagonal.orbitBox_mono
        (hexagonal.bufferedRadius_strictMono.monotone (Nat.le_succ n)) v.2))
  inj' x y h := by
    apply Subtype.ext
    have hx := Classical.choose_spec
      (hexagonal_orbitBox_subset_triHexPlanarFiniteStar_range_succ
        (hexagonal.bufferedRadius (n + 1))
        (hexagonal.orbitBox_mono
          (hexagonal.bufferedRadius_strictMono.monotone (Nat.le_succ n)) x.2))
    have hy := Classical.choose_spec
      (hexagonal_orbitBox_subset_triHexPlanarFiniteStar_range_succ
        (hexagonal.bufferedRadius (n + 1))
        (hexagonal.orbitBox_mono
          (hexagonal.bufferedRadius_strictMono.monotone (Nat.le_succ n)) y.2))
    exact hx.symm.trans ((congrArg
      (triHexPlanarFiniteStarVertexEmbedding
        (hexagonal.bufferedRadius (n + 1) + 1)) h).trans hy)

theorem triHexPlanarHexBufferedToFiniteStar_embedding_eq
    (n : Nat) (v : hexagonal.BufferedVertex n) :
    triHexPlanarFiniteStarVertexEmbedding
        (triHexPlanarHexBufferedOuterStarLevel n)
        (triHexPlanarHexBufferedToFiniteStar n v) = v.1 :=
  by
    simpa [triHexPlanarHexBufferedOuterStarLevel,
      triHexPlanarHexBufferedToFiniteStar] using
      (Classical.choose_spec
        (hexagonal_orbitBox_subset_triHexPlanarFiniteStar_range_succ
          (hexagonal.bufferedRadius (n + 1))
          (hexagonal.orbitBox_mono
            (hexagonal.bufferedRadius_strictMono.monotone
              (Nat.le_succ n)) v.2)))

theorem triHexPlanarHexBufferedToFiniteStar_adjMatch (n : Nat) :
    ocd_AdjMatch (hexagonal.bufferedGraph n)
      (triHexPlanarFiniteStarGraph
        (triHexPlanarHexBufferedOuterStarLevel n))
      (triHexPlanarHexBufferedToFiniteStar n) := by
  intro x y
  rw [triHexPlanarFiniteStarGraph_adj_iff_hexagonal]
  rw [triHexPlanarHexBufferedToFiniteStar_embedding_eq,
    triHexPlanarHexBufferedToFiniteStar_embedding_eq]
  rfl

theorem triHexPlanarHexBufferedToFiniteStar_not_boundary
    (n : Nat) (v : hexagonal.BufferedVertex n) :
    ¬ triHexPlanarFiniteStarBoundary
      (triHexPlanarHexBufferedOuterStarLevel n)
      (triHexPlanarHexBufferedToFiniteStar n v) := by
  rw [triHexPlanarFiniteStar_boundary_iff_ambient]
  rintro ⟨w, hadj, hw⟩
  rw [triHexPlanarHexBufferedToFiniteStar_embedding_eq] at hadj
  apply hw
  apply hexagonal_orbitBox_subset_triHexPlanarFiniteStar_range_succ
    (hexagonal.bufferedRadius (n + 1))
  exact hexagonal.neighbor_mem_buffered_succ n v.2 hadj

theorem triHexPlanarHexBuffered_boundary_of_outsideGraph_adj
    (n : Nat) (psi : ConfigSpace
      (Sym2 (TriHexPlanarFiniteStarVertex
        (triHexPlanarHexBufferedOuterStarLevel n))))
    (x : hexagonal.BufferedVertex n)
    {c : TriHexPlanarFiniteStarVertex
      (triHexPlanarHexBufferedOuterStarLevel n)}
    (h : (ocd_outsideGraph
      (triHexPlanarFiniteStarGraph
        (triHexPlanarHexBufferedOuterStarLevel n))
      (triHexPlanarHexBufferedToFiniteStar n)
      (triHexPlanarFiniteStarBoundary
        (triHexPlanarHexBufferedOuterStarLevel n)) psi).Adj
        (triHexPlanarHexBufferedToFiniteStar n x) c) :
    hexagonal.bufferedBoundary n x := by
  rw [ocd_outsideGraph_adj] at h
  rcases h with ⟨hadj, _, hnotRange⟩ | ⟨_, houter, _⟩
  · refine ⟨triHexPlanarFiniteStarVertexEmbedding
      (triHexPlanarHexBufferedOuterStarLevel n) c, ?_, ?_⟩
    · rw [← triHexPlanarHexBufferedToFiniteStar_embedding_eq n x]
      exact triHexPlanarFiniteStarGraph_adj_hexagonal _ hadj
    · intro hc
      apply hnotRange
      let z : hexagonal.BufferedVertex n :=
        ⟨triHexPlanarFiniteStarVertexEmbedding
            (triHexPlanarHexBufferedOuterStarLevel n) c, hc⟩
      refine ⟨s(x, z), ?_⟩
      rw [ocd_innerEdge_mk]
      congr 1
      apply (triHexPlanarFiniteStarVertexEmbedding
        (triHexPlanarHexBufferedOuterStarLevel n)).injective
      rw [triHexPlanarHexBufferedToFiniteStar_embedding_eq]
  · exact (triHexPlanarHexBufferedToFiniteStar_not_boundary n x houter).elim

theorem triHexPlanarHexBuffered_inducedWiring_le
    (n : Nat) (psi : ConfigSpace
      (Sym2 (TriHexPlanarFiniteStarVertex
        (triHexPlanarHexBufferedOuterStarLevel n)))) :
    ocd_inducedWiring
        (triHexPlanarFiniteStarGraph
          (triHexPlanarHexBufferedOuterStarLevel n))
        (triHexPlanarHexBufferedToFiniteStar n)
        (triHexPlanarFiniteStarBoundary
          (triHexPlanarHexBufferedOuterStarLevel n)) psi ≤
      boundaryCliqueGraph (hexagonal.bufferedBoundary n) := by
  intro x y hxy
  obtain ⟨hne, hreach⟩ := hxy
  rw [boundaryCliqueGraph_adj]
  refine ⟨hne, ?_, ?_⟩
  · have hne' : triHexPlanarHexBufferedToFiniteStar n x ≠
        triHexPlanarHexBufferedToFiniteStar n y :=
      fun h => hne ((triHexPlanarHexBufferedToFiniteStar n).injective h)
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    rcases hreach.cases_head with heq | ⟨c, hadj, _⟩
    · exact (hne' heq).elim
    · exact triHexPlanarHexBuffered_boundary_of_outsideGraph_adj n psi x hadj
  · have hreach' := hreach.symm
    have hne' : triHexPlanarHexBufferedToFiniteStar n y ≠
        triHexPlanarHexBufferedToFiniteStar n x :=
      fun h => hne ((triHexPlanarHexBufferedToFiniteStar n).injective h).symm
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach'
    rcases hreach'.cases_head with heq | ⟨c, hadj, _⟩
    · exact (hne' heq).elim
    · exact triHexPlanarHexBuffered_boundary_of_outsideGraph_adj n psi y hadj



theorem triHexPlanarHexBuffered_outerStar_dominated
    (n : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace
      (Sym2 (hexagonal.BufferedVertex n)))} (hA : IsIncreasing A) :
    (∑ rho,
        (ocd_innerRestrict (triHexPlanarHexBufferedToFiniteStar n) ⁻¹' A).indicator
          (fun _ => (1 : Real)) rho *
        wiredFkProb
          (triHexPlanarFiniteStarGraph
            (triHexPlanarHexBufferedOuterStarLevel n))
          (triHexPlanarFiniteStarBoundary
            (triHexPlanarHexBufferedOuterStarLevel n)) p q rho) ≤
      ∑ omega, A.indicator (fun _ => (1 : Real)) omega *
        wiredFkProb (hexagonal.bufferedGraph n)
          (hexagonal.bufferedBoundary n) p q omega := by
  have h := ocd_wired_inner_dominated_bcProb
    (triHexPlanarHexBufferedToFiniteStar n).injective
    (triHexPlanarHexBufferedToFiniteStar_adjMatch n)
    (hexagonal.bufferedBoundary n) hp hp1 hq
    (triHexPlanarHexBuffered_inducedWiring_le n) hA
  simpa only [bcProb_clique_eq_wiredFkProb] using h




def triHexPlanarHexWhiteRoot : HexVertex := (hexagonalStep 0, true)


def triHexPlanarFiniteStarRoot (n : Nat) :
    TriHexPlanarFiniteStarVertex n :=
  Sum.inr (triHexPlanarFiniteTerminalMap n
    (triHexPlanarFiniteRootCell n) 0)

@[simp] theorem triHexPlanarFiniteStarRoot_embedding
    (n : Nat) :
    triHexPlanarFiniteStarVertexEmbedding n
      (triHexPlanarFiniteStarRoot n) = triHexPlanarHexWhiteRoot := by
  apply Prod.ext
  · ext k
    fin_cases k <;>
      simp [triHexPlanarFiniteStarRoot, triHexPlanarHexWhiteRoot,
        triHexPlanarFiniteTerminalMap, triHexPlanarFiniteRootCell,
        triHexPlanarCellTerminal, hexagonalStep]
  · rfl


def triHexPlanarHexWhiteBufferedRoot (n : Nat) :
    hexagonal.BufferedVertex (n + 1) :=
  ⟨triHexPlanarHexWhiteRoot, by
    apply hexagonal.orbitBox_mono
      ((Nat.succ_le_succ (Nat.zero_le n)).trans
        (hexagonal.id_le_bufferedRadius (n + 1)))
    rw [hexagonal_mem_orbitBox_iff_box]
    intro k
    fin_cases k <;> simp [triHexPlanarHexWhiteRoot, hexagonalStep]⟩

theorem triHexPlanarFiniteStarToHexBuffered_root (n : Nat) :
    triHexPlanarFiniteStarToHexBuffered n
        (triHexPlanarFiniteStarRoot n) =
      triHexPlanarHexWhiteBufferedRoot (n + 1) := by
  apply Subtype.ext
  exact triHexPlanarFiniteStarRoot_embedding n

def triHexPlanarFiniteStarRootBoundaryEvent (n : Nat) :
    Set (ConfigSpace (Sym2 (TriHexPlanarFiniteStarVertex n))) :=
  finiteRootBoundaryEvent (triHexPlanarFiniteStarGraph n)
    (triHexPlanarFiniteStarBoundary n) (triHexPlanarFiniteStarRoot n)

def triHexPlanarHexWhiteBufferedRootBoundaryEvent (n : Nat) :
    Set (ConfigSpace (Sym2 (hexagonal.BufferedVertex (n + 1)))) :=
  finiteRootBoundaryEvent (hexagonal.bufferedGraph (n + 1))
    (hexagonal.bufferedBoundary (n + 1))
    (triHexPlanarHexWhiteBufferedRoot n)

theorem triHexPlanarFiniteStarToHexBuffered_cross_boundary
    (n : Nat) (x : TriHexPlanarFiniteStarVertex n)
    (c : hexagonal.BufferedVertex (n + 2))
    (hadj : (hexagonal.bufferedGraph (n + 2)).Adj
      (triHexPlanarFiniteStarToHexBuffered n x) c)
    (hc : c ∉ Set.range (triHexPlanarFiniteStarToHexBuffered n)) :
    triHexPlanarFiniteStarBoundary n x := by
  apply (triHexPlanarFiniteStar_boundary_iff_ambient n x).2
  refine ⟨c.1, hadj, ?_⟩
  rintro ⟨z, hz⟩
  apply hc
  refine ⟨z, Subtype.ext hz⟩

theorem triHexPlanarHexWhiteBuffered_outerEvent_subset_starRestrict
    (n : Nat) :
    triHexPlanarHexWhiteBufferedRootBoundaryEvent (n + 1) ⊆
      ocd_innerRestrict (triHexPlanarFiniteStarToHexBuffered n) ⁻¹'
        triHexPlanarFiniteStarRootBoundaryEvent n := by
  simpa only [triHexPlanarHexWhiteBufferedRootBoundaryEvent,
    triHexPlanarFiniteStarRootBoundaryEvent,
    triHexPlanarFiniteStarToHexBuffered_root] using
    outerRootBoundaryEvent_subset_innerRestrict
      (triHexPlanarFiniteStarGraph n)
      (hexagonal.bufferedGraph (n + 2))
      (triHexPlanarFiniteStarToHexBuffered n)
      (triHexPlanarFiniteStarBoundary n)
      (hexagonal.bufferedBoundary (n + 2))
      (triHexPlanarFiniteStarToHexBuffered_adjMatch n)
      (triHexPlanarFiniteStarToHexBuffered_not_boundary n)
      (triHexPlanarFiniteStarToHexBuffered_cross_boundary n)
      (triHexPlanarFiniteStarRoot n)

theorem triHexPlanarHexBufferedToFiniteStar_root (n : Nat) :
    triHexPlanarHexBufferedToFiniteStar (n + 1)
        (triHexPlanarHexWhiteBufferedRoot n) =
      triHexPlanarFiniteStarRoot
        (triHexPlanarHexBufferedOuterStarLevel (n + 1)) := by
  apply (triHexPlanarFiniteStarVertexEmbedding
    (triHexPlanarHexBufferedOuterStarLevel (n + 1))).injective
  rw [triHexPlanarHexBufferedToFiniteStar_embedding_eq,
    triHexPlanarFiniteStarRoot_embedding]
  rfl

theorem triHexPlanarHexBufferedToFiniteStar_cross_boundary
    (n : Nat) (x : hexagonal.BufferedVertex n)
    (c : TriHexPlanarFiniteStarVertex
      (triHexPlanarHexBufferedOuterStarLevel n))
    (hadj : (triHexPlanarFiniteStarGraph
      (triHexPlanarHexBufferedOuterStarLevel n)).Adj
        (triHexPlanarHexBufferedToFiniteStar n x) c)
    (hc : c ∉ Set.range (triHexPlanarHexBufferedToFiniteStar n)) :
    hexagonal.bufferedBoundary n x := by
  refine ⟨triHexPlanarFiniteStarVertexEmbedding
      (triHexPlanarHexBufferedOuterStarLevel n) c, ?_, ?_⟩
  · rw [← triHexPlanarHexBufferedToFiniteStar_embedding_eq n x]
    exact triHexPlanarFiniteStarGraph_adj_hexagonal _ hadj
  · intro hw
    apply hc
    let z : hexagonal.BufferedVertex n :=
      ⟨triHexPlanarFiniteStarVertexEmbedding
        (triHexPlanarHexBufferedOuterStarLevel n) c, hw⟩
    refine ⟨z, ?_⟩
    apply (triHexPlanarFiniteStarVertexEmbedding
      (triHexPlanarHexBufferedOuterStarLevel n)).injective
    rw [triHexPlanarHexBufferedToFiniteStar_embedding_eq]

theorem triHexPlanarFiniteStar_outerEvent_subset_hexBufferedRestrict
    (n : Nat) :
    triHexPlanarFiniteStarRootBoundaryEvent
        (triHexPlanarHexBufferedOuterStarLevel (n + 1)) ⊆
      ocd_innerRestrict (triHexPlanarHexBufferedToFiniteStar (n + 1)) ⁻¹'
        triHexPlanarHexWhiteBufferedRootBoundaryEvent n := by
  simpa only [triHexPlanarHexWhiteBufferedRootBoundaryEvent,
    triHexPlanarFiniteStarRootBoundaryEvent,
    triHexPlanarHexBufferedToFiniteStar_root] using
    outerRootBoundaryEvent_subset_innerRestrict
      (hexagonal.bufferedGraph (n + 1))
      (triHexPlanarFiniteStarGraph
        (triHexPlanarHexBufferedOuterStarLevel (n + 1)))
      (triHexPlanarHexBufferedToFiniteStar (n + 1))
      (hexagonal.bufferedBoundary (n + 1))
      (triHexPlanarFiniteStarBoundary
        (triHexPlanarHexBufferedOuterStarLevel (n + 1)))
      (triHexPlanarHexBufferedToFiniteStar_adjMatch (n + 1))
      (triHexPlanarHexBufferedToFiniteStar_not_boundary (n + 1))
      (triHexPlanarHexBufferedToFiniteStar_cross_boundary (n + 1))
      (triHexPlanarHexWhiteBufferedRoot n)

theorem triHexPlanarFiniteStarWiredBoundaryProbability_eq_eventMass
    (n : Nat) {p q : Real} :
    triHexPlanarFiniteStarWiredBoundaryProbability n p q =
      finiteWiredEventMass (triHexPlanarFiniteStarGraph n)
        (triHexPlanarFiniteStarBoundary n) p q
        (triHexPlanarFiniteStarRootBoundaryEvent n) := by
  classical
  unfold triHexPlanarFiniteStarWiredBoundaryProbability
    finiteWiredEventMass
  apply Finset.sum_congr rfl
  intro omega _
  congr 1
  unfold triHexPlanarFiniteStarBoundaryReachIndicator
  have hgraph := openSub_extendActive_restrictActive_eq
    (triHexPlanarFiniteStarGraph n) omega
  have hiff : (∃ y : TriHexPlanarFiniteTerminal n,
      triHexPlanarFiniteBoundary n y ∧
      (openSub (triHexPlanarFiniteStarGraph n)
        (extendActive (triHexPlanarFiniteStarGraph n)
          (restrictActive (triHexPlanarFiniteStarGraph n) omega))).Reachable
        (Sum.inr (triHexPlanarFiniteTerminalMap n
          (triHexPlanarFiniteRootCell n) 0)) (Sum.inr y)) ↔
    ∃ y, triHexPlanarFiniteStarBoundary n y ∧
      (openSub (triHexPlanarFiniteStarGraph n) omega).Reachable
        (Sum.inr (triHexPlanarFiniteTerminalMap n
          (triHexPlanarFiniteRootCell n) 0)) y := by
    rw [hgraph]
    constructor
    · rintro ⟨y, hy, hreach⟩
      exact ⟨Sum.inr y, hy, hreach⟩
    · rintro ⟨y, hy, hreach⟩
      rcases y with z | y
      · exact hy.elim
      · exact ⟨y, hy, hreach⟩
  have hiff' : (∃ y : TriHexPlanarFiniteTerminal n,
      triHexPlanarFiniteBoundary n y ∧
      (openSub (triHexPlanarFiniteStarGraph n)
        (extendActive (triHexPlanarFiniteStarGraph n)
          (restrictActive (triHexPlanarFiniteStarGraph n) omega))).Reachable
        (Sum.inr (triHexPlanarFiniteTerminalMap n
          (triHexPlanarFiniteRootCell n) 0)) (Sum.inr y)) ↔
      omega ∈ triHexPlanarFiniteStarRootBoundaryEvent n := by
    rw [hiff]
    rfl
  rw [if_congr hiff' rfl rfl]
  simp only [Set.indicator]



theorem triHexPlanarHexWhiteBuffered_mass_le_star
    (n : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    finiteWiredEventMass (hexagonal.bufferedGraph (n + 2))
        (hexagonal.bufferedBoundary (n + 2)) p q
        (triHexPlanarHexWhiteBufferedRootBoundaryEvent (n + 1)) ≤
      triHexPlanarFiniteStarWiredBoundaryProbability n p q := by
  rw [triHexPlanarFiniteStarWiredBoundaryProbability_eq_eventMass]
  calc
    finiteWiredEventMass (hexagonal.bufferedGraph (n + 2))
        (hexagonal.bufferedBoundary (n + 2)) p q
        (triHexPlanarHexWhiteBufferedRootBoundaryEvent (n + 1)) ≤
      finiteWiredEventMass (hexagonal.bufferedGraph (n + 2))
        (hexagonal.bufferedBoundary (n + 2)) p q
        (ocd_innerRestrict (triHexPlanarFiniteStarToHexBuffered n) ⁻¹'
          triHexPlanarFiniteStarRootBoundaryEvent n) :=
      finiteWiredEventMass_mono _ _ hp hp1 (zero_lt_one.trans_le hq)
        (triHexPlanarHexWhiteBuffered_outerEvent_subset_starRestrict n)
    _ ≤ finiteWiredEventMass (triHexPlanarFiniteStarGraph n)
        (triHexPlanarFiniteStarBoundary n) p q
        (triHexPlanarFiniteStarRootBoundaryEvent n) := by
      simpa only [finiteWiredEventMass] using
        triHexPlanarFiniteStar_outerBuffered_dominated n hp hp1 hq
          (finiteRootBoundaryEvent_isIncreasing _ _ _)



theorem triHexPlanarFiniteStar_le_hexWhiteBuffered_mass
    (n : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    triHexPlanarFiniteStarWiredBoundaryProbability
        (triHexPlanarHexBufferedOuterStarLevel (n + 1)) p q ≤
      finiteWiredEventMass (hexagonal.bufferedGraph (n + 1))
        (hexagonal.bufferedBoundary (n + 1)) p q
        (triHexPlanarHexWhiteBufferedRootBoundaryEvent n) := by
  rw [triHexPlanarFiniteStarWiredBoundaryProbability_eq_eventMass]
  calc
    finiteWiredEventMass
        (triHexPlanarFiniteStarGraph
          (triHexPlanarHexBufferedOuterStarLevel (n + 1)))
        (triHexPlanarFiniteStarBoundary
          (triHexPlanarHexBufferedOuterStarLevel (n + 1))) p q
        (triHexPlanarFiniteStarRootBoundaryEvent
          (triHexPlanarHexBufferedOuterStarLevel (n + 1))) ≤
      finiteWiredEventMass
        (triHexPlanarFiniteStarGraph
          (triHexPlanarHexBufferedOuterStarLevel (n + 1)))
        (triHexPlanarFiniteStarBoundary
          (triHexPlanarHexBufferedOuterStarLevel (n + 1))) p q
        (ocd_innerRestrict
          (triHexPlanarHexBufferedToFiniteStar (n + 1)) ⁻¹'
          triHexPlanarHexWhiteBufferedRootBoundaryEvent n) :=
      finiteWiredEventMass_mono _ _ hp hp1 (zero_lt_one.trans_le hq)
        (triHexPlanarFiniteStar_outerEvent_subset_hexBufferedRestrict n)
    _ ≤ finiteWiredEventMass (hexagonal.bufferedGraph (n + 1))
        (hexagonal.bufferedBoundary (n + 1)) p q
        (triHexPlanarHexWhiteBufferedRootBoundaryEvent n) := by
      simpa only [finiteWiredEventMass] using
        triHexPlanarHexBuffered_outerStar_dominated (n + 1) hp hp1 hq
          (finiteRootBoundaryEvent_isIncreasing _ _ _)

theorem triHexPlanarHexWhiteBufferedRootBoundaryEvent_eq_setBoundary
    (n : Nat) :
    triHexPlanarHexWhiteBufferedRootBoundaryEvent n =
      hexagonal.bufferedSetBoundaryEvent
        ({triHexPlanarHexWhiteRoot} : Set HexVertex) (n + 1) := by
  ext eta
  constructor
  · rintro ⟨y, hy, hreach⟩
    exact ⟨triHexPlanarHexWhiteBufferedRoot n, Set.mem_singleton _,
      y, hy, hreach⟩
  · rintro ⟨x, hx, y, hy, hreach⟩
    have hx' : x = triHexPlanarHexWhiteBufferedRoot n := by
      apply Subtype.ext
      simpa only [Set.mem_singleton_iff] using hx
    subst x
    exact ⟨y, hy, hreach⟩

theorem triHexPlanarHexWhiteBuffered_eventMass_eq_measure
    (n : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    finiteWiredEventMass (hexagonal.bufferedGraph (n + 1))
        (hexagonal.bufferedBoundary (n + 1)) p q
        (triHexPlanarHexWhiteBufferedRootBoundaryEvent n) =
      (hexagonal.wiredBufferedMeasure (n + 1) hp hp1 hq :
        Measure (ConfigSpace (Sym2 HexVertex))).real
        (hexagonal.bufferedCylinder (n + 1)
          (hexagonal.bufferedSetBoundaryEvent
            ({triHexPlanarHexWhiteRoot} : Set HexVertex) (n + 1))) := by
  rw [hexagonal.wiredBufferedMeasure_real_cylinder (le_refl (n + 1))
    hp hp1 hq]
  unfold finiteWiredEventMass
  rw [triHexPlanarHexWhiteBufferedRootBoundaryEvent_eq_setBoundary]
  apply Finset.sum_congr rfl
  intro omega _
  rfl

theorem triHexPlanarHexWhiteBuffered_eventMass_tendsto
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto
      (fun n => finiteWiredEventMass (hexagonal.bufferedGraph (n + 1))
        (hexagonal.bufferedBoundary (n + 1)) p q
        (triHexPlanarHexWhiteBufferedRootBoundaryEvent n)) atTop
      (nhds ((hexagonal.wiredBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real
          (hexagonal.setHitsInfinite
            ({triHexPlanarHexWhiteRoot} : Set HexVertex)))) := by
  have hdiag := hexagonal.wiredBufferedSetBoundary_diag_tendsto
    ({triHexPlanarHexWhiteRoot} : Set HexVertex) (Set.finite_singleton _)
    1 (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact (triHexPlanarHexWhiteBufferedRoot 0).2)
    hp hp1 hq
  apply hdiag.congr'
  filter_upwards with n
  rw [triHexPlanarHexWhiteBuffered_eventMass_eq_measure n hp hp1
    (zero_lt_one.trans_le hq)]
  rw [Nat.one_add]

theorem triHexPlanarHexStarCofinalLevel_tendsto :
    Tendsto (fun n => triHexPlanarHexBufferedOuterStarLevel (n + 1))
      atTop atTop := by
  apply StrictMono.tendsto_atTop
  intro a b hab
  unfold triHexPlanarHexBufferedOuterStarLevel
  exact Nat.add_lt_add_right
    (hexagonal.bufferedRadius_strictMono
      (Nat.add_lt_add_right (Nat.add_lt_add_right hab 1) 1)) 1



theorem triHexPlanarFiniteStar_cofinal_tendsto_hexWhiteInfinite
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto
      (fun n => triHexPlanarFiniteStarWiredBoundaryProbability
        (triHexPlanarHexBufferedOuterStarLevel (n + 1)) p q) atTop
      (nhds ((hexagonal.wiredBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real
          (hexagonal.setHitsInfinite
            ({triHexPlanarHexWhiteRoot} : Set HexVertex)))) := by
  let c := fun n => finiteWiredEventMass (hexagonal.bufferedGraph (n + 1))
    (hexagonal.bufferedBoundary (n + 1)) p q
    (triHexPlanarHexWhiteBufferedRootBoundaryEvent n)
  have hc := triHexPlanarHexWhiteBuffered_eventMass_tendsto hp hp1 hq
  have hindex : Tendsto
      (fun n => triHexPlanarHexBufferedOuterStarLevel (n + 1) + 1)
      atTop atTop :=
    (tendsto_add_atTop_nat 1).comp
      triHexPlanarHexStarCofinalLevel_tendsto
  have hlo : Tendsto
      (fun n => c (triHexPlanarHexBufferedOuterStarLevel (n + 1) + 1))
      atTop _ := hc.comp hindex
  have hhi : Tendsto c atTop _ := hc
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards with n
    exact triHexPlanarHexWhiteBuffered_mass_le_star
      (triHexPlanarHexBufferedOuterStarLevel (n + 1)) hp hp1 hq
  · filter_upwards with n
    exact triHexPlanarFiniteStar_le_hexWhiteBuffered_mass n hp hp1 hq





theorem triHexPlanarFiniteBoundary_of_triangular_adj_not_terminal
    (n : Nat) (v : TriHexPlanarFiniteTerminal n) (w : Site 2)
    (hvw : triangularGraph.Adj v.1 w)
    (hw : w ∉ triHexPlanarFiniteTerminalFinset n) :
    triHexPlanarFiniteBoundary n v := by
  let e : triangularGraph.edgeSet := ⟨s(v.1, w), by
    rwa [SimpleGraph.mem_edgeSet]⟩
  let a := triangularEdgeChartEquiv.symm e
  rcases hpair : triHexPlanarTriangleIndexEquiv.symm a with ⟨z, i⟩
  have ha : triHexPlanarTriangleIndexEquiv (z, i) = a := by
    rw [← hpair]
    exact triHexPlanarTriangleIndexEquiv.apply_symm_apply a
  have hchart : triangularIndexedEdge a = s(v.1, w) :=
    congrArg Subtype.val (triangularEdgeChartEquiv.apply_symm_apply e)
  have hedge :
      s(triHexPlanarCellTerminal z (triHexTriangleEdgeTerminal1 i),
        triHexPlanarCellTerminal z (triHexTriangleEdgeTerminal2 i)) =
          s(v.1, w) := by
    rw [← hchart, ← ha]
    exact (triangularIndexedEdge_rebase_eq_cellEdge z i).symm
  have hz : z ∉ box 2 n := by
    intro hz
    rw [Sym2.eq_iff] at hedge
    rcases hedge with ⟨_, hwEq⟩ | ⟨hwEq, _⟩
    · apply hw
      apply Finset.mem_image.mpr
      exact ⟨(z, triHexTriangleEdgeTerminal2 i),
        Finset.mem_product.mpr ⟨by simpa using hz, Finset.mem_univ _⟩, hwEq⟩
    · apply hw
      apply Finset.mem_image.mpr
      exact ⟨(z, triHexTriangleEdgeTerminal1 i),
        Finset.mem_product.mpr ⟨by simpa using hz, Finset.mem_univ _⟩, hwEq⟩
  rw [Sym2.eq_iff] at hedge
  rcases hedge with ⟨hv, _⟩ | ⟨_, hv⟩
  · refine ⟨triHexTriangleEdgeTerminal1 i, ?_⟩
    change v.1 - hexagonalStep (triHexTriangleEdgeTerminal1 i) ∉ box 2 n
    rw [← hv]
    simpa [triHexPlanarCellTerminal] using hz
  · refine ⟨triHexTriangleEdgeTerminal2 i, ?_⟩
    change v.1 - hexagonalStep (triHexTriangleEdgeTerminal2 i) ∉ box 2 n
    rw [← hv]
    simpa [triHexPlanarCellTerminal] using hz

def triHexPlanarFiniteTriangleToBuffered (n : Nat) :
    TriHexPlanarFiniteTerminal n ↪ triangular.BufferedVertex (n + 2) :=
  (Function.Embedding.refl (Site 2)).subtypeMap fun {v} hv => by
    apply triangular.orbitBox_mono
      ((Nat.succ_le_succ (Nat.le_succ n)).trans
        (triangular.id_le_bufferedRadius (n + 2)))
    exact triHexPlanarFiniteTerminal_subset_triangular_orbitBox_succ n ⟨v, hv⟩

theorem triHexPlanarFiniteTriangleToBuffered_adjMatch (n : Nat) :
    ocd_AdjMatch (triHexPlanarFiniteTriangleInducedGraph n)
      (triangular.bufferedGraph (n + 2))
      (triHexPlanarFiniteTriangleToBuffered n) := by
  intro x y
  rfl

theorem triHexPlanarFiniteTriangleToBuffered_not_boundary
    (n : Nat) (v : TriHexPlanarFiniteTerminal n) :
    ¬ triangular.bufferedBoundary (n + 2)
      (triHexPlanarFiniteTriangleToBuffered n v) := by
  let vPrev : triangular.BufferedVertex (n + 1) :=
    ⟨v.1, by
      apply triangular.orbitBox_mono (triangular.id_le_bufferedRadius (n + 1))
      exact triHexPlanarFiniteTerminal_subset_triangular_orbitBox_succ n v⟩
  have hnot := triangular.not_bufferedBoundary_incl_succ (n + 1) vPrev
  simpa [triHexPlanarFiniteTriangleToBuffered, vPrev, Nat.add_assoc] using hnot

theorem triHexPlanarFiniteTriangleToBuffered_cross_boundary
    (n : Nat) (v : TriHexPlanarFiniteTerminal n)
    (c : triangular.BufferedVertex (n + 2))
    (hadj : (triangular.bufferedGraph (n + 2)).Adj
      (triHexPlanarFiniteTriangleToBuffered n v) c)
    (hc : c ∉ Set.range (triHexPlanarFiniteTriangleToBuffered n)) :
    triHexPlanarFiniteBoundary n v := by
  apply triHexPlanarFiniteBoundary_of_triangular_adj_not_terminal n v c.1 hadj
  intro hcTerm
  apply hc
  exact ⟨⟨c.1, hcTerm⟩, Subtype.ext rfl⟩

theorem triHexPlanarFiniteTriangle_inducedWiring_le
    (n : Nat) (psi : ConfigSpace
      (Sym2 (triangular.BufferedVertex (n + 2)))) :
    ocd_inducedWiring (triangular.bufferedGraph (n + 2))
        (triHexPlanarFiniteTriangleToBuffered n)
        (triangular.bufferedBoundary (n + 2)) psi ≤
      boundaryCliqueGraph (triHexPlanarFiniteBoundary n) := by
  intro x y hxy
  obtain ⟨hne, hreach⟩ := hxy
  rw [boundaryCliqueGraph_adj]
  refine ⟨hne, ?_, ?_⟩
  · have hne' : triHexPlanarFiniteTriangleToBuffered n x ≠
        triHexPlanarFiniteTriangleToBuffered n y :=
      fun h => hne ((triHexPlanarFiniteTriangleToBuffered n).injective h)
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    rcases hreach.cases_head with heq | ⟨c, hadj, _⟩
    · exact (hne' heq).elim
    · rw [ocd_outsideGraph_adj] at hadj
      rcases hadj with ⟨ha, _, hr⟩ | ⟨_, hb, _⟩
      · exact triHexPlanarFiniteTriangleToBuffered_cross_boundary n x c ha
          (by rintro ⟨z, hz⟩; exact hr ⟨s(x, z), by
            rw [ocd_innerEdge_mk]; congr 1⟩)
      · exact (triHexPlanarFiniteTriangleToBuffered_not_boundary n x hb).elim
  · have hreach' := hreach.symm
    have hne' : triHexPlanarFiniteTriangleToBuffered n y ≠
        triHexPlanarFiniteTriangleToBuffered n x :=
      fun h => hne ((triHexPlanarFiniteTriangleToBuffered n).injective h).symm
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach'
    rcases hreach'.cases_head with heq | ⟨c, hadj, _⟩
    · exact (hne' heq).elim
    · rw [ocd_outsideGraph_adj] at hadj
      rcases hadj with ⟨ha, _, hr⟩ | ⟨_, hb, _⟩
      · exact triHexPlanarFiniteTriangleToBuffered_cross_boundary n y c ha
          (by rintro ⟨z, hz⟩; exact hr ⟨s(y, z), by
            rw [ocd_innerEdge_mk]; congr 1⟩)
      · exact (triHexPlanarFiniteTriangleToBuffered_not_boundary n y hb).elim

theorem triHexPlanarFiniteTriangle_outerBuffered_dominated
    (n : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace
      (Sym2 (TriHexPlanarFiniteTerminal n)))} (hA : IsIncreasing A) :
    finiteWiredEventMass (triangular.bufferedGraph (n + 2))
        (triangular.bufferedBoundary (n + 2)) p q
        (ocd_innerRestrict (triHexPlanarFiniteTriangleToBuffered n) ⁻¹' A) ≤
      finiteWiredEventMass (triHexPlanarFiniteTriangleInducedGraph n)
        (triHexPlanarFiniteBoundary n) p q A := by
  have h := ocd_wired_inner_dominated_bcProb
    (triHexPlanarFiniteTriangleToBuffered n).injective
    (triHexPlanarFiniteTriangleToBuffered_adjMatch n)
    (triHexPlanarFiniteBoundary n) hp hp1 hq
    (triHexPlanarFiniteTriangle_inducedWiring_le n) hA
  simpa only [bcProb_clique_eq_wiredFkProb, finiteWiredEventMass] using h

def triHexPlanarTriBufferedOuterLevel (n : Nat) : Nat :=
  triangular.bufferedRadius (n + 1) + 1

def triHexPlanarTriBufferedToFiniteTerminal (n : Nat) :
    triangular.BufferedVertex n ↪
      TriHexPlanarFiniteTerminal (triHexPlanarTriBufferedOuterLevel n) where
  toFun v := ⟨v.1, by
    apply triangular_orbitBox_subset_triHexPlanarFiniteTerminal_succ
      (triangular.bufferedRadius (n + 1))
    exact triangular.orbitBox_mono
      (triangular.bufferedRadius_strictMono.monotone (Nat.le_succ n)) v.2⟩
  inj' _ _ h := Subtype.ext
    (congrArg (fun z : TriHexPlanarFiniteTerminal
      (triHexPlanarTriBufferedOuterLevel n) => z.1) h)

theorem triHexPlanarTriBufferedToFiniteTerminal_adjMatch (n : Nat) :
    ocd_AdjMatch (triangular.bufferedGraph n)
      (triHexPlanarFiniteTriangleInducedGraph
        (triHexPlanarTriBufferedOuterLevel n))
      (triHexPlanarTriBufferedToFiniteTerminal n) := by
  intro x y
  rfl

theorem triHexPlanarTriBufferedToFiniteTerminal_not_boundary
    (n : Nat) (v : triangular.BufferedVertex n) :
    ¬ triHexPlanarFiniteBoundary (triHexPlanarTriBufferedOuterLevel n)
      (triHexPlanarTriBufferedToFiniteTerminal n v) := by
  rintro ⟨i, hi⟩
  apply hi
  apply box_mono 2 (show triangular.bufferedRadius n + 1 ≤
    triHexPlanarTriBufferedOuterLevel n by
      unfold triHexPlanarTriBufferedOuterLevel
      exact Nat.succ_le_succ
        (triangular.bufferedRadius_strictMono.monotone (Nat.le_succ n)))
  have hv : v.1 ∈ box 2 (triangular.bufferedRadius n) := by
    rw [← triangular_mem_orbitBox_iff_box]
    exact v.2
  intro k
  fin_cases i <;> fin_cases k <;>
    simp [triHexPlanarTriBufferedToFiniteTerminal, hexagonalStep] at hv ⊢ <;>
    omega

theorem triHexPlanarTriBufferedToFiniteTerminal_cross_boundary
    (n : Nat) (x : triangular.BufferedVertex n)
    (c : TriHexPlanarFiniteTerminal (triHexPlanarTriBufferedOuterLevel n))
    (hadj : (triHexPlanarFiniteTriangleInducedGraph
      (triHexPlanarTriBufferedOuterLevel n)).Adj
        (triHexPlanarTriBufferedToFiniteTerminal n x) c)
    (hc : c ∉ Set.range (triHexPlanarTriBufferedToFiniteTerminal n)) :
    triangular.bufferedBoundary n x := by
  refine ⟨c.1, hadj, ?_⟩
  intro hcbox
  apply hc
  exact ⟨⟨c.1, hcbox⟩, Subtype.ext rfl⟩

theorem triHexPlanarTriBuffered_boundary_of_outsideGraph_adj
    (n : Nat) (psi : ConfigSpace
      (Sym2 (TriHexPlanarFiniteTerminal
        (triHexPlanarTriBufferedOuterLevel n))))
    (x : triangular.BufferedVertex n)
    {c : TriHexPlanarFiniteTerminal
      (triHexPlanarTriBufferedOuterLevel n)}
    (h : (ocd_outsideGraph
      (triHexPlanarFiniteTriangleInducedGraph
        (triHexPlanarTriBufferedOuterLevel n))
      (triHexPlanarTriBufferedToFiniteTerminal n)
      (triHexPlanarFiniteBoundary
        (triHexPlanarTriBufferedOuterLevel n)) psi).Adj
        (triHexPlanarTriBufferedToFiniteTerminal n x) c) :
    triangular.bufferedBoundary n x := by
  rw [ocd_outsideGraph_adj] at h
  rcases h with ⟨hadj, _, hnotRange⟩ | ⟨_, houter, _⟩
  · apply triHexPlanarTriBufferedToFiniteTerminal_cross_boundary
      n x c hadj
    rintro ⟨z, hz⟩
    apply hnotRange
    refine ⟨s(x, z), ?_⟩
    rw [ocd_innerEdge_mk]
    congr 1
  · exact (triHexPlanarTriBufferedToFiniteTerminal_not_boundary
      n x houter).elim

theorem triHexPlanarTriBuffered_inducedWiring_le
    (n : Nat) (psi : ConfigSpace
      (Sym2 (TriHexPlanarFiniteTerminal
        (triHexPlanarTriBufferedOuterLevel n)))) :
    ocd_inducedWiring
        (triHexPlanarFiniteTriangleInducedGraph
          (triHexPlanarTriBufferedOuterLevel n))
        (triHexPlanarTriBufferedToFiniteTerminal n)
        (triHexPlanarFiniteBoundary
          (triHexPlanarTriBufferedOuterLevel n)) psi ≤
      boundaryCliqueGraph (triangular.bufferedBoundary n) := by
  intro x y hxy
  obtain ⟨hne, hreach⟩ := hxy
  rw [boundaryCliqueGraph_adj]
  refine ⟨hne, ?_, ?_⟩
  · have hne' : triHexPlanarTriBufferedToFiniteTerminal n x ≠
        triHexPlanarTriBufferedToFiniteTerminal n y :=
      fun h => hne ((triHexPlanarTriBufferedToFiniteTerminal n).injective h)
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach
    rcases hreach.cases_head with heq | ⟨c, hadj, _⟩
    · exact (hne' heq).elim
    · exact triHexPlanarTriBuffered_boundary_of_outsideGraph_adj
        n psi x hadj
  · have hreach' := hreach.symm
    have hne' : triHexPlanarTriBufferedToFiniteTerminal n y ≠
        triHexPlanarTriBufferedToFiniteTerminal n x :=
      fun h => hne ((triHexPlanarTriBufferedToFiniteTerminal n).injective h).symm
    rw [SimpleGraph.reachable_iff_reflTransGen] at hreach'
    rcases hreach'.cases_head with heq | ⟨c, hadj, _⟩
    · exact (hne' heq).elim
    · exact triHexPlanarTriBuffered_boundary_of_outsideGraph_adj
        n psi y hadj



theorem triHexPlanarTriBuffered_outerTriangle_dominated
    (n : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q)
    {A : Set (ConfigSpace
      (Sym2 (triangular.BufferedVertex n)))} (hA : IsIncreasing A) :
    finiteWiredEventMass
        (triHexPlanarFiniteTriangleInducedGraph
          (triHexPlanarTriBufferedOuterLevel n))
        (triHexPlanarFiniteBoundary
          (triHexPlanarTriBufferedOuterLevel n)) p q
        (ocd_innerRestrict
          (triHexPlanarTriBufferedToFiniteTerminal n) ⁻¹' A) ≤
      finiteWiredEventMass (triangular.bufferedGraph n)
        (triangular.bufferedBoundary n) p q A := by
  have h := ocd_wired_inner_dominated_bcProb
    (triHexPlanarTriBufferedToFiniteTerminal n).injective
    (triHexPlanarTriBufferedToFiniteTerminal_adjMatch n)
    (triangular.bufferedBoundary n) hp hp1 hq
    (triHexPlanarTriBuffered_inducedWiring_le n) hA
  simpa only [bcProb_clique_eq_wiredFkProb, finiteWiredEventMass] using h





def triHexPlanarTriRoot : Site 2 := hexagonalStep 0

def triHexPlanarFiniteTriangleRoot (n : Nat) :
    TriHexPlanarFiniteTerminal n :=
  triHexPlanarFiniteTerminalMap n (triHexPlanarFiniteRootCell n) 0

@[simp] theorem triHexPlanarFiniteTriangleRoot_val (n : Nat) :
    (triHexPlanarFiniteTriangleRoot n).1 = triHexPlanarTriRoot := by
  ext k
  fin_cases k <;>
    simp [triHexPlanarFiniteTriangleRoot, triHexPlanarTriRoot,
      triHexPlanarFiniteTerminalMap, triHexPlanarFiniteRootCell,
      triHexPlanarCellTerminal, hexagonalStep]

def triHexPlanarTriBufferedRoot (n : Nat) :
    triangular.BufferedVertex (n + 1) :=
  ⟨triHexPlanarTriRoot, by
    apply triangular.orbitBox_mono
      ((Nat.succ_le_succ (Nat.zero_le n)).trans
        (triangular.id_le_bufferedRadius (n + 1)))
    rw [triangular_mem_orbitBox_iff_box]
    intro k
    fin_cases k <;> simp [triHexPlanarTriRoot, hexagonalStep]⟩

theorem triHexPlanarFiniteTriangleToBuffered_root (n : Nat) :
    triHexPlanarFiniteTriangleToBuffered n
        (triHexPlanarFiniteTriangleRoot n) =
      triHexPlanarTriBufferedRoot (n + 1) := by
  apply Subtype.ext
  exact triHexPlanarFiniteTriangleRoot_val n

theorem triHexPlanarTriBufferedToFiniteTerminal_root (n : Nat) :
    triHexPlanarTriBufferedToFiniteTerminal (n + 1)
        (triHexPlanarTriBufferedRoot n) =
      triHexPlanarFiniteTriangleRoot
        (triHexPlanarTriBufferedOuterLevel (n + 1)) := by
  apply Subtype.ext
  exact (triHexPlanarFiniteTriangleRoot_val _).symm

def triHexPlanarFiniteTriangleRootBoundaryEvent (n : Nat) :
    Set (ConfigSpace (Sym2 (TriHexPlanarFiniteTerminal n))) :=
  finiteRootBoundaryEvent (triHexPlanarFiniteTriangleInducedGraph n)
    (triHexPlanarFiniteBoundary n) (triHexPlanarFiniteTriangleRoot n)

def triHexPlanarTriBufferedRootBoundaryEvent (n : Nat) :
    Set (ConfigSpace (Sym2 (triangular.BufferedVertex (n + 1)))) :=
  finiteRootBoundaryEvent (triangular.bufferedGraph (n + 1))
    (triangular.bufferedBoundary (n + 1))
    (triHexPlanarTriBufferedRoot n)

theorem triHexPlanarTriBuffered_outerEvent_subset_triangleRestrict
    (n : Nat) :
    triHexPlanarTriBufferedRootBoundaryEvent (n + 1) ⊆
      ocd_innerRestrict (triHexPlanarFiniteTriangleToBuffered n) ⁻¹'
        triHexPlanarFiniteTriangleRootBoundaryEvent n := by
  simpa only [triHexPlanarTriBufferedRootBoundaryEvent,
    triHexPlanarFiniteTriangleRootBoundaryEvent,
    triHexPlanarFiniteTriangleToBuffered_root] using
    outerRootBoundaryEvent_subset_innerRestrict
      (triHexPlanarFiniteTriangleInducedGraph n)
      (triangular.bufferedGraph (n + 2))
      (triHexPlanarFiniteTriangleToBuffered n)
      (triHexPlanarFiniteBoundary n)
      (triangular.bufferedBoundary (n + 2))
      (triHexPlanarFiniteTriangleToBuffered_adjMatch n)
      (triHexPlanarFiniteTriangleToBuffered_not_boundary n)
      (triHexPlanarFiniteTriangleToBuffered_cross_boundary n)
      (triHexPlanarFiniteTriangleRoot n)

theorem triHexPlanarFiniteTriangle_outerEvent_subset_triBufferedRestrict
    (n : Nat) :
    triHexPlanarFiniteTriangleRootBoundaryEvent
        (triHexPlanarTriBufferedOuterLevel (n + 1)) ⊆
      ocd_innerRestrict
          (triHexPlanarTriBufferedToFiniteTerminal (n + 1)) ⁻¹'
        triHexPlanarTriBufferedRootBoundaryEvent n := by
  simpa only [triHexPlanarTriBufferedRootBoundaryEvent,
    triHexPlanarFiniteTriangleRootBoundaryEvent,
    triHexPlanarTriBufferedToFiniteTerminal_root] using
    outerRootBoundaryEvent_subset_innerRestrict
      (triangular.bufferedGraph (n + 1))
      (triHexPlanarFiniteTriangleInducedGraph
        (triHexPlanarTriBufferedOuterLevel (n + 1)))
      (triHexPlanarTriBufferedToFiniteTerminal (n + 1))
      (triangular.bufferedBoundary (n + 1))
      (triHexPlanarFiniteBoundary
        (triHexPlanarTriBufferedOuterLevel (n + 1)))
      (triHexPlanarTriBufferedToFiniteTerminal_adjMatch (n + 1))
      (triHexPlanarTriBufferedToFiniteTerminal_not_boundary (n + 1))
      (triHexPlanarTriBufferedToFiniteTerminal_cross_boundary (n + 1))
      (triHexPlanarTriBufferedRoot n)

theorem triHexPlanarFiniteTriangleInducedWiredBoundaryProbability_eq_eventMass
    (n : Nat) {p q : Real} :
    triHexPlanarFiniteTriangleInducedWiredBoundaryProbability n p q =
      finiteWiredEventMass (triHexPlanarFiniteTriangleInducedGraph n)
        (triHexPlanarFiniteBoundary n) p q
        (triHexPlanarFiniteTriangleRootBoundaryEvent n) := by
  classical
  unfold triHexPlanarFiniteTriangleInducedWiredBoundaryProbability
    finiteWiredEventMass
  apply Finset.sum_congr rfl
  intro omega _
  congr 1
  unfold triHexPlanarFiniteTriangleInducedBoundaryReachIndicator
    triHexPlanarFiniteTriangleRootBoundaryEvent finiteRootBoundaryEvent
    triHexPlanarFiniteTriangleRoot
  have hgraph := openSub_extendActive_restrictActive_eq
    (triHexPlanarFiniteTriangleInducedGraph n) omega
  have hiff : (∃ y : TriHexPlanarFiniteTerminal n,
      triHexPlanarFiniteBoundary n y ∧
      (openSub (triHexPlanarFiniteTriangleInducedGraph n)
        (extendActive (triHexPlanarFiniteTriangleInducedGraph n)
          (restrictActive (triHexPlanarFiniteTriangleInducedGraph n) omega))).Reachable
        (triHexPlanarFiniteTerminalMap n
          (triHexPlanarFiniteRootCell n) 0) y) ↔
    ∃ y : TriHexPlanarFiniteTerminal n,
      triHexPlanarFiniteBoundary n y ∧
      (openSub (triHexPlanarFiniteTriangleInducedGraph n) omega).Reachable
        (triHexPlanarFiniteTerminalMap n
          (triHexPlanarFiniteRootCell n) 0) y := by
    simpa only [hgraph]
  rw [if_congr hiff rfl rfl]
  simp only [Set.indicator]
  rfl



theorem triHexPlanarTriBuffered_mass_le_triangle
    (n : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    finiteWiredEventMass (triangular.bufferedGraph (n + 2))
        (triangular.bufferedBoundary (n + 2)) p q
        (triHexPlanarTriBufferedRootBoundaryEvent (n + 1)) ≤
      triHexPlanarFiniteTriangleInducedWiredBoundaryProbability n p q := by
  rw [triHexPlanarFiniteTriangleInducedWiredBoundaryProbability_eq_eventMass]
  calc
    finiteWiredEventMass (triangular.bufferedGraph (n + 2))
        (triangular.bufferedBoundary (n + 2)) p q
        (triHexPlanarTriBufferedRootBoundaryEvent (n + 1)) ≤
      finiteWiredEventMass (triangular.bufferedGraph (n + 2))
        (triangular.bufferedBoundary (n + 2)) p q
        (ocd_innerRestrict (triHexPlanarFiniteTriangleToBuffered n) ⁻¹'
          triHexPlanarFiniteTriangleRootBoundaryEvent n) :=
      finiteWiredEventMass_mono _ _ hp hp1 (zero_lt_one.trans_le hq)
        (triHexPlanarTriBuffered_outerEvent_subset_triangleRestrict n)
    _ ≤ finiteWiredEventMass
        (triHexPlanarFiniteTriangleInducedGraph n)
        (triHexPlanarFiniteBoundary n) p q
        (triHexPlanarFiniteTriangleRootBoundaryEvent n) :=
      triHexPlanarFiniteTriangle_outerBuffered_dominated n hp hp1 hq
        (finiteRootBoundaryEvent_isIncreasing _ _ _)



theorem triHexPlanarFiniteTriangle_le_triBuffered_mass
    (n : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    triHexPlanarFiniteTriangleInducedWiredBoundaryProbability
        (triHexPlanarTriBufferedOuterLevel (n + 1)) p q ≤
      finiteWiredEventMass (triangular.bufferedGraph (n + 1))
        (triangular.bufferedBoundary (n + 1)) p q
        (triHexPlanarTriBufferedRootBoundaryEvent n) := by
  rw [triHexPlanarFiniteTriangleInducedWiredBoundaryProbability_eq_eventMass]
  calc
    finiteWiredEventMass
        (triHexPlanarFiniteTriangleInducedGraph
          (triHexPlanarTriBufferedOuterLevel (n + 1)))
        (triHexPlanarFiniteBoundary
          (triHexPlanarTriBufferedOuterLevel (n + 1))) p q
        (triHexPlanarFiniteTriangleRootBoundaryEvent
          (triHexPlanarTriBufferedOuterLevel (n + 1))) ≤
      finiteWiredEventMass
        (triHexPlanarFiniteTriangleInducedGraph
          (triHexPlanarTriBufferedOuterLevel (n + 1)))
        (triHexPlanarFiniteBoundary
          (triHexPlanarTriBufferedOuterLevel (n + 1))) p q
        (ocd_innerRestrict
          (triHexPlanarTriBufferedToFiniteTerminal (n + 1)) ⁻¹'
          triHexPlanarTriBufferedRootBoundaryEvent n) :=
      finiteWiredEventMass_mono _ _ hp hp1 (zero_lt_one.trans_le hq)
        (triHexPlanarFiniteTriangle_outerEvent_subset_triBufferedRestrict n)
    _ ≤ finiteWiredEventMass (triangular.bufferedGraph (n + 1))
        (triangular.bufferedBoundary (n + 1)) p q
        (triHexPlanarTriBufferedRootBoundaryEvent n) :=
      triHexPlanarTriBuffered_outerTriangle_dominated (n + 1)
        hp hp1 hq (finiteRootBoundaryEvent_isIncreasing _ _ _)

theorem triHexPlanarTriBufferedRootBoundaryEvent_eq_setBoundary
    (n : Nat) :
    triHexPlanarTriBufferedRootBoundaryEvent n =
      triangular.bufferedSetBoundaryEvent
        ({triHexPlanarTriRoot} : Set (Site 2)) (n + 1) := by
  ext eta
  constructor
  · rintro ⟨y, hy, hreach⟩
    exact ⟨triHexPlanarTriBufferedRoot n, Set.mem_singleton _,
      y, hy, hreach⟩
  · rintro ⟨x, hx, y, hy, hreach⟩
    have hx' : x = triHexPlanarTriBufferedRoot n := by
      apply Subtype.ext
      simpa only [Set.mem_singleton_iff] using hx
    subst x
    exact ⟨y, hy, hreach⟩

theorem triHexPlanarTriBuffered_eventMass_eq_measure
    (n : Nat) {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    finiteWiredEventMass (triangular.bufferedGraph (n + 1))
        (triangular.bufferedBoundary (n + 1)) p q
        (triHexPlanarTriBufferedRootBoundaryEvent n) =
      (triangular.wiredBufferedMeasure (n + 1) hp hp1 hq :
        Measure (ConfigSpace (Sym2 (Site 2)))).real
        (triangular.bufferedCylinder (n + 1)
          (triangular.bufferedSetBoundaryEvent
            ({triHexPlanarTriRoot} : Set (Site 2)) (n + 1))) := by
  rw [triangular.wiredBufferedMeasure_real_cylinder (le_refl (n + 1))
    hp hp1 hq]
  unfold finiteWiredEventMass
  rw [triHexPlanarTriBufferedRootBoundaryEvent_eq_setBoundary]
  apply Finset.sum_congr rfl
  intro omega _
  rfl

theorem triHexPlanarTriBuffered_eventMass_tendsto
    {p q : Real} (hp : 0 < p) (hp1 : p < 1) (hq : 1 ≤ q) :
    Tendsto
      (fun n => finiteWiredEventMass
        (triangular.bufferedGraph (n + 1))
        (triangular.bufferedBoundary (n + 1)) p q
        (triHexPlanarTriBufferedRootBoundaryEvent n)) atTop
      (nhds ((triangular.wiredBufferedInfiniteVolume hp hp1
        (zero_lt_one.trans_le hq) : Measure
          (ConfigSpace (Sym2 (Site 2)))).real
          (triangular.setHitsInfinite
            ({triHexPlanarTriRoot} : Set (Site 2))))) := by
  have hdiag := triangular.wiredBufferedSetBoundary_diag_tendsto
    ({triHexPlanarTriRoot} : Set (Site 2)) (Set.finite_singleton _)
    1 (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      exact (triHexPlanarTriBufferedRoot 0).2)
    hp hp1 hq
  apply hdiag.congr'
  filter_upwards with n
  rw [triHexPlanarTriBuffered_eventMass_eq_measure n hp hp1
    (zero_lt_one.trans_le hq)]
  rw [Nat.one_add]

theorem triHexPlanarTriCofinalLevel_tendsto :
    Tendsto (fun n => triHexPlanarTriBufferedOuterLevel (n + 1))
      atTop atTop := by
  apply StrictMono.tendsto_atTop
  intro a b hab
  unfold triHexPlanarTriBufferedOuterLevel
  exact Nat.add_lt_add_right
    (triangular.bufferedRadius_strictMono
      (Nat.add_lt_add_right (Nat.add_lt_add_right hab 1) 1)) 1



theorem triHexPlanar_fixedRootInfinite_real_eq
    {p q : Real} (hq : 1 ≤ q) (hp : p ∈ Set.Ioo (0 : Real) 1)
    (hsurface : FrontierA.triangularFKCriticalPolynomial q
      (FrontierA.fkEdgeOdds p) = 0) :
    (hexagonal.wiredBufferedInfiniteVolume
        (BeffaraDC.dualParam_pos hp.1 hp.2 (zero_lt_one.trans_le hq))
        (BeffaraDC.dualParam_lt_one hp.1 hp.2 (zero_lt_one.trans_le hq))
        (zero_lt_one.trans_le hq) : Measure
          (ConfigSpace (Sym2 HexVertex))).real
      (hexagonal.setHitsInfinite
        ({triHexPlanarHexWhiteRoot} : Set HexVertex)) =
    (triangular.wiredBufferedInfiniteVolume hp.1 hp.2
        (zero_lt_one.trans_le hq) : Measure
          (ConfigSpace (Sym2 (Site 2)))).real
      (triangular.setHitsInfinite
        ({triHexPlanarTriRoot} : Set (Site 2))) := by
  let pd := BeffaraDC.dualParam p q
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  have hpd0 : 0 < pd := BeffaraDC.dualParam_pos hp.1 hp.2 hq0
  have hpd1 : pd < 1 := BeffaraDC.dualParam_lt_one hp.1 hp.2 hq0
  let cHex := fun n => finiteWiredEventMass
    (hexagonal.bufferedGraph (n + 1))
    (hexagonal.bufferedBoundary (n + 1)) pd q
    (triHexPlanarHexWhiteBufferedRootBoundaryEvent n)
  let cTri := fun n => finiteWiredEventMass
    (triangular.bufferedGraph (n + 1))
    (triangular.bufferedBoundary (n + 1)) p q
    (triHexPlanarTriBufferedRootBoundaryEvent n)
  have hcHex := triHexPlanarHexWhiteBuffered_eventMass_tendsto
    hpd0 hpd1 hq
  have hcTri := triHexPlanarTriBuffered_eventMass_tendsto
    hp.1 hp.2 hq
  apply le_antisymm
  · have hindex : Tendsto
        (fun n => triHexPlanarTriBufferedOuterLevel (n + 1) + 1)
        atTop atTop :=
      (tendsto_add_atTop_nat 1).comp triHexPlanarTriCofinalLevel_tendsto
    have hlo : Tendsto
        (fun n => cHex
          (triHexPlanarTriBufferedOuterLevel (n + 1) + 1)) atTop _ :=
      hcHex.comp hindex
    apply le_of_tendsto_of_tendsto hlo hcTri
    filter_upwards with n
    have heq :=
      triHexPlanarFiniteInducedWiredBoundaryProbability_eq_homogeneous
        (triangular.bufferedRadius (n + 2)) hq0 hp hsurface
    calc
      cHex (triHexPlanarTriBufferedOuterLevel (n + 1) + 1) ≤
          triHexPlanarFiniteStarWiredBoundaryProbability
            (triHexPlanarTriBufferedOuterLevel (n + 1)) pd q := by
        exact triHexPlanarHexWhiteBuffered_mass_le_star
          (triHexPlanarTriBufferedOuterLevel (n + 1)) hpd0 hpd1 hq
      _ = triHexPlanarFiniteTriangleInducedWiredBoundaryProbability
            (triHexPlanarTriBufferedOuterLevel (n + 1)) p q := by
        simpa [pd, triHexPlanarTriBufferedOuterLevel, Nat.add_assoc] using heq
      _ ≤ cTri n := by
        exact triHexPlanarFiniteTriangle_le_triBuffered_mass
          n hp.1 hp.2 hq
  · have hindex : Tendsto
        (fun n => triHexPlanarHexBufferedOuterStarLevel (n + 1) + 1)
        atTop atTop :=
      (tendsto_add_atTop_nat 1).comp
        triHexPlanarHexStarCofinalLevel_tendsto
    have hlo : Tendsto
        (fun n => cTri
          (triHexPlanarHexBufferedOuterStarLevel (n + 1) + 1)) atTop _ :=
      hcTri.comp hindex
    apply le_of_tendsto_of_tendsto hlo hcHex
    filter_upwards with n
    have heq :=
      triHexPlanarFiniteInducedWiredBoundaryProbability_eq_homogeneous
        (hexagonal.bufferedRadius (n + 2)) hq0 hp hsurface
    calc
      cTri (triHexPlanarHexBufferedOuterStarLevel (n + 1) + 1) ≤
          triHexPlanarFiniteTriangleInducedWiredBoundaryProbability
            (triHexPlanarHexBufferedOuterStarLevel (n + 1)) p q := by
        exact triHexPlanarTriBuffered_mass_le_triangle
          (triHexPlanarHexBufferedOuterStarLevel (n + 1)) hp.1 hp.2 hq
      _ = triHexPlanarFiniteStarWiredBoundaryProbability
            (triHexPlanarHexBufferedOuterStarLevel (n + 1)) pd q := by
        simpa [pd, triHexPlanarHexBufferedOuterStarLevel,
          Nat.add_assoc] using heq.symm
      _ ≤ cHex n := by
        exact triHexPlanarFiniteStar_le_hexWhiteBuffered_mass
          n hpd0 hpd1 hq

end

end StatMech.FK.PeriodicPlanar
