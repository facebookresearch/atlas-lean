/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Duality

/-!
# Edge duality between the triangular and hexagonal lattices

Indexed edge charts for the triangular and hexagonal lattices and the bijection between their
edge sets given by planar duality.

## i. Overview

Both lattices are periodic under `Site 2`. Every triangular edge is `s(x, x + triangularStep i)`
for a unique pair `(x, i) : Site 2 × Fin 3`, and every hexagonal edge is
`s((x, false), (x + hexagonalStep i, true))` for a unique `(x, i)`. Composing these charts with a
reindexing of the third edge direction gives `triHexDualEdgeEquiv`, the bijection sending a
triangular edge to the hexagonal edge that crosses it. `triangular_edge_incident_faces` checks the
combinatorial picture: the two hexagonal vertices of the dual edge are the two triangular faces
containing the primal edge. All results are proved unconditionally.

## ii. Key results

- `triangularEdgeChartEquiv`, `hexagonalEdgeChartEquiv` : edge sets as `Site 2 × Fin 3`.
- `triHexDualEdgeEquiv` : the triangular–hexagonal edge duality.
- `triangular_edge_incident_faces` : the dual edge joins the two faces of the primal edge.

## iii. Table of contents

- A. Triangular edge charts
- B. Hexagonal edge charts
- C. The triangular–hexagonal edge duality

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006), Ch. 6.
- V. Beffara and H. Duminil-Copin, *The self-dual point of the two-dimensional random-cluster
  model is critical for q ≥ 1*, Probab. Theory Related Fields 153 (2012), 511–542.
-/

@[expose] public section

open Finset Set SimpleGraph

namespace StatMech
namespace FK
namespace PeriodicPlanar

open StatMech.Lattice

/-! ## A. Triangular edge charts -/

/-- Edge index `(x, i)` shared by both lattices: a base site and one of three edge directions. -/
abbrev TriHexEdgeIndex := Site 2 × Fin 3

lemma triangularStep_injective : Function.Injective triangularStep := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [triangularStep]

lemma triangularStep_add_ne_zero (i j : Fin 3) :
    triangularStep i + triangularStep j ≠ 0 := by
  fin_cases i <;> fin_cases j <;> simp [triangularStep, funext_iff]

/-- The triangular edge `s(x, x + triangularStep i)` with index `(x, i)`. -/
def triangularIndexedEdge (a : TriHexEdgeIndex) : Sym2 (Site 2) :=
  s(a.1, a.1 + triangularStep a.2)

lemma triangularIndexedEdge_mem (a : TriHexEdgeIndex) :
    triangularIndexedEdge a ∈ triangularGraph.edgeSet := by
  change triangularGraph.Adj a.1 (a.1 + triangularStep a.2)
  exact triangular_adj_neighbor a.1 (a.2, true)

/-- The triangular edge with a given index, as an element of the edge set. -/
def triangularEdgeChart (a : TriHexEdgeIndex) : triangularGraph.edgeSet :=
  ⟨triangularIndexedEdge a, triangularIndexedEdge_mem a⟩

lemma triangularEdgeChart_injective : Function.Injective triangularEdgeChart := by
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  have he : s(x, x + triangularStep i) = s(y, y + triangularStep j) :=
    congrArg Subtype.val h
  rw [Sym2.eq_iff] at he
  rcases he with hdir | hswap
  · have hxy : x = y := hdir.1
    subst y
    have hs : triangularStep i = triangularStep j :=
      add_left_cancel hdir.2
    exact Prod.ext rfl (triangularStep_injective hs)
  · have hsecond := hswap.2
    rw [hswap.1] at hsecond
    have hzero : triangularStep j + triangularStep i = 0 := by
      apply add_left_cancel (a := y)
      simpa [add_assoc] using hsecond
    exact (triangularStep_add_ne_zero j i hzero).elim

lemma triangularEdgeChart_surjective : Function.Surjective triangularEdgeChart := by
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet, triangularGraph_adj, triangularAdj] at he
      obtain ⟨i, h | h⟩ := he
      · have hy : y = x + triangularStep i := by
          ext k
          have hk := congrFun h k
          simp only [Pi.sub_apply, Pi.add_apply] at hk ⊢
          omega
        refine ⟨(x, i), Subtype.ext ?_⟩
        simp [triangularEdgeChart, triangularIndexedEdge, hy]
      · have hx : x = y + triangularStep i := by
          ext k
          have hk := congrFun h k
          simp only [Pi.sub_apply, Pi.add_apply] at hk ⊢
          omega
        refine ⟨(y, i), Subtype.ext ?_⟩
        simp [triangularEdgeChart, triangularIndexedEdge, hx]

/-- The edge set of the triangular lattice is in bijection with `Site 2 × Fin 3`. -/
noncomputable def triangularEdgeChartEquiv :
    TriHexEdgeIndex ≃ triangularGraph.edgeSet :=
  Equiv.ofBijective triangularEdgeChart
    ⟨triangularEdgeChart_injective, triangularEdgeChart_surjective⟩

/-! ## B. Hexagonal edge charts -/

lemma hexagonalStep_injective : Function.Injective hexagonalStep := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [hexagonalStep]

/-- The hexagonal edge from the black vertex `(x, false)` to the white vertex `(x + hexagonalStep i,
true)`. -/
def hexagonalIndexedEdge (a : TriHexEdgeIndex) : Sym2 HexVertex :=
  s((a.1, false), (a.1 + hexagonalStep a.2, true))

lemma hexagonalIndexedEdge_mem (a : TriHexEdgeIndex) :
    hexagonalIndexedEdge a ∈ hexagonalGraph.edgeSet := by
  change hexagonalGraph.Adj (a.1, false) (a.1 + hexagonalStep a.2, true)
  exact hexagonal_adj_neighbor (a.1, false) a.2

/-- The hexagonal edge with a given index, as an element of the edge set. -/
def hexagonalEdgeChart (a : TriHexEdgeIndex) : hexagonalGraph.edgeSet :=
  ⟨hexagonalIndexedEdge a, hexagonalIndexedEdge_mem a⟩

lemma hexagonalEdgeChart_injective : Function.Injective hexagonalEdgeChart := by
  rintro ⟨x, i⟩ ⟨y, j⟩ h
  have he : s((x, false), (x + hexagonalStep i, true)) =
      s((y, false), (y + hexagonalStep j, true)) := congrArg Subtype.val h
  rw [Sym2.eq_iff] at he
  rcases he with hdir | hswap
  · have hxy : x = y := congrArg Prod.fst hdir.1
    subst y
    have hs0 : x + hexagonalStep i = x + hexagonalStep j :=
      congrArg Prod.fst hdir.2
    have hs : hexagonalStep i = hexagonalStep j := add_left_cancel hs0
    exact Prod.ext rfl (hexagonalStep_injective hs)
  · have hbool : (false : Bool) = true := congrArg Prod.snd hswap.1
    simp at hbool

lemma hexagonalEdgeChart_surjective : Function.Surjective hexagonalEdgeChart := by
  rintro ⟨e, he⟩
  induction e using Sym2.inductionOn with
  | _ u v =>
      rw [SimpleGraph.mem_edgeSet, hexagonalGraph_adj, hexagonalAdj] at he
      rcases he with ⟨hu, hv, i, hi⟩ | ⟨hv, hu, i, hi⟩
      · have hvSite : v.1 = u.1 + hexagonalStep i := by
          ext k
          have hk := congrFun hi k
          simp only [Pi.sub_apply, Pi.add_apply] at hk ⊢
          omega
        refine ⟨(u.1, i), Subtype.ext ?_⟩
        apply Sym2.eq_iff.mpr
        left
        constructor
        · exact Prod.ext rfl hu.symm
        · exact Prod.ext hvSite.symm hv.symm
      · have huSite : u.1 = v.1 + hexagonalStep i := by
          ext k
          have hk := congrFun hi k
          simp only [Pi.sub_apply, Pi.add_apply] at hk ⊢
          omega
        refine ⟨(v.1, i), Subtype.ext ?_⟩
        apply Sym2.eq_iff.mpr
        right
        constructor
        · exact Prod.ext rfl hv.symm
        · exact Prod.ext huSite.symm hu.symm

/-- The edge set of the hexagonal lattice is in bijection with `Site 2 × Fin 3`. -/
noncomputable def hexagonalEdgeChartEquiv :
    TriHexEdgeIndex ≃ hexagonalGraph.edgeSet :=
  Equiv.ofBijective hexagonalEdgeChart
    ⟨hexagonalEdgeChart_injective, hexagonalEdgeChart_surjective⟩

/-! ## C. The triangular–hexagonal edge duality -/

/-- Reindexing of the edge indices matching a triangular edge with the hexagonal edge crossing it:
the third direction is shifted by `-triangularStep 0`. -/
def triHexIndexEquiv : TriHexEdgeIndex ≃ TriHexEdgeIndex where
  toFun a := (if a.2 = 2 then a.1 - triangularStep 0 else a.1, a.2)
  invFun a := (if a.2 = 2 then a.1 + triangularStep 0 else a.1, a.2)
  left_inv := by
    rintro ⟨z, i⟩
    fin_cases i <;> ext <;> simp
  right_inv := by
    rintro ⟨z, i⟩
    fin_cases i <;> ext <;> simp

/-- Planar duality between the edge sets of the triangular and hexagonal lattices: each triangular
edge goes to the hexagonal edge crossing it. -/
noncomputable def triHexDualEdgeEquiv :
    triangularGraph.edgeSet ≃ hexagonalGraph.edgeSet :=
  triangularEdgeChartEquiv.symm.trans
    (triHexIndexEquiv.trans hexagonalEdgeChartEquiv)

/-- The three triangular sites around the triangular face labelled by the hexagonal vertex `u`
(white faces point down, black faces point up). -/
def triangularFace (u : HexVertex) : Finset (Site 2) :=
  if u.2 then
    {u.1, u.1 - triangularStep 0, u.1 - triangularStep 1}
  else
    {u.1, u.1 + triangularStep 0, u.1 + triangularStep 1}

/-- The two hexagonal vertices (triangular faces) incident to the triangular edge with index `a`. -/
def incidentHexFaces (a : TriHexEdgeIndex) : HexVertex × HexVertex :=
  let b := triHexIndexEquiv a
  ((b.1, false), (b.1 + hexagonalStep b.2, true))

lemma incidentHexFaces_adj (a : TriHexEdgeIndex) :
    hexagonalGraph.Adj (incidentHexFaces a).1 (incidentHexFaces a).2 := by
  exact hexagonal_adj_neighbor
    ((triHexIndexEquiv a).1, false) (triHexIndexEquiv a).2

/-- Both endpoints of a triangular edge lie on both faces joined by its dual hexagonal edge. -/
theorem triangular_edge_incident_faces (a : TriHexEdgeIndex) :
    let x := a.1
    let y := a.1 + triangularStep a.2
    x ∈ triangularFace (incidentHexFaces a).1 ∧
      y ∈ triangularFace (incidentHexFaces a).1 ∧
      x ∈ triangularFace (incidentHexFaces a).2 ∧
      y ∈ triangularFace (incidentHexFaces a).2 := by
  rcases a with ⟨x, i⟩
  have hx : x = ![x 0, x 1] := by
    funext j
    fin_cases j <;> simp
  rw [hx]
  fin_cases i <;>
    simp [incidentHexFaces, triHexIndexEquiv, triangularFace,
      triangularStep, hexagonalStep, funext_iff]
  all_goals ring

lemma triHexDualEdgeEquiv_chart (a : TriHexEdgeIndex) :
    (triHexDualEdgeEquiv (triangularEdgeChart a) : Sym2 HexVertex) =
      hexagonalIndexedEdge (triHexIndexEquiv a) := by
  simp only [triHexDualEdgeEquiv, Equiv.trans_apply]
  have ht : triangularEdgeChartEquiv a = triangularEdgeChart a := rfl
  rw [← ht, Equiv.symm_apply_apply]
  rfl

end PeriodicPlanar
end FK
end StatMech
