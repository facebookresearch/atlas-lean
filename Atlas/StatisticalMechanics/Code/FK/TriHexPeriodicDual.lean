/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FK.PeriodicPlanarDuality

open Finset Set SimpleGraph

namespace StatMech
namespace FK
namespace PeriodicPlanar

open Lattice

abbrev TriHexEdgeIndex := Site 2 × Fin 3

theorem triangularStep_injective : Function.Injective triangularStep := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [triangularStep]

theorem triangularStep_add_ne_zero (i j : Fin 3) :
    triangularStep i + triangularStep j ≠ 0 := by
  fin_cases i <;> fin_cases j <;> simp [triangularStep, funext_iff]


def triangularIndexedEdge (a : TriHexEdgeIndex) : Sym2 (Site 2) :=
  s(a.1, a.1 + triangularStep a.2)

theorem triangularIndexedEdge_mem (a : TriHexEdgeIndex) :
    triangularIndexedEdge a ∈ triangularGraph.edgeSet := by
  change triangularGraph.Adj a.1 (a.1 + triangularStep a.2)
  exact triangular_adj_neighbor a.1 (a.2, true)

def triangularEdgeChart (a : TriHexEdgeIndex) : triangularGraph.edgeSet :=
  ⟨triangularIndexedEdge a, triangularIndexedEdge_mem a⟩

theorem triangularEdgeChart_injective : Function.Injective triangularEdgeChart := by
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

theorem triangularEdgeChart_surjective : Function.Surjective triangularEdgeChart := by
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


noncomputable def triangularEdgeChartEquiv :
    TriHexEdgeIndex ≃ triangularGraph.edgeSet :=
  Equiv.ofBijective triangularEdgeChart
    ⟨triangularEdgeChart_injective, triangularEdgeChart_surjective⟩

theorem hexagonalStep_injective : Function.Injective hexagonalStep := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp_all [hexagonalStep]


def hexagonalIndexedEdge (a : TriHexEdgeIndex) : Sym2 HexVertex :=
  s((a.1, false), (a.1 + hexagonalStep a.2, true))

theorem hexagonalIndexedEdge_mem (a : TriHexEdgeIndex) :
    hexagonalIndexedEdge a ∈ hexagonalGraph.edgeSet := by
  change hexagonalGraph.Adj (a.1, false) (a.1 + hexagonalStep a.2, true)
  exact hexagonal_adj_neighbor (a.1, false) a.2

def hexagonalEdgeChart (a : TriHexEdgeIndex) : hexagonalGraph.edgeSet :=
  ⟨hexagonalIndexedEdge a, hexagonalIndexedEdge_mem a⟩

theorem hexagonalEdgeChart_injective : Function.Injective hexagonalEdgeChart := by
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

theorem hexagonalEdgeChart_surjective : Function.Surjective hexagonalEdgeChart := by
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


noncomputable def hexagonalEdgeChartEquiv :
    TriHexEdgeIndex ≃ hexagonalGraph.edgeSet :=
  Equiv.ofBijective hexagonalEdgeChart
    ⟨hexagonalEdgeChart_injective, hexagonalEdgeChart_surjective⟩



def triHexIndexEquiv : TriHexEdgeIndex ≃ TriHexEdgeIndex where
  toFun a := (if a.2 = 2 then a.1 - triangularStep 0 else a.1, a.2)
  invFun a := (if a.2 = 2 then a.1 + triangularStep 0 else a.1, a.2)
  left_inv := by
    rintro ⟨z, i⟩
    fin_cases i <;> ext <;> simp
  right_inv := by
    rintro ⟨z, i⟩
    fin_cases i <;> ext <;> simp



noncomputable def triHexDualEdgeEquiv :
    triangularGraph.edgeSet ≃ hexagonalGraph.edgeSet :=
  triangularEdgeChartEquiv.symm.trans
    (triHexIndexEquiv.trans hexagonalEdgeChartEquiv)




def triangularFace (u : HexVertex) : Finset (Site 2) :=
  if u.2 then
    {u.1, u.1 - triangularStep 0, u.1 - triangularStep 1}
  else
    {u.1, u.1 + triangularStep 0, u.1 + triangularStep 1}


def incidentHexFaces (a : TriHexEdgeIndex) : HexVertex × HexVertex :=
  let b := triHexIndexEquiv a
  ((b.1, false), (b.1 + hexagonalStep b.2, true))

theorem incidentHexFaces_adj (a : TriHexEdgeIndex) :
    hexagonalGraph.Adj (incidentHexFaces a).1 (incidentHexFaces a).2 := by
  exact hexagonal_adj_neighbor
    ((triHexIndexEquiv a).1, false) (triHexIndexEquiv a).2



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

theorem triHexDualEdgeEquiv_chart (a : TriHexEdgeIndex) :
    (triHexDualEdgeEquiv (triangularEdgeChart a) : Sym2 HexVertex) =
      hexagonalIndexedEdge (triHexIndexEquiv a) := by
  simp only [triHexDualEdgeEquiv, Equiv.trans_apply]
  have ht : triangularEdgeChartEquiv a = triangularEdgeChart a := rfl
  rw [← ht, Equiv.symm_apply_apply]
  rfl

end PeriodicPlanar
end FK
end StatMech
