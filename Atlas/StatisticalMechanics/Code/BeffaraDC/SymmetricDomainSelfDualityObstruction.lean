/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.BeffaraDC.SymmetricDomainSelfDuality
import Code.FK.PcNontrivial

open Set SimpleGraph
open StatMech.Lattice

namespace StatMech
namespace BeffaraDC
namespace SymmetricDomain

noncomputable section


def degenerateSite : Site 2 := ![0, 0]


def degenerateWalk : LatticePath degenerateSite degenerateSite :=
  SimpleGraph.Walk.nil




def degenerateSymmetricDomain : SymmetricDomain where
  u₁ := degenerateSite
  v₁ := degenerateSite
  u₂ := degenerateSite
  v₂ := degenerateSite
  γ₁ := degenerateWalk
  γ₂ := degenerateWalk
  isSymm := by
    simp [IsSymmetricPair, degenerateWalk, degenerateSite, diagReflFun]
  G := {degenerateSite}
  finite := Set.finite_singleton degenerateSite
  γ₁_subset := by simp [degenerateWalk]
  γ₂_subset := by simp [degenerateWalk]
  G_symm := by
    simp [degenerateSite, diagReflFun]



theorem mixedDualComplementRN_isEmpty_of_all_connected
    (D : SymmetricDomain) (q : Real)
    (hall : ∀ omega, D.MixedConnected omega) :
    IsEmpty (MixedDualComplementRN D q) := by
  constructor
  intro R
  let omega : ConfigSpace (Sym2 D.Vertex) := fun _ => false
  have hdual : D.MixedConnected (R.dual omega) := hall _
  have hnot : ¬D.MixedConnected omega :=
    (R.connected_dual_iff omega).mp hdual
  exact hnot (hall omega)



theorem mixedDualComplementRN_isEmpty_of_all_disconnected
    (D : SymmetricDomain) (q : Real)
    (hall : ∀ omega, ¬D.MixedConnected omega) :
    IsEmpty (MixedDualComplementRN D q) := by
  constructor
  intro R
  let omega : ConfigSpace (Sym2 D.Vertex) := fun _ => false
  have hdual : D.MixedConnected (R.dual omega) :=
    (R.connected_dual_iff omega).mpr (hall omega)
  exact hall (R.dual omega) hdual



theorem degenerate_openConnected_all
    (omega : ConfigSpace (Sym2 degenerateSymmetricDomain.Vertex)) :
    degenerateSymmetricDomain.OpenConnected omega := by
  let x := degenerateSymmetricDomain.gammaOneStart
  let y := degenerateSymmetricDomain.gammaTwoStart
  have hxy : x = y := Subtype.ext (by rfl)
  refine ⟨x, y, onGammaOne_gammaOneStart _,
    onGammaTwo_gammaTwoStart _, ?_⟩
  rw [hxy]



theorem degenerate_mixedConnected_all
    (omega : ConfigSpace (Sym2 degenerateSymmetricDomain.Vertex)) :
    degenerateSymmetricDomain.MixedConnected omega :=
  (mixedConnected_iff_openConnected degenerateSymmetricDomain omega).2
    (degenerate_openConnected_all omega)



theorem degenerate_mixedDualComplementRN_isEmpty (q : Real) :
    IsEmpty (MixedDualComplementRN degenerateSymmetricDomain q) :=
  mixedDualComplementRN_isEmpty_of_all_connected
    degenerateSymmetricDomain q degenerate_mixedConnected_all




def separatedSiteOne : Site 2 := ![0, 1]
def separatedSiteTwo : Site 2 := ![1, 0]

@[simp] theorem diagReflFun_separatedSiteOne :
    diagReflFun separatedSiteOne = separatedSiteTwo := by
  rfl

@[simp] theorem diagReflFun_separatedSiteTwo :
    diagReflFun separatedSiteTwo = separatedSiteOne := by
  rfl




def separatedSymmetricDomain : SymmetricDomain where
  u₁ := separatedSiteOne
  v₁ := separatedSiteOne
  u₂ := separatedSiteTwo
  v₂ := separatedSiteTwo
  γ₁ := SimpleGraph.Walk.nil
  γ₂ := SimpleGraph.Walk.nil
  isSymm := by
    simp [IsSymmetricPair]
  G := {separatedSiteOne, separatedSiteTwo}
  finite := Set.toFinite _
  γ₁_subset := by simp
  γ₂_subset := by simp
  G_symm := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl
      · exact Or.inr rfl
      · exact Or.inl rfl
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact ⟨separatedSiteTwo, by simp, by simp⟩
      · exact ⟨separatedSiteOne, by simp, by simp⟩


theorem separated_finiteGraph_eq_bot :
    separatedSymmetricDomain.finiteGraph = ⊥ := by
  ext x y
  constructor
  · intro hxy
    have hx : (x.1 : Site 2) = separatedSiteOne ∨
        (x.1 : Site 2) = separatedSiteTwo := by
      have hxmem := x.2
      change x.1 ∈ ({separatedSiteOne, separatedSiteTwo} : Set (Site 2)) at hxmem
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hxmem
    have hy : (y.1 : Site 2) = separatedSiteOne ∨
        (y.1 : Site 2) = separatedSiteTwo := by
      have hymem := y.2
      change y.1 ∈ ({separatedSiteOne, separatedSiteTwo} : Set (Site 2)) at hymem
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hymem
    change (hypercubicLattice 2).Adj x.1 y.1 at hxy
    rcases hx with hx | hx <;> rcases hy with hy | hy <;>
      rw [hx, hy, hypercubicLattice_adj, Fin.sum_univ_two] at hxy <;>
      norm_num [separatedSiteOne, separatedSiteTwo] at hxy
  · simp



theorem separated_not_openConnected
    (omega : ConfigSpace (Sym2 separatedSymmetricDomain.Vertex)) :
    ¬separatedSymmetricDomain.OpenConnected omega := by
  rintro ⟨x, y, hx, hy, hxy⟩
  have hxval : (x.1 : Site 2) = separatedSiteOne := by
    simpa [OnGammaOne, separatedSymmetricDomain] using hx
  have hyval : (y.1 : Site 2) = separatedSiteTwo := by
    simpa [OnGammaTwo, separatedSymmetricDomain] using hy
  have hbot : (FK.openSub separatedSymmetricDomain.finiteGraph omega) = ⊥ := by
    rw [separated_finiteGraph_eq_bot]
    ext u v
    simp [FK.openSub]
  rw [hbot] at hxy
  have hxyEq : x = y := by simpa using hxy
  have hval := congrArg Subtype.val hxyEq
  rw [hxval, hyval] at hval
  norm_num [separatedSiteOne, separatedSiteTwo] at hval



theorem separated_not_mixedConnected
    (omega : ConfigSpace (Sym2 separatedSymmetricDomain.Vertex)) :
    ¬separatedSymmetricDomain.MixedConnected omega := by
  rw [mixedConnected_iff_openConnected]
  exact separated_not_openConnected omega


theorem separated_openConnectionProbability_eq_zero (q : Real) :
    separatedSymmetricDomain.openConnectionProbability q = 0 := by
  unfold openConnectionProbability
  apply Finset.sum_eq_zero
  intro omega _
  simp [separated_not_openConnected omega]




theorem separated_selfDuality_lower_bound_false :
    ¬(1 / (1 + (1 : Real) ^ 2) ≤
      separatedSymmetricDomain.openConnectionProbability 1) := by
  rw [separated_openConnectionProbability_eq_zero]
  norm_num


theorem separated_mixedDualComplementRN_isEmpty (q : Real) :
    IsEmpty (MixedDualComplementRN separatedSymmetricDomain q) :=
  mixedDualComplementRN_isEmpty_of_all_disconnected
    separatedSymmetricDomain q separated_not_mixedConnected




def connectedBridgeSite : Site 2 := ![0, 0]

@[simp] theorem diagReflFun_connectedBridgeSite :
    diagReflFun connectedBridgeSite = connectedBridgeSite := by
  rfl




def connectedSymmetricDomain : SymmetricDomain where
  u₁ := separatedSiteOne
  v₁ := separatedSiteOne
  u₂ := separatedSiteTwo
  v₂ := separatedSiteTwo
  γ₁ := SimpleGraph.Walk.nil
  γ₂ := SimpleGraph.Walk.nil
  isSymm := by
    simp [IsSymmetricPair]
  G := {separatedSiteOne, separatedSiteTwo, connectedBridgeSite}
  finite := Set.toFinite _
  γ₁_subset := by simp
  γ₂_subset := by simp
  G_symm := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
      rcases hx with rfl | rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl rfl
      · exact Or.inr (Or.inr rfl)
    · intro hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact ⟨separatedSiteTwo, by simp, by simp⟩
      · exact ⟨separatedSiteOne, by simp, by simp⟩
      · exact ⟨connectedBridgeSite, by simp, by simp⟩


def connectedVertexOne : connectedSymmetricDomain.Vertex :=
  ⟨separatedSiteOne, by simp [connectedSymmetricDomain]⟩

def connectedVertexTwo : connectedSymmetricDomain.Vertex :=
  ⟨separatedSiteTwo, by simp [connectedSymmetricDomain]⟩

def connectedVertexBridge : connectedSymmetricDomain.Vertex :=
  ⟨connectedBridgeSite, by simp [connectedSymmetricDomain]⟩

@[simp] theorem connected_adj_one_bridge :
    connectedSymmetricDomain.finiteGraph.Adj
      connectedVertexOne connectedVertexBridge := by
  norm_num [finiteGraph, connectedVertexOne, connectedVertexBridge,
    separatedSiteOne, connectedBridgeSite, hypercubicLattice_adj,
    Fin.sum_univ_two]

@[simp] theorem connected_adj_two_bridge :
    connectedSymmetricDomain.finiteGraph.Adj
      connectedVertexTwo connectedVertexBridge := by
  norm_num [finiteGraph, connectedVertexTwo, connectedVertexBridge,
    separatedSiteTwo, connectedBridgeSite, hypercubicLattice_adj,
    Fin.sum_univ_two]


theorem bcProb_one_eq_fkProb_one {V : Type*} [Fintype V] [DecidableEq V]
    (G C : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel C.Adj]
    (p : Real) (omega : ConfigSpace (Sym2 V)) :
    FK.bcProb G C p 1 omega = FK.fkProb G p 1 omega := by
  have hw : ∀ eta, FK.bcWeight G C p 1 eta = FK.fkWeight G p 1 eta := by
    intro eta
    simp [FK.bcWeight, FK.fkWeight]
  have hZ : FK.bcZ G C p 1 = FK.fkZ G p 1 := by
    rw [FK.bcZ, FK.fkZ]
    exact Finset.sum_congr rfl (fun eta _ => hw eta)
  rw [FK.bcProb, FK.fkProb, hw, hZ]

theorem connected_vertex_cases (z : connectedSymmetricDomain.Vertex) :
    z = connectedVertexOne ∨ z = connectedVertexTwo ∨
      z = connectedVertexBridge := by
  have hz := z.2
  change z.1 ∈ ({separatedSiteOne, separatedSiteTwo,
    connectedBridgeSite} : Set (Site 2)) at hz
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
  rcases hz with hz | hz | hz
  · exact Or.inl (Subtype.ext hz)
  · exact Or.inr (Or.inl (Subtype.ext hz))
  · exact Or.inr (Or.inr (Subtype.ext hz))

theorem connected_vertex_one_ne_two :
    connectedVertexOne ≠ connectedVertexTwo := by
  intro h
  have hv := congrArg Subtype.val h
  norm_num [connectedVertexOne, connectedVertexTwo,
    separatedSiteOne, separatedSiteTwo] at hv


theorem connected_finiteGraph_connected :
    connectedSymmetricDomain.finiteGraph.Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  refine ⟨connectedVertexOne, ?_⟩
  intro z
  rcases connected_vertex_cases z with rfl | rfl | rfl
  · exact SimpleGraph.Reachable.rfl
  · exact connected_adj_one_bridge.reachable.trans
      connected_adj_two_bridge.symm.reachable
  · exact connected_adj_one_bridge.reachable


theorem connected_boundary_paths_disjoint :
    connectedSymmetricDomain.γ₁.support ∩
      connectedSymmetricDomain.γ₂.support = ∅ := by
  ext z
  simp [connectedSymmetricDomain, separatedSiteOne, separatedSiteTwo]



theorem connected_openConnected_iff
    (omega : ConfigSpace (Sym2 connectedSymmetricDomain.Vertex)) :
    connectedSymmetricDomain.OpenConnected omega ↔
      omega s(connectedVertexOne, connectedVertexBridge) = true ∧
      omega s(connectedVertexTwo, connectedVertexBridge) = true := by
  constructor
  · rintro ⟨x, y, hx, hy, hreach⟩
    have hxEq : x = connectedVertexOne := by
      apply Subtype.ext
      simpa [OnGammaOne, connectedSymmetricDomain,
        connectedVertexOne] using hx
    have hyEq : y = connectedVertexTwo := by
      apply Subtype.ext
      simpa [OnGammaTwo, connectedSymmetricDomain,
        connectedVertexTwo] using hy
    subst x
    subst y
    constructor
    · by_contra hone
      apply (SimpleGraph.not_reachable_of_neighborSet_left_eq_empty
        connected_vertex_one_ne_two ?_) hreach
      ext z
      simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false,
        iff_false]
      intro haz
      rw [FK.openSub_adj] at haz
      rcases connected_vertex_cases z with rfl | rfl | rfl
      · exact haz.1.ne rfl
      · norm_num [finiteGraph, connectedVertexOne, connectedVertexTwo,
          separatedSiteOne, separatedSiteTwo, hypercubicLattice_adj,
          Fin.sum_univ_two] at haz
      · exact hone haz.2
    · by_contra htwo
      apply (SimpleGraph.not_reachable_of_neighborSet_right_eq_empty
        connected_vertex_one_ne_two ?_) hreach
      ext z
      simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false,
        iff_false]
      intro haz
      rw [FK.openSub_adj] at haz
      rcases connected_vertex_cases z with rfl | rfl | rfl
      · norm_num [finiteGraph, connectedVertexOne, connectedVertexTwo,
          separatedSiteOne, separatedSiteTwo, hypercubicLattice_adj,
          Fin.sum_univ_two] at haz
      · exact haz.1.ne rfl
      · apply htwo
        simpa only [Sym2.eq_swap] using haz.2
  · rintro ⟨hone, htwo⟩
    refine ⟨connectedVertexOne, connectedVertexTwo, ?_, ?_, ?_⟩
    · simp [OnGammaOne, connectedSymmetricDomain, connectedVertexOne]
    · simp [OnGammaTwo, connectedSymmetricDomain, connectedVertexTwo]
    · apply SimpleGraph.Reachable.trans
        ((FK.openSub_adj _ _ _ _).2 ⟨connected_adj_one_bridge, hone⟩).reachable
      apply ((FK.openSub_adj _ _ _ _).2
        ⟨connected_adj_two_bridge.symm, ?_⟩).reachable
      simpa only [Sym2.eq_swap] using htwo



def connectedRequiredEdges :
    Finset (Sym2 connectedSymmetricDomain.Vertex) :=
  {s(connectedVertexOne, connectedVertexBridge),
    s(connectedVertexTwo, connectedVertexBridge)}

theorem connectedRequiredEdges_subset :
    connectedRequiredEdges ⊆ connectedSymmetricDomain.finiteGraph.edgeFinset := by
  intro e he
  simp only [connectedRequiredEdges, Finset.mem_insert,
    Finset.mem_singleton] at he
  rcases he with rfl | rfl
  · simpa only [SimpleGraph.mem_edgeFinset] using connected_adj_one_bridge
  · simpa only [SimpleGraph.mem_edgeFinset] using connected_adj_two_bridge

@[simp] theorem connectedRequiredEdges_card :
    connectedRequiredEdges.card = 2 := by
  simp [connectedRequiredEdges, connectedVertexOne, connectedVertexTwo,
    connectedVertexBridge, separatedSiteOne, separatedSiteTwo,
    connectedBridgeSite]




theorem connected_openConnectionProbability_eq_quarter :
    connectedSymmetricDomain.openConnectionProbability 1 = 1 / 4 := by
  have hsd : selfDualPoint 1 = (1 / 2 : Real) := by
    norm_num [selfDualPoint]
  unfold openConnectionProbability mixedMass
  rw [hsd]
  simp_rw [bcProb_one_eq_fkProb_one]
  calc
    (∑ omega : ConfigSpace (Sym2 connectedSymmetricDomain.Vertex),
        if connectedSymmetricDomain.OpenConnected omega then
          FK.fkProb connectedSymmetricDomain.finiteGraph (1 / 2) 1 omega
        else 0) =
      ∑ omega : ConfigSpace (Sym2 connectedSymmetricDomain.Vertex),
        (if (∀ e ∈ connectedRequiredEdges, omega e = true) then
          (1 : Real) else 0) *
          FK.fkProb connectedSymmetricDomain.finiteGraph (1 / 2) 1 omega := by
        apply Finset.sum_congr rfl
        intro omega _
        simp only [connected_openConnected_iff]
        simp [connectedRequiredEdges]
    _ = (1 / 2 : Real) ^ connectedRequiredEdges.card :=
      FK.fkProbOne_cylinder (G := connectedSymmetricDomain.finiteGraph)
        (by norm_num) (by norm_num) connectedRequiredEdges
        connectedRequiredEdges_subset
    _ = 1 / 4 := by norm_num



theorem connected_selfDuality_lower_bound_false :
    ¬(1 / (1 + (1 : Real) ^ 2) ≤
      connectedSymmetricDomain.openConnectionProbability 1) := by
  rw [connected_openConnectionProbability_eq_quarter]
  norm_num



theorem connected_mixedDualComplementRN_isEmpty :
    IsEmpty (MixedDualComplementRN connectedSymmetricDomain 1) := by
  constructor
  intro R
  apply connected_selfDuality_lower_bound_false
  exact openConnectionProbability_ge_one_div_one_add_q_sq
    connectedSymmetricDomain (by norm_num) R



theorem not_all_symmetricDomain_selfDuality_lower_bounds :
    ¬∀ D : SymmetricDomain,
      1 / (1 + (1 : Real) ^ 2) ≤ D.openConnectionProbability 1 := by
  intro hall
  exact separated_selfDuality_lower_bound_false (hall separatedSymmetricDomain)



theorem no_universal_mixedDualComplementRN (q : Real) :
    ¬∀ D : SymmetricDomain, Nonempty (MixedDualComplementRN D q) := by
  intro hall
  rcases hall separatedSymmetricDomain with ⟨R⟩
  exact (separated_mixedDualComplementRN_isEmpty q).false R

end

end SymmetricDomain
end BeffaraDC
end StatMech
