/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


















import Code.BeffaraDC.AnnulusDefs
import Code.BeffaraDC.PlanarFKDuality
import Code.FK.MonoBC

open Finset SimpleGraph
open scoped BigOperators
open StatMech.Lattice

namespace StatMech
namespace BeffaraDC

noncomputable section

namespace SymmetricDomain


abbrev Vertex (D : SymmetricDomain) := {x : Site 2 // x ∈ D.G}

noncomputable instance instFintypeVertex (D : SymmetricDomain) :
    Fintype D.Vertex :=
  Set.Finite.fintype D.finite


def finiteGraph (D : SymmetricDomain) : SimpleGraph D.Vertex :=
  (hypercubicLattice 2).comap Subtype.val

noncomputable instance instFiniteGraphDecidableAdj (D : SymmetricDomain) :
    DecidableRel D.finiteGraph.Adj :=
  Classical.decRel _



def planarDomain (D : SymmetricDomain) : PlanarZ2Subgraph where
  V := D.Vertex
  finV := inferInstance
  decV := inferInstance
  G := D.finiteGraph
  emb := ⟨Subtype.val, Subtype.val_injective⟩
  isSub := by
    intro x y hxy
    exact hxy


def OnGammaOne (D : SymmetricDomain) (x : D.Vertex) : Prop :=
  x.1 ∈ D.γ₁.support


def OnGammaTwo (D : SymmetricDomain) (x : D.Vertex) : Prop :=
  x.1 ∈ D.γ₂.support

instance instDecidablePredOnGammaOne (D : SymmetricDomain) :
    DecidablePred D.OnGammaOne := Classical.decPred _

instance instDecidablePredOnGammaTwo (D : SymmetricDomain) :
    DecidablePred D.OnGammaTwo := Classical.decPred _


def gammaOneStart (D : SymmetricDomain) : D.Vertex :=
  ⟨D.u₁, D.γ₁_subset D.γ₁.start_mem_support⟩


def gammaTwoStart (D : SymmetricDomain) : D.Vertex :=
  ⟨D.u₂, D.γ₂_subset D.γ₂.start_mem_support⟩

@[simp] theorem onGammaOne_gammaOneStart (D : SymmetricDomain) :
    D.OnGammaOne D.gammaOneStart := by
  exact D.γ₁.start_mem_support

@[simp] theorem onGammaTwo_gammaTwoStart (D : SymmetricDomain) :
    D.OnGammaTwo D.gammaTwoStart := by
  exact D.γ₂.start_mem_support




def mixedWiring (D : SymmetricDomain) : SimpleGraph D.Vertex :=
  StatMech.Lattice.boundaryCliqueGraph D.OnGammaOne ⊔
    StatMech.Lattice.boundaryCliqueGraph D.OnGammaTwo

noncomputable instance instMixedWiringDecidableAdj (D : SymmetricDomain) :
    DecidableRel D.mixedWiring.Adj :=
  Classical.decRel _


def MixedConnected (D : SymmetricDomain)
    (omega : ConfigSpace (Sym2 D.Vertex)) : Prop :=
  ∃ x y : D.Vertex,
    D.OnGammaOne x ∧ D.OnGammaTwo y ∧
      (FK.openSub D.finiteGraph omega ⊔ D.mixedWiring).Reachable x y

noncomputable instance instMixedConnectedDecidable (D : SymmetricDomain) :
    DecidablePred D.MixedConnected :=
  Classical.decPred _



def OpenConnected (D : SymmetricDomain)
    (omega : ConfigSpace (Sym2 D.Vertex)) : Prop :=
  ∃ x y : D.Vertex,
    D.OnGammaOne x ∧ D.OnGammaTwo y ∧
      (FK.openSub D.finiteGraph omega).Reachable x y

noncomputable instance instOpenConnectedDecidable (D : SymmetricDomain) :
    DecidablePred D.OpenConnected :=
  Classical.decPred _




theorem mixedConnected_iff_openConnected (D : SymmetricDomain)
    (omega : ConfigSpace (Sym2 D.Vertex)) :
    D.MixedConnected omega ↔ D.OpenConnected omega := by
  let O := FK.openSub D.finiteGraph omega
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    apply hxy.elim
    intro p
    let P : D.Vertex → Prop := fun z =>
      (∃ a, D.OnGammaOne a ∧ O.Reachable a z) ∨ D.OpenConnected omega
    have hP : P y :=
      (SimpleGraph.Walk.concatRec
        (motive := fun u z _ => D.OnGammaOne u → P z)
        (fun {u} hu => Or.inl ⟨u, hu, SimpleGraph.Reachable.rfl⟩)
        (fun {u v w} p huv ih hu => by
          have ih' := ih hu
          rw [SimpleGraph.sup_adj, mixedWiring, SimpleGraph.sup_adj] at huv
          rcases huv with hopen | hone | htwo
          · rcases ih' with ⟨a, ha, hau⟩ | hconn
            · exact Or.inl ⟨a, ha, hau.trans hopen.reachable⟩
            · exact Or.inr hconn
          · rcases ih' with hreach | hconn
            · have hw : D.OnGammaOne w :=
                (StatMech.Lattice.boundaryCliqueGraph_adj
                  D.OnGammaOne v w).mp hone |>.2.2
              exact Or.inl ⟨w, hw, SimpleGraph.Reachable.rfl⟩
            · exact Or.inr hconn
          · rcases ih' with ⟨a, ha, hau⟩ | hconn
            · have hv : D.OnGammaTwo v :=
                (StatMech.Lattice.boundaryCliqueGraph_adj
                  D.OnGammaTwo v w).mp htwo |>.2.1
              exact Or.inr ⟨a, v, ha, hv, hau⟩
            · exact Or.inr hconn)
        p) hx
    rcases hP with ⟨a, ha, hay⟩ | hconn
    · exact ⟨a, y, ha, hy, hay⟩
    · exact hconn
  · rintro ⟨x, y, hx, hy, hxy⟩
    exact ⟨x, y, hx, hy, hxy.mono le_sup_left⟩


noncomputable def mixedMass (D : SymmetricDomain) (q : Real)
    (omega : ConfigSpace (Sym2 D.Vertex)) : Real :=
  FK.bcProb D.finiteGraph D.mixedWiring (selfDualPoint q) q omega


noncomputable def mixedConnectionProbability (D : SymmetricDomain) (q : Real) : Real :=
  ∑ omega : ConfigSpace (Sym2 D.Vertex),
    if D.MixedConnected omega then D.mixedMass q omega else 0


noncomputable def openConnectionProbability (D : SymmetricDomain) (q : Real) : Real :=
  ∑ omega : ConfigSpace (Sym2 D.Vertex),
    if D.OpenConnected omega then D.mixedMass q omega else 0



theorem mixedConnectionProbability_eq_openConnectionProbability
    (D : SymmetricDomain) (q : Real) :
    D.mixedConnectionProbability q = D.openConnectionProbability q := by
  unfold mixedConnectionProbability openConnectionProbability
  apply Finset.sum_congr rfl
  intro omega _
  simp only [mixedConnected_iff_openConnected]


noncomputable def mixedDisconnectionProbability (D : SymmetricDomain) (q : Real) : Real :=
  ∑ omega : ConfigSpace (Sym2 D.Vertex),
    if ¬D.MixedConnected omega then D.mixedMass q omega else 0


theorem mixedConnection_add_disconnection_eq_one
    (D : SymmetricDomain) {q : Real} (hq : 1 ≤ q) :
    D.mixedConnectionProbability q + D.mixedDisconnectionProbability q = 1 := by
  have hq0 : 0 < q := one_pos.trans_le hq
  obtain ⟨hp0, hp1⟩ := selfDualPoint_mem_Ioo hq0
  rw [mixedConnectionProbability, mixedDisconnectionProbability,
    ← Finset.sum_add_distrib]
  calc
    (∑ omega : ConfigSpace (Sym2 D.Vertex),
        ((if D.MixedConnected omega then D.mixedMass q omega else 0) +
          if ¬D.MixedConnected omega then D.mixedMass q omega else 0)) =
        ∑ omega : ConfigSpace (Sym2 D.Vertex), D.mixedMass q omega := by
          apply Finset.sum_congr rfl
          intro omega _
          by_cases hconn : D.MixedConnected omega <;> simp [hconn]
    _ = 1 := FK.bcProb_sum_eq_one D.finiteGraph D.mixedWiring hp0 hp1 hq0







structure MixedDualComplementRN (D : SymmetricDomain) (q : Real) where
  dual : ConfigSpace (Sym2 D.Vertex) ≃ ConfigSpace (Sym2 D.Vertex)
  connected_dual_iff : ∀ omega,
    D.MixedConnected (dual omega) ↔ ¬D.MixedConnected omega
  rn_upper : ∀ eta,
    D.mixedMass q (dual.symm eta) ≤ q ^ 2 * D.mixedMass q eta



noncomputable def MixedDualComplementRN.disconnectedEquivConnected
    {D : SymmetricDomain} {q : Real} (R : MixedDualComplementRN D q) :
    {omega : ConfigSpace (Sym2 D.Vertex) // ¬D.MixedConnected omega} ≃
      {eta : ConfigSpace (Sym2 D.Vertex) // D.MixedConnected eta} where
  toFun omega := ⟨R.dual omega.1,
    (R.connected_dual_iff omega.1).mpr omega.2⟩
  invFun eta := ⟨R.dual.symm eta.1, by
    apply (R.connected_dual_iff (R.dual.symm eta.1)).mp
    simpa using eta.2⟩
  left_inv omega := by
    apply Subtype.ext
    exact R.dual.symm_apply_apply omega.1
  right_inv eta := by
    apply Subtype.ext
    exact R.dual.apply_symm_apply eta.1




theorem MixedDualComplementRN.card_disconnected_eq_card_connected
    {D : SymmetricDomain} {q : Real} (R : MixedDualComplementRN D q) :
    Fintype.card
        {omega : ConfigSpace (Sym2 D.Vertex) // ¬D.MixedConnected omega} =
      Fintype.card
        {eta : ConfigSpace (Sym2 D.Vertex) // D.MixedConnected eta} :=
  Fintype.card_congr R.disconnectedEquivConnected



theorem MixedDualComplementRN.exists_connected_and_disconnected
    {D : SymmetricDomain} {q : Real} (R : MixedDualComplementRN D q) :
    (∃ omega, D.MixedConnected omega) ∧
      ∃ eta, ¬D.MixedConnected eta := by
  let omega : ConfigSpace (Sym2 D.Vertex) := fun _ => false
  by_cases hconnected : D.MixedConnected omega
  · refine ⟨⟨omega, hconnected⟩, ?_⟩
    let eta := R.dual.symm omega
    refine ⟨eta, ?_⟩
    apply (R.connected_dual_iff eta).mp
    simpa [eta] using hconnected
  · exact ⟨⟨R.dual omega,
      (R.connected_dual_iff omega).mpr hconnected⟩, ⟨omega, hconnected⟩⟩





def BoundaryBlocksOverlap (D : SymmetricDomain) : Prop :=
  ∃ x : D.Vertex, D.OnGammaOne x ∧ D.OnGammaTwo x



theorem mixedConnected_all_of_boundaryBlocksOverlap
    (D : SymmetricDomain) (h : D.BoundaryBlocksOverlap)
    (omega : ConfigSpace (Sym2 D.Vertex)) :
    D.MixedConnected omega := by
  obtain ⟨x, hx₁, hx₂⟩ := h
  exact ⟨x, x, hx₁, hx₂, SimpleGraph.Reachable.rfl⟩




theorem no_mixedDualComplementRN_of_boundaryBlocksOverlap
    (D : SymmetricDomain) (q : Real) (h : D.BoundaryBlocksOverlap) :
    MixedDualComplementRN D q → False := by
  intro R
  let omega : ConfigSpace (Sym2 D.Vertex) := fun _ => false
  have hconnected : D.MixedConnected (R.dual omega) :=
    mixedConnected_all_of_boundaryBlocksOverlap D h _
  have hnot : ¬D.MixedConnected omega :=
    (R.connected_dual_iff omega).mp hconnected
  exact hnot (mixedConnected_all_of_boundaryBlocksOverlap D h omega)



def overlappingSingletonDomain : SymmetricDomain where
  u₁ := ![0, 0]
  v₁ := ![0, 0]
  u₂ := ![0, 0]
  v₂ := ![0, 0]
  γ₁ := SimpleGraph.Walk.nil
  γ₂ := SimpleGraph.Walk.nil
  isSymm := by
    simp [IsSymmetricPair]
  G := {![0, 0]}
  finite := Set.finite_singleton _
  γ₁_subset := by simp
  γ₂_subset := by simp
  G_symm := by
    simp [diagReflFun_apply]


theorem overlappingSingletonDomain_boundaryBlocksOverlap :
    overlappingSingletonDomain.BoundaryBlocksOverlap := by
  refine ⟨⟨![0, 0], by simp [overlappingSingletonDomain]⟩, ?_, ?_⟩ <;>
    simp [OnGammaOne, OnGammaTwo, overlappingSingletonDomain]



theorem overlappingSingletonDomain_no_mixedDualComplementRN (q : Real) :
    MixedDualComplementRN overlappingSingletonDomain q → False :=
  no_mixedDualComplementRN_of_boundaryBlocksOverlap _ q
    overlappingSingletonDomain_boundaryBlocksOverlap


def disjointLeftPoint : Site 2 := ![0, 1]


def disjointRightPoint : Site 2 := ![1, 0]



def disjointDisconnectedDomain : SymmetricDomain where
  u₁ := disjointLeftPoint
  v₁ := disjointLeftPoint
  u₂ := disjointRightPoint
  v₂ := disjointRightPoint
  γ₁ := SimpleGraph.Walk.nil
  γ₂ := SimpleGraph.Walk.nil
  isSymm := by
    simp [IsSymmetricPair, disjointLeftPoint, disjointRightPoint]
  G := {disjointLeftPoint, disjointRightPoint}
  finite := (Set.finite_singleton disjointRightPoint).insert disjointLeftPoint
  γ₁_subset := by simp
  γ₂_subset := by simp
  G_symm := by
    ext z
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, (rfl | rfl), rfl⟩
      · exact Or.inr (by
          simp [diagReflFun, disjointLeftPoint, disjointRightPoint])
      · exact Or.inl (by
          simp [diagReflFun, disjointLeftPoint, disjointRightPoint])
    · rintro (rfl | rfl)
      · refine ⟨disjointRightPoint, Or.inr rfl, ?_⟩
        simp [diagReflFun, disjointLeftPoint, disjointRightPoint]
      · refine ⟨disjointLeftPoint, Or.inl rfl, ?_⟩
        simp [diagReflFun, disjointLeftPoint, disjointRightPoint]



theorem disjointDisconnectedDomain_boundaryBlocksDisjoint :
    ¬disjointDisconnectedDomain.BoundaryBlocksOverlap := by
  rintro ⟨x, hx₁, hx₂⟩
  have hleft : x.1 = disjointLeftPoint := by
    simpa [OnGammaOne, disjointDisconnectedDomain] using hx₁
  have hright : x.1 = disjointRightPoint := by
    simpa [OnGammaTwo, disjointDisconnectedDomain] using hx₂
  have := hleft.symm.trans hright
  simp [disjointLeftPoint, disjointRightPoint] at this



theorem disjointDisconnectedDomain_finiteGraph_no_adj
    (x y : disjointDisconnectedDomain.Vertex) :
    ¬disjointDisconnectedDomain.finiteGraph.Adj x y := by
  intro hxy
  have hx : x.1 = disjointLeftPoint ∨ x.1 = disjointRightPoint := by
    have hxmem := x.2
    change x.1 ∈ ({disjointLeftPoint, disjointRightPoint} : Set (Site 2)) at hxmem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hxmem
  have hy : y.1 = disjointLeftPoint ∨ y.1 = disjointRightPoint := by
    have hymem := y.2
    change y.1 ∈ ({disjointLeftPoint, disjointRightPoint} : Set (Site 2)) at hymem
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hymem
  rcases hx with hx | hx <;> rcases hy with hy | hy <;>
    simp [finiteGraph, hypercubicLattice_adj, Fin.sum_univ_two, hx, hy,
      disjointLeftPoint, disjointRightPoint] at hxy



theorem disjointDisconnectedDomain_mixedWiring_no_adj
    (x y : disjointDisconnectedDomain.Vertex) :
    ¬disjointDisconnectedDomain.mixedWiring.Adj x y := by
  rw [mixedWiring, SimpleGraph.sup_adj]
  rintro (hgamma | hgamma)
  · rw [StatMech.Lattice.boundaryCliqueGraph_adj] at hgamma
    apply hgamma.1
    apply Subtype.ext
    have hx : x.1 = disjointLeftPoint := by
      simpa [OnGammaOne, disjointDisconnectedDomain] using hgamma.2.1
    have hy : y.1 = disjointLeftPoint := by
      simpa [OnGammaOne, disjointDisconnectedDomain] using hgamma.2.2
    exact hx.trans hy.symm
  · rw [StatMech.Lattice.boundaryCliqueGraph_adj] at hgamma
    apply hgamma.1
    apply Subtype.ext
    have hx : x.1 = disjointRightPoint := by
      simpa [OnGammaTwo, disjointDisconnectedDomain] using hgamma.2.1
    have hy : y.1 = disjointRightPoint := by
      simpa [OnGammaTwo, disjointDisconnectedDomain] using hgamma.2.2
    exact hx.trans hy.symm



theorem disjointDisconnectedDomain_not_mixedConnected
    (omega : ConfigSpace (Sym2 disjointDisconnectedDomain.Vertex)) :
    ¬disjointDisconnectedDomain.MixedConnected omega := by
  rintro ⟨x, y, hx, hy, hreach⟩
  have hgraph :
      FK.openSub disjointDisconnectedDomain.finiteGraph omega ⊔
          disjointDisconnectedDomain.mixedWiring = ⊥ := by
    ext u v
    simp only [SimpleGraph.sup_adj, SimpleGraph.bot_adj, iff_false, not_or]
    exact ⟨fun huv => disjointDisconnectedDomain_finiteGraph_no_adj u v
        (FK.openSub_le disjointDisconnectedDomain.finiteGraph omega huv),
      disjointDisconnectedDomain_mixedWiring_no_adj u v⟩
  rw [hgraph, SimpleGraph.reachable_bot] at hreach
  have hleft : x.1 = disjointLeftPoint := by
    simpa [OnGammaOne, disjointDisconnectedDomain] using hx
  have hright : y.1 = disjointRightPoint := by
    simpa [OnGammaTwo, disjointDisconnectedDomain] using hy
  have hpoints : disjointLeftPoint = disjointRightPoint :=
    hleft.symm.trans (congrArg Subtype.val hreach) |>.trans hright
  simp [disjointLeftPoint, disjointRightPoint] at hpoints



theorem disjointDisconnectedDomain_no_mixedDualComplementRN (q : Real) :
    MixedDualComplementRN disjointDisconnectedDomain q → False := by
  intro R
  let omega : ConfigSpace (Sym2 disjointDisconnectedDomain.Vertex) :=
    fun _ => false
  have hnot := disjointDisconnectedDomain_not_mixedConnected omega
  have hconnected :
      disjointDisconnectedDomain.MixedConnected (R.dual omega) :=
    (R.connected_dual_iff omega).mpr hnot
  exact disjointDisconnectedDomain_not_mixedConnected _ hconnected




def connectedVAxisPoint : Site 2 := ![0, 0]



def connectedVDomain : SymmetricDomain where
  u₁ := disjointLeftPoint
  v₁ := disjointLeftPoint
  u₂ := disjointRightPoint
  v₂ := disjointRightPoint
  γ₁ := SimpleGraph.Walk.nil
  γ₂ := SimpleGraph.Walk.nil
  isSymm := by
    simp [IsSymmetricPair, disjointLeftPoint, disjointRightPoint]
  G := {connectedVAxisPoint, disjointLeftPoint, disjointRightPoint}
  finite :=
    ((Set.finite_singleton disjointRightPoint).insert disjointLeftPoint).insert
      connectedVAxisPoint
  γ₁_subset := by simp
  γ₂_subset := by simp
  G_symm := by
    ext z
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, (rfl | rfl | rfl), rfl⟩
      · exact Or.inl (by simp [diagReflFun, connectedVAxisPoint])
      · exact Or.inr (Or.inr (by
          simp [diagReflFun, disjointLeftPoint, disjointRightPoint]))
      · exact Or.inr (Or.inl (by
          simp [diagReflFun, disjointLeftPoint, disjointRightPoint]))
    · rintro (rfl | rfl | rfl)
      · refine ⟨connectedVAxisPoint, Or.inl rfl, ?_⟩
        simp [diagReflFun, connectedVAxisPoint]
      · refine ⟨disjointRightPoint, Or.inr (Or.inr rfl), ?_⟩
        simp [diagReflFun, disjointLeftPoint, disjointRightPoint]
      · refine ⟨disjointLeftPoint, Or.inr (Or.inl rfl), ?_⟩
        simp [diagReflFun, disjointLeftPoint, disjointRightPoint]


def connectedVAxis : connectedVDomain.Vertex :=
  ⟨connectedVAxisPoint, by simp [connectedVDomain]⟩


def connectedVLeft : connectedVDomain.Vertex :=
  ⟨disjointLeftPoint, by simp [connectedVDomain]⟩


def connectedVRight : connectedVDomain.Vertex :=
  ⟨disjointRightPoint, by simp [connectedVDomain]⟩


theorem connectedVDomain_vertex_cases (x : connectedVDomain.Vertex) :
    x = connectedVAxis ∨ x = connectedVLeft ∨ x = connectedVRight := by
  have hx := x.2
  change x.1 ∈
    ({connectedVAxisPoint, disjointLeftPoint, disjointRightPoint} : Set (Site 2)) at hx
  rcases (by
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hx) with
    hx | hx | hx
  · exact Or.inl (Subtype.ext hx)
  · exact Or.inr (Or.inl (Subtype.ext hx))
  · exact Or.inr (Or.inr (Subtype.ext hx))


theorem connectedVDomain_left_axis_adj :
    connectedVDomain.finiteGraph.Adj connectedVLeft connectedVAxis := by
  simp [finiteGraph, hypercubicLattice_adj, Fin.sum_univ_two,
    connectedVLeft, connectedVAxis, connectedVAxisPoint, disjointLeftPoint]


theorem connectedVDomain_axis_right_adj :
    connectedVDomain.finiteGraph.Adj connectedVAxis connectedVRight := by
  simp [finiteGraph, hypercubicLattice_adj, Fin.sum_univ_two,
    connectedVRight, connectedVAxis, connectedVAxisPoint, disjointRightPoint]



theorem connectedVDomain_finiteGraph_connected :
    connectedVDomain.finiteGraph.Connected := by
  letI : Nonempty connectedVDomain.Vertex := ⟨connectedVAxis⟩
  refine SimpleGraph.Connected.mk ?_
  intro x y
  rcases connectedVDomain_vertex_cases x with rfl | rfl | rfl <;>
    rcases connectedVDomain_vertex_cases y with rfl | rfl | rfl
  · exact SimpleGraph.Reachable.rfl
  · exact connectedVDomain_left_axis_adj.symm.reachable
  · exact connectedVDomain_axis_right_adj.reachable
  · exact connectedVDomain_left_axis_adj.reachable
  · exact SimpleGraph.Reachable.rfl
  · exact connectedVDomain_left_axis_adj.reachable.trans
      connectedVDomain_axis_right_adj.reachable
  · exact connectedVDomain_axis_right_adj.symm.reachable
  · exact connectedVDomain_axis_right_adj.symm.reachable.trans
      connectedVDomain_left_axis_adj.symm.reachable
  · exact SimpleGraph.Reachable.rfl



theorem connectedVDomain_boundaryBlocksDisjoint :
    ¬connectedVDomain.BoundaryBlocksOverlap := by
  rintro ⟨x, hx₁, hx₂⟩
  have hleft : x.1 = disjointLeftPoint := by
    simpa [OnGammaOne, connectedVDomain] using hx₁
  have hright : x.1 = disjointRightPoint := by
    simpa [OnGammaTwo, connectedVDomain] using hx₂
  have := hleft.symm.trans hright
  simp [disjointLeftPoint, disjointRightPoint] at this


def connectedVLeftEdge : Sym2 connectedVDomain.Vertex :=
  s(connectedVLeft, connectedVAxis)

def connectedVRightEdge : Sym2 connectedVDomain.Vertex :=
  s(connectedVAxis, connectedVRight)


theorem connectedV_edges_ne : connectedVLeftEdge ≠ connectedVRightEdge := by
  intro h
  have hmem : connectedVLeft ∈ connectedVRightEdge := by
    rw [← h]
    simp [connectedVLeftEdge]
  simp [connectedVRightEdge, connectedVLeft, connectedVAxis, connectedVRight,
    connectedVAxisPoint, disjointLeftPoint, disjointRightPoint] at hmem




theorem connectedVDomain_mixedConnected_iff
    (omega : ConfigSpace (Sym2 connectedVDomain.Vertex)) :
    connectedVDomain.MixedConnected omega ↔
      omega connectedVLeftEdge = true ∧ omega connectedVRightEdge = true := by
  rw [mixedConnected_iff_openConnected]
  constructor
  · rintro ⟨x, y, hx, hy, hreach⟩
    have hxval : x.1 = disjointLeftPoint := by
      simpa [OnGammaOne, connectedVDomain] using hx
    have hyval : y.1 = disjointRightPoint := by
      simpa [OnGammaTwo, connectedVDomain] using hy
    have hxeq : x = connectedVLeft :=
      Subtype.ext hxval
    have hyeq : y = connectedVRight :=
      Subtype.ext hyval
    subst x
    subst y
    have hlr : connectedVLeft ≠ connectedVRight := by
      intro h
      have := congrArg Subtype.val h
      simp [connectedVLeft, connectedVRight, disjointLeftPoint,
        disjointRightPoint] at this
    constructor
    · by_contra hleft
      have hisolated :
          (FK.openSub connectedVDomain.finiteGraph omega).neighborSet
              connectedVLeft = ∅ := by
        ext z
        simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false, iff_false]
        rcases connectedVDomain_vertex_cases z with rfl | rfl | rfl
        · intro hopen
          rw [FK.openSub_adj] at hopen
          exact hleft (by simpa [connectedVLeftEdge] using hopen.2)
        · exact
            (FK.openSub connectedVDomain.finiteGraph omega).loopless.irrefl _
        · simp [FK.openSub_adj, finiteGraph, hypercubicLattice_adj,
            Fin.sum_univ_two, connectedVLeft, connectedVRight,
            disjointLeftPoint, disjointRightPoint]
      exact (SimpleGraph.not_reachable_of_neighborSet_left_eq_empty
        hlr hisolated) hreach
    · by_contra hright
      have hisolated :
          (FK.openSub connectedVDomain.finiteGraph omega).neighborSet
              connectedVRight = ∅ := by
        ext z
        simp only [SimpleGraph.mem_neighborSet, Set.mem_empty_iff_false, iff_false]
        rcases connectedVDomain_vertex_cases z with rfl | rfl | rfl
        · intro hopen
          rw [FK.openSub_adj] at hopen
          exact hright (by
            simpa [connectedVRightEdge, Sym2.eq_swap] using hopen.2)
        · simp [FK.openSub_adj, finiteGraph, hypercubicLattice_adj,
            Fin.sum_univ_two, connectedVLeft, connectedVRight,
            disjointLeftPoint, disjointRightPoint]
        · exact
            (FK.openSub connectedVDomain.finiteGraph omega).loopless.irrefl _
      exact (SimpleGraph.not_reachable_of_neighborSet_right_eq_empty
        hlr hisolated) hreach
  · rintro ⟨hleft, hright⟩
    refine ⟨connectedVLeft, connectedVRight, ?_, ?_, ?_⟩
    · simp [OnGammaOne, connectedVDomain, connectedVLeft]
    · simp [OnGammaTwo, connectedVDomain, connectedVRight]
    · exact (SimpleGraph.Adj.reachable
          ((FK.openSub_adj _ _ _ _).mpr
            ⟨connectedVDomain_left_axis_adj, hleft⟩)).trans
        (SimpleGraph.Adj.reachable
          ((FK.openSub_adj _ _ _ _).mpr
            ⟨connectedVDomain_axis_right_adj, hright⟩))






abbrev TwoCoordinateRemainder {E : Type*} (a b : E) (hab : a ≠ b) :=
  {j : {j : E // j ≠ a} // j ≠ (⟨b, hab.symm⟩ : {j : E // j ≠ a})}



noncomputable def twoCoordinateSplit {E : Type*} [Fintype E] [DecidableEq E]
    (a b : E) (hab : a ≠ b) :
    (E → Bool) ≃
      Bool × (Bool × (TwoCoordinateRemainder a b hab → Bool)) :=
  (Equiv.funSplitAt a Bool).trans
    (Equiv.prodCongr (Equiv.refl Bool)
      (Equiv.funSplitAt
        (⟨b, hab.symm⟩ : {j : E // j ≠ a}) Bool))



def boolPairTrueEquiv (R : Type*) :
    {p : Bool × (Bool × R) // p.1 = true ∧ p.2.1 = true} ≃ R where
  toFun p := p.1.2.2
  invFun r := ⟨(true, (true, r)), by simp⟩
  left_inv := by
    rintro ⟨⟨x, y, r⟩, hx, hy⟩
    change x = true at hx
    change y = true at hy
    subst x
    subst y
    rfl
  right_inv _ := rfl



noncomputable def twoCoordinateTrueEquiv {E : Type*} [Fintype E] [DecidableEq E]
    (a b : E) (hab : a ≠ b) :
    {omega : E → Bool // omega a = true ∧ omega b = true} ≃
      (TwoCoordinateRemainder a b hab → Bool) :=
  ((twoCoordinateSplit a b hab).subtypeEquiv (by
      intro omega
      simp [twoCoordinateSplit])).trans
    (boolPairTrueEquiv _)



theorem card_config_eq_four_mul_twoCoordinateRemainder
    {E : Type*} [Fintype E] [DecidableEq E] (a b : E) (hab : a ≠ b) :
    Fintype.card (E → Bool) =
      4 * Fintype.card (TwoCoordinateRemainder a b hab → Bool) := by
  calc
    Fintype.card (E → Bool) =
        Fintype.card
          (Bool × (Bool × (TwoCoordinateRemainder a b hab → Bool))) :=
      Fintype.card_congr (twoCoordinateSplit a b hab)
    _ = 4 * Fintype.card (TwoCoordinateRemainder a b hab → Bool) := by
      simp only [Fintype.card_prod, Fintype.card_bool]
      omega



theorem card_not_twoCoordinateTrue_eq_three_mul_card_twoCoordinateTrue
    {E : Type*} [Fintype E] [DecidableEq E] (a b : E) (hab : a ≠ b) :
    Fintype.card
        {omega : E → Bool // ¬(omega a = true ∧ omega b = true)} =
      3 * Fintype.card
        {omega : E → Bool // omega a = true ∧ omega b = true} := by
  classical
  let C := Fintype.card (TwoCoordinateRemainder a b hab → Bool)
  have htrue :
      Fintype.card
          {omega : E → Bool // omega a = true ∧ omega b = true} = C :=
    Fintype.card_congr (twoCoordinateTrueEquiv a b hab)
  have htotal : Fintype.card (E → Bool) = 4 * C :=
    card_config_eq_four_mul_twoCoordinateRemainder a b hab
  rw [Fintype.card_subtype_compl]
  rw [htrue, htotal]
  omega



theorem card_not_twoCoordinateTrue_ne_card_twoCoordinateTrue
    {E : Type*} [Fintype E] [DecidableEq E] (a b : E) (hab : a ≠ b) :
    Fintype.card
        {omega : E → Bool // ¬(omega a = true ∧ omega b = true)} ≠
      Fintype.card
        {omega : E → Bool // omega a = true ∧ omega b = true} := by
  classical
  have hratio :=
    card_not_twoCoordinateTrue_eq_three_mul_card_twoCoordinateTrue a b hab
  have hpos :
      0 < Fintype.card
        {omega : E → Bool // omega a = true ∧ omega b = true} := by
    apply Fintype.card_pos_iff.mpr
    exact ⟨⟨fun _ => true, by simp⟩⟩
  omega


theorem connectedVDomain_card_disconnected_eq_three_mul_connected :
    Fintype.card
        {omega : ConfigSpace (Sym2 connectedVDomain.Vertex) //
          ¬connectedVDomain.MixedConnected omega} =
      3 * Fintype.card
        {omega : ConfigSpace (Sym2 connectedVDomain.Vertex) //
          connectedVDomain.MixedConnected omega} := by
  classical
  let eConnected :
      {omega : ConfigSpace (Sym2 connectedVDomain.Vertex) //
          connectedVDomain.MixedConnected omega} ≃
        {omega : ConfigSpace (Sym2 connectedVDomain.Vertex) //
          omega connectedVLeftEdge = true ∧
            omega connectedVRightEdge = true} :=
    Equiv.subtypeEquivRight connectedVDomain_mixedConnected_iff
  let eDisconnected :
      {omega : ConfigSpace (Sym2 connectedVDomain.Vertex) //
          ¬connectedVDomain.MixedConnected omega} ≃
        {omega : ConfigSpace (Sym2 connectedVDomain.Vertex) //
          ¬(omega connectedVLeftEdge = true ∧
            omega connectedVRightEdge = true)} :=
    Equiv.subtypeEquivRight fun omega =>
      not_congr (connectedVDomain_mixedConnected_iff omega)
  calc
    Fintype.card
        {omega : ConfigSpace (Sym2 connectedVDomain.Vertex) //
          ¬connectedVDomain.MixedConnected omega} =
        Fintype.card
          {omega : ConfigSpace (Sym2 connectedVDomain.Vertex) //
            ¬(omega connectedVLeftEdge = true ∧
              omega connectedVRightEdge = true)} :=
      Fintype.card_congr eDisconnected
    _ = 3 * Fintype.card
          {omega : ConfigSpace (Sym2 connectedVDomain.Vertex) //
            omega connectedVLeftEdge = true ∧
              omega connectedVRightEdge = true} :=
      card_not_twoCoordinateTrue_eq_three_mul_card_twoCoordinateTrue
        connectedVLeftEdge connectedVRightEdge connectedV_edges_ne
    _ = 3 * Fintype.card
          {omega : ConfigSpace (Sym2 connectedVDomain.Vertex) //
            connectedVDomain.MixedConnected omega} := by
      exact congrArg (3 * ·) (Fintype.card_congr eConnected).symm




theorem connectedVDomain_no_mixedDualComplementRN (q : Real) :
    MixedDualComplementRN connectedVDomain q → False := by
  classical
  intro R
  have hratio := connectedVDomain_card_disconnected_eq_three_mul_connected
  have hequal := R.card_disconnected_eq_card_connected
  have hpos :
      0 < Fintype.card
        {omega : ConfigSpace (Sym2 connectedVDomain.Vertex) //
          connectedVDomain.MixedConnected omega} := by
    apply Fintype.card_pos_iff.mpr
    refine ⟨⟨fun _ => true, ?_⟩⟩
    rw [connectedVDomain_mixedConnected_iff]
    simp
  omega



theorem mixedDisconnectionProbability_eq_dualPull
    (D : SymmetricDomain) (q : Real) (R : MixedDualComplementRN D q) :
    D.mixedDisconnectionProbability q =
      ∑ eta : ConfigSpace (Sym2 D.Vertex),
        if D.MixedConnected eta then D.mixedMass q (R.dual.symm eta) else 0 := by
  have hsum := Equiv.sum_comp R.dual
    (fun eta : ConfigSpace (Sym2 D.Vertex) =>
      if D.MixedConnected eta then D.mixedMass q (R.dual.symm eta) else 0)
  simpa [mixedDisconnectionProbability, R.connected_dual_iff] using hsum


theorem mixedDisconnectionProbability_le_q_sq_mul
    (D : SymmetricDomain) (q : Real) (R : MixedDualComplementRN D q) :
    D.mixedDisconnectionProbability q ≤
      q ^ 2 * D.mixedConnectionProbability q := by
  rw [mixedDisconnectionProbability_eq_dualPull D q R,
    mixedConnectionProbability, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro eta _
  by_cases hconn : D.MixedConnected eta
  · simp only [hconn, if_true]
    exact R.rn_upper eta
  · simp [hconn]




theorem mixedConnectionProbability_ge_one_div_one_add_q_sq
    (D : SymmetricDomain) {q : Real} (hq : 1 ≤ q)
    (R : MixedDualComplementRN D q) :
    1 / (1 + q ^ 2) ≤ D.mixedConnectionProbability q :=
  dlt_self_duality_estimate
    (mixedConnection_add_disconnection_eq_one D hq)
    (mixedDisconnectionProbability_le_q_sq_mul D q R)



theorem openConnectionProbability_ge_one_div_one_add_q_sq
    (D : SymmetricDomain) {q : Real} (hq : 1 ≤ q)
    (R : MixedDualComplementRN D q) :
    1 / (1 + q ^ 2) ≤ D.openConnectionProbability q := by
  rw [← mixedConnectionProbability_eq_openConnectionProbability D q]
  exact mixedConnectionProbability_ge_one_div_one_add_q_sq D hq R





def unionWiring (D : SymmetricDomain) : SimpleGraph D.Vertex :=
  StatMech.Lattice.boundaryCliqueGraph
    (fun x => D.OnGammaOne x ∨ D.OnGammaTwo x)

noncomputable instance instUnionWiringDecidableAdj (D : SymmetricDomain) :
    DecidableRel D.unionWiring.Adj :=
  Classical.decRel _


def UnionConnected (D : SymmetricDomain)
    (omega : ConfigSpace (Sym2 D.Vertex)) : Prop :=
  ∃ x y : D.Vertex,
    D.OnGammaOne x ∧ D.OnGammaTwo y ∧
      (FK.openSub D.finiteGraph omega ⊔ D.unionWiring).Reachable x y



theorem unionConnected_all (D : SymmetricDomain)
    (omega : ConfigSpace (Sym2 D.Vertex)) :
    D.UnionConnected omega := by
  let x := D.gammaOneStart
  let y := D.gammaTwoStart
  refine ⟨x, y, onGammaOne_gammaOneStart D,
    onGammaTwo_gammaTwoStart D, ?_⟩
  by_cases hxy : x = y
  · rw [hxy]
  · apply Adj.reachable
    rw [SimpleGraph.sup_adj]
    exact Or.inr ((StatMech.Lattice.boundaryCliqueGraph_adj
      (fun z : D.Vertex => D.OnGammaOne z ∨ D.OnGammaTwo z) x y).2
        ⟨hxy, Or.inl (onGammaOne_gammaOneStart D),
          Or.inr (onGammaTwo_gammaTwoStart D)⟩)




theorem no_unionWiring_dual_complement (D : SymmetricDomain) :
    ¬∃ dual : ConfigSpace (Sym2 D.Vertex) ≃ ConfigSpace (Sym2 D.Vertex),
      ∀ omega, D.UnionConnected (dual omega) ↔ ¬D.UnionConnected omega := by
  rintro ⟨dual, hdual⟩
  let omega : ConfigSpace (Sym2 D.Vertex) := fun _ => false
  have hleft : D.UnionConnected (dual omega) := unionConnected_all D _
  have hright : ¬D.UnionConnected omega := (hdual omega).mp hleft
  exact hright (unionConnected_all D omega)

end SymmetricDomain

end

end BeffaraDC
end StatMech
