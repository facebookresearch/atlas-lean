/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Universality.RSWConnectorCentralFaceCarrier
import Code.FrontierD.FKQgt4SquareFaceDualFrame










open Finset SimpleGraph Set

namespace StatMech.Universality

open StatMech.Percolation StatMech.Lattice StatMech.RSW.Box

noncomputable section


def rlc_connectorCentralFaceFiniteGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y := (hypercubicLattice 2).Adj x.1 y.1 ∧
    s(x.1, y.1) ∈ rlc_connectorCentralFaceEdges gamma gamma'
  symm := by
    rintro x y ⟨hxy, he⟩
    exact ⟨hxy.symm, by simpa [Sym2.eq_swap] using he⟩
  loopless := ⟨fun x hxx => hxx.1.ne rfl⟩

noncomputable instance rlc_connectorCentralFaceFiniteGraphDecidableAdj
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_connectorCentralFaceFiniteGraph gamma gamma').Adj :=
  Classical.decRel _


def rlc_connectorCentralFaceClosureGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    SimpleGraph (RlcConnectorVertex n) where
  Adj x y := (hypercubicLattice 2).Adj x.1 y.1 ∧
    s(x.1, y.1) ∈ rlc_connectorCentralFacePlanarEdges gamma gamma'
  symm := by
    rintro x y ⟨hxy, he⟩
    exact ⟨hxy.symm, by simpa [Sym2.eq_swap] using he⟩
  loopless := ⟨fun x hxx => hxx.1.ne rfl⟩

noncomputable instance rlc_connectorCentralFaceClosureGraphDecidableAdj
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n) :
    DecidableRel (rlc_connectorCentralFaceClosureGraph gamma gamma').Adj :=
  Classical.decRel _

theorem rlc_connectorCentralFaceFiniteGraph_le_closureGraph {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    rlc_connectorCentralFaceFiniteGraph gamma gamma' ≤
      rlc_connectorCentralFaceClosureGraph gamma gamma' := by
  rintro x y ⟨hxy, he⟩
  exact ⟨hxy, Finset.mem_union_left _ (Finset.mem_sdiff.mp he).1⟩



def rlc_finiteCentralFaceRandomConnectorEvent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (ConfigSpace (Sym2 (RlcConnectorVertex n))) :=
  {rho | ∃ x y : RlcConnectorVertex n,
    rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
      (FK.openSub (rlc_connectorCentralFaceFiniteGraph gamma gamma') rho).Reachable x y}



def rlc_finiteCentralFaceClosureConnectorEvent {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n) :
    Set (ConfigSpace (Sym2 (RlcConnectorVertex n))) :=
  {rho | ∃ x y : RlcConnectorVertex n,
    rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
      (FK.openSub (rlc_connectorCentralFaceClosureGraph gamma gamma') rho).Reachable x y}




theorem rlc_exists_connector_iff_traceAnchors {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (H : SimpleGraph (RlcConnectorVertex n)) :
    (∃ x y : RlcConnectorVertex n,
        rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
          H.Reachable x y) ↔
      (H ⊔ rlc_connectorTraceWiring gamma gamma').Reachable
        (rlc_connectorRightAnchor gamma)
        (rlc_connectorLeftAnchor gamma') := by
  constructor
  · rintro ⟨x, y, hx, hy, hxy⟩
    have hright := (rlc_connectorTraceWiring_reachable_right gamma gamma'
      (rlc_connectorRightAnchor_onRight gamma) hx).mono
        (show rlc_connectorTraceWiring gamma gamma' ≤
          H ⊔ rlc_connectorTraceWiring gamma gamma' from le_sup_right)
    have hmiddle : (H ⊔ rlc_connectorTraceWiring gamma gamma').Reachable x y :=
      hxy.mono le_sup_left
    have hleft := (rlc_connectorTraceWiring_reachable_left gamma gamma'
      hy (rlc_connectorLeftAnchor_onLeft gamma')).mono
        (show rlc_connectorTraceWiring gamma gamma' ≤
          H ⊔ rlc_connectorTraceWiring gamma gamma' from le_sup_right)
    exact hright.trans (hmiddle.trans hleft)
  · intro hanchors
    by_contra hno
    have hpropagate : ∀ {u v : RlcConnectorVertex n},
        (H ⊔ rlc_connectorSeparateWiring gamma gamma').Walk u v →
        (∃ x, rlc_connectorOnRight gamma x ∧ H.Reachable x u) →
        ∃ x, rlc_connectorOnRight gamma x ∧ H.Reachable x v := by
      intro u v w
      induction w with
      | nil => exact fun hu => hu
      | @cons u v z huv w ih =>
          intro hu
          apply ih
          rcases huv with hH | hsep
          · obtain ⟨x, hx, hxu⟩ := hu
            exact ⟨x, hx, hxu.trans hH.reachable⟩
          · rw [rlc_connectorSeparateWiring, SimpleGraph.sup_adj] at hsep
            rcases hsep with hright | hleft
            · rw [Lattice.boundaryCliqueGraph_adj] at hright
              exact ⟨v, hright.2.2, Reachable.refl _⟩
            · rw [Lattice.boundaryCliqueGraph_adj] at hleft
              obtain ⟨x, hx, hxu⟩ := hu
              exact False.elim (hno ⟨x, u, hx, hleft.2.1, hxu⟩)
    have hanchorsSeparate :
        (H ⊔ rlc_connectorSeparateWiring gamma gamma').Reachable
          (rlc_connectorRightAnchor gamma)
          (rlc_connectorLeftAnchor gamma') :=
      (rlc_connectorTraceWiring_reachable_iff_separateWiring gamma gamma' H
        (rlc_connectorRightAnchor gamma)
        (rlc_connectorLeftAnchor gamma')).mp hanchors
    obtain ⟨w⟩ := hanchorsSeparate
    obtain ⟨x, hx, hxleft⟩ := hpropagate w
      ⟨rlc_connectorRightAnchor gamma,
        rlc_connectorRightAnchor_onRight gamma, Reachable.refl _⟩
    exact hno ⟨x, rlc_connectorLeftAnchor gamma', hx,
      rlc_connectorLeftAnchor_onLeft gamma', hxleft⟩

private theorem centralFaceEdge_exists_lift {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_connectorCentralFaceEdges gamma gamma') :
    ∃ f : Sym2 (RlcConnectorVertex n), f.map Subtype.val = e := by
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hx := rlc_connectorCentralFaceEdge_endpoints_mem_box
        gamma gamma' he (Sym2.mem_mk_left x y)
      have hy := rlc_connectorCentralFaceEdge_endpoints_mem_box
        gamma gamma' he (Sym2.mem_mk_right x y)
      exact ⟨s(⟨x, by simpa [rlc_connectorBox] using hx⟩,
          ⟨y, by simpa [rlc_connectorBox] using hy⟩), by
        simp [Sym2.map_mk]⟩

noncomputable def rlc_connectorCentralFaceEdgeLift {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (e : Sym2 (Site 2))
    (he : e ∈ rlc_connectorCentralFaceEdges gamma gamma') :
    Sym2 (RlcConnectorVertex n) :=
  Classical.choose (centralFaceEdge_exists_lift he)

@[simp] theorem rlc_connectorCentralFaceEdgeLift_map {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    (e : Sym2 (Site 2))
    (he : e ∈ rlc_connectorCentralFaceEdges gamma gamma') :
    (rlc_connectorCentralFaceEdgeLift e he).map Subtype.val = e :=
  Classical.choose_spec (centralFaceEdge_exists_lift he)



noncomputable def rlc_connectorCentralFaceAmbientConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (Sym2 (Site 2)) :=
  fun e => if he : e ∈ rlc_connectorCentralFaceEdges gamma gamma' then
    rho (rlc_connectorCentralFaceEdgeLift e he)
  else if e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1 then true
  else false

@[simp] theorem rlc_connectorCentralFaceAmbientConfig_support {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_connectorCentralFaceEdges gamma gamma') :
    rlc_connectorCentralFaceAmbientConfig gamma gamma' rho e =
      rho (rlc_connectorCentralFaceEdgeLift e he) := by
  simp [rlc_connectorCentralFaceAmbientConfig, he]

@[simp] theorem rlc_connectorCentralFaceAmbientConfig_trace {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)}
    (he : e ∈ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1) :
    rlc_connectorCentralFaceAmbientConfig gamma gamma' rho e = true := by
  have hnot : e ∉ rlc_connectorCentralFaceEdges gamma gamma' := by
    intro hrandom
    apply (Finset.mem_sdiff.mp hrandom).2
    exact Finset.mem_union_left _ he
  simp [rlc_connectorCentralFaceAmbientConfig, hnot, he]

theorem rlc_connectorCentralFaceAmbientConfig_eq_false_of_lifts_closed
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    {e : Sym2 (Site 2)}
    (htrace : e ∉ rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1)
    (hclosed : ∀ f : Sym2 (RlcConnectorVertex n),
      f.map Subtype.val = e → rho f = false) :
    rlc_connectorCentralFaceAmbientConfig gamma gamma' rho e = false := by
  unfold rlc_connectorCentralFaceAmbientConfig
  split
  · rename_i he
    exact hclosed _ (rlc_connectorCentralFaceEdgeLift_map e he)
  · simp [htrace]



noncomputable def rlc_connectorCentralFacePIMSConfig {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    ConfigSpace (Sym2 (RlcConnectorVertex n)) :=
  rlc_connectorRestrictConfig
    (rlc_dualReflectConfig
      (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho))

theorem rlc_connectorCentralFacePIMSConfig_apply {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n)))
    (e : Sym2 (RlcConnectorVertex n)) :
    rlc_connectorCentralFacePIMSConfig gamma gamma' rho e =
      !(rlc_connectorCentralFaceAmbientConfig gamma gamma' rho
        (rlc_pimsEdgeEquiv (e.map Subtype.val))) := by
  unfold rlc_connectorCentralFacePIMSConfig rlc_connectorRestrictConfig
  exact rlc_dualReflectConfig_eq_pims _ _

private theorem centralFaceEdgeLift_eq_mk {n : Int}
    {gamma : RlcRightDiagonalPath n} {gamma' : RlcLeftDiagonalPath n}
    {x y : RlcConnectorVertex n}
    (he : s((x : Site 2), (y : Site 2)) ∈
      rlc_connectorCentralFaceEdges gamma gamma') :
    rlc_connectorCentralFaceEdgeLift
        s((x : Site 2), (y : Site 2)) he = s(x, y) := by
  apply Sym2.map.injective Subtype.val_injective
  rw [rlc_connectorCentralFaceEdgeLift_map]
  rfl




theorem rlc_openSub_centralFaceClosure_ambient {n : Int}
    (gamma : RlcRightDiagonalPath n) (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    FK.openSub (rlc_connectorCentralFaceClosureGraph gamma gamma')
        (rlc_connectorRestrictConfig
          (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho)) =
      FK.openSub (rlc_connectorCentralFaceFiniteGraph gamma gamma') rho ⊔
        rlc_connectorTraceWiring gamma gamma' := by
  ext x y
  rw [FK.openSub_adj, SimpleGraph.sup_adj]
  let e : Sym2 (Site 2) := s((x : Site 2), (y : Site 2))
  have herase : (s(x, y) : Sym2 (RlcConnectorVertex n)).map Subtype.val = e := by
    rfl
  constructor
  · rintro ⟨⟨hxy, hplanar⟩, hopen⟩
    change rlc_connectorCentralFaceAmbientConfig gamma gamma' rho e = true at hopen
    by_cases hrandom : e ∈ rlc_connectorCentralFaceEdges gamma gamma'
    · left
      refine ⟨⟨hxy, hrandom⟩, ?_⟩
      rw [rlc_connectorCentralFaceAmbientConfig_support
        gamma gamma' rho hrandom, centralFaceEdgeLift_eq_mk hrandom] at hopen
      exact hopen
    · have hfour : e ∈ rlc_connectorFourTraceEdges gamma gamma' := by
        rw [rlc_connectorCentralFacePlanarEdges, Finset.mem_union] at hplanar
        rcases hplanar with hclosure | hfour
        · by_contra hnot
          exact hrandom (Finset.mem_sdiff.mpr ⟨hclosure, hnot⟩)
        · exact hfour
      rw [rlc_connectorFourTraceEdges, Finset.mem_union] at hfour
      rcases hfour with horiginal | hreflected
      · right
        exact ⟨hxy, horiginal⟩
      · by_cases horiginal : e ∈
            rlc_pathEdges gamma.1 ∪ rlc_pathEdges gamma'.1
        · right
          exact ⟨hxy, horiginal⟩
        · simp [rlc_connectorCentralFaceAmbientConfig, hrandom,
            horiginal] at hopen
  · rintro (hrandom | htrace)
    · obtain ⟨⟨hxy, he⟩, hopen⟩ := hrandom
      refine ⟨⟨hxy, ?_⟩, ?_⟩
      · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp he).1
      · change rlc_connectorCentralFaceAmbientConfig gamma gamma' rho e = true
        rw [rlc_connectorCentralFaceAmbientConfig_support gamma gamma' rho he,
          centralFaceEdgeLift_eq_mk he]
        exact hopen
    · obtain ⟨hxy, he⟩ := htrace
      refine ⟨⟨hxy, ?_⟩, ?_⟩
      · apply Finset.mem_union_right
        rw [rlc_connectorFourTraceEdges, Finset.mem_union]
        exact Or.inl he
      · change rlc_connectorCentralFaceAmbientConfig gamma gamma' rho e = true
        exact rlc_connectorCentralFaceAmbientConfig_trace gamma gamma' rho he



theorem rlc_mem_randomConnectorEvent_iff_ambientClosureConnectorEvent
    {n : Int} (gamma : RlcRightDiagonalPath n)
    (gamma' : RlcLeftDiagonalPath n)
    (rho : ConfigSpace (Sym2 (RlcConnectorVertex n))) :
    rho ∈ rlc_finiteCentralFaceRandomConnectorEvent gamma gamma' ↔
      rlc_connectorRestrictConfig
          (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho) ∈
        rlc_finiteCentralFaceClosureConnectorEvent gamma gamma' := by
  change
    (∃ x y : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
        (FK.openSub (rlc_connectorCentralFaceFiniteGraph gamma gamma') rho).Reachable x y) ↔
    (∃ x y : RlcConnectorVertex n,
      rlc_connectorOnRight gamma x ∧ rlc_connectorOnLeft gamma' y ∧
        (FK.openSub (rlc_connectorCentralFaceClosureGraph gamma gamma')
          (rlc_connectorRestrictConfig
            (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho))).Reachable x y)
  rw [rlc_exists_connector_iff_traceAnchors]
  constructor
  · intro hanchors
    refine ⟨rlc_connectorRightAnchor gamma,
      rlc_connectorLeftAnchor gamma',
      rlc_connectorRightAnchor_onRight gamma,
      rlc_connectorLeftAnchor_onLeft gamma', ?_⟩
    rw [rlc_openSub_centralFaceClosure_ambient]
    exact hanchors
  · rintro ⟨x, y, hx, hy, hxy⟩
    have hright := (rlc_connectorTraceWiring_reachable_right gamma gamma'
      (rlc_connectorRightAnchor_onRight gamma) hx).mono
        (show rlc_connectorTraceWiring gamma gamma' ≤
          FK.openSub (rlc_connectorCentralFaceClosureGraph gamma gamma')
            (rlc_connectorRestrictConfig
              (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho)) by
          rw [rlc_openSub_centralFaceClosure_ambient]
          exact le_sup_right)
    have hleft := (rlc_connectorTraceWiring_reachable_left gamma gamma'
      hy (rlc_connectorLeftAnchor_onLeft gamma')).mono
        (show rlc_connectorTraceWiring gamma gamma' ≤
          FK.openSub (rlc_connectorCentralFaceClosureGraph gamma gamma')
            (rlc_connectorRestrictConfig
              (rlc_connectorCentralFaceAmbientConfig gamma gamma' rho)) by
          rw [rlc_openSub_centralFaceClosure_ambient]
          exact le_sup_right)
    rw [rlc_openSub_centralFaceClosure_ambient] at hright hxy hleft
    exact hright.trans (hxy.trans hleft)

end

end StatMech.Universality
