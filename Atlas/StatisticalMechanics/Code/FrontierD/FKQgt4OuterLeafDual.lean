/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













import Code.FrontierD.FKQgt4SquareFiniteDuality

open Finset Set SimpleGraph

namespace StatMech.FrontierD

open StatMech.Lattice StatMech.BeffaraDC StatMech.Ising

noncomputable section


noncomputable def pfdOuterFace (P : PlanarZ2Subgraph) : kwg_Face P :=
  (kwg_unique_outerFace P).choose

theorem pfdOuterFace_infinite (P : PlanarZ2Subgraph) :
    (pfdOuterFace P).supp.Infinite :=
  (kwg_unique_outerFace P).choose_spec.1

theorem pfdFace_eq_outer_of_infinite (P : PlanarZ2Subgraph)
    {C : kwg_Face P} (hC : C.supp.Infinite) :
    C = pfdOuterFace P :=
  (kwg_unique_outerFace P).choose_spec.2 C hC



abbrev pfdOuterLeafVertex (P : PlanarZ2Subgraph) :=
  {C : kwg_Face P // C ≠ pfdOuterFace P} ⊕
    (Unit ⊕ (kwg_Edge P × Bool))

noncomputable instance pfdOuterLeafVertexFintype (P : PlanarZ2Subgraph) :
    Fintype (pfdOuterLeafVertex P) := Fintype.ofFinite _

noncomputable instance pfdOuterLeafVertexDecidableEq (P : PlanarZ2Subgraph) :
    DecidableEq (pfdOuterLeafVertex P) := Classical.decEq _


def pfdOuterLeafBoundary (P : PlanarZ2Subgraph) :
    pfdOuterLeafVertex P → Prop
  | Sum.inl _ => False
  | Sum.inr _ => True

instance pfdOuterLeafBoundaryDecidable (P : PlanarZ2Subgraph) :
    DecidablePred (pfdOuterLeafBoundary P) := fun x => by
  cases x <;> simp only [pfdOuterLeafBoundary] <;>
    exact Classical.propDecidable _


def pfdOuterLeafCollapse (P : PlanarZ2Subgraph) :
    pfdOuterLeafVertex P → kwg_Face P
  | Sum.inl C => C.1
  | Sum.inr _ => pfdOuterFace P


def pfdOuterLeafSideFace (P : PlanarZ2Subgraph) (e : kwg_Edge P)
    (side : Bool) : kwg_Face P :=
  if side then
    (whb_faceRegion (imageGraph P)).connectedComponentMk (kwg_flankRight P e)
  else
    (whb_faceRegion (imageGraph P)).connectedComponentMk (kwg_flankLeft P e)



def pfdOuterLeafEndpoint (P : PlanarZ2Subgraph) (e : kwg_Edge P)
    (side : Bool) : pfdOuterLeafVertex P :=
  if h : pfdOuterLeafSideFace P e side = pfdOuterFace P then
    Sum.inr (Sum.inr (e, side))
  else
    Sum.inl ⟨pfdOuterLeafSideFace P e side, h⟩

@[simp] theorem pfdOuterLeafCollapse_endpoint (P : PlanarZ2Subgraph)
    (e : kwg_Edge P) (side : Bool) :
    pfdOuterLeafCollapse P (pfdOuterLeafEndpoint P e side) =
      pfdOuterLeafSideFace P e side := by
  unfold pfdOuterLeafEndpoint
  split
  · simpa [pfdOuterLeafCollapse] using ‹pfdOuterLeafSideFace P e side = pfdOuterFace P›.symm
  · rfl


def pfdOuterLeafEnds (P : PlanarZ2Subgraph) (e : kwg_Edge P) :
    Sym2 (pfdOuterLeafVertex P) :=
  s(pfdOuterLeafEndpoint P e false, pfdOuterLeafEndpoint P e true)

theorem pfdOuterLeafEnds_collapse (P : PlanarZ2Subgraph)
    (e : kwg_Edge P) :
    Sym2.map (pfdOuterLeafCollapse P) (pfdOuterLeafEnds P e) =
      kwg_dualEnds P e := by
  simp only [pfdOuterLeafEnds, Sym2.map_pair_eq, pfdOuterLeafCollapse_endpoint,
    pfdOuterLeafSideFace, Bool.false_eq_true, if_false, if_true, kwg_dualEnds]




def pfdOuterLeafOpenGraph (P : PlanarZ2Subgraph) (F : Set (kwg_Edge P)) :
    SimpleGraph (pfdOuterLeafVertex P) where
  Adj x y := x ≠ y ∧ ∃ e, e ∈ F ∧ pfdOuterLeafEnds P e = s(x, y)
  symm := by
    rintro x y ⟨hne, e, heF, he⟩
    exact ⟨hne.symm, e, heF, he.trans Sym2.eq_swap⟩
  loopless := ⟨fun x h => h.1 rfl⟩

@[simp] theorem pfdOuterLeafOpenGraph_adj (P : PlanarZ2Subgraph)
    (F : Set (kwg_Edge P)) (x y : pfdOuterLeafVertex P) :
    (pfdOuterLeafOpenGraph P F).Adj x y ↔
      x ≠ y ∧ ∃ e, e ∈ F ∧ pfdOuterLeafEnds P e = s(x, y) := Iff.rfl


def pfdOuterLeafWiredGraph (P : PlanarZ2Subgraph)
    (F : Set (kwg_Edge P)) : SimpleGraph (pfdOuterLeafVertex P) :=
  pfdOuterLeafOpenGraph P F ⊔
    boundaryCliqueGraph (pfdOuterLeafBoundary P)

@[simp] theorem pfdOuterLeafWiredGraph_adj (P : PlanarZ2Subgraph)
    (F : Set (kwg_Edge P)) (x y : pfdOuterLeafVertex P) :
    (pfdOuterLeafWiredGraph P F).Adj x y ↔
      (x ≠ y ∧ ∃ e, e ∈ F ∧ pfdOuterLeafEnds P e = s(x, y)) ∨
      (x ≠ y ∧ pfdOuterLeafBoundary P x ∧ pfdOuterLeafBoundary P y) := by
  rw [pfdOuterLeafWiredGraph, SimpleGraph.sup_adj,
    pfdOuterLeafOpenGraph_adj, boundaryCliqueGraph_adj]


def pfdOuterLeafClosedEdges (P : PlanarZ2Subgraph) (K : SimpleGraph P.V) :
    Set (kwg_Edge P) :=
  {e | e.1 ∉ K.edgeSet}


def pfdOuterLeafLift (P : PlanarZ2Subgraph) (C : kwg_Face P) :
    pfdOuterLeafVertex P :=
  if h : C = pfdOuterFace P then Sum.inr (Sum.inl ())
  else Sum.inl ⟨C, h⟩

@[simp] theorem pfdOuterLeafCollapse_lift (P : PlanarZ2Subgraph)
    (C : kwg_Face P) :
    pfdOuterLeafCollapse P (pfdOuterLeafLift P C) = C := by
  unfold pfdOuterLeafLift
  split
  · simpa [pfdOuterLeafCollapse] using ‹C = pfdOuterFace P›.symm
  · rfl



theorem pfdOuterLeaf_reachable_of_collapse_eq (P : PlanarZ2Subgraph)
    (F : Set (kwg_Edge P)) {x y : pfdOuterLeafVertex P}
    (hxy : pfdOuterLeafCollapse P x = pfdOuterLeafCollapse P y) :
    (pfdOuterLeafWiredGraph P F).Reachable x y := by
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          have hsub : x = y := Subtype.ext hxy
          subst y
          exact ⟨Walk.nil⟩
      | inr y =>
          exfalso
          exact x.2 hxy
  | inr x =>
      cases y with
      | inl y =>
          exfalso
          exact y.2 hxy.symm
      | inr y =>
          by_cases h : Sum.inr x = (Sum.inr y : pfdOuterLeafVertex P)
          · exact h ▸ ⟨Walk.nil⟩
          · exact (pfdOuterLeafWiredGraph_adj P F _ _).2
              (Or.inr ⟨h, by cases x <;> trivial, by cases y <;> trivial⟩) |>.reachable


theorem pfdOuterLeaf_collapse_reachable_of_adj (P : PlanarZ2Subgraph)
    (K : SimpleGraph P.V) {x y : pfdOuterLeafVertex P}
    (hxy : (pfdOuterLeafWiredGraph P
      (pfdOuterLeafClosedEdges P K)).Adj x y) :
    (pfdClosedDual P K).Reachable
      (pfdOuterLeafCollapse P x) (pfdOuterLeafCollapse P y) := by
  rw [pfdOuterLeafWiredGraph_adj] at hxy
  rcases hxy with hopen | hboundary
  · obtain ⟨_, e, heK, heends⟩ := hopen
    by_cases heq : pfdOuterLeafCollapse P x = pfdOuterLeafCollapse P y
    · simpa [heq]
    · apply SimpleGraph.Adj.reachable
      rw [pfdClosedDual_adj]
      refine ⟨heq, e, heK, ?_⟩
      have hmap := congrArg (Sym2.map (pfdOuterLeafCollapse P)) heends
      rw [pfdOuterLeafEnds_collapse] at hmap
      simpa using hmap
  · have hx : pfdOuterLeafCollapse P x = pfdOuterFace P := by
      cases x <;> simp_all [pfdOuterLeafBoundary, pfdOuterLeafCollapse]
    have hy : pfdOuterLeafCollapse P y = pfdOuterFace P := by
      cases y <;> simp_all [pfdOuterLeafBoundary, pfdOuterLeafCollapse]
    simpa [hx, hy]


theorem pfdOuterLeaf_collapse_reachable (P : PlanarZ2Subgraph)
    (K : SimpleGraph P.V) {x y : pfdOuterLeafVertex P}
    (hxy : (pfdOuterLeafWiredGraph P
      (pfdOuterLeafClosedEdges P K)).Reachable x y) :
    (pfdClosedDual P K).Reachable
      (pfdOuterLeafCollapse P x) (pfdOuterLeafCollapse P y) := by
  rcases hxy with ⟨w⟩
  induction w with
  | nil => exact ⟨Walk.nil⟩
  | cons h w ih =>
      exact (pfdOuterLeaf_collapse_reachable_of_adj P K h).trans ih



theorem pfdOuterLeaf_reachable_of_dualAdj (P : PlanarZ2Subgraph)
    (K : SimpleGraph P.V) {x y : pfdOuterLeafVertex P}
    (hxy : (pfdClosedDual P K).Adj
      (pfdOuterLeafCollapse P x) (pfdOuterLeafCollapse P y)) :
    (pfdOuterLeafWiredGraph P
      (pfdOuterLeafClosedEdges P K)).Reachable x y := by
  obtain ⟨hne, e, heK, heends⟩ := (pfdClosedDual_adj P K _ _).mp hxy
  let u := pfdOuterLeafEndpoint P e false
  let v := pfdOuterLeafEndpoint P e true
  have huvCollapse :
      s(pfdOuterLeafCollapse P u, pfdOuterLeafCollapse P v) =
        s(pfdOuterLeafCollapse P x, pfdOuterLeafCollapse P y) := by
    rw [← heends, ← pfdOuterLeafEnds_collapse]
    rfl
  have huvNe : u ≠ v := by
    intro huv
    apply hne
    rw [huv] at huvCollapse
    rw [Sym2.eq_iff] at huvCollapse
    rcases huvCollapse with h | h
    · exact h.1.symm.trans h.2
    · exact h.2.symm.trans h.1
  have hedge : (pfdOuterLeafWiredGraph P
      (pfdOuterLeafClosedEdges P K)).Adj u v := by
    rw [pfdOuterLeafWiredGraph_adj]
    exact Or.inl ⟨huvNe, e, heK, rfl⟩
  rw [Sym2.eq_iff] at huvCollapse
  rcases huvCollapse with hs | hs
  · exact (pfdOuterLeaf_reachable_of_collapse_eq P _ hs.1.symm).trans
      (hedge.reachable.trans
        (pfdOuterLeaf_reachable_of_collapse_eq P _ hs.2))
  · exact (pfdOuterLeaf_reachable_of_collapse_eq P _ hs.2.symm).trans
      (hedge.symm.reachable.trans
        (pfdOuterLeaf_reachable_of_collapse_eq P _ hs.1))


theorem pfdOuterLeaf_lift_reachable_of_dual (P : PlanarZ2Subgraph)
    (K : SimpleGraph P.V) {C D : kwg_Face P}
    (hCD : (pfdClosedDual P K).Reachable C D) :
    (pfdOuterLeafWiredGraph P
      (pfdOuterLeafClosedEdges P K)).Reachable
        (pfdOuterLeafLift P C) (pfdOuterLeafLift P D) := by
  rcases hCD with ⟨w⟩
  induction w with
  | nil => exact ⟨Walk.nil⟩
  | @cons A B C hAB w ih =>
      exact (pfdOuterLeaf_reachable_of_dualAdj P K
        (x := pfdOuterLeafLift P A) (y := pfdOuterLeafLift P B)
        (by simpa using hAB)).trans ih


theorem pfdOuterLeaf_reachable_iff_dual (P : PlanarZ2Subgraph)
    (K : SimpleGraph P.V) {x y : pfdOuterLeafVertex P} :
    (pfdOuterLeafWiredGraph P
      (pfdOuterLeafClosedEdges P K)).Reachable x y ↔
    (pfdClosedDual P K).Reachable
      (pfdOuterLeafCollapse P x) (pfdOuterLeafCollapse P y) := by
  constructor
  · exact pfdOuterLeaf_collapse_reachable P K
  · intro hxy
    exact (pfdOuterLeaf_reachable_of_collapse_eq P _
      (pfdOuterLeafCollapse_lift P _).symm).trans
      ((pfdOuterLeaf_lift_reachable_of_dual P K hxy).trans
        (pfdOuterLeaf_reachable_of_collapse_eq P _
          (pfdOuterLeafCollapse_lift P _)))



noncomputable def pfdOuterLeafComponentEquiv (P : PlanarZ2Subgraph)
    (K : SimpleGraph P.V) :
    (pfdOuterLeafWiredGraph P
      (pfdOuterLeafClosedEdges P K)).ConnectedComponent ≃
      (pfdClosedDual P K).ConnectedComponent := by
  let f : (pfdOuterLeafWiredGraph P
      (pfdOuterLeafClosedEdges P K)).ConnectedComponent →
      (pfdClosedDual P K).ConnectedComponent :=
    fun C => (pfdClosedDual P K).connectedComponentMk
      (pfdOuterLeafCollapse P C.out)
  apply Equiv.ofBijective f
  constructor
  · intro C D hCD
    change (pfdClosedDual P K).connectedComponentMk
      (pfdOuterLeafCollapse P C.out) =
        (pfdClosedDual P K).connectedComponentMk
          (pfdOuterLeafCollapse P D.out) at hCD
    have hleaf := (pfdOuterLeaf_reachable_iff_dual P K).mpr
      (ConnectedComponent.eq.mp hCD)
    rw [← C.out_eq, ← D.out_eq]
    exact ConnectedComponent.sound hleaf
  · intro D
    let x := pfdOuterLeafLift P D.out
    refine ⟨(pfdOuterLeafWiredGraph P
      (pfdOuterLeafClosedEdges P K)).connectedComponentMk x, ?_⟩
    dsimp only [f]
    rw [← D.out_eq]
    apply ConnectedComponent.sound
    have hout : (pfdOuterLeafWiredGraph P
        (pfdOuterLeafClosedEdges P K)).Reachable
        ((pfdOuterLeafWiredGraph P
          (pfdOuterLeafClosedEdges P K)).connectedComponentMk x).out x :=
      ConnectedComponent.exact
        ((pfdOuterLeafWiredGraph P
          (pfdOuterLeafClosedEdges P K)).connectedComponentMk x).out_eq
    have hdual := pfdOuterLeaf_collapse_reachable P K hout
    simpa only [x, pfdOuterLeafCollapse_lift] using hdual



theorem pfdOuterLeaf_numClusters_eq (P : PlanarZ2Subgraph)
    (K : SimpleGraph P.V) :
    Nat.card (pfdOuterLeafWiredGraph P
      (pfdOuterLeafClosedEdges P K)).ConnectedComponent =
      Nat.card (pfdClosedDual P K).ConnectedComponent := by
  exact Nat.card_congr (pfdOuterLeafComponentEquiv P K)




theorem pfdDualWeight_eq_outerLeaf (P : PlanarZ2Subgraph)
    (p q : Real) (K : SimpleGraph P.V) :
    pfdDualWeight P p q K =
      edgeProductCount p P.G.edgeFinset.card
          (P.G.edgeFinset.card - K.edgeSet.ncard) *
        q ^ Nat.card (pfdOuterLeafWiredGraph P
          (pfdOuterLeafClosedEdges P K)).ConnectedComponent := by
  unfold pfdDualWeight
  rw [pfdOuterLeaf_numClusters_eq]


theorem fkSquareBox_pfdDualWeight_eq_outerLeaf (n : Nat)
    (p q : Real) (K : SimpleGraph (FK.boxVerts 2 n)) :
    pfdDualWeight (fkSquareBoxPlanar n) p q K =
      edgeProductCount p (FK.boxGraph 2 n).edgeFinset.card
          ((FK.boxGraph 2 n).edgeFinset.card - K.edgeSet.ncard) *
        q ^ Nat.card (pfdOuterLeafWiredGraph (fkSquareBoxPlanar n)
          (pfdOuterLeafClosedEdges (fkSquareBoxPlanar n) K)).ConnectedComponent := by
  exact pfdDualWeight_eq_outerLeaf (fkSquareBoxPlanar n) p q K

end

end StatMech.FrontierD
