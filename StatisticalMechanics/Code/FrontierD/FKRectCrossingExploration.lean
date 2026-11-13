/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectPrimalDualCrossings
import Code.Probability.FiniteWitnessUnionBound
import Code.FK.DomainMarkov
import Code.FK.TwoPoint
import Code.FK.OffCentreFreeDomination










namespace StatMech.FrontierD

noncomputable section

local instance instDecidableRelFKRectCrossingExplorationTorusGraph
    (R : FKRectTorus) : DecidableRel (fkRectTorusGraph R).Adj :=
  Classical.decRel _

theorem fkRectCriticalEventMass_eq_finiteEventMass
    (R : FKRectTorus) (q : Real) (A : Set R.Configuration) :
    fkRectCriticalEventMass R q A =
      StatMech.Probability.finiteEventMass
        (fun eta => fkRectCriticalRandomClusterProb R q eta) A := by
  classical
  unfold fkRectCriticalEventMass StatMech.Probability.finiteEventMass
  apply Finset.sum_congr rfl
  intro eta heta
  by_cases hA : eta ∈ A <;> simp [Set.indicator, hA]



def FKRectPrimalDualCrossingSourceWitnessCore
    (R : FKRectTorus) (S : Finset (Fin (2 * R.height)))
    (eta : R.Configuration) : Prop :=
  S ⊆ fkRectPrimalDualCrossingRepresentativeSourceIndices R eta


def FKRectPrimalDualCrossingSourceWitness
    (R : FKRectTorus) (S : Finset (Fin (2 * R.height)))
    (eta : R.Configuration) : Prop :=
  FKRectCutClosedConfiguration R eta ∧
    FKRectPrimalDualCrossingSourceWitnessCore R S eta




def FKRectPrimalCrossingSourceWitnessCore
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) : Prop :=
  S ⊆ fkRectRawHorizontalCrossingRepresentativeIndices R
    (fkRectForceCutClosed R eta)



def FKRectPrimalExploredVertex
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) (v : R.Vertex) : Prop :=
  ∃ i ∈ S,
    (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Reachable
      (fkRectLeftColumn R, i) v



def fkRectTorusCutGraphEdges (R : FKRectTorus) :
    Finset (Sym2 R.Vertex) :=
  (fkRectTorusCutEdges R).image (fkRectTorusIndexedEdge R)

@[simp] theorem mem_fkRectTorusCutGraphEdges
    (R : FKRectTorus) (a : R.EdgeIndex) :
    fkRectTorusIndexedEdge R a ∈ fkRectTorusCutGraphEdges R ↔
      a ∈ fkRectTorusCutEdges R := by
  classical
  unfold fkRectTorusCutGraphEdges
  rw [Finset.mem_image]
  constructor
  · rintro ⟨b, hb, hab⟩
    exact (fkRectTorusIndexedEdge_injective R hab).symm ▸ hb
  · intro ha
    exact ⟨a, ha, rfl⟩

theorem fkRectFullGraphConfiguration_forceCut_eq_false_of_cutEdge
    (R : FKRectTorus) (eta : R.Configuration)
    {e : Sym2 R.Vertex} (he : e ∈ fkRectTorusCutGraphEdges R) :
    fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta) e = false := by
  classical
  rw [fkRectTorusCutGraphEdges, Finset.mem_image] at he
  rcases he with ⟨a, ha, rfl⟩
  rw [fkRectFullGraphConfiguration_indexedEdge,
    fkRectForceCutClosed_of_mem R eta a ha]


noncomputable def fkRectCutGraph (R : FKRectTorus) : SimpleGraph R.Vertex :=
  SimpleGraph.fromEdgeSet
    ((fkRectTorusGraph R).edgeSet \
      (fkRectTorusCutGraphEdges R : Set (Sym2 R.Vertex)))

noncomputable instance instDecidableRelFKRectCutGraph
    (R : FKRectTorus) : DecidableRel (fkRectCutGraph R).Adj :=
  fun _ _ => Classical.dec _

theorem fkRectCutGraph_adj_iff
    (R : FKRectTorus) (x y : R.Vertex) :
    (fkRectCutGraph R).Adj x y ↔
      (fkRectTorusGraph R).Adj x y ∧
        s(x, y) ∉ fkRectTorusCutGraphEdges R := by
  rw [fkRectCutGraph, SimpleGraph.fromEdgeSet_adj]
  constructor
  · rintro ⟨⟨hedge, hcut⟩, _⟩
    exact ⟨(SimpleGraph.mem_edgeSet (fkRectTorusGraph R)).1 hedge, hcut⟩
  · rintro ⟨hxy, hcut⟩
    exact ⟨⟨(SimpleGraph.mem_edgeSet (fkRectTorusGraph R)).2 hxy,
      hcut⟩, hxy.ne⟩




noncomputable def fkRectPrimalUnexploredEdges
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) : Finset (Sym2 R.Vertex) := by
  classical
  exact (fkRectTorusGraph R).edgeFinset.filter fun e =>
    e ∉ fkRectTorusCutGraphEdges R ∧
      ¬ ∃ v w : R.Vertex, e = s(v, w) ∧
        (FKRectPrimalExploredVertex R S eta v ∨
          FKRectPrimalExploredVertex R S eta w)


noncomputable def fkRectPrimalUnexploredGraph
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) : SimpleGraph R.Vertex :=
  SimpleGraph.fromEdgeSet
    (fkRectPrimalUnexploredEdges R S eta : Set (Sym2 R.Vertex))


def FKRectPrimalUnexploredVertex
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) :=
  {v : R.Vertex // ¬ FKRectPrimalExploredVertex R S eta v}

noncomputable instance instFintypeFKRectPrimalUnexploredVertex
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) :
    Fintype (FKRectPrimalUnexploredVertex R S eta) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable instance instDecidableEqFKRectPrimalUnexploredVertex
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) :
    DecidableEq (FKRectPrimalUnexploredVertex R S eta) :=
  Classical.decEq _



noncomputable def fkRectPrimalUnexploredInducedGraph
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) :
    SimpleGraph (FKRectPrimalUnexploredVertex R S eta) :=
  (fkRectCutGraph R).comap Subtype.val

noncomputable instance instDecidableRelPrimalUnexploredInducedGraph
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) :
    DecidableRel (fkRectPrimalUnexploredInducedGraph R S eta).Adj :=
  fun _ _ => Classical.dec _

theorem fkRectPrimalUnexploredInducedGraph_adjMatch
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) :
    FK.ocd_AdjMatch
      (fkRectPrimalUnexploredInducedGraph R S eta)
      (fkRectCutGraph R)
      (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex) := by
  intro x y
  rfl





noncomputable def fkRectPrimalUnexploredPairEdges
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) : Finset (Sym2 R.Vertex) :=
  FK.ocd_innerEdgeFinset
    (Vin := FKRectPrimalUnexploredVertex R S eta)
    (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex)



theorem fkRectPrimalExploration_cutGraph_condFkProb_eq_induced
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta omega : R.Configuration) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.condFkProb (fkRectCutGraph R) p q
        (fkRectPrimalUnexploredPairEdges R S eta)
        (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))
        (fkRectFullGraphConfiguration R omega) =
      FK.inducedFkProb (fkRectCutGraph R) p q
        (fkRectPrimalUnexploredPairEdges R S eta)
        (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))
        (fkRectFullGraphConfiguration R omega) := by
  exact FK.condFkProb_eq_inducedFkProb
    (fkRectCutGraph R) hp hp1 hq _ _ _

noncomputable instance instDecidableRelPrimalUnexploredGraph
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) :
    DecidableRel (fkRectPrimalUnexploredGraph R S eta).Adj :=
  fun _ _ => Classical.dec _



def FKRectPrimalInsertionArmEvent
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (i : Fin R.height) (eta : R.Configuration) :
    Set (ConfigSpace (Sym2 R.Vertex)) :=
  {omega | ∃ z : Fin R.height,
    (FK.openSub (fkRectPrimalUnexploredGraph R S eta) omega).Reachable
      (fkRectLeftColumn R, i) (fkRectRightColumn R, z)}

theorem fkRectPrimalInsertionArmEvent_isIncreasing
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (i : Fin R.height) (eta : R.Configuration) :
    IsIncreasing (FKRectPrimalInsertionArmEvent R S i eta) := by
  intro omega omega' hle
  rintro ⟨z, hreach⟩
  exact ⟨z, hreach.mono (FK.openSub_mono _ hle)⟩

private theorem fkRectPrimalCrossing_insert_cluster_disjoint_explored_aux
    (R : FKRectTorus) (eta : R.Configuration)
    (S : Finset (Fin R.height)) (i : Fin R.height)
    (hi : i ∉ S)
    (hwitness : FKRectPrimalCrossingSourceWitnessCore R (insert i S) eta)
    {v : R.Vertex}
    (hiv : (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Reachable
      (fkRectLeftColumn R, i) v) :
    ¬ FKRectPrimalExploredVertex R S eta v := by
  intro hexplored
  rcases hexplored with ⟨j, hj, hjv⟩
  have hri : i ∈ fkRectRawHorizontalCrossingRepresentativeIndices R
      (fkRectForceCutClosed R eta) :=
    hwitness (Finset.mem_insert_self i S)
  have hrj : j ∈ fkRectRawHorizontalCrossingRepresentativeIndices R
      (fkRectForceCutClosed R eta) :=
    hwitness (Finset.mem_insert_of_mem hj)
  have hcomponent := SimpleGraph.ConnectedComponent.sound
    (hiv.trans hjv.symm)
  have hij := eq_of_representativeIndices_of_component_eq R
    (fkRectForceCutClosed R eta) hri hrj hcomponent
  exact hi (hij ▸ hj)



theorem fkRectPrimalUnexploredGraph_adj_of_insert_reachable
    (R : FKRectTorus) (eta : R.Configuration)
    (S : Finset (Fin R.height)) (i : Fin R.height)
    (hi : i ∉ S)
    (hwitness : FKRectPrimalCrossingSourceWitnessCore R (insert i S) eta)
    {x y : R.Vertex}
    (hix : (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Reachable
      (fkRectLeftColumn R, i) x)
    (hxy : (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Adj x y) :
    (FK.openSub (fkRectPrimalUnexploredGraph R S eta)
      (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))).Adj x y := by
  classical
  have hiy := hix.trans hxy.reachable
  have hxy_ne : x ≠ y := hxy.ne
  have hxNot := fkRectPrimalCrossing_insert_cluster_disjoint_explored_aux
    R eta S i hi hwitness hix
  have hyNot := fkRectPrimalCrossing_insert_cluster_disjoint_explored_aux
    R eta S i hi hwitness hiy
  rcases hxy with ⟨a, haopen, haedge⟩
  have haNotCut : a ∉ fkRectTorusCutEdges R := by
    intro hacut
    have := fkRectForceCutClosed_of_mem R eta a hacut
    rw [haopen] at this
    exact Bool.noConfusion this
  have hedgeNotCut : s(x, y) ∉ fkRectTorusCutGraphEdges R := by
    rw [← haedge, mem_fkRectTorusCutGraphEdges]
    exact haNotCut
  have hnotTouch : ¬ ∃ v w : R.Vertex, s(x, y) = s(v, w) ∧
      (FKRectPrimalExploredVertex R S eta v ∨
        FKRectPrimalExploredVertex R S eta w) := by
    rintro ⟨v, w, hvw, hv | hw⟩
    · rcases Sym2.eq_iff.mp hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hxNot hv
      · exact hyNot hv
    · rcases Sym2.eq_iff.mp hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hyNot hw
      · exact hxNot hw
  constructor
  · rw [fkRectPrimalUnexploredGraph, SimpleGraph.fromEdgeSet_adj]
    have htorusAdj : (fkRectTorusGraph R).Adj x y :=
      (SimpleGraph.mem_edgeSet (fkRectTorusGraph R)).1
        ((mem_fkRectTorusGraph_edgeSet_iff R _).2 ⟨a, haedge⟩)
    exact ⟨Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨SimpleGraph.mem_edgeFinset.mpr htorusAdj,
        hedgeNotCut, hnotTouch⟩), hxy_ne⟩
  · rw [← haedge, fkRectFullGraphConfiguration_indexedEdge]
    exact haopen



theorem fkRectPrimalUnexplored_reachable_of_insert_reachable
    (R : FKRectTorus) (eta : R.Configuration)
    (S : Finset (Fin R.height)) (i : Fin R.height)
    (hi : i ∉ S)
    (hwitness : FKRectPrimalCrossingSourceWitnessCore R (insert i S) eta)
    {v : R.Vertex}
    (hiv : (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Reachable
      (fkRectLeftColumn R, i) v) :
    (FK.openSub (fkRectPrimalUnexploredGraph R S eta)
      (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))).Reachable
        (fkRectLeftColumn R, i) v := by
  let source : R.Vertex := (fkRectLeftColumn R, i)
  let G := fkRectOpenGraph R (fkRectForceCutClosed R eta)
  let H := FK.openSub (fkRectPrimalUnexploredGraph R S eta)
    (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))
  let liftWalk : ∀ {x y : R.Vertex}, G.Walk x y →
      G.Reachable source x → H.Walk x y := by
    intro x y p
    induction p with
    | nil => intro _; exact SimpleGraph.Walk.nil
    | @cons x y z hxy p ih =>
        intro hsx
        exact SimpleGraph.Walk.cons
          (fkRectPrimalUnexploredGraph_adj_of_insert_reachable
            R eta S i hi hwitness hsx hxy)
          (ih (hsx.trans hxy.reachable))
  exact hiv.elim fun p =>
    ⟨liftWalk p (SimpleGraph.Reachable.refl source)⟩



theorem fkRectPrimalCrossingSourceWitnessCore_insert_imp_arm
    (R : FKRectTorus) (eta : R.Configuration)
    (S : Finset (Fin R.height)) (i : Fin R.height)
    (hi : i ∉ S)
    (hwitness : FKRectPrimalCrossingSourceWitnessCore R (insert i S) eta) :
    fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta) ∈
      FKRectPrimalInsertionArmEvent R S i eta := by
  have hrep : i ∈ fkRectRawHorizontalCrossingRepresentativeIndices R
      (fkRectForceCutClosed R eta) :=
    hwitness (Finset.mem_insert_self i S)
  obtain ⟨z, hiz⟩ :=
    fkRectRawHorizontalCrossingRepresentativeIndices_subset_sources
      R (fkRectForceCutClosed R eta) i hrep
  exact ⟨z, fkRectPrimalUnexplored_reachable_of_insert_reachable
    R eta S i hi hwitness hiz⟩



theorem fkRectPrimalCrossing_insert_cluster_disjoint_explored
    (R : FKRectTorus) (eta : R.Configuration)
    (S : Finset (Fin R.height)) (i : Fin R.height)
    (hi : i ∉ S)
    (hwitness : FKRectPrimalCrossingSourceWitnessCore R (insert i S) eta)
    {v : R.Vertex}
    (hiv : (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Reachable
      (fkRectLeftColumn R, i) v) :
    ¬ FKRectPrimalExploredVertex R S eta v := by
  intro hexplored
  rcases hexplored with ⟨j, hj, hjv⟩
  have hri : i ∈ fkRectRawHorizontalCrossingRepresentativeIndices R
      (fkRectForceCutClosed R eta) :=
    hwitness (Finset.mem_insert_self i S)
  have hrj : j ∈ fkRectRawHorizontalCrossingRepresentativeIndices R
      (fkRectForceCutClosed R eta) :=
    hwitness (Finset.mem_insert_of_mem hj)
  have hcomponent := SimpleGraph.ConnectedComponent.sound
    (hiv.trans hjv.symm)
  have hij := eq_of_representativeIndices_of_component_eq R
    (fkRectForceCutClosed R eta) hri hrj hcomponent
  exact hi (hij ▸ hj)


theorem fkRectPrimalCrossing_insert_source_not_explored
    (R : FKRectTorus) (eta : R.Configuration)
    (S : Finset (Fin R.height)) (i : Fin R.height)
    (hi : i ∉ S)
    (hwitness : FKRectPrimalCrossingSourceWitnessCore R (insert i S) eta) :
    ¬ FKRectPrimalExploredVertex R S eta (fkRectLeftColumn R, i) := by
  apply fkRectPrimalCrossing_insert_cluster_disjoint_explored
    R eta S i hi hwitness
  exact SimpleGraph.Reachable.refl (fkRectLeftColumn R, i)




def fkRectPrimalExplorationOutsideOpenGraph
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) : SimpleGraph R.Vertex where
  Adj x y :=
    (fkRectTorusGraph R).Adj x y ∧
      fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta) s(x, y) = true ∧
      s(x, y) ∉ fkRectPrimalUnexploredEdges R S eta
  symm := by
    rintro x y ⟨hxy, hopen, hout⟩
    refine ⟨hxy.symm, ?_, ?_⟩ <;> simpa only [Sym2.eq_swap]
  loopless := ⟨by rintro x ⟨hxx, _, _⟩; exact hxx.ne rfl⟩

noncomputable instance instDecidableRelPrimalExplorationOutsideOpenGraph
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) :
    DecidableRel (fkRectPrimalExplorationOutsideOpenGraph R S eta).Adj :=
  fun _ _ => Classical.dec _




def fkRectPrimalExplorationInducedBoundary
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) : SimpleGraph R.Vertex where
  Adj x y := x ≠ y ∧
    (fkRectPrimalExplorationOutsideOpenGraph R S eta).Reachable x y
  symm := by
    rintro x y ⟨hxy, hreach⟩
    exact ⟨hxy.symm, hreach.symm⟩
  loopless := ⟨by rintro x ⟨hxx, _⟩; exact hxx rfl⟩

noncomputable instance instDecidableRelPrimalExplorationInducedBoundary
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) :
    DecidableRel (fkRectPrimalExplorationInducedBoundary R S eta).Adj :=
  fun _ _ => Classical.dec _



theorem fkRectPrimalExploredVertex_of_openAdj_right
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) {x y : R.Vertex}
    (hxy : (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Adj x y)
    (hy : FKRectPrimalExploredVertex R S eta y) :
    FKRectPrimalExploredVertex R S eta x := by
  rcases hy with ⟨i, hi, hiy⟩
  exact ⟨i, hi, hiy.trans hxy.symm.reachable⟩



theorem not_primalExplorationOutsideOpenGraph_adj_of_not_explored
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) {x y : R.Vertex}
    (hx : ¬ FKRectPrimalExploredVertex R S eta x) :
    ¬ (fkRectPrimalExplorationOutsideOpenGraph R S eta).Adj x y := by
  classical
  rintro ⟨hxy, hopen, hout⟩
  have hOpenAdj :
      (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Adj x y := by
    obtain ⟨a, ha⟩ :=
      (mem_fkRectTorusGraph_edgeSet_iff R s(x, y)).1
        ((SimpleGraph.mem_edgeSet (fkRectTorusGraph R)).2 hxy)
    refine ⟨a, ?_, ha⟩
    rw [← fkRectFullGraphConfiguration_indexedEdge R
      (fkRectForceCutClosed R eta) a, ha]
    exact hopen
  have htouch : ∃ v w : R.Vertex, s(x, y) = s(v, w) ∧
      (FKRectPrimalExploredVertex R S eta v ∨
        FKRectPrimalExploredVertex R S eta w) := by
    by_contra hnot
    have hnotCut : s(x, y) ∉ fkRectTorusCutGraphEdges R := by
      intro hcut
      have hfalse :=
        fkRectFullGraphConfiguration_forceCut_eq_false_of_cutEdge
          R eta hcut
      rw [hopen] at hfalse
      exact Bool.noConfusion hfalse
    exact hout (Finset.mem_filter.mpr
      ⟨SimpleGraph.mem_edgeFinset.mpr hxy, hnotCut, hnot⟩)
  rcases htouch with ⟨v, w, hvw, hv | hw⟩
  · rcases Sym2.eq_iff.mp hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hx hv
    · exact hx (fkRectPrimalExploredVertex_of_openAdj_right
        R S eta hOpenAdj hv)
  · rcases Sym2.eq_iff.mp hvw with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hx (fkRectPrimalExploredVertex_of_openAdj_right
        R S eta hOpenAdj hw)
    · exact hx hw




theorem not_primalExplorationInducedBoundary_adj_of_not_explored
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) {x y : R.Vertex}
    (hx : ¬ FKRectPrimalExploredVertex R S eta x)
    (hy : ¬ FKRectPrimalExploredVertex R S eta y) :
    ¬ (fkRectPrimalExplorationInducedBoundary R S eta).Adj x y := by
  rintro ⟨hxy, hreach⟩
  apply hxy
  exact hreach.elim fun p => by
    have hpzero : p.length = 0 := by
      cases p with
      | nil => rfl
      | cons hadj rest =>
          exact False.elim
            (not_primalExplorationOutsideOpenGraph_adj_of_not_explored
              R S eta hx hadj)
    exact p.eq_of_length_eq_zero hpzero


def FKRectNoBoundary (_ : FKRectTorus) (_ : Unit) : Prop := False

local instance instDecidablePredFKRectNoBoundary (R : FKRectTorus) :
    DecidablePred (fun _ : R.Vertex => False) :=
  fun _ => isFalse id



theorem not_ocdOutsideGraph_adj_from_unexplored
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration)
    (x : FKRectPrimalUnexploredVertex R S eta) (y : R.Vertex) :
    ¬ (FK.ocd_outsideGraph (fkRectCutGraph R)
      (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex)
      (fun _ : R.Vertex => False)
      (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))).Adj
        x.1 y := by
  intro hadj
  rw [FK.ocd_outsideGraph_adj] at hadj
  rcases hadj with hout | hboundary
  · rcases hout with ⟨hcut, hopen, hrange⟩
    have htorus : (fkRectTorusGraph R).Adj x.1 y :=
      (fkRectCutGraph_adj_iff R x.1 y).1 hcut |>.1
    obtain ⟨a, haedge⟩ :=
      (mem_fkRectTorusGraph_edgeSet_iff R s(x.1, y)).1
        ((SimpleGraph.mem_edgeSet (fkRectTorusGraph R)).2 htorus)
    have hopenIndexed : fkRectForceCutClosed R eta a = true := by
      rw [← fkRectFullGraphConfiguration_indexedEdge R
        (fkRectForceCutClosed R eta) a, haedge]
      exact hopen
    have hopenAdj :
        (fkRectOpenGraph R (fkRectForceCutClosed R eta)).Adj x.1 y :=
      ⟨a, hopenIndexed, haedge⟩
    by_cases hy : FKRectPrimalExploredVertex R S eta y
    · exact x.2 (fkRectPrimalExploredVertex_of_openAdj_right
        R S eta hopenAdj hy)
    · apply hrange
      let y' : FKRectPrimalUnexploredVertex R S eta := ⟨y, hy⟩
      refine ⟨s(x, y'), ?_⟩
      simp [FK.ocd_innerEdge, y']
  · exact hboundary.2.1.elim

theorem eq_of_ocdOutsideGraph_reachable_from_unexplored
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) {x y : R.Vertex}
    (hx : ¬ FKRectPrimalExploredVertex R S eta x)
    (hreach : (FK.ocd_outsideGraph (fkRectCutGraph R)
      (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex)
      (fun _ : R.Vertex => False)
      (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))).Reachable
        x y) :
    x = y := by
  exact hreach.elim fun p => by
    cases p with
    | nil => rfl
    | cons hstep rest =>
        exact False.elim
          (not_ocdOutsideGraph_adj_from_unexplored R S eta ⟨x, hx⟩ _ hstep)



theorem fkRectPrimalExploration_ocdInducedWiring_le_bot
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) :
    FK.ocd_inducedWiring (fkRectCutGraph R)
        (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex)
        (fun _ : R.Vertex => False)
        (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)) ≤
      (⊥ : SimpleGraph (FKRectPrimalUnexploredVertex R S eta)) := by
  intro x y hadj
  exfalso
  apply hadj.1
  exact Subtype.ext
    (eq_of_ocdOutsideGraph_reachable_from_unexplored
      R S eta x.2 hadj.2)

theorem fkRectPrimalExploration_ocdInducedWiring_eq_bot
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) :
    FK.ocd_inducedWiring (fkRectCutGraph R)
        (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex)
        (fun _ : R.Vertex => False)
        (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)) =
      (⊥ : SimpleGraph (FKRectPrimalUnexploredVertex R S eta)) := by
  exact le_antisymm
    (fkRectPrimalExploration_ocdInducedWiring_le_bot R S eta) bot_le




theorem fkRectPrimalExploration_condBcProb_eq_freeUnexplored
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta : R.Configuration) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q)
    (omega : ConfigSpace
      (Sym2 (FKRectPrimalUnexploredVertex R S eta))) :
    FK.condBcProb (fkRectCutGraph R)
        (StatMech.Lattice.boundaryCliqueGraph
          (fun _ : R.Vertex => False)) p q
        (fkRectPrimalUnexploredPairEdges R S eta)
        (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))
        (@FK.ocd_psiExt
          (FKRectPrimalUnexploredVertex R S eta) R.Vertex
          (instFintypeFKRectPrimalUnexploredVertex R S eta)
          (by infer_instance)
          (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex)
          (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)) omega) =
      FK.fkProb (fkRectPrimalUnexploredInducedGraph R S eta) p q omega := by
  have hdm := FK.ocd_condBcProb_psiExt_eq_bcProb
    (Gin := fkRectPrimalUnexploredInducedGraph R S eta)
    (Gout := fkRectCutGraph R)
    (ιV := (Subtype.val :
      FKRectPrimalUnexploredVertex R S eta → R.Vertex))
    (bdryOut := fun _ : R.Vertex => False)
    Subtype.val_injective
    (fkRectPrimalUnexploredInducedGraph_adjMatch R S eta)
    hp hp1 hq
    (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)) omega
  have hbot :
      FK.ocd_inducedWiring (fkRectCutGraph R)
          (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex)
          (fun _ : R.Vertex => False)
          (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)) =
        (⊥ : SimpleGraph (FKRectPrimalUnexploredVertex R S eta)) :=
    fkRectPrimalExploration_ocdInducedWiring_eq_bot R S eta
  have hfree := @FK.bcProb_congr_boundary
    (FKRectPrimalUnexploredVertex R S eta)
    (instFintypeFKRectPrimalUnexploredVertex R S eta)
    (instDecidableEqFKRectPrimalUnexploredVertex R S eta)
    (fkRectPrimalUnexploredInducedGraph R S eta)
    (FK.ocd_inducedWiring (fkRectCutGraph R)
      (Subtype.val : FKRectPrimalUnexploredVertex R S eta → R.Vertex)
      (fun _ : R.Vertex => False)
      (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta)))
    (⊥ : SimpleGraph (FKRectPrimalUnexploredVertex R S eta))
    (instDecidableRelPrimalUnexploredInducedGraph R S eta)
    (FK.instDecidableRelAdjOcd_inducedWiring _ _ _)
    (by infer_instance)
    hbot p q omega
  rw [FK.bcProb_bot_eq_fkProb] at hfree
  simpa only [fkRectPrimalUnexploredPairEdges] using hdm.trans hfree




theorem fkRectPrimalExploration_condFkProb_eq_induced
    (R : FKRectTorus) (S : Finset (Fin R.height))
    (eta omega : R.Configuration) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    FK.condFkProb (fkRectTorusGraph R) p q
        (fkRectPrimalUnexploredEdges R S eta)
        (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))
        (fkRectFullGraphConfiguration R omega) =
      FK.inducedFkProb (fkRectTorusGraph R) p q
        (fkRectPrimalUnexploredEdges R S eta)
        (fkRectFullGraphConfiguration R (fkRectForceCutClosed R eta))
        (fkRectFullGraphConfiguration R omega) := by
  exact FK.condFkProb_eq_inducedFkProb
    (fkRectTorusGraph R) hp hp1 hq _ _ _



theorem exists_primalDualCrossingSourceWitness
    (R : FKRectTorus) (eta : R.Configuration) (n : Nat)
    (hclosed : FKRectCutClosedConfiguration R eta)
    (hn : n <=
      fkRectPrimalDualHorizontalCrossingClusterCount R eta) :
    exists S : Finset (Fin (2 * R.height)),
      S.card = n /\ FKRectPrimalDualCrossingSourceWitness R S eta := by
  classical
  let available :=
    fkRectPrimalDualCrossingRepresentativeSourceIndices R eta
  have hnAvailable : n <= available.card := by
    rw [card_fkRectPrimalDualCrossingRepresentativeSourceIndices]
    exact hn
  obtain ⟨S, hSsub, hScard⟩ :=
    Finset.exists_subset_card_eq hnAvailable
  exact ⟨S, hScard, hclosed, hSsub⟩



theorem fkRectCritical_primalDualCrossingTail_le_choose_mul_pow
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (n : Nat) (hn : 0 < n) (a : Real)
    (Witness : Finset (Fin (2 * R.height)) -> R.Configuration -> Prop)
    (hcover : forall eta : R.Configuration,
      FKRectCutClosedConfiguration R eta ->
        n <= fkRectPrimalDualHorizontalCrossingClusterCount R eta ->
        exists S : Finset (Fin (2 * R.height)),
          S.card = n /\ Witness S eta)
    (hmass : forall S : Finset (Fin (2 * R.height)), S.card = n ->
      fkRectCriticalEventMass R q {eta | Witness S eta} <= a ^ n) :
    fkRectCriticalEventMass R q
        {eta | FKRectCutClosedConfiguration R eta ∧ n <=
          fkRectPrimalDualHorizontalCrossingClusterCount R eta} <=
      Nat.choose (2 * R.height) n * a ^ n := by
  classical
  let K : R.Configuration -> Nat := fun eta =>
    if FKRectCutClosedConfiguration R eta then
      fkRectPrimalDualHorizontalCrossingClusterCount R eta else 0
  rw [fkRectCriticalEventMass_eq_finiteEventMass]
  have htail := StatMech.Probability.finiteEventMass_tail_le_choose_mul_pow
    (fun eta => fkRectCriticalRandomClusterProb R q eta)
    (fun eta => fkRectCriticalRandomClusterProb_nonneg R hq eta)
    K (2 * R.height) n a Witness (by
      intro eta heta
      by_cases hc : FKRectCutClosedConfiguration R eta
      · exact hcover eta hc (by simpa [K, hc] using heta)
      · simp [K, hc, Nat.not_le.mpr hn] at heta) (by
        intro S hS
        rw [<- fkRectCriticalEventMass_eq_finiteEventMass]
        exact hmass S hS)
  have hset : {eta : R.Configuration | n <= K eta} =
      {eta | FKRectCutClosedConfiguration R eta ∧
        n <= fkRectPrimalDualHorizontalCrossingClusterCount R eta} := by
    ext eta
    by_cases hc : FKRectCutClosedConfiguration R eta
    · simp [K, hc]
    · simp [K, hc, Nat.not_le.mpr hn]
  rw [<- hset]
  exact htail


theorem fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (n : Nat) (a : Real)
    (Witness : Finset (Fin (2 * R.height)) -> R.Configuration -> Prop)
    (hcover : forall eta : R.Configuration,
      FKRectCutClosedConfiguration R eta ->
        n < fkRectPrimalDualHorizontalCrossingClusterCount R eta ->
        exists S : Finset (Fin (2 * R.height)),
          S.card = n + 1 /\ Witness S eta)
    (hmass : forall S : Finset (Fin (2 * R.height)), S.card = n + 1 ->
      fkRectCriticalEventMass R q {eta | Witness S eta} <= a ^ (n + 1)) :
    fkRectCriticalEventMass R q
        {eta | FKRectCutClosedConfiguration R eta ∧ n <
          fkRectPrimalDualHorizontalCrossingClusterCount R eta} <=
      Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) := by
  simpa only [Nat.lt_iff_add_one_le] using
    fkRectCritical_primalDualCrossingTail_le_choose_mul_pow
      R hq (n + 1) (Nat.succ_pos n) a Witness (by
        intro eta hclosed heta
        exact hcover eta hclosed (Nat.lt_iff_add_one_le.mpr heta)) hmass



theorem fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow_of_sourceMass
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (n : Nat) (a : Real)
    (hmass : forall S : Finset (Fin (2 * R.height)), S.card = n + 1 ->
      fkRectCriticalEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitness R S eta} <=
        a ^ (n + 1)) :
    fkRectCriticalEventMass R q
        {eta | FKRectCutClosedConfiguration R eta ∧ n <
          fkRectPrimalDualHorizontalCrossingClusterCount R eta} <=
      Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) := by
  apply fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow
    R hq n a (FKRectPrimalDualCrossingSourceWitness R)
  · intro eta hclosed heta
    exact exists_primalDualCrossingSourceWitness R eta (n + 1) hclosed
      (Nat.succ_le_of_lt heta)
  · exact hmass




theorem fkRectCritical_sourceWitnessMass_le_pow_of_step
    (R : FKRectTorus) {q : Real} (hq : 0 < q) {a : Real} (ha : 0 <= a)
    (hstep : forall (T : Finset (Fin (2 * R.height)))
      (i : Fin (2 * R.height)), i ∉ T ->
      fkRectCriticalEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitness R (insert i T) eta} <=
        a * fkRectCriticalEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitness R T eta})
    (S : Finset (Fin (2 * R.height))) :
    fkRectCriticalEventMass R q
        {eta | FKRectPrimalDualCrossingSourceWitness R S eta} <=
      a ^ S.card := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      calc
        fkRectCriticalEventMass R q
            {eta | FKRectPrimalDualCrossingSourceWitness R ∅ eta} <=
          fkRectCriticalEventMass R q Set.univ :=
            fkRectCriticalEventMass_mono R hq (Set.subset_univ _)
        _ = 1 := by
          unfold fkRectCriticalEventMass
          simpa using sum_fkRectCriticalRandomClusterProb R hq
  | @insert i S hi ih =>
      calc
        fkRectCriticalEventMass R q
            {eta | FKRectPrimalDualCrossingSourceWitness R (insert i S) eta} <=
          a * fkRectCriticalEventMass R q
            {eta | FKRectPrimalDualCrossingSourceWitness R S eta} :=
          hstep S i hi
        _ <= a * a ^ S.card := mul_le_mul_of_nonneg_left ih ha
        _ = a ^ (insert i S).card := by
          rw [Finset.card_insert_of_notMem hi, pow_succ]
          ring



theorem fkRectCritical_sourceWitnessStep_of_cutFreeStep
    (R : FKRectTorus) {q : Real} (hq : 1 <= q) (a : Real)
    (hstep : forall (T : Finset (Fin (2 * R.height)))
      (i : Fin (2 * R.height)), i ∉ T ->
      fkRectCriticalCutFreeEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitnessCore R (insert i T) eta} <=
        a * fkRectCriticalCutFreeEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitnessCore R T eta})
    (T : Finset (Fin (2 * R.height)))
    (i : Fin (2 * R.height)) (hi : i ∉ T) :
    fkRectCriticalEventMass R q
        {eta | FKRectPrimalDualCrossingSourceWitness R (insert i T) eta} <=
      a * fkRectCriticalEventMass R q
        {eta | FKRectPrimalDualCrossingSourceWitness R T eta} := by
  let Z := fkRectCriticalClosedMass R q (fkRectTorusCutEdges R)
  have hZ : 0 <= Z := (fkRectCriticalClosedMass_cut_pos R hq).le
  calc
    fkRectCriticalEventMass R q
        {eta | FKRectPrimalDualCrossingSourceWitness R (insert i T) eta} =
      Z * fkRectCriticalCutFreeEventMass R q
        {eta | FKRectPrimalDualCrossingSourceWitnessCore R (insert i T) eta} := by
          symm
          simpa [Z, FKRectPrimalDualCrossingSourceWitness] using
            closedMass_mul_fkRectCriticalCutFreeEventMass R hq
              {eta | FKRectPrimalDualCrossingSourceWitnessCore R
                (insert i T) eta}
    _ <= Z * (a * fkRectCriticalCutFreeEventMass R q
        {eta | FKRectPrimalDualCrossingSourceWitnessCore R T eta}) :=
      mul_le_mul_of_nonneg_left (hstep T i hi) hZ
    _ = a * (Z * fkRectCriticalCutFreeEventMass R q
        {eta | FKRectPrimalDualCrossingSourceWitnessCore R T eta}) := by ring
    _ = a * fkRectCriticalEventMass R q
        {eta | FKRectPrimalDualCrossingSourceWitness R T eta} := by
          congr 1
          simpa [Z, FKRectPrimalDualCrossingSourceWitness] using
            closedMass_mul_fkRectCriticalCutFreeEventMass R hq
              {eta | FKRectPrimalDualCrossingSourceWitnessCore R T eta}


theorem fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow_of_step
    (R : FKRectTorus) {q : Real} (hq : 0 < q)
    (n : Nat) {a : Real} (ha : 0 <= a)
    (hstep : forall (T : Finset (Fin (2 * R.height)))
      (i : Fin (2 * R.height)), i ∉ T ->
      fkRectCriticalEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitness R (insert i T) eta} <=
        a * fkRectCriticalEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitness R T eta}) :
    fkRectCriticalEventMass R q
        {eta | FKRectCutClosedConfiguration R eta ∧
          n < fkRectPrimalDualHorizontalCrossingClusterCount R eta} <=
      Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) := by
  apply
    fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow_of_sourceMass
      R hq n a
  intro S hS
  simpa only [hS] using
    fkRectCritical_sourceWitnessMass_le_pow_of_step R hq ha hstep S



theorem fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow_of_cutFreeStep
    (R : FKRectTorus) {q : Real} (hq : 1 <= q)
    (n : Nat) {a : Real} (ha : 0 <= a)
    (hstep : forall (T : Finset (Fin (2 * R.height)))
      (i : Fin (2 * R.height)), i ∉ T ->
      fkRectCriticalCutFreeEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitnessCore R (insert i T) eta} <=
        a * fkRectCriticalCutFreeEventMass R q
          {eta | FKRectPrimalDualCrossingSourceWitnessCore R T eta}) :
    fkRectCriticalEventMass R q
        {eta | FKRectCutClosedConfiguration R eta ∧
          n < fkRectPrimalDualHorizontalCrossingClusterCount R eta} <=
      Nat.choose (2 * R.height) (n + 1) * a ^ (n + 1) := by
  apply fkRectCritical_primalDualCrossingStrictTail_le_choose_mul_pow_of_step
    R (lt_of_lt_of_le zero_lt_one hq) n ha
  intro T i hi
  exact fkRectCritical_sourceWitnessStep_of_cutFreeStep
    R hq a hstep T i hi

end

end StatMech.FrontierD
