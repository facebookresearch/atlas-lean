/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.FKRectCriticalFullGraphLaw
import Code.FK.OffCentreConditionalLowerProduct



open SimpleGraph

namespace StatMech.FrontierD

noncomputable section


def FKRectInducedVertex (R : FKRectTorus) (S : Set R.Vertex) := S

noncomputable instance instFintypeFKRectInducedVertex
    (R : FKRectTorus) (S : Set R.Vertex) :
    Fintype (FKRectInducedVertex R S) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

noncomputable instance instDecidableEqFKRectInducedVertex
    (R : FKRectTorus) (S : Set R.Vertex) :
    DecidableEq (FKRectInducedVertex R S) := Classical.decEq _


def fkRectInducedGraph (R : FKRectTorus) (S : Set R.Vertex) :
    SimpleGraph (FKRectInducedVertex R S) :=
  (fkRectTorusGraph R).comap Subtype.val

noncomputable instance instDecidableRelFKRectInducedGraph
    (R : FKRectTorus) (S : Set R.Vertex) :
    DecidableRel (fkRectInducedGraph R S).Adj := Classical.decRel _

noncomputable instance instDecidableRelFKRectInducedOuterGraph
    (R : FKRectTorus) :
    DecidableRel (fkRectTorusGraph R).Adj := Classical.decRel _

theorem fkRectInducedGraph_adjMatch (R : FKRectTorus)
    (S : Set R.Vertex) :
    FK.ocd_AdjMatch (fkRectInducedGraph R S) (fkRectTorusGraph R)
      (Subtype.val : FKRectInducedVertex R S → R.Vertex) := by
  intro x y
  rfl


def fkRectFullGraphEvent (R : FKRectTorus)
    (B : Set R.Configuration) :
    Set (ConfigSpace (Sym2 R.Vertex)) :=
  FK.ecz_closeOff (fkRectTorusGraph R) ⁻¹' fkRectFullEdgeEvent R B



theorem fkRectFullGraphEvent_mass_eq
    (R : FKRectTorus) {q : Real} (hq : 1 ≤ q)
    (B : Set R.Configuration) :
    (∑ rho : ConfigSpace (Sym2 R.Vertex),
        (fkRectFullGraphEvent R B).indicator (fun _ => (1 : Real)) rho *
          FK.fkProb (fkRectTorusGraph R) (fkRectCriticalP q) q rho) =
      fkRectCriticalEventMass R q B := by
  exact (fkRectCriticalEventMass_eq_fullGraph R hq B).symm



def FKRectDependsOnOutsideRegion (R : FKRectTorus)
    (S : Set R.Vertex) (B : Set R.Configuration) : Prop :=
  ∀ omega tau : R.Configuration,
    (∀ a : R.EdgeIndex,
      fkRectTorusIndexedEdge R a ∉
        Set.range (FK.ocd_innerEdge
          (Subtype.val : FKRectInducedVertex R S → R.Vertex)) →
      omega a = tau a) →
    (omega ∈ B ↔ tau ∈ B)



theorem fkRectFullGraphEvent_dependsOnOutside
    (R : FKRectTorus) (S : Set R.Vertex)
    {B : Set R.Configuration}
    (hB : FKRectDependsOnOutsideRegion R S B) :
    FK.DependsOnOutside
      (FK.ocd_innerEdgeFinset
        (Vin := FKRectInducedVertex R S)
        (Subtype.val : FKRectInducedVertex R S → R.Vertex))
      (fkRectFullGraphEvent R B) := by
  intro psi rho hagree
  change (fkRectFullEdgeConfigEquiv R).symm
      (FK.ecz_closeOff (fkRectTorusGraph R) psi) ∈ B ↔
    (fkRectFullEdgeConfigEquiv R).symm
      (FK.ecz_closeOff (fkRectTorusGraph R) rho) ∈ B
  apply hB
  intro a ha
  change (FK.ecz_closeOff (fkRectTorusGraph R) psi).1
      (fkRectTorusIndexedEdge R a) =
    (FK.ecz_closeOff (fkRectTorusGraph R) rho).1
      (fkRectTorusIndexedEdge R a)
  have hedge : fkRectTorusIndexedEdge R a ∈
      (fkRectTorusGraph R).edgeFinset := by
    rw [SimpleGraph.mem_edgeFinset]
    exact (mem_fkRectTorusGraph_edgeSet_iff R _).2 ⟨a, rfl⟩
  rw [FK.ecz_closeOff_apply_edge _ _ hedge,
    FK.ecz_closeOff_apply_edge _ _ hedge]
  have hoff : fkRectTorusIndexedEdge R a ∉
      FK.ocd_innerEdgeFinset
        (Vin := FKRectInducedVertex R S)
        (Subtype.val : FKRectInducedVertex R S → R.Vertex) := by
    rw [FK.ocd_mem_innerEdgeFinset]
    exact ha
  exact (hagree _ hoff).symm




theorem fkRectInduced_freeMass_mul_eventMass_le_genericInter
    (R : FKRectTorus) (S : Set R.Vertex)
    {q : Real} (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 (FKRectInducedVertex R S)))}
    (hA : IsIncreasing A)
    {B : Set R.Configuration}
    (hB : FK.DependsOnOutside
      (FK.ocd_innerEdgeFinset
        (Vin := FKRectInducedVertex R S)
        (Subtype.val : FKRectInducedVertex R S → R.Vertex))
      (fkRectFullGraphEvent R B)) :
    (∑ omega,
        A.indicator (fun _ => (1 : Real)) omega *
          FK.fkProb (fkRectInducedGraph R S)
            (fkRectCriticalP q) q omega) *
        fkRectCriticalEventMass R q B ≤
      ∑ rho,
        ((FK.ocd_innerRestrict
            (Subtype.val : FKRectInducedVertex R S → R.Vertex) ⁻¹' A) ∩
          fkRectFullGraphEvent R B).indicator
            (fun _ => (1 : Real)) rho *
          FK.fkProb (fkRectTorusGraph R)
            (fkRectCriticalP q) q rho := by
  have hq0 : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hprod := FK.ocd_freeMass_mul_freeOutsideMass_le_inter
    (fkRectInducedGraph R S) (fkRectTorusGraph R)
    (Subtype.val : FKRectInducedVertex R S → R.Vertex)
    Subtype.val_injective (fkRectInducedGraph_adjMatch R S)
    (fkRectCriticalP_pos hq0) (fkRectCriticalP_lt_one hq0) hq hA hB
  rw [fkRectFullGraphEvent_mass_eq R hq B] at hprod
  exact hprod



theorem fkRectInduced_freeMass_mul_indexedOutsideMass_le_genericInter
    (R : FKRectTorus) (S : Set R.Vertex)
    {q : Real} (hq : 1 ≤ q)
    {A : Set (ConfigSpace (Sym2 (FKRectInducedVertex R S)))}
    (hA : IsIncreasing A)
    {B : Set R.Configuration}
    (hB : FKRectDependsOnOutsideRegion R S B) :
    (∑ omega,
        A.indicator (fun _ => (1 : Real)) omega *
          FK.fkProb (fkRectInducedGraph R S)
            (fkRectCriticalP q) q omega) *
        fkRectCriticalEventMass R q B ≤
      ∑ rho,
        ((FK.ocd_innerRestrict
            (Subtype.val : FKRectInducedVertex R S → R.Vertex) ⁻¹' A) ∩
          fkRectFullGraphEvent R B).indicator
            (fun _ => (1 : Real)) rho *
          FK.fkProb (fkRectTorusGraph R)
            (fkRectCriticalP q) q rho :=
  fkRectInduced_freeMass_mul_eventMass_le_genericInter R S hq hA
    (fkRectFullGraphEvent_dependsOnOutside R S hB)

end

end StatMech.FrontierD
