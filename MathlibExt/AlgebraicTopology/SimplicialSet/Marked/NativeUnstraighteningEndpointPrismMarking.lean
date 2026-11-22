/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.NativeUnstraighteningEndpointPrismBoundary
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.EndpointPrismMarking

/-!
# Original endpoint-prism markings on actual native model maps

The two original product triangles retain the same whole native prism.
Relative composition marks the original mixed edge from the marked
vertical and target row; relative cancellation marks the source row.
The prescribed whole marked target prism supplies the original target
edge marks. Every interval edge is one of its two original degeneracies
or its original fundamental edge. No intrinsic fibrancy or marking
saturation outcome is a premise.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped Simplicial

namespace SSet.Marked
open CategoryTheory.CoherentRealization
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory

/-- Both original product triangles retain their same mixed and source-edge marks under an actual native
model-fibration map. -/
theorem nativeUnstraightening_endpointPrism_mixed_and_source (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) {T I : SSet.{u}}
    (L : T ⊗ I ⟶ (nativeUnstraighteningTotal B F).toSSet)
    {t₀ t₁ : T _⦋0⦌} (a : Edge t₀ t₁) {i₀ i₁ : I _⦋0⦌} (b : Edge i₀ i₁)
    (hv₀ : (((Edge.id t₀).tensor b).map L).edge ∈ (nativeUnstraighteningTotal B F).marking)
    (hv₁ : (((Edge.id t₁).tensor b).map L).edge ∈ (nativeUnstraighteningTotal B F).marking)
    (hh₁ : ((a.tensor (Edge.id i₁)).map L).edge ∈ (nativeUnstraighteningTotal B F).marking)
    (hGmix : ((nativeUnstraightening B).map q).left.hom.app (op ⦋1⦌) ((a.tensor b).map L).edge ∈
      (nativeUnstraighteningTotal B G).marking)
    (hGsource : ((nativeUnstraightening B).map q).left.hom.app (op ⦋1⦌) ((a.tensor (Edge.id i₀)).map L).edge ∈
      (nativeUnstraighteningTotal B G).marking) :
    let _ := coherentDiagramModelCategory B
    Fibration q → ((a.tensor b).map L).edge ∈ (nativeUnstraighteningTotal B F).marking ∧
      ((a.tensor (Edge.id i₀)).map L).edge ∈ (nativeUnstraighteningTotal B F).marking := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  let H := ((Edge.CompStruct.idComp a).tensor (Edge.CompStruct.compId b)).map L
  let H' := ((Edge.CompStruct.compId a).tensor (Edge.CompStruct.idComp b)).map L
  have hm := nativeUnstraightening_map_relativeCompStruct B q H hv₀ hh₁ hGmix hq
  exact ⟨hm, nativeUnstraightening_map_relativeCancellationCompStruct B q H' hv₁ hm hGsource hq⟩

private abbrev nativeEndpointIntervalFundamental : Edge
    (stdSimplex.obj₀Equiv.symm (0 : Fin 2) : (Δ[1] : SSet.{u}) _⦋0⦌)
    (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) :=
  Edge.mk (yonedaEquiv (𝟙 (Δ[1] : SSet.{u})))
    (by apply stdSimplex.ext; intro i; fin_cases i; rfl)
    (by apply stdSimplex.ext; intro i; fin_cases i; rfl)

private theorem nativeEndpointInterval_edges_induction (P : (Δ[1] : SSet.{u}) _⦋1⦌ → Prop)
    (hzero : P ((Δ[1] : SSet.{u}).σ 0 (stdSimplex.obj₀Equiv.symm (0 : Fin 2))))
    (hfundamental : P nativeEndpointIntervalFundamental.{u}.edge)
    (hone : P ((Δ[1] : SSet.{u}).σ 0 (stdSimplex.obj₀Equiv.symm (1 : Fin 2))))
    (b : (Δ[1] : SSet.{u}) _⦋1⦌) : P b := by
  obtain ⟨j, hj⟩ := stdSimplex.objMk₁_surjective b
  apply (congrArg P hj).to_iff.mp
  fin_cases j
  · have he : stdSimplex.objMk₁.{u} (0 : Fin 3) =
        (Δ[1] : SSet.{u}).σ 0 (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
      apply stdSimplex.ext
      intro i
      fin_cases i <;> rfl
    exact (congrArg P he).to_iff.mpr hone
  · have he : stdSimplex.objMk₁.{u} (1 : Fin 3) = nativeEndpointIntervalFundamental.{u}.edge := by
      apply stdSimplex.ext
      intro i
      fin_cases i <;> rfl
    exact (congrArg P he).to_iff.mpr hfundamental
  · have he : stdSimplex.objMk₁.{u} (2 : Fin 3) =
        (Δ[1] : SSet.{u}).σ 0 (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
      apply stdSimplex.ext
      intro i
      fin_cases i <;> rfl
    exact (congrArg P he).to_iff.mpr hzero

/-- The same whole original native endpoint prism carries every original marked product edge, through genuine
relative composition and cancellation. -/
def nativeMarkedEndpointPrismOfTarget (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) {T : Marked.{u}}
    (L : T.toSSet ⊗ Δ[1] ⟶ (nativeUnstraighteningTotal B F).toSSet)
    (K : prod T (max (Δ[1] : SSet.{u})) ⟶ nativeUnstraighteningTotal B G)
    (hbase : L ≫ ((nativeUnstraightening B).map q).left.hom = K.hom)
    (hvert : nativePrismOneVerticalsMarked B F L)
    (hrow : ∀ a : T.toSSet _⦋1⦌, a ∈ T.marking →
      (prismSectionAt T.toSSet (1 : Fin 2) ≫ L).app (op ⦋1⦌) a ∈ (nativeUnstraighteningTotal B F).marking) :
    let _ := coherentDiagramModelCategory B
    Fibration q → (prod T (max (Δ[1] : SSet.{u})) ⟶ nativeUnstraighteningTotal B F) := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro hq
  exact
    { hom := L
      preserve {z} hz := by
        let a : T.toSSet _⦋1⦌ := z.1
        let b : (Δ[1] : SSet.{u}) _⦋1⦌ := z.2
        let P : (Δ[1] : SSet.{u}) _⦋1⦌ → Prop :=
          fun t => L.app (op ⦋1⦌) (a, t) ∈ (nativeUnstraighteningTotal B F).marking
        have hrow' := hrow a hz.1
        rw [prismSectionAt_app_one] at hrow'
        have htarget (t : (Δ[1] : SSet.{u}) _⦋1⦌) :
            ((nativeUnstraightening B).map q).left.hom.app (op ⦋1⦌)
              (L.app (op ⦋1⦌) (a, t)) ∈ (nativeUnstraighteningTotal B G).marking := by
          have hm := K.preserve (show (a, t) ∈ (prod T (max (Δ[1] : SSet.{u}))).marking from
            ⟨hz.1, Set.mem_univ _⟩)
          have he := congrArg
            (fun f : T.toSSet ⊗ (Δ[1] : SSet.{u}) ⟶ (nativeUnstraighteningTotal B G).toSSet =>
              f.app (op ⦋1⦌) (a, t)) hbase
          exact he.symm ▸ hm
        have h := nativeUnstraightening_endpointPrism_mixed_and_source B q L (Edge.mk' a)
          nativeEndpointIntervalFundamental (hvert _) (hvert _) hrow'
          (htarget nativeEndpointIntervalFundamental.edge)
          (htarget ((Δ[1] : SSet.{u}).σ 0 (stdSimplex.obj₀Equiv.symm (0 : Fin 2)))) hq
        exact nativeEndpointInterval_edges_induction P h.2 h.1 hrow' b }

/-- The marked extension is exactly the same entire original simplicial prism map. -/
theorem nativeMarkedEndpointPrismOfTarget_hom (B : SSet.{u})
    {F G : EnrichedDiagram (realization B)ᵒᵖ} (q : F ⟶ G) {T : Marked.{u}}
    (L : T.toSSet ⊗ Δ[1] ⟶ (nativeUnstraighteningTotal B F).toSSet)
    (K : prod T (max (Δ[1] : SSet.{u})) ⟶ nativeUnstraighteningTotal B G)
    (hbase : L ≫ ((nativeUnstraightening B).map q).left.hom = K.hom)
    (hvert : nativePrismOneVerticalsMarked B F L)
    (hrow : ∀ a : T.toSSet _⦋1⦌, a ∈ T.marking →
      (prismSectionAt T.toSSet (1 : Fin 2) ≫ L).app (op ⦋1⦌) a ∈ (nativeUnstraighteningTotal B F).marking) :
    let _ := coherentDiagramModelCategory B
    ∀ _hq : Fibration q, (nativeMarkedEndpointPrismOfTarget B q L K hbase hvert hrow _hq).hom = L := by
  let _ := coherentDiagramModelCategory B
  dsimp only
  intro _hq
  rfl

end SSet.Marked
