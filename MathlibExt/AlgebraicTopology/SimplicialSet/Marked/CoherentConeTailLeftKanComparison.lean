/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeTailImageLegs
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeTailFreeMonomorphisms
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeFullFreeColimit

/-!
# The actual whole original tail left-extension isomorphism

Native free-image charts preserve every original vertex and relation
cocone leg. The original marked face inclusions are monic, so those
leg equations give full naturality of the same charts. The genuine
free colimits and the existing left-extension adjunction then prove
that the original unit-mate comparison is an isomorphism. Its forward
map remains the original coface operator mate.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory vertexDecidableEq

/-- The actual native vertex-image chart preserves the original whole extended vertex cocone leg. -/
theorem coneTailVertexImageIso_hom_leg (n : ℕ) (j : Vertex.{u} n) :
    (EnrichedLeftKan.leftExtension (coneTailIndex n)).map
        (coneVertexFreeLeg (OrderHom.id : Vertex.{u} n →o Vertex.{u} n) j) ≫ coneTailLeftKanMap n =
      (coneTailVertexImageIso n j).hom ≫ coneTailFreeLeg n j :=
  (coneTailVertexImageIso n j).inv_comp_eq.mp (coneTailVertexImageIso_inv_leg n j)

/-- The actual native relation-image chart preserves the original whole extended relation cocone leg. -/
theorem coneTailRelationImageIso_hom_leg (n : ℕ) (p : (MultispanShape.ofLinearOrder (Vertex.{u} n)).L) :
    (EnrichedLeftKan.leftExtension (coneTailIndex n)).map
        ((coneVertexFreeCocone (OrderHom.id : Vertex.{u} n →o Vertex.{u} n)).ι.app (.left p)) ≫ coneTailLeftKanMap n =
      (coneTailRelationImageIso n p).hom ≫ (coneTailFreeCocone n).ι.app (.left p) :=
  (coneTailRelationImageIso n p).inv_comp_eq.mp (coneTailRelationImageIso_inv_leg n p)

/-- The original native free-image charts give a whole natural isomorphism of the original extended
  vertex/relation diagram. -/
def coneTailLeftKanFreeSpanIso (n : ℕ) :
    (coneVertexFreeSpan (OrderHom.id : Vertex.{u} n →o Vertex.{u} n)).multispan ⋙
        EnrichedLeftKan.leftExtension (coneTailIndex n) ≅ (coneTailFreeSpan n).multispan := by
  refine WalkingMultispan.functorExt (fun p => coneTailRelationImageIso n p)
    (fun j => coneTailVertexImageIso n j) ?_ ?_
  · intro p
    let L := EnrichedLeftKan.leftExtension (coneTailIndex.{u} n)
    let s := coneVertexFreeCocone (OrderHom.id : Vertex.{u} n →o Vertex.{u} n)
    let t := coneTailFreeCocone.{u} n
    let a := (coneVertexFreeSpan (OrderHom.id : Vertex.{u} n →o Vertex.{u} n)).fst p
    let b := s.π p.val.1
    let c := s.ι.app (.left p)
    let a' := (coneTailFreeSpan n).fst p
    let b' := coneTailFreeLeg n p.val.1
    let c' := t.ι.app (.left p)
    have hs : a ≫ b = c := rfl
    have ht : a' ≫ b' = c' := rfl
    let _ : Mono b' := coneTailFreeLeg_mono n p.val.1
    apply (cancel_mono b').mp
    change (L.map a ≫ (coneTailVertexImageIso n p.val.1).hom) ≫ b' =
      ((coneTailRelationImageIso n p).hom ≫ a') ≫ b'
    have h₁ := Category.assoc (L.map a) (coneTailVertexImageIso n p.val.1).hom b'
    have h₂ := congrArg (fun f => L.map a ≫ f) (coneTailVertexImageIso_hom_leg n p.val.1).symm
    have h₃ := (Category.assoc (L.map a) (L.map b) (coneTailLeftKanMap.{u} n)).symm
    have h₄ := congrArg (fun f => f ≫ coneTailLeftKanMap.{u} n) (L.map_comp a b).symm
    have h₅ := congrArg (fun f : (coneVertexFreeSpan (OrderHom.id : Vertex.{u} n →o Vertex.{u} n)).left p ⟶
      coneDiagram.{u} n => L.map f ≫ coneTailLeftKanMap.{u} n) hs
    have h₆ : L.map c ≫ coneTailLeftKanMap.{u} n = (coneTailRelationImageIso n p).hom ≫ c' :=
      coneTailRelationImageIso_hom_leg n p
    have h₇ := (congrArg (fun f => (coneTailRelationImageIso n p).hom ≫ f) ht.symm).trans
      (Category.assoc (coneTailRelationImageIso n p).hom a' b').symm
    exact h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans h₇)))))
  · intro p
    let L := EnrichedLeftKan.leftExtension (coneTailIndex.{u} n)
    let s := coneVertexFreeCocone (OrderHom.id : Vertex.{u} n →o Vertex.{u} n)
    let t := coneTailFreeCocone.{u} n
    let a := (coneVertexFreeSpan (OrderHom.id : Vertex.{u} n →o Vertex.{u} n)).snd p
    let b := s.π p.val.2
    let c := s.ι.app (.left p)
    let a' := (coneTailFreeSpan n).snd p
    let b' := coneTailFreeLeg n p.val.2
    let c' := t.ι.app (.left p)
    have hs : a ≫ b = c := (Multicofork.snd_app_right s p).symm
    have ht : a' ≫ b' = c' := (Multicofork.snd_app_right t p).symm
    let _ : Mono b' := coneTailFreeLeg_mono n p.val.2
    apply (cancel_mono b').mp
    change (L.map a ≫ (coneTailVertexImageIso n p.val.2).hom) ≫ b' =
      ((coneTailRelationImageIso n p).hom ≫ a') ≫ b'
    have h₁ := Category.assoc (L.map a) (coneTailVertexImageIso n p.val.2).hom b'
    have h₂ := congrArg (fun f => L.map a ≫ f) (coneTailVertexImageIso_hom_leg n p.val.2).symm
    have h₃ := (Category.assoc (L.map a) (L.map b) (coneTailLeftKanMap.{u} n)).symm
    have h₄ := congrArg (fun f => f ≫ coneTailLeftKanMap.{u} n) (L.map_comp a b).symm
    have h₅ := congrArg (fun f : (coneVertexFreeSpan (OrderHom.id : Vertex.{u} n →o Vertex.{u} n)).left p ⟶
      coneDiagram.{u} n => L.map f ≫ coneTailLeftKanMap.{u} n) hs
    have h₆ : L.map c ≫ coneTailLeftKanMap.{u} n = (coneTailRelationImageIso n p).hom ≫ c' :=
      coneTailRelationImageIso_hom_leg n p
    have h₇ := (congrArg (fun f => (coneTailRelationImageIso n p).hom ≫ f) ht.symm).trans
      (Category.assoc (coneTailRelationImageIso n p).hom a' b').symm
    exact h₁.trans (h₂.trans (h₃.trans (h₄.trans (h₅.trans (h₆.trans h₇)))))

/-- The original unit-mate comparison is a genuine whole marked enriched tail left-extension isomorphism. -/
def coneTailLeftKanIso (n : ℕ) :
    EnrichedLeftKan.object (coneTailIndex n) (coneDiagram n) ≅
      coneAfterDiagram (⊥ : Vertex.{u} (n + 1)) := by
  let L := EnrichedLeftKan.leftExtension (coneTailIndex.{u} n)
  let s := coneVertexFreeCocone (OrderHom.id : Vertex.{u} n →o Vertex.{u} n)
  let t := coneTailFreeCocone.{u} n
  let _ : PreservesColimitsOfSize.{u, u} L := (EnrichedLeftKan.adjunction (coneTailIndex
    n)).leftAdjoint_preservesColimits
  let hs : IsColimit (L.mapCocone s) := isColimitOfPreserves L (coneFullFreeIsColimit.{u} n)
  let d := coneTailLeftKanFreeSpanIso.{u} n
  let e : EnrichedLeftKan.object (coneTailIndex n) (coneDiagram n) ≅
      coneAfterDiagram (⊥ : Vertex.{u} (n + 1)) :=
    IsColimit.coconePointsIsoOfNatIso hs (coneTailFreeIsColimit.{u} n) d
  have he : e.hom = coneTailLeftKanMap n := by
    apply hs.hom_ext
    intro j
    have h := hs.fac ((Cocone.precompose d.hom).obj t) j
    cases j with
    | left p => exact h.trans (coneTailRelationImageIso_hom_leg n p).symm
    | right j => exact h.trans (coneTailVertexImageIso_hom_leg n j).symm
  exact
    { hom := coneTailLeftKanMap n
      inv := e.inv
      hom_inv_id := he ▸ e.hom_inv_id
      inv_hom_id := he ▸ e.inv_hom_id }

/-- The forward whole tail isomorphism is the same actual original universal coface mate. -/
theorem coneTailLeftKanIso_hom (n : ℕ) : (coneTailLeftKanIso.{u} n).hom = coneTailLeftKanMap n := rfl

end SSet.Marked.CoherentWeight
