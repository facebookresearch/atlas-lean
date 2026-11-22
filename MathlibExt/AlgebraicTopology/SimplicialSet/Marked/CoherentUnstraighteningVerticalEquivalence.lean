/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentUnstraighteningConstantCoefficient

/-!
# The SAME original constant-base inverse triangles detect marking

The whole original marked section comparison identifies the shared
original inverse edge of two actual constant-base triangles. Their
original long unit faces and constant-maximum root edges make both
original coefficient composites equivalences. Actual inverse algebra
then proves that the SAME original coefficient edge is an equivalence,
so actual coefficient fibrancy marks it. No returned marking, lift or
Cartesian-edge equivalence outcome is supplied as a premise.
-/

noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] markedSimplicialCategory enrichedDiagramCategory coefficientMarkedModelCategory

private theorem isIso_middle_of_composites {D : Type*} [Category* D] {w x y z : D}
    (a : w ⟶ x) (b : x ⟶ y) (c : y ⟶ z) [IsIso (a ≫ b)] [IsIso (b ≫ c)] : IsIso b := by
  let r := c ≫ inv (b ≫ c)
  let l := inv (a ≫ b) ≫ a
  have hr : b ≫ r = 𝟙 x :=
    (Category.assoc b c (inv (b ≫ c))).symm.trans (IsIso.hom_inv_id (b ≫ c))
  have hl : l ≫ b = 𝟙 y :=
    (Category.assoc (inv (a ≫ b)) a b).trans (IsIso.inv_hom_id (a ≫ b))
  have hrl : r = l :=
    (Category.id_comp r).symm.trans
      ((congrArg (fun f => f ≫ r) hl.symm).trans
        ((Category.assoc l b r).trans
          ((congrArg (fun f => l ≫ f) hr).trans (Category.comp_id l))))
  exact ⟨r, hr, (congrArg (fun f => f ≫ b) hrl).trans hl⟩

private theorem edge_equivalence_of_unit_composites {A : SSet.{u}}
    {x₀ x₁ x₂ y₀ y₁ y₂ : A _⦋0⦌}
    {g : Edge x₀ x₁} {e : Edge x₁ x₂} {h : Edge y₀ y₁} {g' : Edge y₁ y₂}
    {l : Edge x₀ x₂} {l' : Edge y₀ y₂}
    (H : Edge.CompStruct g e l) (H' : Edge.CompStruct h g' l')
    (hshared : g'.edge = g.edge) (hl : l.IsEquivalence) (hl' : l'.IsEquivalence) : e.IsEquivalence := by
  have hy₁ : y₁ = x₀ := g'.src_eq.symm.trans ((congrArg (A.δ (1 : Fin 2)) hshared).trans g.src_eq)
  have hy₂ : y₂ = x₁ := g'.tgt_eq.symm.trans ((congrArg (A.δ (0 : Fin 2)) hshared).trans g.tgt_eq)
  subst y₁
  subst y₂
  have hg' : g' = g := Edge.ext hshared
  subst g'
  let _ : IsIso (h.toHoHom ≫ g.toHoHom) := by
    rw [Edge.toHoHom_comp H']
    exact hl'
  let _ : IsIso (g.toHoHom ≫ e.toHoHom) := by
    rw [Edge.toHoHom_comp H]
    exact hl
  let _ : IsIso g.toHoHom := isIso_middle_of_composites h.toHoHom g.toHoHom e.toHoHom
  exact IsIso.of_isIso_comp_left g.toHoHom e.toHoHom

variable {C : Type u} [EnrichedCategory SSet.{u} C]

/-- The SAME full original constant-base inverse sections and their original long unit marks prove marking of the
SAME original coefficient edge by actual coefficient-model fibrancy. -/
theorem originalConstantSections_inverse_marking (F : EnrichedDiagram Cᵒᵖ)
    (v : EnrichedFunctor SSet.{u} (Index.{u} 0) C)
    (hA : IsFibrant (F.obj (op (v.obj (SimplicialThickening.mk (ULift.up (0 : Fin 1)))))))
    (s t : EnrichedDiagramMap (coneDiagram 2) (originalConstantCoefficient F v 2))
    (hshared : originalConstantSectionFace F v (coneCofaceEmbedding (2 : Fin 3)).toOrderHom s =
      originalConstantSectionFace F v (coneCofaceEmbedding (0 : Fin 3)).toOrderHom t)
    (hs : originalConstantSectionRead F v
      (originalConstantSectionFace F v (coneCofaceEmbedding (1 : Fin 3)).toOrderHom s) ∈
        (F.obj (op (v.obj (SimplicialThickening.mk (ULift.up (0 : Fin 1)))))).marking)
    (ht : originalConstantSectionRead F v
      (originalConstantSectionFace F v (coneCofaceEmbedding (1 : Fin 3)).toOrderHom t) ∈
        (F.obj (op (v.obj (SimplicialThickening.mk (ULift.up (0 : Fin 1)))))).marking) :
    originalConstantSectionRead F v
      (originalConstantSectionFace F v (coneCofaceEmbedding (0 : Fin 3)).toOrderHom s) ∈
        (F.obj (op (v.obj (SimplicialThickening.mk (ULift.up (0 : Fin 1)))))).marking := by
  let A := F.obj (op (v.obj (SimplicialThickening.mk (ULift.up (0 : Fin 1)))))
  let i₀ : (Index.{u} 2)ᵒᵖ := op (SimplicialThickening.mk rootTriangleZero)
  let gs : coneWeight rootTriangleZero ⟶ A := s.app i₀
  let gt : coneWeight rootTriangleZero ⟶ A := t.app i₀
  have full (a : EnrichedDiagramMap (coneDiagram 2) (originalConstantCoefficient F v 2))
      (ha : originalConstantSectionRead F v
        (originalConstantSectionFace F v (coneCofaceEmbedding (1 : Fin 3)).toOrderHom a) ∈ A.marking) :
      ((nerve.edgeMk rootTriangleFull).map (a.app i₀).hom).IsEquivalence := by
    rw [originalConstantSectionRead_direct] at ha
    have hd : ((nerve.edgeMk rootTriangleDirect).map (a.app i₀).hom).IsEquivalence :=
      ((coefficientFibrant_marking_iff A hA _).mp ha).of_edge_eq rfl
    have hc : ((nerve.edgeMk rootTriangleConstant).map (a.app i₀).hom).IsEquivalence :=
      ((coefficientFibrant_marking_iff A hA _).mp ((a.app i₀).preserve rootTriangle_constant_marked)).of_edge_eq rfl
    exact Edge.IsEquivalence.of_compStruct (rootTriangleSecondComp.map (a.app i₀).hom) hd hc
  have heq : ((nerve.edgeMk rootTriangleMiddle).map gt.hom).edge =
      ((nerve.edgeMk rootTriangleFirst).map gs.hom).edge := by
    have h := congrArg (originalConstantSectionRead F v) hshared
    rw [originalConstantSectionRead_first, originalConstantSectionRead_middle] at h
    exact h.symm
  have he := edge_equivalence_of_unit_composites (rootTriangleFirstComp.map gs.hom)
    (rootTriangleFirstComp.map gt.hom) heq (full s hs) (full t ht)
  rw [originalConstantSectionRead_middle]
  exact (coefficientFibrant_marking_iff A hA _).mpr (he.of_edge_eq rfl)

end SSet.Marked.CoherentWeight
