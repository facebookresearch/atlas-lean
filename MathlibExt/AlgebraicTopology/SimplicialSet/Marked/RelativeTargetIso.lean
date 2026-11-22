/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.RelativeUnderlying
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.MappingNaturality

/-!
# Original target-isomorphism transport of relative marked mapping complexes

An original marked isomorphism over the same base acts by its actual
postcomposition map on every whole prism. The existing native pullback-map
isomorphism transports the fixed-base complex and retains its original point
coordinate. No replacement or model comparison is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits

namespace SSet.Marked

/-- The original marked target isomorphism postcomposes every original whole prism. -/
def mappingComplexPostIso (k : ParameterMarking) (X : Marked.{u}) {Y Y' : Marked.{u}}
    (e : Y ≅ Y') : mappingComplex k X Y ≅ mappingComplex k X Y' where
  hom := mappingComplexPost k X e.hom
  inv := mappingComplexPost k X e.inv
  hom_inv_id := by
    rw [← mappingComplexPost_comp, e.hom_inv_id, mappingComplexPost_id]
  inv_hom_id := by
    rw [← mappingComplexPost_comp, e.inv_hom_id, mappingComplexPost_id]

/-- The actual marked target isomorphism over the base gives the original native pullback isomorphism. -/
def relativeMappingTargetIso (k : ParameterMarking) {X Y Y' Z : Marked.{u}}
    (r : X ⟶ Z) (e : Y ≅ Y') (p : Y ⟶ Z) (p' : Y' ⟶ Z) (he : e.hom ≫ p' = p) :
    relativeMappingComplex k r p ≅ relativeMappingComplex k r p' := by
  let _ : IsIso (mappingComplexPost k X e.hom) := by
    change IsIso (mappingComplexPostIso k X e).hom
    infer_instance
  let a := mappingComplexPost k X p
  let b := mappingComplexPost k X p'
  let c := mappingBasePoint k r
  let t := mappingComplexPost k X e.hom
  have h₁ : a ≫ 𝟙 _ = t ≫ b := by
    rw [Category.comp_id, ← mappingComplexPost_comp, he]
  have h₂ : c ≫ 𝟙 _ = 𝟙 _ ≫ c := by simp
  let f : relativeMappingComplex k r p ⟶ relativeMappingComplex k r p' :=
    pullback.map a c b c t (𝟙 _) (𝟙 _) h₁ h₂
  let _ : IsIso f := pullback.map_isIso a c b c t (𝟙 _) (𝟙 _) h₁ h₂
  exact asIso f

/-- Target transport retains the original postcomposition of the whole marked prism. -/
theorem relativeMappingTargetIso_hom_fst (k : ParameterMarking) {X Y Y' Z : Marked.{u}}
    (r : X ⟶ Z) (e : Y ≅ Y') (p : Y ⟶ Z) (p' : Y' ⟶ Z) (he : e.hom ≫ p' = p) :
    (relativeMappingTargetIso k r e p p' he).hom ≫
        pullback.fst (mappingComplexPost k X p') (mappingBasePoint k r) =
      pullback.fst (mappingComplexPost k X p) (mappingBasePoint k r) ≫ mappingComplexPost k X e.hom :=
  pullback.lift_fst _ _ _

/-- Target transport retains the original fixed-base point coordinate. -/
theorem relativeMappingTargetIso_hom_snd (k : ParameterMarking) {X Y Y' Z : Marked.{u}}
    (r : X ⟶ Z) (e : Y ≅ Y') (p : Y ⟶ Z) (p' : Y' ⟶ Z) (he : e.hom ≫ p' = p) :
    (relativeMappingTargetIso k r e p p' he).hom ≫
        pullback.snd (mappingComplexPost k X p') (mappingBasePoint k r) =
      pullback.snd (mappingComplexPost k X p) (mappingBasePoint k r) := by
  have h : (relativeMappingTargetIso k r e p p' he).hom ≫
      pullback.snd (mappingComplexPost k X p') (mappingBasePoint k r) =
      pullback.snd (mappingComplexPost k X p) (mappingBasePoint k r) ≫ 𝟙 _ :=
    pullback.lift_snd _ _ _
  exact h.trans (Category.comp_id _)

end SSet.Marked
