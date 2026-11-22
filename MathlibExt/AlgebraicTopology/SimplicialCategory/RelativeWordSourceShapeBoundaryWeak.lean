/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.RelativeWordSourceShapeBoundaries

/-!
# Genuine original shape-boundary comparison weakness

The original boundary in each positive shape is the full old Hom factor
times the SAME union of attaching-image letters and the shorter boundary.
The native union-product pushout and canonical original tensor weakness
prove the actual boundary source map weak by finite-shape induction.
No whole attaching-pushout weakness is supplied as an input.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory Opposite
open scoped SSet.modelCategoryQuillen

namespace CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
open RelativeWords
variable {O : Type u} {C D : FixedObjects O}

/-- The empty-left union factor is literally the SAME old Hom tensor the shorter boundary. -/
def emptyLeftUnionIso (X Y : SSet.{u}) (B : Y.Subcomplex) :
    ((⊥ : X.Subcomplex).unionProd B).toSSet ≅ X ⊗ B.toSSet where
  hom := {
    app q := ↾fun p => ⟨p.val.1, ⟨p.val.2, by
      rcases (SSet.Subcomplex.mem_unionProd_iff (⊥ : X.Subcomplex) B p.val).mp p.property with h | h
      · exact h
      · exact h.elim⟩⟩
    naturality q r f := by ext p; rfl }
  inv := SSet.Subcomplex.unionProd.ι₁ (⊥ : X.Subcomplex) B
  hom_inv_id := by ext q p; apply Subtype.ext; rfl
  inv_hom_id := by
    apply NatTrans.ext
    funext q
    apply ConcreteCategory.hom_ext
    intro p
    apply Prod.ext
    · rfl
    · apply Subtype.ext; rfl

/-- The SAME actual original shape boundary source map is genuinely weak on all full original factors. -/
theorem shapeBoundarySourceChange_weak (T : Data C) (F : C ⟶ D)
    (hF : FixedObjectModel.weakEquivalences O F) {n : ℕ} (s : Shape O n) (a b : O) :
    SSet.realizationWeakEquivalences (shapeBoundarySourceChange T F s a b) := by
  have h := (FixedObjectModel.weakEquivalences_iff F).mp hF
  induction s generalizing a b with
  | nil =>
    let e : (shapeBoundary T Shape.nil a b).toSSet ≅
        (shapeBoundary (sourceChange T F) Shape.nil a b).toSSet :=
      { hom := shapeBoundarySourceChange T F Shape.nil a b
        inv := { app q := ↾fun p => p.property.elim
                 naturality q r f := by ext p; exact p.property.elim }
        hom_inv_id := by ext q p; exact p.property.elim
        inv_hom_id := by ext q p; exact p.property.elim }
    let _ : IsIso e.hom := e.isIso_hom
    exact SSet.realizationWeakEquivalences.of_isIso e.hom
  | cons x y s ih =>
    let Y := T.target.Hom x y
    let Z := shapeSpace T s y b
    let Z' := shapeSpace (sourceChange T F) s y b
    let A := SSet.Subcomplex.range (T.inclusion x y)
    let B := shapeBoundary T s y b
    let B' := shapeBoundary (sourceChange T F) s y b
    let u : Z ⟶ Z' := shapeSourceChange T F s y b
    let v : B.toSSet ⟶ B'.toSSet := shapeBoundarySourceChange T F s y b
    let m := SSet.Subcomplex.unionProdMap A B A B' (𝟙 Y) u
      (fun _ _ h => h) (fun q p hp => (shapeSourceChange_boundary_iff T F q s p).mpr hp)
    have wm : SSet.realizationWeakEquivalences m := SSet.Subcomplex.unionProdMap_weak A B A B'
      (𝟙 Y) u (fun _ _ h => h) (fun q p hp => (shapeSourceChange_boundary_iff T F q s p).mpr hp)
      (𝟙 A.toSSet) v ((Category.id_comp A.ι).trans (Category.comp_id A.ι).symm)
      (shapeBoundarySourceChange_ι T F s y b) (SSet.realizationWeakEquivalences.id_mem _)
      (shapeSourceChange_weak T F hF s y b) (SSet.realizationWeakEquivalences.id_mem _) (ih y b)
    let e := emptyLeftUnionIso (hom C a x) (Y ⊗ Z) (A.unionProd B)
    let e' := emptyLeftUnionIso (hom D a x) (Y ⊗ Z') (A.unionProd B')
    let _ : IsIso e.hom := e.isIso_hom
    let _ : IsIso e'.hom := e'.isIso_hom
    have he : shapeBoundarySourceChange T F (Shape.cons x y s) a b ≫ e'.hom =
        e.hom ≫ (homMap F a x ⊗ₘ m) := by
      apply NatTrans.ext
      funext q
      apply ConcreteCategory.hom_ext
      intro p
      apply Prod.ext
      · rfl
      · apply Subtype.ext; rfl
    have wt : SSet.realizationWeakEquivalences (e.hom ≫ (homMap F a x ⊗ₘ m)) :=
      SSet.realizationWeakEquivalences.comp_mem _ _ (SSet.realizationWeakEquivalences.of_isIso _)
        (SSet.realizationWeakEquivalences.tensorHom _ _ (h a x) wm)
    have we' : SSet.realizationWeakEquivalences e'.hom := by
      exact @MorphismProperty.of_isIso _ _ SSet.realizationWeakEquivalences inferInstance inferInstance
        _ _ e'.hom e'.isIso_hom
    exact SSet.realizationWeakEquivalences.of_postcomp _ _ we'
      ((congrArg (fun f => SSet.realizationWeakEquivalences f) he).mpr wt)

end CategoryTheory.SimplicialEnrichment.FixedObjects.RelativeAttachment
