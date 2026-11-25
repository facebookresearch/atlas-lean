/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex
module

public import MathlibExt.AlgebraicTopology.ModelCategory.FiniteResolutionTensor
public import MathlibExt.AlgebraicTopology.ModelCategory.FramingHomotopy
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedFramings
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedReplacementConstruction
public import MathlibExt.AlgebraicTopology.ModelCategory.RightFrameHomKan

/-!
# Function-complex diagrams from the genuine original generated frames

The left, right, and two-sided simplicial Hom objects use the actual
cosimplicial Q and simplicial R frames. Their natural comparisons use
the same original frame resolutions and every original coefficient map.
Each represented vertex retains the actual original q and r arrows.
-/

section

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uC vC

open CategoryTheory Limits MorphismProperty
open scoped Simplicial

namespace HomotopicalAlgebra.GeneratedFrameHomComplex

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open GeneratedFunctorialReplacements GeneratedFramings

/-- The right function-complex bifunctor uses the same original Q and actual simplicial R frame. -/
def rightBifunctor : Cᵒᵖ ⥤ C ⥤ SSet.{vC} :=
  ResolutionHomComplex.ofFunctors (Q d ⋙ CosimplicialObject.const C) (rightFrame d)

/-- The left function-complex bifunctor uses the actual cosimplicial Q frame and same original R. -/
def leftBifunctor : Cᵒᵖ ⥤ C ⥤ SSet.{vC} :=
  ResolutionHomComplex.ofFunctors (leftFrame d) (R d ⋙ SimplicialObject.const C)

/-- The two-sided function-complex bifunctor uses both actual original generated frames. -/
def twoSidedBifunctor : Cᵒᵖ ⥤ C ⥤ SSet.{vC} :=
  ResolutionHomComplex.ofFunctors (leftFrame d) (rightFrame d)

/-- The original right function complex. -/
abbrev rightSpace (X Y : C) : SSet.{vC} := ((rightBifunctor d).obj (.op X)).obj Y

/-- The original left function complex. -/
abbrev leftSpace (X Y : C) : SSet.{vC} := ((leftBifunctor d).obj (.op X)).obj Y

/-- The original two-sided function complex. -/
abbrev twoSidedSpace (X Y : C) : SSet.{vC} := ((twoSidedBifunctor d).obj (.op X)).obj Y

/-- The right complex uses the same original Q object and actual R-frame object in every degree. -/
theorem rightSpace_eq (X Y : C) :
    rightSpace d X Y = ResolutionHomComplex.right ((Q d).obj X) ((rightFrame d).obj Y) := rfl

/-- The left complex uses the actual Q-frame and the same original R object in every degree. -/
theorem leftSpace_eq (X Y : C) :
    leftSpace d X Y = ResolutionHomComplex.left ((leftFrame d).obj X) ((R d).obj Y) := rfl

/-- The two-sided complex retains both actual original frame objects. -/
theorem twoSidedSpace_eq (X Y : C) :
    twoSidedSpace d X Y = ResolutionHomComplex.obj ((leftFrame d).obj X) ((rightFrame d).obj Y) :=
        rfl

/-- The full original left frame resolution gives the right-to-two-sided mapping comparison. -/
def rightToTwoSided : rightBifunctor d ⟶ twoSidedBifunctor d :=
  Functor.whiskerRight
    (Functor.whiskerRight (NatTrans.op (leftResolution d))
        (ResolutionHomComplex.bifunctor (C := C)))
    ((Functor.whiskeringLeft C (SimplicialObject C) SSet.{vC}).obj (rightFrame d))

/-- The full original right frame resolution gives the left-to-two-sided mapping comparison. -/
def leftToTwoSided : leftBifunctor d ⟶ twoSidedBifunctor d :=
  Functor.whiskerLeft ((leftFrame d).op ⋙ ResolutionHomComplex.bifunctor (C := C))
    ((Functor.whiskeringLeft C (SimplicialObject C) SSet.{vC}).map (rightResolution d))

/-- Every right comparison component uses the unchanged whole original left frame map. -/
theorem rightToTwoSided_app (X Y : C) :
    ((rightToTwoSided d).app (.op X)).app Y =
      ResolutionHomComplex.precomp ((leftResolution d).app X) ((rightFrame d).obj Y) := rfl

/-- Every left comparison component uses the unchanged whole original right frame map. -/
theorem leftToTwoSided_app (X Y : C) :
    ((leftToTwoSided d).app (.op X)).app Y =
      ResolutionHomComplex.postcomp ((leftFrame d).obj X) ((rightResolution d).app Y) := rfl

/-- Every original represented arrow is a right-complex vertex through the same original q and r. -/
def representedRightVertex {X Y : C} (f : X ⟶ Y) : (rightSpace d X Y).obj (.op ⦋0⦌) :=
  (counit d).app X ≫ f ≫ (unit d).app Y ≫ (rightZeroIso d).hom.app Y

/-- Every original represented arrow is a left-complex vertex through the same original q and r. -/
def representedLeftVertex {X Y : C} (f : X ⟶ Y) : (leftSpace d X Y).obj (.op ⦋0⦌) :=
  (leftZeroIso d).hom.app X ≫ (counit d).app X ≫ f ≫ (unit d).app Y

/-- The two-sided represented vertex keeps both original replacement maps and frame identifications.
-/
def representedTwoSidedVertex {X Y : C} (f : X ⟶ Y) :
    (twoSidedSpace d X Y).obj (.op ⦋0⦌) :=
  (leftZeroIso d).hom.app X ≫ (counit d).app X ≫ f ≫ (unit d).app Y ≫
    (rightZeroIso d).hom.app Y

/-- The right comparison preserves the complete original represented arrow. -/
theorem rightToTwoSided_represented {X Y : C} (f : X ⟶ Y) :
    (((rightToTwoSided d).app (.op X)).app Y).app (.op ⦋0⦌)
        (representedRightVertex d f) = representedTwoSidedVertex d f := by
  rw [rightToTwoSided_app]
  change ((leftResolution d).app X).app ⦋0⦌ ≫
      ((counit d).app X ≫ f ≫ (unit d).app Y ≫ (rightZeroIso d).hom.app Y) = _
  rw [← leftZeroIso_hom]
  rfl

/-- The left comparison preserves the complete original represented arrow. -/
theorem leftToTwoSided_represented {X Y : C} (f : X ⟶ Y) :
    (((leftToTwoSided d).app (.op X)).app Y).app (.op ⦋0⦌)
        (representedLeftVertex d f) = representedTwoSidedVertex d f := by
  rw [leftToTwoSided_app]
  change ((leftZeroIso d).hom.app X ≫ (counit d).app X ≫ f ≫ (unit d).app Y) ≫
      ((rightResolution d).app Y).app (.op ⦋0⦌) = _
  rw [← rightZeroIso_hom]
  simp only [representedTwoSidedVertex, Category.assoc]

/-- Both actual right-frame comparison maps retain every original source morphism. -/
theorem rightToTwoSided_source_naturality {X X' : C} (f : X ⟶ X') (Y : C) :
    ((rightBifunctor d).map f.op).app Y ≫ ((rightToTwoSided d).app (.op X)).app Y =
      ((rightToTwoSided d).app (.op X')).app Y ≫ ((twoSidedBifunctor d).map f.op).app Y :=
  congrArg (fun t : ((rightBifunctor d).obj (.op X')) ⟶ ((twoSidedBifunctor d).obj (.op X)) =>
      t.app Y) ((rightToTwoSided d).naturality f.op)

/-- Both actual right-frame comparison maps retain every original target morphism. -/
theorem rightToTwoSided_target_naturality (X : C) {Y Y' : C} (f : Y ⟶ Y') :
    ((rightBifunctor d).obj (.op X)).map f ≫ ((rightToTwoSided d).app (.op X)).app Y' =
      ((rightToTwoSided d).app (.op X)).app Y ≫ ((twoSidedBifunctor d).obj (.op X)).map f :=
  ((rightToTwoSided d).app (.op X)).naturality f

/-- Both actual left-frame comparison maps retain every original source morphism. -/
theorem leftToTwoSided_source_naturality {X X' : C} (f : X ⟶ X') (Y : C) :
    ((leftBifunctor d).map f.op).app Y ≫ ((leftToTwoSided d).app (.op X)).app Y =
      ((leftToTwoSided d).app (.op X')).app Y ≫ ((twoSidedBifunctor d).map f.op).app Y :=
  congrArg (fun t : ((leftBifunctor d).obj (.op X')) ⟶ ((twoSidedBifunctor d).obj (.op X)) =>
      t.app Y) ((leftToTwoSided d).naturality f.op)

/-- Both actual left-frame comparison maps retain every original target morphism. -/
theorem leftToTwoSided_target_naturality (X : C) {Y Y' : C} (f : Y ⟶ Y') :
    ((leftBifunctor d).obj (.op X)).map f ≫ ((leftToTwoSided d).app (.op X)).app Y' =
      ((leftToTwoSided d).app (.op X)).app Y ≫ ((twoSidedBifunctor d).obj (.op X)).map f :=
  ((leftToTwoSided d).app (.op X)).naturality f

end HomotopicalAlgebra.GeneratedFrameHomComplex

end
end
end

section



/-!
# The same original Q/R arrows on full localization Hom sets

Both inverse replacement functions use the actual localized original q and r.
The complete equivalence retains all original morphism naturalities in
both variables and both represented-map functions.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uC vC uH vH

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.GeneratedReplacementHomEquivalence

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)
  {H : Type uH} [Category.{vH} H] (L : C ⥤ H) [L.IsLocalization (weakEquivalences C)]

open GeneratedFunctorialReplacements

/-- The same original generated Q counit is an isomorphism under the actual localization. -/
instance counit_map_isIso (X : C) : IsIso (L.map ((counit d).app X)) :=
  Localization.inverts L (weakEquivalences C) _ (counit_weak d X)

/-- The same original generated R unit is an isomorphism under the actual localization. -/
instance unit_map_isIso (Y : C) : IsIso (L.map ((unit d).app Y)) :=
  Localization.inverts L (weakEquivalences C) _ (unit_weak d Y)

/-- The complete Hom equivalence uses both same original localized replacement arrows. -/
def homEquiv (X Y : C) : (L.obj ((Q d).obj X) ⟶ L.obj ((R d).obj Y)) ≃ (L.obj X ⟶ L.obj Y) where
  toFun f := inv (L.map ((counit d).app X)) ≫ f ≫ inv (L.map ((unit d).app Y))
  invFun f := L.map ((counit d).app X) ≫ f ≫ L.map ((unit d).app Y)
  left_inv f := by simp
  right_inv f := by simp

/-- The full forward Hom function retains both actual original mapped inverses. -/
theorem homEquiv_apply (X Y : C) (f : L.obj ((Q d).obj X) ⟶ L.obj ((R d).obj Y)) :
    homEquiv d L X Y f =
      inv (L.map ((counit d).app X)) ≫ f ≫ inv (L.map ((unit d).app Y)) := rfl

/-- The full inverse Hom function retains both actual original mapped arrows. -/
theorem homEquiv_symm_apply (X Y : C) (f : L.obj X ⟶ L.obj Y) :
    (homEquiv d L X Y).symm f = L.map ((counit d).app X) ≫ f ≫ L.map ((unit d).app Y) := rfl

/-- Every represented original morphism is recovered through the same q and r. -/
theorem homEquiv_original_map {X Y : C} (f : X ⟶ Y) :
    homEquiv d L X Y (L.map ((counit d).app X ≫ f ≫ (unit d).app Y)) = L.map f := by
  simp [homEquiv, L.map_comp]

/-- Every inverse represented original morphism keeps the same q and r. -/
theorem homEquiv_symm_original_map {X Y : C} (f : X ⟶ Y) :
    (homEquiv d L X Y).symm (L.map f) = L.map ((counit d).app X ≫ f ≫ (unit d).app Y) := by
  simp [homEquiv, L.map_comp]

/-- Naturality in every original source morphism retains the complete original Q map and inverse q.
-/
theorem homEquiv_naturality_source {X X' : C} (p : X ⟶ X') (Y : C)
    (f : L.obj ((Q d).obj X') ⟶ L.obj ((R d).obj Y)) :
    homEquiv d L X Y (L.map ((Q d).map p) ≫ f) = L.map p ≫ homEquiv d L X' Y f := by
  have hn : L.map ((Q d).map p) ≫ L.map ((counit d).app X') =
      L.map ((counit d).app X) ≫ L.map p := by
    rw [← L.map_comp, (counit d).naturality p, L.map_comp, Functor.id_map]
  have hi : inv (L.map ((counit d).app X)) ≫ L.map ((Q d).map p) =
      L.map p ≫ inv (L.map ((counit d).app X')) := by
    calc
      inv (L.map ((counit d).app X)) ≫ L.map ((Q d).map p) =
          inv (L.map ((counit d).app X)) ≫
            (L.map ((Q d).map p) ≫ L.map ((counit d).app X')) ≫
              inv (L.map ((counit d).app X')) := by simp
      _ = inv (L.map ((counit d).app X)) ≫
          (L.map ((counit d).app X) ≫ L.map p) ≫ inv (L.map ((counit d).app X')) := by rw [hn]
      _ = L.map p ≫ inv (L.map ((counit d).app X')) := by simp
  simp only [homEquiv_apply, ← Category.assoc]
  rw [hi]

/-- Naturality in every original target morphism retains the complete original R map and inverse r.
-/
theorem homEquiv_naturality_target (X : C) {Y Y' : C} (p : Y ⟶ Y')
    (f : L.obj ((Q d).obj X) ⟶ L.obj ((R d).obj Y)) :
    homEquiv d L X Y' (f ≫ L.map ((R d).map p)) = homEquiv d L X Y f ≫ L.map p := by
  have hn : L.map ((unit d).app Y) ≫ L.map ((R d).map p) =
      L.map p ≫ L.map ((unit d).app Y') := by
    rw [← L.map_comp, ← (unit d).naturality p, L.map_comp, Functor.id_map]
  have hi : L.map ((R d).map p) ≫ inv (L.map ((unit d).app Y')) =
      inv (L.map ((unit d).app Y)) ≫ L.map p := by
    calc
      L.map ((R d).map p) ≫ inv (L.map ((unit d).app Y')) =
          inv (L.map ((unit d).app Y)) ≫
            (L.map ((unit d).app Y) ≫ L.map ((R d).map p)) ≫
              inv (L.map ((unit d).app Y')) := by simp
      _ = inv (L.map ((unit d).app Y)) ≫
          (L.map p ≫ L.map ((unit d).app Y')) ≫ inv (L.map ((unit d).app Y')) := by rw [hn]
      _ = inv (L.map ((unit d).app Y)) ≫ L.map p := by simp
  simp only [homEquiv_apply, Category.assoc]
  rw [hi]

/-- The inverse full Hom function preserves every original source morphism. -/
theorem homEquiv_symm_naturality_source {X X' : C} (p : X ⟶ X') (Y : C)
    (f : L.obj X' ⟶ L.obj Y) :
    (homEquiv d L X Y).symm (L.map p ≫ f) =
      L.map ((Q d).map p) ≫ (homEquiv d L X' Y).symm f := by
  apply (homEquiv d L X Y).injective
  rw [Equiv.apply_symm_apply, homEquiv_naturality_source, Equiv.apply_symm_apply]

/-- The inverse full Hom function preserves every original target morphism. -/
theorem homEquiv_symm_naturality_target (X : C) {Y Y' : C} (p : Y ⟶ Y')
    (f : L.obj X ⟶ L.obj Y) :
    (homEquiv d L X Y').symm (f ≫ L.map p) =
      (homEquiv d L X Y).symm f ≫ L.map ((R d).map p) := by
  apply (homEquiv d L X Y').injective
  rw [Equiv.apply_symm_apply, homEquiv_naturality_target, Equiv.apply_symm_apply]

end HomotopicalAlgebra.GeneratedReplacementHomEquivalence

end
end
end

section



/-!
# Components of the actual original generated frame complexes

Both original good first-degree geometries identify the actual function-
complex components with original Q/R Hom sets. The same localized q and r
arrows give their full correspondence with the original unrestricted Hom
sets. No frame, component, or replacement equivalence is supplied as input.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uC vC uH vH

open CategoryTheory Limits MorphismProperty
open scoped Simplicial

namespace HomotopicalAlgebra.GeneratedFrameHomComplex

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open GeneratedFunctorialReplacements GeneratedFramings

/-- The same original Q supplies the source cofibrancy of every actual complex. -/
instance originalSource_isCofibrant (X : C) : IsCofibrant ((Q d).obj X) := Q_isCofibrant d X

/-- The same original R supplies the target fibrancy of every actual complex. -/
instance originalTarget_isFibrant (Y : C) : IsFibrant ((R d).obj Y) := R_isFibrant d Y

/-- The actual original left frame retraction is weak. -/
instance actualLeftProjection_weak (X : C) :
    WeakEquivalence (((leftFrame d).obj X).σ (0 : Fin 1) ≫ ((leftZeroIso d).app X).symm.inv) :=
  (weakEquivalence_iff _).mpr (leftCylinder_projection_weak d X)

/-- The actual original left frame ordered coproduct map is a cofibration. -/
instance actualLeftInclusion_cofibration (X : C) :
    Cofibration (coprod.desc
      (((leftZeroIso d).app X).symm.hom ≫ ((leftFrame d).obj X).δ (0 : Fin 2))
      (((leftZeroIso d).app X).symm.hom ≫ ((leftFrame d).obj X).δ (1 : Fin 2))) :=
  (cofibration_iff _).mpr (leftCylinder_inclusion_cofibration d X)

/-- The actual original right frame section is weak. -/
instance actualRightSection_weak (Y : C) :
    WeakEquivalence (((rightZeroIso d).app Y).hom ≫ ((rightFrame d).obj Y).σ (0 : Fin 1)) :=
  (weakEquivalence_iff _).mpr (rightPath_section_weak d Y)

/-- The actual original right frame ordered product map is a fibration. -/
instance actualRightProjection_fibration (Y : C) :
    Fibration (prod.lift
      (((rightFrame d).obj Y).δ (0 : Fin 2) ≫ ((rightZeroIso d).app Y).inv)
      (((rightFrame d).obj Y).δ (1 : Fin 2) ≫ ((rightZeroIso d).app Y).inv)) :=
  (fibration_iff _).mpr (rightPath_projection_fibration d Y)

variable {H : Type uH} [Category.{vH} H] (L : C ⥤ H) [L.IsLocalization (weakEquivalences C)]

/-- The complete component correspondence for the actual original left function complex. -/
def leftPiZeroEquiv (X Y : C) : SSet.π₀ (leftSpace d X Y) ≃ (L.obj X ⟶ L.obj Y) :=
  (ResolutionHomComplex.LeftPiZero.piZeroEquiv ((leftFrame d).obj X)
      ((leftZeroIso d).app X).symm L ((R d).obj Y)).trans
    (GeneratedReplacementHomEquivalence.homEquiv d L X Y)

/-- The complete component correspondence for the actual original right function complex. -/
def rightPiZeroEquiv (X Y : C) : SSet.π₀ (rightSpace d X Y) ≃ (L.obj X ⟶ L.obj Y) :=
  (ResolutionHomComplex.RightPiZero.piZeroEquiv ((rightFrame d).obj Y)
      ((rightZeroIso d).app Y) ((Q d).obj X) L).trans
    (GeneratedReplacementHomEquivalence.homEquiv d L X Y)

/-- Every left-complex vertex keeps both original frame identification and localized replacement
inverses. -/
theorem leftPiZeroEquiv_mk (X Y : C)
    (f : ((leftFrame d).obj X).obj ⦋0⦌ ⟶ (R d).obj Y) :
    leftPiZeroEquiv d L X Y (SSet.π₀.mk f) =
      inv (L.map ((counit d).app X)) ≫
        L.map ((leftZeroIso d).inv.app X ≫ f) ≫ inv (L.map ((unit d).app Y)) := by
  change GeneratedReplacementHomEquivalence.homEquiv d L X Y
      (ResolutionHomComplex.LeftPiZero.piZeroEquiv ((leftFrame d).obj X)
        ((leftZeroIso d).app X).symm L ((R d).obj Y) (SSet.π₀.mk f)) = _
  rw [ResolutionHomComplex.LeftPiZero.piZeroEquiv_mk,
    GeneratedReplacementHomEquivalence.homEquiv_apply]
  rfl

/-- Every right-complex vertex keeps both original frame identification and localized replacement
inverses. -/
theorem rightPiZeroEquiv_mk (X Y : C)
    (f : (Q d).obj X ⟶ ((rightFrame d).obj Y).obj (.op ⦋0⦌)) :
    rightPiZeroEquiv d L X Y (SSet.π₀.mk f) =
      inv (L.map ((counit d).app X)) ≫
        L.map (f ≫ (rightZeroIso d).inv.app Y) ≫ inv (L.map ((unit d).app Y)) := by
  change GeneratedReplacementHomEquivalence.homEquiv d L X Y
      (ResolutionHomComplex.RightPiZero.piZeroEquiv ((rightFrame d).obj Y)
        ((rightZeroIso d).app Y) ((Q d).obj X) L (SSet.π₀.mk f)) = _
  rw [ResolutionHomComplex.RightPiZero.piZeroEquiv_mk,
    GeneratedReplacementHomEquivalence.homEquiv_apply]
  rfl

/-- Every original represented arrow is mapped by the unchanged original localization function. -/
theorem leftPiZeroEquiv_original_map {X Y : C} (f : X ⟶ Y) :
    leftPiZeroEquiv d L X Y (SSet.π₀.mk (representedLeftVertex d f)) = L.map f := by
  calc
    leftPiZeroEquiv d L X Y (SSet.π₀.mk (representedLeftVertex d f)) =
        inv (L.map ((counit d).app X)) ≫
          L.map ((leftZeroIso d).inv.app X ≫ representedLeftVertex d f) ≫
            inv (L.map ((unit d).app Y)) := leftPiZeroEquiv_mk d L X Y _
    _ = L.map f := by simp [representedLeftVertex, L.map_comp]

/-- Every original represented arrow is mapped by the unchanged original localization function. -/
theorem rightPiZeroEquiv_original_map {X Y : C} (f : X ⟶ Y) :
    rightPiZeroEquiv d L X Y (SSet.π₀.mk (representedRightVertex d f)) = L.map f := by
  calc
    rightPiZeroEquiv d L X Y (SSet.π₀.mk (representedRightVertex d f)) =
        inv (L.map ((counit d).app X)) ≫
          L.map (representedRightVertex d f ≫ (rightZeroIso d).inv.app Y) ≫
            inv (L.map ((unit d).app Y)) := rightPiZeroEquiv_mk d L X Y _
    _ = L.map f := by simp [representedRightVertex, L.map_comp]

/-- The inverse left component correspondence retains every original represented morphism. -/
theorem leftPiZeroEquiv_symm_original_map {X Y : C} (f : X ⟶ Y) :
    (leftPiZeroEquiv d L X Y).symm (L.map f) = SSet.π₀.mk (representedLeftVertex d f) := by
  apply (leftPiZeroEquiv d L X Y).injective
  rw [Equiv.apply_symm_apply, leftPiZeroEquiv_original_map]

/-- The inverse right component correspondence retains every original represented morphism. -/
theorem rightPiZeroEquiv_symm_original_map {X Y : C} (f : X ⟶ Y) :
    (rightPiZeroEquiv d L X Y).symm (L.map f) = SSet.π₀.mk (representedRightVertex d f) := by
  apply (rightPiZeroEquiv d L X Y).injective
  rw [Equiv.apply_symm_apply, rightPiZeroEquiv_original_map]

set_option backward.isDefEq.respectTransparency false in
/-- The right correspondence retains every original source morphism through the same Q map. -/
theorem rightPiZeroEquiv_naturality_source {X X' : C} (f : X ⟶ X') (Y : C)
    (q : SSet.π₀ (rightSpace d X' Y)) :
    rightPiZeroEquiv d L X Y (SSet.mapπ₀ (((rightBifunctor d).map f.op).app Y) q) =
      L.map f ≫ rightPiZeroEquiv d L X' Y q := by
  change GeneratedReplacementHomEquivalence.homEquiv d L X Y
      (ResolutionHomComplex.RightPiZero.piZeroEquiv ((rightFrame d).obj Y)
        ((rightZeroIso d).app Y) ((Q d).obj X) L
        (SSet.mapπ₀ (ResolutionHomComplex.precomp
          ((CosimplicialObject.const C).map ((Q d).map f)) ((rightFrame d).obj Y)) q)) = _
  rw [ResolutionHomComplex.RightPiZero.piZeroEquiv_naturality_source,
    GeneratedReplacementHomEquivalence.homEquiv_naturality_source]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The right correspondence retains every original target morphism and actual R-frame map. -/
theorem rightPiZeroEquiv_naturality_target (X : C) {Y Y' : C} (f : Y ⟶ Y')
    (q : SSet.π₀ (rightSpace d X Y)) :
    rightPiZeroEquiv d L X Y'
        (SSet.mapπ₀ (((rightBifunctor d).obj (.op X)).map f) q) =
      rightPiZeroEquiv d L X Y q ≫ L.map f := by
  have he : ((rightZeroIso d).app Y).hom ≫ ((rightFrame d).map f).app (.op ⦋0⦌) =
      (R d).map f ≫ ((rightZeroIso d).app Y').hom :=
    ((rightZeroIso d).hom.naturality f).symm
  change GeneratedReplacementHomEquivalence.homEquiv d L X Y'
      (ResolutionHomComplex.RightPiZero.piZeroEquiv ((rightFrame d).obj Y')
        ((rightZeroIso d).app Y') ((Q d).obj X) L
        (SSet.mapπ₀ (ResolutionHomComplex.postcomp
          ((CosimplicialObject.const C).obj ((Q d).obj X)) ((rightFrame d).map f)) q)) = _
  rw [ResolutionHomComplex.RightPiZero.piZeroEquiv_naturality_target
    ((rightFrame d).obj Y) ((rightZeroIso d).app Y) ((Q d).obj X) L
    ((rightZeroIso d).app Y') ((rightFrame d).map f) ((R d).map f) he,
    GeneratedReplacementHomEquivalence.homEquiv_naturality_target]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The left correspondence retains every original source morphism and actual Q-frame map. -/
theorem leftPiZeroEquiv_naturality_source {X X' : C} (f : X ⟶ X') (Y : C)
    (q : SSet.π₀ (leftSpace d X' Y)) :
    leftPiZeroEquiv d L X Y (SSet.mapπ₀ (((leftBifunctor d).map f.op).app Y) q) =
      L.map f ≫ leftPiZeroEquiv d L X' Y q := by
  have he : ((leftZeroIso d).app X).symm.hom ≫ ((leftFrame d).map f).app ⦋0⦌ =
      (Q d).map f ≫ ((leftZeroIso d).app X').symm.hom :=
    ((leftZeroIso d).inv.naturality f).symm
  change GeneratedReplacementHomEquivalence.homEquiv d L X Y
      (ResolutionHomComplex.LeftPiZero.piZeroEquiv ((leftFrame d).obj X)
        ((leftZeroIso d).app X).symm L ((R d).obj Y)
        (SSet.mapπ₀ (ResolutionHomComplex.precomp
          ((leftFrame d).map f) ((SimplicialObject.const C).obj ((R d).obj Y))) q)) = _
  rw [ResolutionHomComplex.LeftPiZero.piZeroEquiv_naturality_source
    ((leftFrame d).obj X) ((leftZeroIso d).app X).symm L
    ((leftZeroIso d).app X').symm ((leftFrame d).map f) ((Q d).map f) he,
    GeneratedReplacementHomEquivalence.homEquiv_naturality_source]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The left correspondence retains every original target morphism through the same R map. -/
theorem leftPiZeroEquiv_naturality_target (X : C) {Y Y' : C} (f : Y ⟶ Y')
    (q : SSet.π₀ (leftSpace d X Y)) :
    leftPiZeroEquiv d L X Y'
        (SSet.mapπ₀ (((leftBifunctor d).obj (.op X)).map f) q) =
      leftPiZeroEquiv d L X Y q ≫ L.map f := by
  change GeneratedReplacementHomEquivalence.homEquiv d L X Y'
      (ResolutionHomComplex.LeftPiZero.piZeroEquiv ((leftFrame d).obj X)
        ((leftZeroIso d).app X).symm L ((R d).obj Y')
        (SSet.mapπ₀ (ResolutionHomComplex.postcomp ((leftFrame d).obj X)
          ((SimplicialObject.const C).map ((R d).map f))) q)) = _
  rw [ResolutionHomComplex.LeftPiZero.piZeroEquiv_naturality_target,
    GeneratedReplacementHomEquivalence.homEquiv_naturality_target]
  rfl

/-- The full inverse right correspondence retains the original source morphism. -/
theorem rightPiZeroEquiv_symm_naturality_source {X X' : C} (f : X ⟶ X') (Y : C)
    (q : L.obj X' ⟶ L.obj Y) :
    (rightPiZeroEquiv d L X Y).symm (L.map f ≫ q) =
      SSet.mapπ₀ (((rightBifunctor d).map f.op).app Y) ((rightPiZeroEquiv d L X' Y).symm q) := by
  apply (rightPiZeroEquiv d L X Y).injective
  rw [Equiv.apply_symm_apply, rightPiZeroEquiv_naturality_source, Equiv.apply_symm_apply]

/-- The full inverse right correspondence retains the original target morphism. -/
theorem rightPiZeroEquiv_symm_naturality_target (X : C) {Y Y' : C} (f : Y ⟶ Y')
    (q : L.obj X ⟶ L.obj Y) :
    (rightPiZeroEquiv d L X Y').symm (q ≫ L.map f) =
      SSet.mapπ₀ (((rightBifunctor d).obj (.op X)).map f) ((rightPiZeroEquiv d L X Y).symm q) := by
  apply (rightPiZeroEquiv d L X Y').injective
  rw [Equiv.apply_symm_apply, rightPiZeroEquiv_naturality_target, Equiv.apply_symm_apply]

/-- The full inverse left correspondence retains the original source morphism. -/
theorem leftPiZeroEquiv_symm_naturality_source {X X' : C} (f : X ⟶ X') (Y : C)
    (q : L.obj X' ⟶ L.obj Y) :
    (leftPiZeroEquiv d L X Y).symm (L.map f ≫ q) =
      SSet.mapπ₀ (((leftBifunctor d).map f.op).app Y) ((leftPiZeroEquiv d L X' Y).symm q) := by
  apply (leftPiZeroEquiv d L X Y).injective
  rw [Equiv.apply_symm_apply, leftPiZeroEquiv_naturality_source, Equiv.apply_symm_apply]

/-- The full inverse left correspondence retains the original target morphism. -/
theorem leftPiZeroEquiv_symm_naturality_target (X : C) {Y Y' : C} (f : Y ⟶ Y')
    (q : L.obj X ⟶ L.obj Y) :
    (leftPiZeroEquiv d L X Y').symm (q ≫ L.map f) =
      SSet.mapπ₀ (((leftBifunctor d).obj (.op X)).map f) ((leftPiZeroEquiv d L X Y).symm q) := by
  apply (leftPiZeroEquiv d L X Y').injective
  rw [Equiv.apply_symm_apply, leftPiZeroEquiv_naturality_target, Equiv.apply_symm_apply]

end HomotopicalAlgebra.GeneratedFrameHomComplex

end
end
end

section



/-!
# Kan complexes from the actual generated right frames

The source is the same original generated Q object. The simplicial target
is the actual generated right frame, with its original R degree-zero
identification and all original structure maps.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w u v

open CategoryTheory Limits Opposite Simplicial

namespace HomotopicalAlgebra.GeneratedFrameHomComplex

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open GeneratedFunctorialReplacements GeneratedFramings RightFrameHornGeometry

/-- Every original positive horn matching map of the actual generated right frame is trivial. -/
theorem rightFrame_hornMatching_trivialFibration (Y : C) (n : ℕ) (k : Fin (n + 2)) :
    trivialFibrations C (PartialFaceMatching.hornMap ((rightFrame d).obj Y) (n + 1) k) :=
  hornMatchingMap_trivialFibration ((rightFrame d).obj Y)
    (rightFrame_matching_fibration d Y) (rightFrame_map_weak d Y) n k

/-- The original generated Q and right frame give a Kan complex for every original object pair. -/
theorem rightSpace_kanComplex (X Y : C) : SSet.KanComplex (rightSpace d X Y) := by
  let _ : IsCofibrant ((Q d).obj X) := Q_isCofibrant d X
  exact right_kanComplex ((Q d).obj X) ((rightFrame d).obj Y)
    (rightFrame_matching_fibration d Y) (rightFrame_map_weak d Y)

instance rightSpace_instKanComplex (X Y : C) : SSet.KanComplex (rightSpace d X Y) :=
  rightSpace_kanComplex d X Y

/-- The original generated Q has an actual coefficient lift for every right-space horn. -/
def rightSpaceCoefficientHornFiller (X Y : C) (n : ℕ) (k : Fin (n + 2))
    (z : (SSet.horn.{v} (n + 1) k : SSet.{v}) ⟶ rightSpace d X Y) :
    (Q d).obj X ⟶ ((rightFrame d).obj Y).obj (op ⦋n + 1⦌) := by
  let _ : IsCofibrant ((Q d).obj X) := Q_isCofibrant d X
  exact coefficientHornFiller ((Q d).obj X) ((rightFrame d).obj Y)
    (rightFrame_matching_fibration d Y) (rightFrame_map_weak d Y) n k z

/-- The actual generated coefficient lift retains its entire original matching factorization. -/
theorem rightSpaceCoefficientHornFiller_fac (X Y : C) (n : ℕ) (k : Fin (n + 2))
    (z : (SSet.horn.{v} (n + 1) k : SSet.{v}) ⟶ rightSpace d X Y) :
    rightSpaceCoefficientHornFiller d X Y n k z ≫
      PartialFaceMatching.hornMap ((rightFrame d).obj Y) (n + 1) k =
        hornHomMap ((Q d).obj X) ((rightFrame d).obj Y) (n + 1) k z := by
  let _ : IsCofibrant ((Q d).obj X) := Q_isCofibrant d X
  exact coefficientHornFiller_fac ((Q d).obj X) ((rightFrame d).obj Y)
    (rightFrame_matching_fibration d Y) (rightFrame_map_weak d Y) n k z

/-- Every original proper mono face of the actual generated coefficient lift is the given horn
coordinate. -/
theorem rightSpaceCoefficientHornFiller_π (X Y : C) (n : ℕ) (k : Fin (n + 2))
    (z : (SSet.horn.{v} (n + 1) k : SSet.{v}) ⟶ rightSpace d X Y)
    (a : SimplexCategory.PartialMatching.HornIndex (n + 1) k) :
    rightSpaceCoefficientHornFiller d X Y n k z ≫
      ((rightFrame d).obj Y).map (SimplexCategory.PartialMatching.arrow a) =
        z.app (SimplexCategory.PartialMatching.target a) (hornLabel (n + 1) k a) := by
  let _ : IsCofibrant ((Q d).obj X) := Q_isCofibrant d X
  exact coefficientHornFiller_π ((Q d).obj X) ((rightFrame d).obj Y)
    (rightFrame_matching_fibration d Y) (rightFrame_map_weak d Y) n k z a

/-- The same generated coefficient lift defines the actual full standard simplex in the original
right space. -/
def rightSpaceHornFiller (X Y : C) (n : ℕ) (k : Fin (n + 2))
    (z : (SSet.horn.{v} (n + 1) k : SSet.{v}) ⟶ rightSpace d X Y) :
    (Δ[n + 1] : SSet.{v}) ⟶ rightSpace d X Y :=
  homSimplex ((Q d).obj X) ((rightFrame d).obj Y) (n + 1)
    (rightSpaceCoefficientHornFiller d X Y n k z)

/-- The actual generated coefficient lift extends the given whole native horn. -/
theorem rightSpaceHornFiller_extension (X Y : C) (n : ℕ) (k : Fin (n + 2))
    (z : (SSet.horn.{v} (n + 1) k : SSet.{v}) ⟶ rightSpace d X Y) :
    (SSet.horn.{v} (n + 1) k).ι ≫ rightSpaceHornFiller d X Y n k z = z :=
  homSimplex_horn_extension ((Q d).obj X) ((rightFrame d).obj Y) n k z
    (rightSpaceCoefficientHornFiller d X Y n k z)
    (rightSpaceCoefficientHornFiller_fac d X Y n k z)

/-- Every original positive horn in the actual right space has an original simplex extension. -/
theorem rightSpace_hornFilling (X Y : C) (n : ℕ) (k : Fin (n + 2))
    (z : (SSet.horn.{v} (n + 1) k : SSet.{v}) ⟶ rightSpace d X Y) :
    ∃ σ : (Δ[n + 1] : SSet.{v}) ⟶ rightSpace d X Y,
      z = (SSet.horn.{v} (n + 1) k).ι ≫ σ :=
  ⟨rightSpaceHornFiller d X Y n k z, (rightSpaceHornFiller_extension d X Y n k z).symm⟩

end HomotopicalAlgebra.GeneratedFrameHomComplex

end
end
end
