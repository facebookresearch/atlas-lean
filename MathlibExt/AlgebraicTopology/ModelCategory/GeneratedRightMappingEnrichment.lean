/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex

module

public import Mathlib.AlgebraicTopology.SimplicialCategory.SimplicialObject
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import MathlibExt.AlgebraicTopology.ModelCategory.FiniteResolutionTensor
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedFrameHomComplex
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedFramings
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyMappingSpaceCategory
public import MathlibExt.AlgebraicTopology.ModelCategory.ResolutionMappingWeakPreservation
public import MathlibExt.AlgebraicTopology.SimplicialSet.ConnectedComponents.Products
public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizationWeakPiZero
public import MathlibExt.CategoryTheory.Enriched.HomTransport
public import MathlibExt.CategoryTheory.Enriched.Ordinary.Basic

/-!
# Canonical composition on the actual generated simplicial frames

The structured simplicial Hom of the genuine bifibrant frames has the canonical
simplicial-object enrichment. Localizing this actual enrichment gives its coherent
composition in the monoidal localization of simplicial sets. Both variable maps
are induced by the unchanged original Q and right-frame functors.

The comparison of these objects with the left and right function complexes, and
the homotopical properties of those comparisons, are proved separately.
-/

section

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uC vC

open CategoryTheory MonoidalCategory
open scoped MonoidalCategory

namespace HomotopicalAlgebra.CanonicalGeneratedFrameEnrichment

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open GeneratedFramings HomotopyMappingSpaceCategory

/-- The complete canonical simplicial Hom bifunctor on the actual generated bifibrant frames. -/
def nativeBifunctor : Cᵒᵖ ⥤ C ⥤ SSet.{vC} :=
  (bifibrantFrame d).op ⋙ SimplicialCategory.sHomFunctor (SimplicialObject C) ⋙
    (Functor.whiskeringLeft C (SimplicialObject C) SSet.{vC}).obj (bifibrantFrame d)

/-- The original structured simplicial Hom between the actual generated frame objects. -/
abbrev nativeSpace (X Y : C) : SSet.{vC} := ((nativeBifunctor d).obj (.op X)).obj Y

/-- Each native object is the same canonical Hom of the actual original generated frames. -/
theorem nativeSpace_eq (X Y : C) : nativeSpace d X Y =
    SimplicialCategory.sHom ((bifibrantFrame d).obj X) ((bifibrantFrame d).obj Y) := rfl

/-- Every original source morphism acts through the complete original frame functor. -/
def nativePrecomp {X Y : C} (f : X ⟶ Y) (Z : C) : nativeSpace d Y Z ⟶ nativeSpace d X Z :=
  ((nativeBifunctor d).map f.op).app Z

/-- Every original target morphism acts through the complete original frame functor. -/
def nativePostcomp (X : C) {Y Z : C} (f : Y ⟶ Z) : nativeSpace d X Y ⟶ nativeSpace d X Z :=
  ((nativeBifunctor d).obj (.op X)).map f

/-- The source action is actual canonical precomposition by the original right-frame image of Q. -/
theorem nativePrecomp_eq {X Y : C} (f : X ⟶ Y) (Z : C) :
    nativePrecomp d f Z =
      eHomWhiskerRight SSet ((rightFrame d).map ((GeneratedFunctorialReplacements.Q d).map f))
        ((bifibrantFrame d).obj Z) := rfl

/-- The target action is actual canonical postcomposition by the original right-frame image of Q. -/
theorem nativePostcomp_eq (X : C) {Y Z : C} (f : Y ⟶ Z) :
    nativePostcomp d X f =
      eHomWhiskerLeft SSet ((bifibrantFrame d).obj X)
        ((rightFrame d).map ((GeneratedFunctorialReplacements.Q d).map f)) := rfl

/-- The original canonical enrichment supplies composition on the genuine frame presentation. -/
def nativeComp (X Y Z : C) : nativeSpace d X Y ⊗ nativeSpace d Y Z ⟶ nativeSpace d X Z :=
  eComp SSet ((bifibrantFrame d).obj X) ((bifibrantFrame d).obj Y) ((bifibrantFrame d).obj Z)

/-- The original canonical enrichment supplies the identity on each genuine frame object. -/
def nativeUnit (X : C) : 𝟙_ SSet.{vC} ⟶ nativeSpace d X X :=
  eId SSet ((bifibrantFrame d).obj X)

/-- Actual canonical enrichment on the frame presentation, retaining all original frame objects. -/
@[instance_reducible]
def nativeEnrichment : EnrichedCategory SSet.{vC} C where
  Hom := nativeSpace d
  id := nativeUnit d
  comp := nativeComp d
  id_comp X Y := e_id_comp SSet ((bifibrantFrame d).obj X) ((bifibrantFrame d).obj Y)
  comp_id X Y := e_comp_id SSet ((bifibrantFrame d).obj X) ((bifibrantFrame d).obj Y)
  assoc W X Y Z :=
    e_assoc SSet ((bifibrantFrame d).obj W) ((bifibrantFrame d).obj X)
      ((bifibrantFrame d).obj Y) ((bifibrantFrame d).obj Z)

/-- Each original source map commutes with the same canonical composition. -/
theorem nativeComp_naturality_source {X X' : C} (f : X ⟶ X') (Y Z : C) :
    nativeComp d X' Y Z ≫ nativePrecomp d f Z =
      nativePrecomp d f Y ▷ nativeSpace d Y Z ≫ nativeComp d X Y Z :=
  eComp_eHomWhiskerRight SSet ((bifibrantFrame d).map f)
    ((bifibrantFrame d).obj Y) ((bifibrantFrame d).obj Z)

/-- Each original target map commutes with the same canonical composition. -/
theorem nativeComp_naturality_target (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    nativeComp d X Y Z ≫ nativePostcomp d X f =
      nativeSpace d X Y ◁ nativePostcomp d Y f ≫ nativeComp d X Y Z' :=
  eComp_eHomWhiskerLeft SSet ((bifibrantFrame d).obj X)
    ((bifibrantFrame d).obj Y) ((bifibrantFrame d).map f)

/-- The same original middle morphism may be composed in either adjoining Hom object. -/
theorem nativeComp_naturality_middle (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    nativePostcomp d X f ▷ nativeSpace d Y' Z ≫ nativeComp d X Y' Z =
      nativeSpace d X Y ◁ nativePrecomp d f Z ≫ nativeComp d X Y Z := by
  ext n ⟨x, y⟩
  apply Functor.functorHom_ext
  intro k g
  change (x.app k g ≫ ((bifibrantFrame d).map f).app k) ≫ y.app k g =
    x.app k g ≫ (((bifibrantFrame d).map f).app k ≫ y.app k g)
  exact Category.assoc _ _ _

/-- The same canonical unit preserves every original input morphism. -/
theorem nativeUnit_naturality {X Y : C} (f : X ⟶ Y) :
    nativeUnit d X ≫ nativePostcomp d X f = nativeUnit d Y ≫ nativePrecomp d f Y := by
  change eId SSet ((bifibrantFrame d).obj X) ≫
      eHomWhiskerLeft SSet ((bifibrantFrame d).obj X) ((bifibrantFrame d).map f) =
    eId SSet ((bifibrantFrame d).obj Y) ≫
      eHomWhiskerRight SSet ((bifibrantFrame d).map f) ((bifibrantFrame d).obj Y)
  rw [eId_comp_eHomWhiskerLeft SSet (SimplicialObject C),
    eId_comp_eHomWhiskerRight SSet (SimplicialObject C)]

/-- The coherent bifunctor is the actual localization of every canonical frame Hom and map. -/
def coherentBifunctor : Cᵒᵖ ⥤ C ⥤ SpaceHo.{vC} :=
  nativeBifunctor d ⋙ (Functor.whiskeringRight C SSet.{vC} SpaceHo.{vC}).obj localize

/-- The coherent mapping object is the same localized original structured frame Hom. -/
abbrev coherentSpace (X Y : C) : SpaceHo.{vC} := ((coherentBifunctor d).obj (.op X)).obj Y

/-- Each coherent mapping object retains the original native mapping object. -/
theorem coherentSpace_eq (X Y : C) : coherentSpace d X Y = localize.obj (nativeSpace d X Y) := rfl

/-- The coherent source action retains the localization of every original frame source map. -/
def coherentPrecomp {X Y : C} (f : X ⟶ Y) (Z : C) :
    coherentSpace d Y Z ⟶ coherentSpace d X Z := ((coherentBifunctor d).map f.op).app Z

/-- The coherent target action retains the localization of every original frame target map. -/
def coherentPostcomp (X : C) {Y Z : C} (f : Y ⟶ Z) :
    coherentSpace d X Y ⟶ coherentSpace d X Z := ((coherentBifunctor d).obj (.op X)).map f

/-- The coherent source function is the same localized original native source function. -/
theorem coherentPrecomp_eq {X Y : C} (f : X ⟶ Y) (Z : C) :
    coherentPrecomp d f Z = localize.map (nativePrecomp d f Z) := rfl

/-- The coherent target function is the same localized original native target function. -/
theorem coherentPostcomp_eq (X : C) {Y Z : C} (f : Y ⟶ Z) :
    coherentPostcomp d X f = localize.map (nativePostcomp d X f) := rfl

/-- Coherent composition uses the actual tensor comparison and original canonical composition. -/
def coherentComp (X Y Z : C) :
    coherentSpace d X Y ⊗ coherentSpace d Y Z ⟶ coherentSpace d X Z :=
  (tensorComparison (nativeSpace d X Y) (nativeSpace d Y Z)).hom ≫ localize.map (nativeComp d X Y Z)

/-- The coherent unit uses the actual monoidal localization unit map and original canonical
identity. -/
def coherentUnit (X : C) : 𝟙_ SpaceHo.{vC} ⟶ coherentSpace d X X :=
  Functor.LaxMonoidal.ε localize ≫ localize.map (nativeUnit d X)

/-- The coherent enrichment is constructed by localizing the actual canonical frame enrichment. -/
@[instance_reducible]
def coherentEnrichment : EnrichedCategory SpaceHo.{vC} C := by
  let _ : EnrichedCategory SSet.{vC} C := nativeEnrichment d
  exact inferInstanceAs (EnrichedCategory SpaceHo.{vC} (TransportEnrichment localize C))

/-- The genuine transported enrichment has the same complete original mapping objects. -/
theorem coherentEnrichment_Hom (X Y : C) : (coherentEnrichment d).Hom X Y = coherentSpace d X Y :=
  rfl

/-- The genuine transported enrichment has the same actual localized unit. -/
theorem coherentEnrichment_id (X : C) : (coherentEnrichment d).id X = coherentUnit d X := rfl

/-- The genuine transported enrichment has the same actual localized composition. -/
theorem coherentEnrichment_comp (X Y Z : C) :
    (coherentEnrichment d).comp X Y Z = coherentComp d X Y Z := rfl

/-- The coherent left unit law retains the actual localized unitor and original frame identity. -/
theorem coherentComp_leftUnit (X Y : C) :
    (λ_ (coherentSpace d X Y)).inv ≫ coherentUnit d X ▷ _ ≫ coherentComp d X X Y =
      𝟙 (coherentSpace d X Y) := (coherentEnrichment d).id_comp X Y

/-- The coherent right unit law retains the actual localized unitor and original frame identity. -/
theorem coherentComp_rightUnit (X Y : C) :
    (ρ_ (coherentSpace d X Y)).inv ≫ _ ◁ coherentUnit d Y ≫ coherentComp d X Y Y =
      𝟙 (coherentSpace d X Y) := (coherentEnrichment d).comp_id X Y

/-- Coherent associativity retains the actual localized associator and all original mapping objects.
-/
theorem coherentComp_assoc (W X Y Z : C) :
    (α_ (coherentSpace d W X) (coherentSpace d X Y) (coherentSpace d Y Z)).inv ≫
        coherentComp d W X Y ▷ _ ≫ coherentComp d W Y Z =
      _ ◁ coherentComp d X Y Z ≫ coherentComp d W X Z :=
  (coherentEnrichment d).assoc W X Y Z

/-- Every original source map commutes with the coherent localized composition. -/
theorem coherentComp_naturality_source {X X' : C} (f : X ⟶ X') (Y Z : C) :
    coherentComp d X' Y Z ≫ coherentPrecomp d f Z =
      coherentPrecomp d f Y ▷ coherentSpace d Y Z ≫ coherentComp d X Y Z := by
  change ((tensorComparison (nativeSpace d X' Y) (nativeSpace d Y Z)).hom ≫
      localize.map (nativeComp d X' Y Z)) ≫ localize.map (nativePrecomp d f Z) =
    localize.map (nativePrecomp d f Y) ▷ localize.obj (nativeSpace d Y Z) ≫
      ((tensorComparison (nativeSpace d X Y) (nativeSpace d Y Z)).hom ≫
        localize.map (nativeComp d X Y Z))
  rw [Category.assoc, ← localize.map_comp, nativeComp_naturality_source, localize.map_comp,
    ← Category.assoc, ← tensorComparison_naturality_left]
  exact Category.assoc _ _ _

/-- Every original target map commutes with the coherent localized composition. -/
theorem coherentComp_naturality_target (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    coherentComp d X Y Z ≫ coherentPostcomp d X f =
      coherentSpace d X Y ◁ coherentPostcomp d Y f ≫ coherentComp d X Y Z' := by
  change ((tensorComparison (nativeSpace d X Y) (nativeSpace d Y Z)).hom ≫
      localize.map (nativeComp d X Y Z)) ≫ localize.map (nativePostcomp d X f) =
    localize.obj (nativeSpace d X Y) ◁ localize.map (nativePostcomp d Y f) ≫
      ((tensorComparison (nativeSpace d X Y) (nativeSpace d Y Z')).hom ≫
        localize.map (nativeComp d X Y Z'))
  rw [Category.assoc, ← localize.map_comp, nativeComp_naturality_target, localize.map_comp,
    ← Category.assoc, ← tensorComparison_naturality_right]
  exact Category.assoc _ _ _

/-- The same original middle morphism retains both coherent composition functions. -/
theorem coherentComp_naturality_middle (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    coherentPostcomp d X f ▷ coherentSpace d Y' Z ≫ coherentComp d X Y' Z =
      coherentSpace d X Y ◁ coherentPrecomp d f Z ≫ coherentComp d X Y Z := by
  change localize.map (nativePostcomp d X f) ▷ localize.obj (nativeSpace d Y' Z) ≫
      ((tensorComparison (nativeSpace d X Y') (nativeSpace d Y' Z)).hom ≫
        localize.map (nativeComp d X Y' Z)) =
    localize.obj (nativeSpace d X Y) ◁ localize.map (nativePrecomp d f Z) ≫
      ((tensorComparison (nativeSpace d X Y) (nativeSpace d Y Z)).hom ≫
        localize.map (nativeComp d X Y Z))
  rw [← Category.assoc, tensorComparison_naturality_left, Category.assoc, ← localize.map_comp,
    nativeComp_naturality_middle, localize.map_comp,
    ← Category.assoc, ← tensorComparison_naturality_right]
  exact Category.assoc _ _ _

/-- Every original input morphism retains the coherent localized unit square. -/
theorem coherentUnit_naturality {X Y : C} (f : X ⟶ Y) :
    coherentUnit d X ≫ coherentPostcomp d X f = coherentUnit d Y ≫ coherentPrecomp d f Y := by
  change (Functor.LaxMonoidal.ε localize ≫ localize.map (nativeUnit d X)) ≫
      localize.map (nativePostcomp d X f) =
    (Functor.LaxMonoidal.ε localize ≫ localize.map (nativeUnit d Y)) ≫
      localize.map (nativePrecomp d f Y)
  rw [Category.assoc, Category.assoc, ← localize.map_comp, ← localize.map_comp,
      nativeUnit_naturality]

end HomotopicalAlgebra.CanonicalGeneratedFrameEnrichment

end
end
end

section



/-!
# The original comparison from canonical frame Hom to the right function complex

The actual bifibrant-frame Hom compares to the original right function complex by
postcomposition with the right-frame image of the original Q counit, followed by
precomposition with the original constant-Q frame comparison. The represented-Hom
isomorphism then returns the original degreewise Q-to-right-frame map. All source,
target, and simplex maps remain the same original maps.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uC vC

open CategoryTheory
open scoped Simplicial MonoidalCategory

namespace HomotopicalAlgebra.GeneratedFrameEnrichmentComparison

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open GeneratedFunctorialReplacements GeneratedFramings
open CanonicalGeneratedFrameEnrichment GeneratedFrameHomComplex

/-- The unchanged original right-frame image of the whole original Q counit. -/
def rightFrameProjection : bifibrantFrame d ⟶ rightFrame d :=
  Functor.whiskerRight (counit d) (rightFrame d) ≫ (rightFrame d).leftUnitor.hom

/-- Every projection is the same original whole right-frame image of q. -/
theorem rightFrameProjection_app (Y : C) :
    (rightFrameProjection d).app Y = (rightFrame d).map ((counit d).app Y) := by
  change _ ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- Every degree of the original projection is weak by the actual right-frame coefficient law. -/
theorem rightFrameProjection_weak (Y : C) (j : SimplexCategoryᵒᵖ) :
    weakEquivalences C (((rightFrameProjection d).app Y).app j) := by
  rw [rightFrameProjection_app]
  exact rightFrame_coefficient_weak d ((counit d).app Y) (counit_weak d Y) j

/-- The canonical comparison bifunctor uses the same constant Q and original right frame. -/
def canonicalRightBifunctor : Cᵒᵖ ⥤ C ⥤ SSet.{vC} :=
  (Q d ⋙ SimplicialObject.const C).op ⋙ SimplicialCategory.sHomFunctor (SimplicialObject C) ⋙
    (Functor.whiskeringLeft C (SimplicialObject C) SSet.{vC}).obj (rightFrame d)

/-- The complete original right complex is naturally the represented canonical constant-source Hom.
-/
def rightCanonicalIso : rightBifunctor d ≅ canonicalRightBifunctor d :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (Q d).op
        (ResolutionHomComplex.CanonicalEnrichment.rightBifunctorIso (C := C)))
    ((Functor.whiskeringLeft C (SimplicialObject C) SSet.{vC}).obj (rightFrame d))

/-- Every component is the same complete original represented-Hom isomorphism. -/
theorem rightCanonicalIso_app (X Y : C) :
    ((rightCanonicalIso d).app (.op X)).app Y =
      ResolutionHomComplex.CanonicalEnrichment.rightIso ((Q d).obj X) ((rightFrame d).obj Y) := rfl

/-- The original projection and constant-Q comparison give a complete natural mapping comparison. -/
def nativeToCanonicalRight : nativeBifunctor d ⟶ canonicalRightBifunctor d :=
  Functor.whiskerLeft
      ((bifibrantFrame d).op ⋙ SimplicialCategory.sHomFunctor (SimplicialObject C))
      ((Functor.whiskeringLeft C (SimplicialObject C) SSet.{vC}).map (rightFrameProjection d)) ≫
    Functor.whiskerRight
      (Functor.whiskerRight (NatTrans.op (bifibrantFromQ d))
        (SimplicialCategory.sHomFunctor (SimplicialObject C)))
      ((Functor.whiskeringLeft C (SimplicialObject C) SSet.{vC}).obj (rightFrame d))

/-- The full comparison to the original right complex retains both original frame arrows. -/
def nativeToRight : nativeBifunctor d ⟶ rightBifunctor d :=
  nativeToCanonicalRight d ≫ (rightCanonicalIso d).inv

/-- Each actual comparison is postcomposition by the original projection and precomposition from Q.
-/
theorem nativeToRight_app (X Y : C) :
    ((nativeToRight d).app (.op X)).app Y =
      eHomWhiskerLeft SSet ((bifibrantFrame d).obj X) ((rightFrameProjection d).app Y) ≫
        eHomWhiskerRight SSet ((bifibrantFromQ d).app X) ((rightFrame d).obj Y) ≫
          (ResolutionHomComplex.CanonicalEnrichment.rightIso
            ((Q d).obj X) ((rightFrame d).obj Y)).inv := by
  change (_ ≫ _) ≫ _ = _
  exact Category.assoc _ _ _

/-- Every original source morphism preserves the complete native-to-right comparison square. -/
theorem nativeToRight_naturality_source {X X' : C} (f : X ⟶ X') (Y : C) :
    ((nativeBifunctor d).map f.op).app Y ≫ ((nativeToRight d).app (.op X)).app Y =
      ((nativeToRight d).app (.op X')).app Y ≫ ((rightBifunctor d).map f.op).app Y :=
  congrArg (fun t => t.app Y) ((nativeToRight d).naturality f.op)

/-- Every original target morphism preserves the complete native-to-right comparison square. -/
theorem nativeToRight_naturality_target (X : C) {Y Y' : C} (f : Y ⟶ Y') :
    ((nativeBifunctor d).obj (.op X)).map f ≫ ((nativeToRight d).app (.op X)).app Y' =
      ((nativeToRight d).app (.op X)).app Y ≫ ((rightBifunctor d).obj (.op X)).map f :=
  ((nativeToRight d).app (.op X)).naturality f

/-- Every original simplex coordinate retains the entire original Q-frame inclusion and q image. -/
theorem nativeToRight_simplex (X Y : C) (n : SimplexCategoryᵒᵖ)
    (x : (nativeSpace d X Y).obj n) :
    (((nativeToRight d).app (.op X)).app Y).app n x =
      ((bifibrantFromQ d).app X).app n ≫ x.app n (𝟙 n) ≫
        ((rightFrame d).map ((counit d).app Y)).app n := by
  rw [nativeToRight_app]
  change ((bifibrantFromQ d).app X).app n ≫
      (x.app n (𝟙 n) ≫ ((rightFrameProjection d).app Y).app n) = _
  rw [rightFrameProjection_app]

/-- The original zero-degree frame comparison retains the complete q/r word. -/
theorem bifibrantFromQ_projection_zero (X : C) :
    ((bifibrantFromQ d).app X).app (.op ⦋0⦌) ≫
        ((rightFrame d).map ((counit d).app X)).app (.op ⦋0⦌) =
      (counit d).app X ≫ (unit d).app X ≫ (rightZeroIso d).hom.app X := by
  rw [bifibrantFromQ_app, ← rightZeroIso_hom]
  let a : (Q d).obj X ⟶ (R d).obj ((Q d).obj X) := (unit d).app ((Q d).obj X)
  let z : (R d).obj ((Q d).obj X) ⟶ ((rightFrame d).obj ((Q d).obj X)).obj (.op ⦋0⦌) :=
    (rightZeroIso d).hom.app ((Q d).obj X)
  let b : ((rightFrame d).obj ((Q d).obj X)).obj (.op ⦋0⦌) ⟶ ((rightFrame d).obj X).obj (.op ⦋0⦌) :=
    ((rightFrame d).map ((counit d).app X)).app (.op ⦋0⦌)
  let c : (R d).obj ((Q d).obj X) ⟶ (R d).obj X := (R d).map ((counit d).app X)
  let v : X ⟶ (R d).obj X := (unit d).app X
  let z' : (R d).obj X ⟶ ((rightFrame d).obj X).obj (.op ⦋0⦌) := (rightZeroIso d).hom.app X
  have hz : z ≫ b = c ≫ z' := ((rightZeroIso d).hom.naturality ((counit d).app X)).symm
  have hu : a ≫ c = (counit d).app X ≫ v := ((unit d).naturality ((counit d).app X)).symm
  change (a ≫ z) ≫ b = (counit d).app X ≫ v ≫ z'
  rw [Category.assoc, hz, ← Category.assoc, hu, Category.assoc]

/-- Every original morphism is represented by its whole original bifibrant-frame natural map. -/
def nativePoint {X Y : C} (f : X ⟶ Y) : 𝟙_ SSet.{vC} ⟶ nativeSpace d X Y :=
  eHomEquiv SSet ((bifibrantFrame d).map f)

/-- Every original composite retains the actual canonical simplicial composition on frame points. -/
theorem nativePoint_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    nativePoint d (f ≫ g) = (λ_ (𝟙_ SSet.{vC})).inv ≫
      (nativePoint d f ⊗ₘ nativePoint d g) ≫ nativeComp d X Y Z := by
  change eHomEquiv SSet ((bifibrantFrame d).map (f ≫ g)) =
    (λ_ (𝟙_ SSet.{vC})).inv ≫
      (eHomEquiv SSet ((bifibrantFrame d).map f) ⊗ₘ eHomEquiv SSet ((bifibrantFrame d).map g)) ≫
        eComp SSet ((bifibrantFrame d).obj X) ((bifibrantFrame d).obj Y) ((bifibrantFrame d).obj Z)
  rw [(bifibrantFrame d).map_comp, eHomEquiv_comp]

/-- Every original represented point returns the same original q/f/r vertex under the comparison. -/
theorem nativeToRight_point_zero {X Y : C} (f : X ⟶ Y)
    (t : (𝟙_ SSet.{vC}).obj (.op ⦋0⦌)) :
    (((nativePoint d f ≫ ((nativeToRight d).app (.op X)).app Y).app (.op ⦋0⦌)) t) =
      representedRightVertex d f := by
  change (((nativeToRight d).app (.op X)).app Y).app (.op ⦋0⦌)
      ((nativePoint d f).app (.op ⦋0⦌) t) = _
  rw [nativeToRight_simplex]
  let a : (Q d).obj X ⟶ ((rightFrame d).obj ((Q d).obj X)).obj (.op ⦋0⦌) :=
    ((bifibrantFromQ d).app X).app (.op ⦋0⦌)
  let a' : (Q d).obj Y ⟶ ((rightFrame d).obj ((Q d).obj Y)).obj (.op ⦋0⦌) :=
    ((bifibrantFromQ d).app Y).app (.op ⦋0⦌)
  let b : ((rightFrame d).obj ((Q d).obj X)).obj (.op ⦋0⦌) ⟶
      ((rightFrame d).obj ((Q d).obj Y)).obj (.op ⦋0⦌) := ((bifibrantFrame d).map f).app (.op ⦋0⦌)
  let c : ((rightFrame d).obj ((Q d).obj Y)).obj (.op ⦋0⦌) ⟶ ((rightFrame d).obj Y).obj (.op ⦋0⦌) :=
    ((rightFrame d).map ((counit d).app Y)).app (.op ⦋0⦌)
  let v : Y ⟶ (R d).obj Y := (unit d).app Y
  let z : (R d).obj Y ⟶ ((rightFrame d).obj Y).obj (.op ⦋0⦌) := (rightZeroIso d).hom.app Y
  have h : a ≫ b = (Q d).map f ≫ a' :=
    (congrArg (fun t => t.app (.op ⦋0⦌)) ((bifibrantFromQ d).naturality f)).symm
  have hz : a' ≫ c = (counit d).app Y ≫ v ≫ z := bifibrantFromQ_projection_zero d Y
  have hq : (Q d).map f ≫ (counit d).app Y = (counit d).app X ≫ f := (counit d).naturality f
  change a ≫ b ≫ c = (counit d).app X ≫ f ≫ v ≫ z
  rw [← Category.assoc, h, Category.assoc, hz, ← Category.assoc, hq, Category.assoc]

/-- Every canonical frame identity maps to the same actual original represented q/r vertex. -/
theorem nativeToRight_unit_zero (X : C) (t : (𝟙_ SSet.{vC}).obj (.op ⦋0⦌)) :
    (((nativeUnit d X ≫ ((nativeToRight d).app (.op X)).app X).app (.op ⦋0⦌)) t) =
      representedRightVertex d (𝟙 X) := by
  change (((nativeToRight d).app (.op X)).app X).app (.op ⦋0⦌)
      ((nativeUnit d X).app (.op ⦋0⦌) t) = _
  rw [nativeToRight_simplex, bifibrantFromQ_app]
  change ((unit d).app ((Q d).obj X) ≫
      ((rightResolution d).app ((Q d).obj X)).app (.op ⦋0⦌)) ≫
    (𝟙 (((rightFrame d).obj ((Q d).obj X)).obj (.op ⦋0⦌)) ≫
      ((rightFrame d).map ((counit d).app X)).app (.op ⦋0⦌)) =
    (counit d).app X ≫ 𝟙 X ≫ (unit d).app X ≫ (rightZeroIso d).hom.app X
  rw [Category.id_comp, ← rightZeroIso_hom]
  have h : (rightZeroIso d).hom.app ((Q d).obj X) ≫
      ((rightFrame d).map ((counit d).app X)).app (.op ⦋0⦌) =
    (R d).map ((counit d).app X) ≫ (rightZeroIso d).hom.app X :=
      ((rightZeroIso d).hom.naturality ((counit d).app X)).symm
  rw [Category.assoc, h, ← Category.assoc, ← (unit d).naturality ((counit d).app X)]
  change ((counit d).app X ≫ (unit d).app X) ≫ (rightZeroIso d).hom.app X =
    (counit d).app X ≫ 𝟙 X ≫ (unit d).app X ≫ (rightZeroIso d).hom.app X
  rw [Category.assoc]
  exact congrArg (fun m : X ⟶ ((rightFrame d).obj X).obj (.op ⦋0⦌) => (counit d).app X ≫ m)
    (Category.id_comp ((unit d).app X ≫ (rightZeroIso d).hom.app X)).symm

end HomotopicalAlgebra.GeneratedFrameEnrichmentComparison

end
end
end

section



/-!
# Entire represented maps and units in the original right function complex

The represented point uses the whole original constant-Q map followed by the
same original R coaugmentation. Its every simplex coordinate is the original
q/f/r word and the actual right resolution map. The canonical frame comparison
preserves these entire simplicial maps and their natural unit squares.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uC vC

open CategoryTheory
open scoped Simplicial MonoidalCategory

namespace HomotopicalAlgebra.GeneratedFrameEnrichmentComparison

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open GeneratedFunctorialReplacements GeneratedFramings
open GeneratedFrameHomComplex CanonicalGeneratedFrameEnrichment

/-- The whole original constant-Q frame map followed by its projection is the original q
coaugmentation. -/
theorem bifibrantFromQ_projection (X : C) :
    (bifibrantFromQ d).app X ≫ (rightFrameProjection d).app X =
      (SimplicialObject.const C).map ((counit d).app X) ≫ (coaugmentation d).app X := by
  rw [rightFrameProjection_app]
  exact ((coaugmentation d).naturality ((counit d).app X)).symm

/-- Every original bifibrant-frame morphism preserves the whole q coaugmentation word. -/
theorem bifibrantFromQ_map_projection {X Y : C} (f : X ⟶ Y) :
    (bifibrantFromQ d).app X ≫ (bifibrantFrame d).map f ≫ (rightFrameProjection d).app Y =
      (SimplicialObject.const C).map ((counit d).app X ≫ f) ≫ (coaugmentation d).app Y := by
  have h : (bifibrantFromQ d).app X ≫ (bifibrantFrame d).map f =
      (SimplicialObject.const C).map ((Q d).map f) ≫ (bifibrantFromQ d).app Y :=
    ((bifibrantFromQ d).naturality f).symm
  rw [← Category.assoc, h, Category.assoc, bifibrantFromQ_projection,
    ← Category.assoc, ← Functor.map_comp, (counit d).naturality f]
  rfl

/-- The entire original represented right-complex point uses q, the input map, r, and the same
frame. -/
def rightPoint {X Y : C} (f : X ⟶ Y) : 𝟙_ SSet.{vC} ⟶ rightSpace d X Y :=
  eHomEquiv SSet ((SimplicialObject.const C).map ((counit d).app X ≫ f) ≫ (coaugmentation d).app Y)
      ≫
    (ResolutionHomComplex.CanonicalEnrichment.rightIso ((Q d).obj X) ((rightFrame d).obj Y)).inv

/-- Every simplex of the represented point retains the full original q/f/r/resolution word. -/
theorem rightPoint_simplex {X Y : C} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ)
    (t : (𝟙_ SSet.{vC}).obj n) :
    (rightPoint d f).app n t = (counit d).app X ≫ f ≫ (unit d).app Y ≫
      ((rightResolution d).app Y).app n := by
  change (((SimplicialObject.const C).map ((counit d).app X ≫ f)) ≫ (coaugmentation d).app Y).app n
      = _
  rw [NatTrans.comp_app, coaugmentation_app]
  change ((counit d).app X ≫ f) ≫ ((unit d).app Y ≫ ((rightResolution d).app Y).app n) = _
  exact Category.assoc _ _ _

/-- The entire canonical represented frame point maps to the same entire original right point. -/
theorem nativePoint_comparison {X Y : C} (f : X ⟶ Y) :
    nativePoint d f ≫ ((nativeToRight d).app (.op X)).app Y = rightPoint d f := by
  rw [nativeToRight_app]
  change eHomEquiv SSet ((bifibrantFrame d).map f) ≫
      (eHomWhiskerLeft SSet ((bifibrantFrame d).obj X) ((rightFrameProjection d).app Y) ≫
        eHomWhiskerRight SSet ((bifibrantFromQ d).app X) ((rightFrame d).obj Y) ≫
          (ResolutionHomComplex.CanonicalEnrichment.rightIso
            ((Q d).obj X) ((rightFrame d).obj Y)).inv) = _
  rw [← Category.assoc, ← Category.assoc,
    eHomEquiv_comp_eHomWhiskerLeft SSet (SimplicialObject C),
    eHomEquiv_comp_eHomWhiskerRight SSet (SimplicialObject C), bifibrantFromQ_map_projection]
  rfl

/-- The whole original right-complex unit is the represented original identity map. -/
abbrev rightUnit (X : C) : 𝟙_ SSet.{vC} ⟶ rightSpace d X X := rightPoint d (𝟙 X)

/-- The complete canonical identity comparison gives the complete original right-complex unit. -/
theorem nativeUnit_comparison (X : C) :
    nativeUnit d X ≫ ((nativeToRight d).app (.op X)).app X = rightUnit d X := by
  have h : nativePoint d (𝟙 X) = nativeUnit d X := by
    change eHomEquiv SSet ((bifibrantFrame d).map (𝟙 X)) = eId SSet ((bifibrantFrame d).obj X)
    rw [(bifibrantFrame d).map_id, eHomEquiv_id]
  rw [← h]
  exact nativePoint_comparison d (𝟙 X)

/-- The whole original unit retains its degree-zero q/r identification. -/
theorem rightUnit_zero (X : C) (t : (𝟙_ SSet.{vC}).obj (.op ⦋0⦌)) :
    (rightUnit d X).app (.op ⦋0⦌) t = representedRightVertex d (𝟙 X) := by
  rw [← nativeUnit_comparison]
  exact nativeToRight_unit_zero d X t

/-- Every original morphism preserves the whole original right-complex unit square. -/
theorem rightUnit_naturality {X Y : C} (f : X ⟶ Y) :
    rightUnit d X ≫ ((rightBifunctor d).obj (.op X)).map f =
      rightUnit d Y ≫ ((rightBifunctor d).map f.op).app Y := by
  have h : nativeUnit d X ≫ ((nativeBifunctor d).obj (.op X)).map f =
      nativeUnit d Y ≫ ((nativeBifunctor d).map f.op).app Y := nativeUnit_naturality d f
  rw [← nativeUnit_comparison, ← nativeUnit_comparison, Category.assoc,
    ← nativeToRight_naturality_target, ← Category.assoc, h, Category.assoc,
    nativeToRight_naturality_source, ← Category.assoc]

end HomotopicalAlgebra.GeneratedFrameEnrichmentComparison

end
end
end

section



/-!
# Genuine weak comparisons and invariance of the original generated function complexes

The actual constant-Q frame map is a Reedy trivial cofibration. The original
right-frame image of q is weak between genuine fibrant frames. The proved
mapping lifting laws and Brown factorizations therefore make the entire original
canonical-to-right comparison weak, retaining both original Q/R arrows.
All original source and target weak maps act weakly on the same full bifunctors.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uC vC

open CategoryTheory
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.GeneratedFrameEnrichmentComparison

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open GeneratedFramingModels GeneratedFramings GeneratedFunctorialReplacements
open CanonicalGeneratedFrameEnrichment GeneratedFrameHomComplex

/-- The entire original right-frame projection is weak in the same genuine simplicial model. -/
theorem rightFrameProjection_model_weak (Y : C) :
    letI := simplicialModel d
    WeakEquivalence ((rightFrameProjection d).app Y) := by
  let _ := simplicialModel d
  rw [rightFrameProjection_app]
  exact rightFrame_model_weak d d ((counit d).app Y) (counit_weak d Y)

/-- The same complete original canonical-to-right function-complex map is a weak equivalence. -/
theorem nativeToRight_weak (X Y : C) :
    WeakEquivalence (((nativeToRight d).app (.op X)).app Y) := by
  let _ := simplicialModel d
  let f₁ : SimplicialCategory.sHom ((bifibrantFrame d).obj X) ((bifibrantFrame d).obj Y) ⟶
      SimplicialCategory.sHom ((bifibrantFrame d).obj X) ((rightFrame d).obj Y) :=
    eHomWhiskerLeft SSet ((bifibrantFrame d).obj X) ((rightFrameProjection d).app Y)
  let f₂ : SimplicialCategory.sHom ((bifibrantFrame d).obj X) ((rightFrame d).obj Y) ⟶
      SimplicialCategory.sHom ((SimplicialObject.const C).obj ((Q d).obj X))
          ((rightFrame d).obj Y) :=
    eHomWhiskerRight SSet ((bifibrantFromQ d).app X) ((rightFrame d).obj Y)
  let f₃ : SimplicialCategory.sHom ((SimplicialObject.const C).obj ((Q d).obj X))
      ((rightFrame d).obj Y) ⟶
      ResolutionHomComplex.right ((Q d).obj X) ((rightFrame d).obj Y) :=
    (ResolutionHomComplex.CanonicalEnrichment.rightIso ((Q d).obj X) ((rightFrame d).obj Y)).inv
  let _ : WeakEquivalence f₁ :=
    ResolutionMappingWeakPreservation.postcomp_weak d ((bifibrantFrame d).obj X)
      ((rightFrameProjection d).app Y) (bifibrantFrame_isCofibrant d d X)
      (rightFrameProjection_model_weak d Y) (bifibrantFrame_isFibrant d d Y)
          (rightFrame_isFibrant d d Y)
  let _ : WeakEquivalence f₂ :=
    (weakEquivalence_iff _).mpr
      (ResolutionMappingWeakPreservation.precomp_trivial d ((bifibrantFromQ d).app X)
        ((rightFrame d).obj Y) (bifibrantFromQ_model_trivialCofibration d d X)
        (rightFrame_isFibrant d d Y)).2
  let _ : WeakEquivalence f₃ :=
    inferInstanceAs (WeakEquivalence
      (ResolutionHomComplex.CanonicalEnrichment.rightIso ((Q d).obj X) ((rightFrame d).obj Y)).inv)
  rw [nativeToRight_app]
  change WeakEquivalence (f₁ ≫ f₂ ≫ f₃)
  infer_instance

/-- Every original weak source map acts weakly on the actual canonical frame Hom bifunctor. -/
theorem native_source_weak {X X' : C} (f : X ⟶ X') (hf : weakEquivalences C f) (Y : C) :
    WeakEquivalence (((nativeBifunctor d).map f.op).app Y) := by
  let _ := simplicialModel d
  exact ResolutionMappingWeakPreservation.precomp_weak d ((bifibrantFrame d).map f)
    ((bifibrantFrame d).obj Y) (bifibrantFrame_model_weak d d f hf)
    (bifibrantFrame_isCofibrant d d X) (bifibrantFrame_isCofibrant d d X')
        (bifibrantFrame_isFibrant d d Y)

/-- Every original weak target map acts weakly on the actual canonical frame Hom bifunctor. -/
theorem native_target_weak (X : C) {Y Y' : C} (f : Y ⟶ Y') (hf : weakEquivalences C f) :
    WeakEquivalence (((nativeBifunctor d).obj (.op X)).map f) := by
  let _ := simplicialModel d
  exact ResolutionMappingWeakPreservation.postcomp_weak d ((bifibrantFrame d).obj X)
    ((bifibrantFrame d).map f) (bifibrantFrame_isCofibrant d d X)
    (bifibrantFrame_model_weak d d f hf) (bifibrantFrame_isFibrant d d Y)
        (bifibrantFrame_isFibrant d d Y')

/-- Every original weak source map acts weakly on the unchanged original Q/right-frame complex. -/
theorem right_source_weak {X X' : C} (f : X ⟶ X') (hf : weakEquivalences C f) (Y : C) :
    WeakEquivalence (((rightBifunctor d).map f.op).app Y) := by
  let _ := native_source_weak d f hf Y
  let _ := nativeToRight_weak d X Y
  let _ := nativeToRight_weak d X' Y
  exact weakEquivalence_of_precomp_of_fac (nativeToRight_naturality_source d f Y).symm

/-- Every original weak target map acts weakly on the unchanged original Q/right-frame complex. -/
theorem right_target_weak (X : C) {Y Y' : C} (f : Y ⟶ Y') (hf : weakEquivalences C f) :
    WeakEquivalence (((rightBifunctor d).obj (.op X)).map f) := by
  let _ := native_target_weak d X f hf
  let _ := nativeToRight_weak d X Y
  let _ := nativeToRight_weak d X Y'
  exact weakEquivalence_of_precomp_of_fac (nativeToRight_naturality_target d X f).symm

end HomotopicalAlgebra.GeneratedFrameEnrichmentComparison

end
end
end

section



/-!
# Coherent composition on the actual original right function-complex objects

The proved original weak comparison becomes a genuine natural isomorphism in
the actual monoidal localization of simplicial sets. Transporting the already
constructed canonical frame enrichment along these actual isomorphisms supplies
coherent composition and units on the same original Q/right-frame spaces.
The complete unit is the localization of the original q/r represented unit.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uC vC

open CategoryTheory MonoidalCategory
open scoped MonoidalCategory SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.GeneratedRightMappingEnrichment

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open HomotopyMappingSpaceCategory CanonicalGeneratedFrameEnrichment
open GeneratedFrameHomComplex GeneratedFrameEnrichmentComparison

/-- The full actual original right mapping bifunctor with the same monoidal localization on every
map. -/
def bifunctor : Cᵒᵖ ⥤ C ⥤ SpaceHo.{vC} :=
  rightBifunctor d ⋙ (Functor.whiskeringRight C SSet.{vC} SpaceHo.{vC}).obj localize

/-- The coherent mapping object is precisely the original right function complex under the same
localization. -/
abbrev space (X Y : C) : SpaceHo.{vC} := ((bifunctor d).obj (.op X)).obj Y

/-- Every coherent right object retains the same actual original Q/right-frame complex. -/
theorem space_eq (X Y : C) : space d X Y = localize.obj (rightSpace d X Y) := rfl

/-- The actual original weak comparison supplies its genuine localized Hom isomorphism. -/
instance comparison_map_isIso (X Y : C) :
    IsIso (localize.map (((nativeToRight d).app (.op X)).app Y)) := by
  have h : SSet.realizationWeakEquivalences (((nativeToRight d).app (.op X)).app Y) := by
    change weakEquivalences SSet.{vC} (((nativeToRight d).app (.op X)).app Y)
    exact (weakEquivalence_iff _).mp (nativeToRight_weak d X Y)
  exact localize_isIso _ h

/-- The same actual localized original comparison gives the complete Hom isomorphism. -/
def comparisonIso (X Y : C) : coherentSpace d X Y ≅ space d X Y :=
  @asIso SpaceHo.{vC} _ (localize.obj (nativeSpace d X Y)) (localize.obj (rightSpace d X Y))
    (localize.map (((nativeToRight d).app (.op X)).app Y)) (comparison_map_isIso d X Y)

/-- The entire forward Hom isomorphism is the localization of the same original full comparison. -/
theorem comparisonIso_hom (X Y : C) :
    (comparisonIso d X Y).hom = localize.map (((nativeToRight d).app (.op X)).app Y) := rfl

/-- The entire inverse Hom isomorphism is the inverse of that same original localized comparison. -/
theorem comparisonIso_inv (X Y : C) :
    (comparisonIso d X Y).inv =
      @inv SpaceHo.{vC} _ (localize.obj (nativeSpace d X Y)) (localize.obj (rightSpace d X Y))
        (localize.map (((nativeToRight d).app (.op X)).app Y)) (comparison_map_isIso d X Y) := rfl

/-- Every original coefficient source and target map is retained in a complete natural Hom
isomorphism. -/
def comparisonBifunctorIso : coherentBifunctor d ≅ bifunctor d :=
  NatIso.ofComponents
    (fun X => NatIso.ofComponents (fun Y => comparisonIso d X.unop Y) (by
      intro Y Y' f
      change localize.map (((nativeBifunctor d).obj X).map f) ≫
          localize.map (((nativeToRight d).app X).app Y') =
        localize.map (((nativeToRight d).app X).app Y) ≫
            localize.map (((rightBifunctor d).obj X).map f)
      rw [← localize.map_comp, ← localize.map_comp]
      exact congrArg localize.map (nativeToRight_naturality_target d X.unop f))) (by
    intro X X' f
    apply NatTrans.ext
    funext Y
    change localize.map (((nativeBifunctor d).map f).app Y) ≫
        localize.map (((nativeToRight d).app X').app Y) =
      localize.map (((nativeToRight d).app X).app Y) ≫
          localize.map (((rightBifunctor d).map f).app Y)
    rw [← localize.map_comp, ← localize.map_comp]
    exact congrArg localize.map (nativeToRight_naturality_source d f.unop Y))

/-- Every component of the full bifunctor comparison is the same actual original localized
comparison. -/
theorem comparisonBifunctorIso_app (X Y : C) :
    ((comparisonBifunctorIso d).app (.op X)).app Y = comparisonIso d X Y := rfl

/-- The actual original right-complex objects receive the genuinely constructed coherent enrichment.
-/
@[instance_reducible]
def enrichment : EnrichedCategory SpaceHo.{vC} C := by
  let _ : EnrichedCategory SpaceHo.{vC} C := coherentEnrichment d
  exact EnrichedHomTransport.enrichedCategoryOnOriginalObjects (space d) (comparisonIso d)

/-- The transported composition keeps both complete actual inverse comparisons and the original
composition. -/
def comp (X Y Z : C) : space d X Y ⊗ space d Y Z ⟶ space d X Z :=
  (enrichment d).comp X Y Z

/-- The transported unit keeps the original canonical unit and the same full actual comparison. -/
def unit (X : C) : 𝟙_ SpaceHo.{vC} ⟶ space d X X := (enrichment d).id X

/-- The complete actual composition uses the original inverse Hom maps and canonical composition. -/
theorem comp_formula (X Y Z : C) : comp d X Y Z =
    ((comparisonIso d X Y).inv ⊗ₘ (comparisonIso d Y Z).inv) ≫
      coherentComp d X Y Z ≫ (comparisonIso d X Z).hom := rfl

/-- The complete actual unit uses the original canonical identity and forward Hom map. -/
theorem unit_formula (X : C) : unit d X = coherentUnit d X ≫ (comparisonIso d X X).hom := rfl

/-- The genuine transported enrichment has exactly the same original right mapping objects. -/
theorem enrichment_hom (X Y : C) : (enrichment d).Hom X Y = space d X Y := rfl

/-- The genuine transported identity is the same entire actual unit formula. -/
theorem enrichment_id (X : C) : (enrichment d).id X = unit d X := rfl

/-- The genuine transported composition is the same entire actual composition formula. -/
theorem enrichment_comp (X Y Z : C) : (enrichment d).comp X Y Z = comp d X Y Z := rfl

/-- The original right-complex unit is the localization of the complete original q/r represented
unit. -/
theorem unit_calculation (X : C) :
    unit d X = Functor.LaxMonoidal.ε localize ≫ localize.map (rightUnit d X) := by
  rw [unit_formula]
  change (Functor.LaxMonoidal.ε localize ≫ localize.map (nativeUnit d X)) ≫
      localize.map (((nativeToRight d).app (.op X)).app X) = _
  rw [Category.assoc, ← localize.map_comp, nativeUnit_comparison]

/-- The exact original right mapping objects satisfy the coherent left unit law. -/
theorem comp_leftUnit (X Y : C) :
    (λ_ (space d X Y)).inv ≫ unit d X ▷ _ ≫ comp d X X Y = 𝟙 (space d X Y) :=
  (enrichment d).id_comp X Y

/-- The exact original right mapping objects satisfy the coherent right unit law. -/
theorem comp_rightUnit (X Y : C) :
    (ρ_ (space d X Y)).inv ≫ _ ◁ unit d Y ≫ comp d X Y Y = 𝟙 (space d X Y) :=
  (enrichment d).comp_id X Y

/-- The exact original right mapping objects retain the actual monoidal associator in full
coherence. -/
theorem comp_assoc (W X Y Z : C) :
    (α_ (space d W X) (space d X Y) (space d Y Z)).inv ≫ comp d W X Y ▷ _ ≫ comp d W Y Z =
      _ ◁ comp d X Y Z ≫ comp d W X Z := (enrichment d).assoc W X Y Z

/-- Every complete original Hom is recovered by the same inverse comparison after the unit. -/
theorem unit_inverse_readback (X : C) : unit d X ≫ (comparisonIso d X X).inv =
    coherentUnit d X := by
  simp only [unit_formula, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Every complete original composition is recovered with both actual inverse input maps. -/
theorem comp_inverse_readback (X Y Z : C) :
    comp d X Y Z ≫ (comparisonIso d X Z).inv =
      ((comparisonIso d X Y).inv ⊗ₘ (comparisonIso d Y Z).inv) ≫ coherentComp d X Y Z := by
  simp only [comp_formula, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Both complete forward comparisons preserve the entire original coherent composition. -/
theorem comp_forward_readback (X Y Z : C) :
    ((comparisonIso d X Y).hom ⊗ₘ (comparisonIso d Y Z).hom) ≫ comp d X Y Z =
      coherentComp d X Y Z ≫ (comparisonIso d X Z).hom := by
  rw [comp_formula, ← Category.assoc, tensorHom_comp_tensorHom, Iso.hom_inv_id, Iso.hom_inv_id,
    id_tensorHom_id, Category.id_comp]

end HomotopicalAlgebra.GeneratedRightMappingEnrichment

end
end
end

section



/-!
# Original represented maps in the coherent right mapping enrichment

The original frame point passes through the same monoidal localization and
actual native-to-right comparison. The entire represented original composite
uses the constructed coherent composition, independently of the Hom-set
correspondence. Its component and identity readbacks use the unchanged
original localization Hom functions.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uC vC uH vH

open CategoryTheory MonoidalCategory
open scoped Simplicial MonoidalCategory SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.HomotopyMappingSpaceCategory

/-- The actual component functor inverts every original realization weak equivalence. -/
theorem componentsInverts : SSet.realizationWeakEquivalences.{vC}.IsInvertedBy SSet.π₀Functor := by
  intro X Y f hf
  rw [isIso_iff_bijective]
  exact SSet.realizationWeakEquivalences.bijective_mapπ₀ hf

/-- The component functor on the same actual localization of simplicial sets. -/
def components : SpaceHo.{vC} ⥤ Type vC :=
  Localization.lift SSet.π₀Functor componentsInverts localize

/-- The same localization factorization retains every original simplicial component map. -/
def componentsComparison : localize.{vC} ⋙ components ≅ SSet.π₀Functor :=
  Localization.fac SSet.π₀Functor componentsInverts localize

/-- The complete chosen factorization is the actual localization lifting. -/
instance componentsLifting :
    Localization.Lifting localize SSet.realizationWeakEquivalences SSet.π₀Functor components :=
  ⟨componentsComparison⟩

/-- Every localized original simplicial set has its actual original component type. -/
def componentsIso (K : SSet.{vC}) : components.obj (localize.obj K) ≅ SSet.π₀ K :=
  (componentsComparison.app K)

/-- The component functor receives its monoidal structure through the actual monoidal localization.
-/
instance componentsMonoidal : components.{vC}.Monoidal :=
  Localization.Monoidal.functorMonoidalOfComp localize SSet.realizationWeakEquivalences components
      SSet.π₀Functor

/-- The complete original component comparison is a monoidal natural transformation. -/
instance componentsComparison_isMonoidal : componentsComparison.{vC}.hom.IsMonoidal :=
  Localization.Monoidal.lifting_isMonoidal localize SSet.realizationWeakEquivalences components
      SSet.π₀Functor

/-- Both complete forward component maps retain every original simplicial morphism. -/
theorem componentsIso_naturality {K L : SSet.{vC}} (f : K ⟶ L) :
    components.map (localize.map f) ≫ (componentsIso L).hom =
      (componentsIso K).hom ≫ SSet.π₀Functor.map f :=
  componentsComparison.hom.naturality f

/-- Both complete inverse component maps retain every original simplicial morphism. -/
theorem componentsIso_inverse_naturality {K L : SSet.{vC}} (f : K ⟶ L) :
    SSet.π₀Functor.map f ≫ (componentsIso L).inv =
      (componentsIso K).inv ≫ components.map (localize.map f) :=
  componentsComparison.inv.naturality f

set_option backward.isDefEq.respectTransparency false in
/-- The entire localized tensor comparison is the same original Cartesian component pairing. -/
theorem componentsIso_tensor (K L : SSet.{vC}) :
    Functor.LaxMonoidal.μ components (localize.obj K) (localize.obj L) ≫
      components.map (tensorComparison K L).hom ≫ (componentsIso (K ⊗ L)).hom =
    ((componentsIso K).hom ⊗ₘ (componentsIso L).hom) ≫
        Functor.LaxMonoidal.μ SSet.π₀Functor K L := by
  change Functor.LaxMonoidal.μ components (localize.obj K) (localize.obj L) ≫
      components.map (Functor.LaxMonoidal.μ localize K L) ≫ componentsComparison.hom.app (K ⊗ L) =
    (componentsComparison.hom.app K ⊗ₘ componentsComparison.hom.app L) ≫
      Functor.LaxMonoidal.μ SSet.π₀Functor K L
  simpa only [Functor.LaxMonoidal.comp_μ, Category.assoc] using
    (NatTrans.IsMonoidal.tensor (τ := componentsComparison.hom) K L)

set_option backward.isDefEq.respectTransparency false in
/-- The entire localized component unit uses the same original monoidal unit comparison. -/
theorem componentsIso_unit :
    Functor.LaxMonoidal.ε components.{vC} ≫ components.map (Functor.LaxMonoidal.ε localize) ≫
      (componentsIso (𝟙_ SSet.{vC})).hom = Functor.LaxMonoidal.ε SSet.π₀Functor := by
  change Functor.LaxMonoidal.ε components ≫ components.map (Functor.LaxMonoidal.ε localize) ≫
      componentsComparison.hom.app (𝟙_ SSet) = Functor.LaxMonoidal.ε SSet.π₀Functor
  simpa only [Functor.LaxMonoidal.comp_ε, Category.assoc] using
    (NatTrans.IsMonoidal.unit (τ := componentsComparison.hom))

set_option backward.isDefEq.respectTransparency false in
/-- The actual monoidal component pairing is the original inverse Cartesian component equivalence.
-/
theorem piZeroFunctor_tensor (K L : SSet.{vC}) (q : SSet.π₀ K × SSet.π₀ L) :
    Functor.LaxMonoidal.μ SSet.π₀Functor K L q = (SSet.piZeroTensorEquiv K L).symm q := by
  apply (SSet.piZeroTensorEquiv K L).injective
  rw [Equiv.apply_symm_apply]
  have h := congrArg (fun k => k q) (Functor.Monoidal.μ_δ SSet.π₀Functor K L)
  have hδ : Functor.OplaxMonoidal.δ SSet.π₀Functor K L =
      (SSet.piZeroTensorEquiv K L).toIso.hom := by
    rw [Functor.OplaxMonoidal.δ_of_cartesianMonoidalCategory]
    apply ConcreteCategory.hom_ext
    intro c
    change (SSet.mapπ₀ (CartesianMonoidalCategory.fst K L) c,
      SSet.mapπ₀ (CartesianMonoidalCategory.snd K L) c) = SSet.piZeroTensorEquiv K L c
    change SSet.π₀ (K ⊗ L) at c
    exact (SSet.piZeroTensorEquiv_apply K L c).symm
  rw [hδ] at h
  exact h

end HomotopicalAlgebra.HomotopyMappingSpaceCategory

namespace HomotopicalAlgebra.GeneratedMappingHomComposition

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open HomotopyMappingSpaceCategory CanonicalGeneratedFrameEnrichment
open GeneratedFrameHomComplex GeneratedFrameEnrichmentComparison

/-- The original represented right point under the same monoidal localization. -/
def point {X Y : C} (f : X ⟶ Y) : 𝟙_ SpaceHo.{vC} ⟶ GeneratedRightMappingEnrichment.space d X Y :=
  Functor.LaxMonoidal.ε localize ≫ localize.map (rightPoint d f)

/-- The canonical represented point under the same monoidal localization. -/
def canonicalPoint {X Y : C} (f : X ⟶ Y) : 𝟙_ SpaceHo.{vC} ⟶ coherentSpace d X Y :=
  Functor.LaxMonoidal.ε localize ≫ localize.map (nativePoint d f)

set_option backward.isDefEq.respectTransparency false in
/-- The entire canonical point maps to the entire original right point. -/
theorem canonicalPoint_comparison {X Y : C} (f : X ⟶ Y) :
    canonicalPoint d f ≫ (GeneratedRightMappingEnrichment.comparisonIso d X Y).hom = point d f := by
  rw [canonicalPoint, point, GeneratedRightMappingEnrichment.comparisonIso_hom,
    Category.assoc, ← localize.map_comp, nativePoint_comparison]

/-- The whole canonical composite point uses the actual localized native composition. -/
theorem canonicalPoint_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    canonicalPoint d (f ≫ g) = (λ_ (𝟙_ SpaceHo.{vC})).inv ≫
      (canonicalPoint d f ⊗ₘ canonicalPoint d g) ≫ coherentComp d X Y Z := by
  change Functor.LaxMonoidal.ε localize ≫ localize.map (nativePoint d (f ≫ g)) =
    (λ_ (𝟙_ SpaceHo.{vC})).inv ≫
      ((Functor.LaxMonoidal.ε localize ≫ localize.map (nativePoint d f)) ⊗ₘ
        (Functor.LaxMonoidal.ε localize ≫ localize.map (nativePoint d g))) ≫
      Functor.LaxMonoidal.μ localize _ _ ≫ localize.map (nativeComp d X Y Z)
  rw [← tensorHom_comp_tensorHom_assoc, tensorHom_def_assoc,
    whiskerRight_id_assoc, unitors_inv_equal, Iso.inv_hom_id_assoc,
    Functor.LaxMonoidal.μ_natural_assoc, Functor.LaxMonoidal.right_unitality_inv_assoc,
    nativePoint_comp, ← localize.map_comp, ← localize.map_comp, unitors_inv_equal]

set_option backward.isDefEq.respectTransparency false in
/-- The whole original composite uses the actual coherent right mapping composition. -/
theorem point_comp {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    point d (f ≫ g) = (λ_ (𝟙_ SpaceHo.{vC})).inv ≫
      (point d f ⊗ₘ point d g) ≫ GeneratedRightMappingEnrichment.comp d X Y Z := by
  rw [← canonicalPoint_comparison d (f ≫ g), ← canonicalPoint_comparison d f,
    ← canonicalPoint_comparison d g, canonicalPoint_comp]
  rw [← tensorHom_comp_tensorHom]
  simp only [Category.assoc]
  rw [GeneratedRightMappingEnrichment.comp_forward_readback]

/-- The entire original identity point is the constructed coherent unit. -/
theorem point_id (X : C) : point d (𝟙 X) = GeneratedRightMappingEnrichment.unit d X :=
  (GeneratedRightMappingEnrichment.unit_calculation d X).symm

/-- The complete original weak comparison induces its actual component equivalence. -/
def componentComparison (X Y : C) : SSet.π₀ (nativeSpace d X Y) ≃ SSet.π₀ (rightSpace d X Y) :=
  Equiv.ofBijective (SSet.mapπ₀ (((nativeToRight d).app (.op X)).app Y))
    (SSet.realizationWeakEquivalences.bijective_mapπ₀
      ((weakEquivalence_iff _).mp (nativeToRight_weak d X Y)))

/-- The native component composition uses the original Cartesian pair and original native
composition. -/
def nativeComponentComp (X Y Z : C) (f : SSet.π₀ (nativeSpace d X Y))
    (g : SSet.π₀ (nativeSpace d Y Z)) : SSet.π₀ (nativeSpace d X Z) :=
  SSet.mapπ₀ (nativeComp d X Y Z)
    ((SSet.piZeroTensorEquiv (nativeSpace d X Y) (nativeSpace d Y Z)).symm (f, g))

/-- The right component composition uses both actual inverse weak comparisons and the same native
composition. -/
def componentComp (X Y Z : C) (f : SSet.π₀ (rightSpace d X Y))
    (g : SSet.π₀ (rightSpace d Y Z)) : SSet.π₀ (rightSpace d X Z) :=
  componentComparison d X Z (nativeComponentComp d X Y Z
    ((componentComparison d X Y).symm f) ((componentComparison d Y Z).symm g))

/-- The literal operation obtained by applying the descended component functor to the actual
Ho-composition. -/
def localizedCompositionMap (X Y Z : C) :
    SSet.π₀ (rightSpace d X Y) ⊗ SSet.π₀ (rightSpace d Y Z) ⟶ SSet.π₀ (rightSpace d X Z) :=
  ((componentsIso (rightSpace d X Y)).inv ⊗ₘ (componentsIso (rightSpace d Y Z)).inv) ≫
    Functor.LaxMonoidal.μ components (GeneratedRightMappingEnrichment.space d X Y)
      (GeneratedRightMappingEnrichment.space d Y Z) ≫
      components.map (GeneratedRightMappingEnrichment.comp d X Y Z) ≫
        (componentsIso (rightSpace d X Z)).hom

/-- The actual localized composition applied to the same pair of arbitrary original components. -/
def localizedComponentComp (X Y Z : C) (f : SSet.π₀ (rightSpace d X Y))
    (g : SSet.π₀ (rightSpace d Y Z)) : SSet.π₀ (rightSpace d X Z) :=
  localizedCompositionMap d X Y Z (f, g)

/-- The literal component unit is obtained by applying the descended functor to the actual coherent
unit. -/
def localizedUnitMap (X : C) : 𝟙_ (Type vC) ⟶ SSet.π₀ (rightSpace d X X) :=
  Functor.LaxMonoidal.ε components ≫ components.map (GeneratedRightMappingEnrichment.unit d X) ≫
    (componentsIso (rightSpace d X X)).hom

set_option backward.isDefEq.respectTransparency false in
/-- The literal localized component unit is the original represented q/r identity component. -/
theorem localizedUnitMap_eq (X : C) :
    localizedUnitMap d X = (↾fun _ => SSet.π₀.mk (representedRightVertex d (𝟙 X))) := by
  unfold localizedUnitMap
  rw [GeneratedRightMappingEnrichment.unit_calculation, components.map_comp]
  simp only [Category.assoc]
  rw [componentsIso_naturality]
  have hu := congrArg (fun h => h ≫ SSet.π₀Functor.map (rightUnit d X))
    componentsIso_unit.{vC}
  simp only [Category.assoc] at hu
  rw [hu]
  apply ConcreteCategory.hom_ext
  intro t
  have hε : Functor.LaxMonoidal.ε SSet.π₀Functor t =
      SSet.π₀.mk (PUnit.unit : (𝟙_ SSet.{vC}).obj (.op ⦋0⦌)) := by
    obtain ⟨v, hv⟩ := SSet.π₀.mk_surjective (Functor.LaxMonoidal.ε SSet.π₀Functor t)
    have hv₀ : v = (PUnit.unit : (𝟙_ SSet.{vC}).obj (.op ⦋0⦌)) := by
      exact Subsingleton.elim (α := PUnit.{vC + 1}) v PUnit.unit
    exact hv.symm.trans (congrArg SSet.π₀.mk hv₀)
  change SSet.mapπ₀ (rightUnit d X) (Functor.LaxMonoidal.ε SSet.π₀Functor t) = _
  rw [hε, SSet.mapπ₀_mk, rightUnit_zero]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The actual coherent native composition retains the whole original component pairing and native
map. -/
theorem components_coherentComp (X Y Z : C) :
    Functor.LaxMonoidal.μ components (coherentSpace d X Y) (coherentSpace d Y Z) ≫
      components.map (coherentComp d X Y Z) ≫ (componentsIso (nativeSpace d X Z)).hom =
    ((componentsIso (nativeSpace d X Y)).hom ⊗ₘ (componentsIso (nativeSpace d Y Z)).hom) ≫
      Functor.LaxMonoidal.μ SSet.π₀Functor (nativeSpace d X Y) (nativeSpace d Y Z) ≫
        SSet.π₀Functor.map (nativeComp d X Y Z) := by
  change Functor.LaxMonoidal.μ components (localize.obj (nativeSpace d X Y))
      (localize.obj (nativeSpace d Y Z)) ≫ components.map (coherentComp d X Y Z) ≫
      (componentsIso (nativeSpace d X Z)).hom = _
  rw [coherentComp, components.map_comp]
  simp only [Category.assoc]
  rw [componentsIso_naturality]
  have h := congrArg (fun t => t ≫ SSet.π₀Functor.map (nativeComp d X Y Z))
    (componentsIso_tensor (nativeSpace d X Y) (nativeSpace d Y Z))
  simpa only [Category.assoc] using h

/-- The component map of the actual coherent native composition, with the whole original
comparisons. -/
def localizedNativeCompositionMap (X Y Z : C) :
    SSet.π₀ (nativeSpace d X Y) ⊗ SSet.π₀ (nativeSpace d Y Z) ⟶ SSet.π₀ (nativeSpace d X Z) :=
  ((componentsIso (nativeSpace d X Y)).inv ⊗ₘ (componentsIso (nativeSpace d Y Z)).inv) ≫
    Functor.LaxMonoidal.μ components (coherentSpace d X Y) (coherentSpace d Y Z) ≫
      components.map (coherentComp d X Y Z) ≫ (componentsIso (nativeSpace d X Z)).hom

set_option backward.isDefEq.respectTransparency false in
/-- Applying the actual localized component functor gives the same original native component
composition map. -/
theorem localizedNativeCompositionMap_eq (X Y Z : C) :
    localizedNativeCompositionMap d X Y Z =
      Functor.LaxMonoidal.μ SSet.π₀Functor (nativeSpace d X Y) (nativeSpace d Y Z) ≫
        SSet.π₀Functor.map (nativeComp d X Y Z) := by
  have h := congrArg (fun t =>
      ((componentsIso (nativeSpace d X Y)).inv ⊗ₘ (componentsIso (nativeSpace d Y Z)).inv) ≫ t)
    (components_coherentComp d X Y Z)
  simp only [tensorHom_comp_tensorHom_assoc, Iso.inv_hom_id,
    id_tensorHom_id, Category.id_comp] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- Both whole original weak comparison maps preserve the literal localized component composition.
-/
theorem localizedCompositionMap_comparison (X Y Z : C) :
    (SSet.π₀Functor.map (((nativeToRight d).app (.op X)).app Y) ⊗ₘ
      SSet.π₀Functor.map (((nativeToRight d).app (.op Y)).app Z)) ≫
      localizedCompositionMap d X Y Z =
    localizedNativeCompositionMap d X Y Z ≫
      SSet.π₀Functor.map (((nativeToRight d).app (.op X)).app Z) := by
  have hXY : SSet.π₀Functor.map (((nativeToRight d).app (.op X)).app Y) ≫
      (componentsIso (rightSpace d X Y)).inv =
    (componentsIso (nativeSpace d X Y)).inv ≫
      components.map (GeneratedRightMappingEnrichment.comparisonIso d X Y).hom := by
    rw [GeneratedRightMappingEnrichment.comparisonIso_hom]
    exact componentsIso_inverse_naturality (((nativeToRight d).app (.op X)).app Y)
  have hYZ : SSet.π₀Functor.map (((nativeToRight d).app (.op Y)).app Z) ≫
      (componentsIso (rightSpace d Y Z)).inv =
    (componentsIso (nativeSpace d Y Z)).inv ≫
      components.map (GeneratedRightMappingEnrichment.comparisonIso d Y Z).hom := by
    rw [GeneratedRightMappingEnrichment.comparisonIso_hom]
    exact componentsIso_inverse_naturality (((nativeToRight d).app (.op Y)).app Z)
  unfold localizedCompositionMap localizedNativeCompositionMap
  simp only [Category.assoc]
  rw [tensorHom_comp_tensorHom_assoc, hXY, hYZ, ← tensorHom_comp_tensorHom_assoc,
    Functor.LaxMonoidal.μ_natural_assoc, ← components.map_comp_assoc,
    GeneratedRightMappingEnrichment.comp_forward_readback, components.map_comp,
    GeneratedRightMappingEnrichment.comparisonIso_hom]
  simp only [Category.assoc]
  rw [componentsIso_naturality]
  rfl

set_option backward.isDefEq.respectTransparency false in
/--
The literal Ho-composition on every pair is the same native-composition transport through actual
weak
comparisons.
-/
theorem localizedComponentComp_eq (X Y Z : C) (f : SSet.π₀ (rightSpace d X Y))
    (g : SSet.π₀ (rightSpace d Y Z)) :
    localizedComponentComp d X Y Z f g = componentComp d X Y Z f g := by
  obtain ⟨f, rfl⟩ := (componentComparison d X Y).surjective f
  obtain ⟨g, rfl⟩ := (componentComparison d Y Z).surjective g
  have h := congrArg (fun k => k (f, g)) (localizedCompositionMap_comparison d X Y Z)
  rw [localizedNativeCompositionMap_eq] at h
  change localizedComponentComp d X Y Z (componentComparison d X Y f)
      (componentComparison d Y Z g) =
    componentComparison d X Z (SSet.mapπ₀ (nativeComp d X Y Z)
      (Functor.LaxMonoidal.μ SSet.π₀Functor (nativeSpace d X Y) (nativeSpace d Y Z) (f, g))) at h
  rw [piZeroFunctor_tensor] at h
  unfold componentComp
  simp only [Equiv.symm_apply_apply]
  exact h

variable {H : Type uH} [Category.{vH} H] (L : C ⥤ H) [L.IsLocalization (weakEquivalences C)]

/-- The native Hom-class function uses the same full weak comparison followed by the original Hom
equivalence. -/
def nativeComponentsToHom (X Y : C) : SSet.π₀ (nativeSpace d X Y) ≃ (L.obj X ⟶ L.obj Y) :=
  (componentComparison d X Y).trans (rightPiZeroEquiv d L X Y)

/-- The same original constant-Q comparison evaluated at degree zero. -/
abbrev frameInclusionZero (X : C) : (GeneratedFunctorialReplacements.Q d).obj X ⟶
    ((GeneratedFramings.bifibrantFrame d).obj X).obj (.op ⦋0⦌) :=
  ((GeneratedFramings.bifibrantFromQ d).app X).app (.op ⦋0⦌)

/-- The actual original degree-zero frame inclusion becomes invertible under the original
localization. -/
instance frameInclusionZero_map_isIso (X : C) : IsIso (L.map (frameInclusionZero d X)) :=
  Localization.inverts L (weakEquivalences C) _ (GeneratedFramings.bifibrantFromQ_weak d X _)

set_option backward.isDefEq.respectTransparency false in
/-- Every native component retains the original frame vertex and both full replacement inverse maps.
-/
theorem nativeComponentsToHom_mk (X Y : C) (f : (nativeSpace d X Y).obj (.op ⦋0⦌)) :
    nativeComponentsToHom d L X Y (SSet.π₀.mk f) =
      inv (L.map ((GeneratedFunctorialReplacements.counit d).app X)) ≫
        L.map (frameInclusionZero d X) ≫ L.map (f.app (.op ⦋0⦌) (𝟙 _)) ≫
          inv (L.map (frameInclusionZero d Y)) ≫
            L.map ((GeneratedFunctorialReplacements.counit d).app Y) := by
  change rightPiZeroEquiv d L X Y
    (SSet.mapπ₀ (((nativeToRight d).app (.op X)).app Y) (SSet.π₀.mk f)) = _
  rw [SSet.mapπ₀_mk, rightPiZeroEquiv_mk, nativeToRight_simplex]
  have hp :
      L.map (((GeneratedFramings.rightFrame d).map
          ((GeneratedFunctorialReplacements.counit d).app Y)).app (.op ⦋0⦌)) ≫
        L.map ((GeneratedFramings.rightZeroIso d).inv.app Y) ≫
          inv (L.map ((GeneratedFunctorialReplacements.unit d).app Y)) =
      inv (L.map (frameInclusionZero d Y)) ≫
        L.map ((GeneratedFunctorialReplacements.counit d).app Y) := by
    apply (cancel_epi (L.map (frameInclusionZero d Y))).mp
    rw [IsIso.hom_inv_id_assoc]
    rw [← L.map_comp_assoc, bifibrantFromQ_projection_zero, L.map_comp, L.map_comp]
    have hz : L.map ((GeneratedFramings.rightZeroIso d).hom.app Y) ≫
        L.map ((GeneratedFramings.rightZeroIso d).inv.app Y) = 𝟙 _ := by
      rw [← L.map_comp, Iso.hom_inv_id_app, L.map_id]
    simp only [Category.assoc]
    rw [reassoc_of% hz, IsIso.hom_inv_id, Category.comp_id]
  simp only [L.map_comp, Category.assoc]
  rw [hp]

set_option backward.isDefEq.respectTransparency false in
/-- All native component pairs preserve the same original homotopy-category composition. -/
theorem nativeComponentsToHom_comp (X Y Z : C)
    (f : SSet.π₀ (nativeSpace d X Y)) (g : SSet.π₀ (nativeSpace d Y Z)) :
    nativeComponentsToHom d L X Z (nativeComponentComp d X Y Z f g) =
      nativeComponentsToHom d L X Y f ≫ nativeComponentsToHom d L Y Z g := by
  obtain ⟨f, rfl⟩ := SSet.π₀.mk_surjective f
  obtain ⟨g, rfl⟩ := SSet.π₀.mk_surjective g
  unfold nativeComponentComp
  rw [SSet.piZeroTensorEquiv_symm_mk, SSet.mapπ₀_mk, nativeComponentsToHom_mk,
    nativeComponentsToHom_mk, nativeComponentsToHom_mk]
  change inv (L.map ((GeneratedFunctorialReplacements.counit d).app X)) ≫
      L.map (frameInclusionZero d X) ≫ L.map (f.app (.op ⦋0⦌) (𝟙 _) ≫ g.app (.op ⦋0⦌) (𝟙 _)) ≫
        inv (L.map (frameInclusionZero d Z)) ≫
          L.map ((GeneratedFunctorialReplacements.counit d).app Z) = _
  simp only [L.map_comp, Category.assoc, IsIso.hom_inv_id_assoc, IsIso.inv_hom_id_assoc]

/-- All original right component pairs preserve the actual original homotopy-category composition.
-/
theorem componentComp_toHom (X Y Z : C) (f : SSet.π₀ (rightSpace d X Y))
    (g : SSet.π₀ (rightSpace d Y Z)) :
    rightPiZeroEquiv d L X Z (componentComp d X Y Z f g) =
      rightPiZeroEquiv d L X Y f ≫ rightPiZeroEquiv d L Y Z g := by
  change nativeComponentsToHom d L X Z (nativeComponentComp d X Y Z
    ((componentComparison d X Y).symm f) ((componentComparison d Y Z).symm g)) = _
  rw [nativeComponentsToHom_comp]
  simp only [nativeComponentsToHom, Equiv.trans_apply, Equiv.apply_symm_apply]


/--
Applying the actual descended component functor to the constructed coherent comp preserves every
original
Ho composite.
-/
theorem localizedComponentComp_toHom (X Y Z : C) (f : SSet.π₀ (rightSpace d X Y))
    (g : SSet.π₀ (rightSpace d Y Z)) :
    rightPiZeroEquiv d L X Z (localizedComponentComp d X Y Z f g) =
      rightPiZeroEquiv d L X Y f ≫ rightPiZeroEquiv d L Y Z g := by
  rw [localizedComponentComp_eq, componentComp_toHom]

/-- The same original Hom correspondence sends the literal localized component unit to the original
Ho identity. -/
theorem localizedUnitMap_toHom (X : C) (t : 𝟙_ (Type vC)) :
    rightPiZeroEquiv d L X X (localizedUnitMap d X t) = 𝟙 (L.obj X) := by
  rw [localizedUnitMap_eq]
  change rightPiZeroEquiv d L X X (SSet.π₀.mk (representedRightVertex d (𝟙 X))) = _
  rw [rightPiZeroEquiv_original_map, L.map_id]

/-- Both entire inverse Hom functions carry arbitrary original Ho composites to the actual component
composition. -/
theorem componentComp_ofHom (X Y Z : C) (f : L.obj X ⟶ L.obj Y) (g : L.obj Y ⟶ L.obj Z) :
    (rightPiZeroEquiv d L X Z).symm (f ≫ g) =
      componentComp d X Y Z ((rightPiZeroEquiv d L X Y).symm f)
        ((rightPiZeroEquiv d L Y Z).symm g) := by
  apply (rightPiZeroEquiv d L X Z).injective
  rw [Equiv.apply_symm_apply, componentComp_toHom, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- Both inverse Hom functions retain the literal composition from the actual localized enrichment.
-/
theorem localizedComponentComp_ofHom (X Y Z : C) (f : L.obj X ⟶ L.obj Y) (g : L.obj Y ⟶ L.obj Z) :
    (rightPiZeroEquiv d L X Z).symm (f ≫ g) =
      localizedComponentComp d X Y Z ((rightPiZeroEquiv d L X Y).symm f)
        ((rightPiZeroEquiv d L Y Z).symm g) := by
  rw [localizedComponentComp_eq, componentComp_ofHom]

/-- The component of the same original represented composite is the original Ho composite. -/
theorem point_comp_components {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    rightPiZeroEquiv d L X Z (SSet.π₀.mk (representedRightVertex d (f ≫ g))) =
      L.map f ≫ L.map g := by
  rw [rightPiZeroEquiv_original_map, L.map_comp]

/-- The component of the same original represented identity is the original Ho identity. -/
theorem point_id_components (X : C) :
    rightPiZeroEquiv d L X X (SSet.π₀.mk (representedRightVertex d (𝟙 X))) = 𝟙 (L.obj X) := by
  rw [rightPiZeroEquiv_original_map, L.map_id]

end HomotopicalAlgebra.GeneratedMappingHomComposition

end
end
end

section



/-!
# Full original right-space composition naturality

The actual original right-space bifunctor retains all source and target
replacement maps. Its genuine natural comparison isomorphism transports the
already proved canonical source, middle, target and unit squares to those
same original maps.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w uC vC

open CategoryTheory MonoidalCategory
open scoped MonoidalCategory SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.GeneratedRightMappingEnrichment

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open HomotopyMappingSpaceCategory CanonicalGeneratedFrameEnrichment GeneratedFrameHomComplex

/-- The source action is the actual original right-space bifunctor source map. -/
def precomp {X X' : C} (f : X ⟶ X') (Y : C) : space d X' Y ⟶ space d X Y :=
  ((bifunctor d).map f.op).app Y

/-- The target action is the actual original right-space bifunctor target map. -/
def postcomp (X : C) {Y Y' : C} (f : Y ⟶ Y') : space d X Y ⟶ space d X Y' :=
  ((bifunctor d).obj (.op X)).map f

/-- Every original source action retains the localization of the exact original right
function-complex map. -/
theorem precomp_eq {X X' : C} (f : X ⟶ X') (Y : C) :
    precomp d f Y = localize.map (((rightBifunctor d).map f.op).app Y) := rfl

/-- Every original target action retains the localization of the exact original right
function-complex map. -/
theorem postcomp_eq (X : C) {Y Y' : C} (f : Y ⟶ Y') :
    postcomp d X f = localize.map (((rightBifunctor d).obj (.op X)).map f) := rfl

/-- The actual complete forward comparison retains every original source map. -/
theorem precomp_comparison_hom {X X' : C} (f : X ⟶ X') (Y : C) :
    coherentPrecomp d f Y ≫ (comparisonIso d X Y).hom =
      (comparisonIso d X' Y).hom ≫ precomp d f Y :=
  congrArg (fun t ↦ t.app Y) ((comparisonBifunctorIso d).hom.naturality f.op)

/-- The actual complete forward comparison retains every original target map. -/
theorem postcomp_comparison_hom (X : C) {Y Y' : C} (f : Y ⟶ Y') :
    coherentPostcomp d X f ≫ (comparisonIso d X Y').hom =
      (comparisonIso d X Y).hom ≫ postcomp d X f :=
  ((comparisonBifunctorIso d).hom.app (.op X)).naturality f

/-- The actual complete inverse comparison retains every original source map. -/
theorem precomp_comparison_inv {X X' : C} (f : X ⟶ X') (Y : C) :
    precomp d f Y ≫ (comparisonIso d X Y).inv =
      (comparisonIso d X' Y).inv ≫ coherentPrecomp d f Y :=
  congrArg (fun t ↦ t.app Y) ((comparisonBifunctorIso d).inv.naturality f.op)

/-- The actual complete inverse comparison retains every original target map. -/
theorem postcomp_comparison_inv (X : C) {Y Y' : C} (f : Y ⟶ Y') :
    postcomp d X f ≫ (comparisonIso d X Y').inv =
      (comparisonIso d X Y).inv ≫ coherentPostcomp d X f :=
  ((comparisonBifunctorIso d).inv.app (.op X)).naturality f

/-- Every original source morphism commutes with the actual original right-space composition. -/
theorem comp_naturality_source {X X' : C} (f : X ⟶ X') (Y Z : C) :
    comp d X' Y Z ≫ precomp d f Z = precomp d f Y ▷ space d Y Z ≫ comp d X Y Z := by
  apply (cancel_mono (comparisonIso d X Z).inv).mp
  calc
    _ = comp d X' Y Z ≫ ((comparisonIso d X' Z).inv ≫ coherentPrecomp d f Z) := by
      rw [Category.assoc, precomp_comparison_inv]
    _ = (comp d X' Y Z ≫ (comparisonIso d X' Z).inv) ≫ coherentPrecomp d f Z :=
      (Category.assoc _ _ _).symm
    _ = (((comparisonIso d X' Y).inv ⊗ₘ (comparisonIso d Y Z).inv) ≫
        coherentComp d X' Y Z) ≫ coherentPrecomp d f Z := by rw [comp_inverse_readback]
    _ = ((comparisonIso d X' Y).inv ⊗ₘ (comparisonIso d Y Z).inv) ≫
        (coherentPrecomp d f Y ▷ coherentSpace d Y Z ≫ coherentComp d X Y Z) := by
      rw [Category.assoc, coherentComp_naturality_source]
    _ = (((comparisonIso d X' Y).inv ≫ coherentPrecomp d f Y) ⊗ₘ
        (comparisonIso d Y Z).inv) ≫ coherentComp d X Y Z := by
      rw [← Category.assoc, tensorHom_comp_whiskerRight]
    _ = ((precomp d f Y ≫ (comparisonIso d X Y).inv) ⊗ₘ (comparisonIso d Y Z).inv) ≫
        coherentComp d X Y Z := by rw [← precomp_comparison_inv]
    _ = precomp d f Y ▷ space d Y Z ≫
        (((comparisonIso d X Y).inv ⊗ₘ (comparisonIso d Y Z).inv) ≫ coherentComp d X Y Z) := by
      rw [whiskerRight_comp_tensorHom_assoc]
    _ = precomp d f Y ▷ space d Y Z ≫ (comp d X Y Z ≫ (comparisonIso d X Z).inv) := by
      rw [comp_inverse_readback]
    _ = (precomp d f Y ▷ space d Y Z ≫ comp d X Y Z) ≫ (comparisonIso d X Z).inv :=
      (Category.assoc _ _ _).symm

/-- Every original target morphism commutes with the actual original right-space composition. -/
theorem comp_naturality_target (X Y : C) {Z Z' : C} (f : Z ⟶ Z') :
    comp d X Y Z ≫ postcomp d X f = space d X Y ◁ postcomp d Y f ≫ comp d X Y Z' := by
  apply (cancel_mono (comparisonIso d X Z').inv).mp
  calc
    _ = comp d X Y Z ≫ ((comparisonIso d X Z).inv ≫ coherentPostcomp d X f) := by
      rw [Category.assoc, postcomp_comparison_inv]
    _ = (comp d X Y Z ≫ (comparisonIso d X Z).inv) ≫ coherentPostcomp d X f :=
      (Category.assoc _ _ _).symm
    _ = (((comparisonIso d X Y).inv ⊗ₘ (comparisonIso d Y Z).inv) ≫
        coherentComp d X Y Z) ≫ coherentPostcomp d X f := by rw [comp_inverse_readback]
    _ = ((comparisonIso d X Y).inv ⊗ₘ (comparisonIso d Y Z).inv) ≫
        (coherentSpace d X Y ◁ coherentPostcomp d Y f ≫ coherentComp d X Y Z') := by
      rw [Category.assoc, coherentComp_naturality_target]
    _ = ((comparisonIso d X Y).inv ⊗ₘ
        ((comparisonIso d Y Z).inv ≫ coherentPostcomp d Y f)) ≫ coherentComp d X Y Z' := by
      rw [← Category.assoc, tensorHom_comp_whiskerLeft]
    _ = ((comparisonIso d X Y).inv ⊗ₘ (postcomp d Y f ≫ (comparisonIso d Y Z').inv)) ≫
        coherentComp d X Y Z' := by rw [← postcomp_comparison_inv]
    _ = space d X Y ◁ postcomp d Y f ≫
        (((comparisonIso d X Y).inv ⊗ₘ (comparisonIso d Y Z').inv) ≫ coherentComp d X Y Z') := by
      rw [whiskerLeft_comp_tensorHom_assoc]
    _ = space d X Y ◁ postcomp d Y f ≫ (comp d X Y Z' ≫ (comparisonIso d X Z').inv) := by
      rw [comp_inverse_readback]
    _ = (space d X Y ◁ postcomp d Y f ≫ comp d X Y Z') ≫ (comparisonIso d X Z').inv :=
      (Category.assoc _ _ _).symm

/-- Every original middle morphism retains both adjoining actual original right-space composition
maps. -/
theorem comp_naturality_middle (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C) :
    postcomp d X f ▷ space d Y' Z ≫ comp d X Y' Z =
      space d X Y ◁ precomp d f Z ≫ comp d X Y Z := by
  apply (cancel_mono (comparisonIso d X Z).inv).mp
  calc
    _ = postcomp d X f ▷ space d Y' Z ≫
        (((comparisonIso d X Y').inv ⊗ₘ (comparisonIso d Y' Z).inv) ≫ coherentComp d X Y' Z) := by
      rw [Category.assoc, comp_inverse_readback]
    _ = ((postcomp d X f ≫ (comparisonIso d X Y').inv) ⊗ₘ (comparisonIso d Y' Z).inv) ≫
        coherentComp d X Y' Z := by rw [whiskerRight_comp_tensorHom_assoc]
    _ = (((comparisonIso d X Y).inv ≫ coherentPostcomp d X f) ⊗ₘ
        (comparisonIso d Y' Z).inv) ≫ coherentComp d X Y' Z := by rw [postcomp_comparison_inv]
    _ = ((comparisonIso d X Y).inv ⊗ₘ (comparisonIso d Y' Z).inv) ≫
        (coherentPostcomp d X f ▷ coherentSpace d Y' Z ≫ coherentComp d X Y' Z) := by
      rw [tensorHom_comp_whiskerRight_assoc]
    _ = ((comparisonIso d X Y).inv ⊗ₘ (comparisonIso d Y' Z).inv) ≫
        (coherentSpace d X Y ◁ coherentPrecomp d f Z ≫ coherentComp d X Y Z) := by
      rw [coherentComp_naturality_middle]
    _ = ((comparisonIso d X Y).inv ⊗ₘ
        ((comparisonIso d Y' Z).inv ≫ coherentPrecomp d f Z)) ≫ coherentComp d X Y Z := by
      rw [← Category.assoc, tensorHom_comp_whiskerLeft]
    _ = ((comparisonIso d X Y).inv ⊗ₘ (precomp d f Z ≫ (comparisonIso d Y Z).inv)) ≫
        coherentComp d X Y Z := by rw [← precomp_comparison_inv]
    _ = space d X Y ◁ precomp d f Z ≫
        (((comparisonIso d X Y).inv ⊗ₘ (comparisonIso d Y Z).inv) ≫ coherentComp d X Y Z) := by
      rw [whiskerLeft_comp_tensorHom_assoc]
    _ = space d X Y ◁ precomp d f Z ≫ (comp d X Y Z ≫ (comparisonIso d X Z).inv) := by
      rw [comp_inverse_readback]
    _ = (space d X Y ◁ precomp d f Z ≫ comp d X Y Z) ≫ (comparisonIso d X Z).inv :=
      (Category.assoc _ _ _).symm

/-- Every original morphism retains the unit square of the actual original right-space bifunctor. -/
theorem unit_naturality {X Y : C} (f : X ⟶ Y) :
    unit d X ≫ postcomp d X f = unit d Y ≫ precomp d f Y := by
  apply (cancel_mono (comparisonIso d X Y).inv).mp
  calc
    _ = unit d X ≫ ((comparisonIso d X X).inv ≫ coherentPostcomp d X f) := by
      rw [Category.assoc, postcomp_comparison_inv]
    _ = coherentUnit d X ≫ coherentPostcomp d X f := by
      rw [← Category.assoc, unit_inverse_readback]
    _ = coherentUnit d Y ≫ coherentPrecomp d f Y := coherentUnit_naturality d f
    _ = (unit d Y ≫ (comparisonIso d Y Y).inv) ≫ coherentPrecomp d f Y := by
      rw [unit_inverse_readback]
    _ = unit d Y ≫ (precomp d f Y ≫ (comparisonIso d X Y).inv) := by
      rw [Category.assoc, ← precomp_comparison_inv]
    _ = (unit d Y ≫ precomp d f Y) ≫ (comparisonIso d X Y).inv := (Category.assoc _ _ _).symm

end HomotopicalAlgebra.GeneratedRightMappingEnrichment

end
end
end
