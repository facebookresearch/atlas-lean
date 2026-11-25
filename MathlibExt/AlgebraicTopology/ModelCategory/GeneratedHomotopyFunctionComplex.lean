/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex

module

public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedFrameHomComplex
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedFramings
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedReplacementComparisons
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedRightMappingEnrichment

/-!
# Full natural weak mapping comparisons for independent original generated choices

The original Q-comparison span and actual common right frame produce a complete
natural mapping comparison from each original right function complex. Every
comparison retains both original Q counits, the original R coaugmentations, and
all coefficient and simplex maps. Its weakness is proved by the genuine Reedy
mapping calculus, without an incoming mapping comparison outcome.
-/

section

@[expose] public section

set_option autoImplicit false

noncomputable section

universe wD wE uC vC

open CategoryTheory
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.GeneratedMappingChoiceComparisons

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
  {κE : Cardinal.{wE}} [Fact κE.IsRegular] [OrderBot κE.ord.ToType]
  (d : CofibrantGenerationData C κD) (e : CofibrantGenerationData C κE)

open GeneratedFunctorialReplacements GeneratedFramings GeneratedFramingModels
open GeneratedFrameHomComplex GeneratedFrameEnrichmentComparison GeneratedFramingChoices

/-- The comparison center retains the whole original Q-composition and the actual common right
frame. -/
def centerBifunctor : Cᵒᵖ ⥤ C ⥤ SSet.{vC} :=
  (Q d ⋙ Q e ⋙ SimplicialObject.const C).op ⋙ SimplicialCategory.sHomFunctor (SimplicialObject C) ⋙
    (Functor.whiskeringLeft C (SimplicialObject C) SSet.{vC}).obj (commonFrame d e)

/-- The first full natural comparison uses the original first frame map and second original Q
counit. -/
def left : rightBifunctor d ⟶ centerBifunctor d e :=
  (rightCanonicalIso d).hom ≫
    Functor.whiskerLeft
      ((Q d ⋙ SimplicialObject.const C).op ⋙ SimplicialCategory.sHomFunctor (SimplicialObject C))
      ((Functor.whiskeringLeft C (SimplicialObject C) SSet.{vC}).map (comparisonLeft d e)) ≫
    Functor.whiskerRight
      (Functor.whiskerRight
        (NatTrans.op (Functor.whiskerRight (qComparisonLeft d e) (SimplicialObject.const C)))
        (SimplicialCategory.sHomFunctor (SimplicialObject C)))
      ((Functor.whiskeringLeft C (SimplicialObject C) SSet.{vC}).obj (commonFrame d e))

/-- The second full natural comparison uses the original second frame map and original Q image of q.
-/
def right : rightBifunctor e ⟶ centerBifunctor d e :=
  (rightCanonicalIso e).hom ≫
    Functor.whiskerLeft
      ((Q e ⋙ SimplicialObject.const C).op ⋙ SimplicialCategory.sHomFunctor (SimplicialObject C))
      ((Functor.whiskeringLeft C (SimplicialObject C) SSet.{vC}).map (comparisonRight d e)) ≫
    Functor.whiskerRight
      (Functor.whiskerRight
        (NatTrans.op (Functor.whiskerRight (qComparisonRight d e) (SimplicialObject.const C)))
        (SimplicialCategory.sHomFunctor (SimplicialObject C)))
      ((Functor.whiskeringLeft C (SimplicialObject C) SSet.{vC}).obj (commonFrame d e))

/-- Every first comparison component retains all original represented, target and source Hom
functions. -/
theorem left_app (X Y : C) :
    ((left d e).app (.op X)).app Y =
      (ResolutionHomComplex.CanonicalEnrichment.rightIso ((Q d).obj X) ((rightFrame d).obj Y)).hom ≫
        eHomWhiskerLeft SSet ((SimplicialObject.const C).obj ((Q d).obj X))
            ((comparisonLeft d e).app Y) ≫
          eHomWhiskerRight SSet ((SimplicialObject.const C).map ((qComparisonLeft d e).app X))
            ((commonFrame d e).obj Y) := rfl

/-- Every second comparison component retains all original represented, target and source Hom
functions. -/
theorem right_app (X Y : C) :
    ((right d e).app (.op X)).app Y =
      (ResolutionHomComplex.CanonicalEnrichment.rightIso ((Q e).obj X) ((rightFrame e).obj Y)).hom ≫
        eHomWhiskerLeft SSet ((SimplicialObject.const C).obj ((Q e).obj X))
            ((comparisonRight d e).app Y) ≫
          eHomWhiskerRight SSet ((SimplicialObject.const C).map ((qComparisonRight d e).app X))
            ((commonFrame d e).obj Y) := rfl

/-- The complete first original mapping comparison is weak at every original input pair. -/
theorem left_weak (X Y : C) : WeakEquivalence (((left d e).app (.op X)).app Y) := by
  let _ := simplicialModel d
  let f₁ : rightSpace d X Y ⟶
      SimplicialCategory.sHom ((SimplicialObject.const C).obj ((Q d).obj X))
          ((rightFrame d).obj Y) :=
    (ResolutionHomComplex.CanonicalEnrichment.rightIso ((Q d).obj X) ((rightFrame d).obj Y)).hom
  let f₂ : SimplicialCategory.sHom ((SimplicialObject.const C).obj ((Q d).obj X))
      ((rightFrame d).obj Y) ⟶
      SimplicialCategory.sHom ((SimplicialObject.const C).obj ((Q d).obj X))
          ((commonFrame d e).obj Y) :=
    eHomWhiskerLeft SSet ((SimplicialObject.const C).obj ((Q d).obj X)) ((comparisonLeft d e).app Y)
  let f₃ : SimplicialCategory.sHom ((SimplicialObject.const C).obj ((Q d).obj X))
      ((commonFrame d e).obj Y) ⟶
      SimplicialCategory.sHom ((SimplicialObject.const C).obj ((Q d ⋙ Q e).obj X))
          ((commonFrame d e).obj Y) :=
    eHomWhiskerRight SSet ((SimplicialObject.const C).map ((qComparisonLeft d e).app X))
      ((commonFrame d e).obj Y)
  let _ : WeakEquivalence f₁ := inferInstanceAs (WeakEquivalence
    (ResolutionHomComplex.CanonicalEnrichment.rightIso ((Q d).obj X) ((rightFrame d).obj Y)).hom)
  let _ : WeakEquivalence ((comparisonLeft d e).app Y) :=
    (weakEquivalence_iff _).mpr (comparisonLeft_trivialCofibration d e Y).2
  let _ : WeakEquivalence f₂ := ResolutionMappingWeakPreservation.postcomp_weak d _ _
    (constant_Q_isCofibrant d d X) inferInstance (rightFrame_isFibrant d d Y)
        (commonFrame_isFibrant d e Y)
  let _ : WeakEquivalence f₃ := ResolutionMappingWeakPreservation.precomp_weak d
    ((SimplicialObject.const C).map ((qComparisonLeft d e).app X)) ((commonFrame d e).obj Y)
    (constant_model_weak d _ (Q_comparison_left_weak d e X))
    (constant_isCofibrant d _ (Q_comparison_center_isCofibrant d e X))
    (constant_Q_isCofibrant d d X) (commonFrame_isFibrant d e Y)
  rw [left_app]
  change WeakEquivalence (f₁ ≫ f₂ ≫ f₃)
  infer_instance

/-- The complete second original mapping comparison is weak for independent replacement cardinals.
-/
theorem right_weak (X Y : C) : WeakEquivalence (((right d e).app (.op X)).app Y) := by
  let _ := simplicialModel d
  let f₁ : rightSpace e X Y ⟶
      SimplicialCategory.sHom ((SimplicialObject.const C).obj ((Q e).obj X))
          ((rightFrame e).obj Y) :=
    (ResolutionHomComplex.CanonicalEnrichment.rightIso ((Q e).obj X) ((rightFrame e).obj Y)).hom
  let f₂ : SimplicialCategory.sHom ((SimplicialObject.const C).obj ((Q e).obj X))
      ((rightFrame e).obj Y) ⟶
      SimplicialCategory.sHom ((SimplicialObject.const C).obj ((Q e).obj X))
          ((commonFrame d e).obj Y) :=
    eHomWhiskerLeft SSet ((SimplicialObject.const C).obj ((Q e).obj X))
        ((comparisonRight d e).app Y)
  let f₃ : SimplicialCategory.sHom ((SimplicialObject.const C).obj ((Q e).obj X))
      ((commonFrame d e).obj Y) ⟶
      SimplicialCategory.sHom ((SimplicialObject.const C).obj ((Q d ⋙ Q e).obj X))
          ((commonFrame d e).obj Y) :=
    eHomWhiskerRight SSet ((SimplicialObject.const C).map ((qComparisonRight d e).app X))
      ((commonFrame d e).obj Y)
  let _ : WeakEquivalence f₁ := inferInstanceAs (WeakEquivalence
    (ResolutionHomComplex.CanonicalEnrichment.rightIso ((Q e).obj X) ((rightFrame e).obj Y)).hom)
  let _ : WeakEquivalence ((comparisonRight d e).app Y) :=
    (weakEquivalence_iff _).mpr (comparisonRight_trivialCofibration d e Y).2
  let _ : WeakEquivalence f₂ := ResolutionMappingWeakPreservation.postcomp_weak d _ _
    (constant_Q_isCofibrant d e X) inferInstance (rightFrame_isFibrant d e Y)
        (commonFrame_isFibrant d e Y)
  let _ : WeakEquivalence f₃ := ResolutionMappingWeakPreservation.precomp_weak d
    ((SimplicialObject.const C).map ((qComparisonRight d e).app X)) ((commonFrame d e).obj Y)
    (constant_model_weak d _ (Q_comparison_right_weak d e X))
    (constant_isCofibrant d _ (Q_comparison_center_isCofibrant d e X))
    (constant_Q_isCofibrant d e X) (commonFrame_isFibrant d e Y)
  rw [right_app]
  change WeakEquivalence (f₁ ≫ f₂ ≫ f₃)
  infer_instance

/-- Every original source map preserves the entire first mapping comparison square. -/
theorem left_naturality_source {X X' : C} (f : X ⟶ X') (Y : C) :
    ((rightBifunctor d).map f.op).app Y ≫ ((left d e).app (.op X)).app Y =
      ((left d e).app (.op X')).app Y ≫ ((centerBifunctor d e).map f.op).app Y :=
  congrArg (fun t => t.app Y) ((left d e).naturality f.op)

/-- Every original target map preserves the entire first mapping comparison square. -/
theorem left_naturality_target (X : C) {Y Y' : C} (f : Y ⟶ Y') :
    ((rightBifunctor d).obj (.op X)).map f ≫ ((left d e).app (.op X)).app Y' =
      ((left d e).app (.op X)).app Y ≫ ((centerBifunctor d e).obj (.op X)).map f :=
  ((left d e).app (.op X)).naturality f

/-- Every original source map preserves the entire second mapping comparison square. -/
theorem right_naturality_source {X X' : C} (f : X ⟶ X') (Y : C) :
    ((rightBifunctor e).map f.op).app Y ≫ ((right d e).app (.op X)).app Y =
      ((right d e).app (.op X')).app Y ≫ ((centerBifunctor d e).map f.op).app Y :=
  congrArg (fun t => t.app Y) ((right d e).naturality f.op)

/-- Every original target map preserves the entire second mapping comparison square. -/
theorem right_naturality_target (X : C) {Y Y' : C} (f : Y ⟶ Y') :
    ((rightBifunctor e).obj (.op X)).map f ≫ ((right d e).app (.op X)).app Y' =
      ((right d e).app (.op X)).app Y ≫ ((centerBifunctor d e).obj (.op X)).map f :=
  ((right d e).app (.op X)).naturality f

end HomotopicalAlgebra.GeneratedMappingChoiceComparisons

end
end
end

section



/-!
# Entire original represented-point compatibility for independent choices

The same two original Q counits give the actual center counit. The entire original
right point from either choice is sent to the same entire canonical center point.
Every scalar degree, original simplex operator, and original coaugmentation word is
retained. No point or choice-compatibility outcome is an input.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe wD wE u v

open CategoryTheory
open scoped Simplicial MonoidalCategory SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.MappingChoiceUnitCompatibility

variable {C : Type u} [Category.{v} C] [ModelCategory C]
variable {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
variable {κE : Cardinal.{wE}} [Fact κE.IsRegular] [OrderBot κE.ord.ToType]
variable (d : CofibrantGenerationData C κD) (e : CofibrantGenerationData C κE)

open GeneratedFunctorialReplacements GeneratedFramings GeneratedFramingChoices
open GeneratedFrameHomComplex GeneratedFrameEnrichmentComparison
open GeneratedMappingChoiceComparisons

/-- The actual center counit keeps the original left Q comparison and original first counit. -/
def centerCounit : Q d ⋙ Q e ⟶ 𝟭 C := qComparisonLeft d e ≫ counit d

/-- The same actual center counit is also the original right comparison and second counit. -/
theorem centerCounit_eq_right : centerCounit d e = qComparisonRight d e ≫ counit e :=
  Q_comparison_counits d e

/-- Every center counit component retains the full original first comparison/counit word. -/
theorem centerCounit_app_left (X : C) :
    (centerCounit d e).app X = (qComparisonLeft d e).app X ≫ (counit d).app X := rfl

/-- Every center counit component retains the full original second comparison/counit word. -/
theorem centerCounit_app_right (X : C) :
    (centerCounit d e).app X = (qComparisonRight d e).app X ≫ (counit e).app X := by
  rw [centerCounit_eq_right]
  rfl

/-- The actual canonical center point is the whole original represented constant-source frame map.
-/
def centerPoint {X Y : C} (f : X ⟶ Y) :
    𝟙_ SSet.{v} ⟶ SimplicialCategory.sHom
      ((SimplicialObject.const C).obj ((Q d ⋙ Q e).obj X)) ((commonFrame d e).obj Y) :=
  eHomEquiv SSet ((SimplicialObject.const C).map ((centerCounit d e).app X ≫ f) ≫
    (commonCoaugmentation d e).app Y)

/-- The entire original represented point is recovered by the same full canonical Hom isomorphism.
-/
theorem rightPoint_canonical {X Y : C} (f : X ⟶ Y) :
    rightPoint d f ≫
      (ResolutionHomComplex.CanonicalEnrichment.rightIso ((Q d).obj X) ((rightFrame d).obj Y)).hom =
        eHomEquiv SSet ((SimplicialObject.const C).map ((counit d).app X ≫ f) ≫
          (coaugmentation d).app Y) := by
  change (_ ≫ (ResolutionHomComplex.CanonicalEnrichment.rightIso
    ((Q d).obj X) ((rightFrame d).obj Y)).inv) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun h => eHomEquiv SSet
      ((SimplicialObject.const C).map ((counit d).app X ≫ f) ≫ (coaugmentation d).app Y) ≫ h)
        (ResolutionHomComplex.CanonicalEnrichment.rightIso
          ((Q d).obj X) ((rightFrame d).obj Y)).inv_hom_id).trans (Category.comp_id _))

/-- The entire first original right point, in SSet, maps to the entire actual center point. -/
theorem rightPoint_left {X Y : C} (f : X ⟶ Y) :
    rightPoint d f ≫ ((left d e).app (.op X)).app Y = centerPoint d e f := by
  rw [left_app]
  let post := eHomWhiskerLeft SSet ((SimplicialObject.const C).obj ((Q d).obj X))
    ((comparisonLeft d e).app Y)
  let pre := eHomWhiskerRight SSet ((SimplicialObject.const C).map ((qComparisonLeft d e).app X))
    ((commonFrame d e).obj Y)
  calc
    _ = (rightPoint d f ≫ (ResolutionHomComplex.CanonicalEnrichment.rightIso
        ((Q d).obj X) ((rightFrame d).obj Y)).hom) ≫ post ≫ pre :=
      (Category.assoc _ _ _).symm
    _ = eHomEquiv SSet ((SimplicialObject.const C).map ((counit d).app X ≫ f) ≫
        (coaugmentation d).app Y) ≫ post ≫ pre :=
      congrArg (fun h => h ≫ post ≫ pre) (rightPoint_canonical d f)
    _ = centerPoint d e f := by
      dsimp only [post, pre]
      rw [← Category.assoc, eHomEquiv_comp_eHomWhiskerLeft SSet (SimplicialObject C),
        eHomEquiv_comp_eHomWhiskerRight SSet (SimplicialObject C)]
      unfold centerPoint
      apply congrArg (eHomEquiv SSet (C := SimplicialObject C)
        (X := (SimplicialObject.const C).obj ((Q d ⋙ Q e).obj X))
        (Y := (commonFrame d e).obj Y))
      simp only [centerCounit, commonCoaugmentation, NatTrans.comp_app,
        CategoryTheory.Functor.map_comp, Category.assoc]

/-- The entire second original right point, in SSet, maps to that same entire center point. -/
theorem rightPoint_right {X Y : C} (f : X ⟶ Y) :
    rightPoint e f ≫ ((right d e).app (.op X)).app Y = centerPoint d e f := by
  rw [right_app]
  let post := eHomWhiskerLeft SSet ((SimplicialObject.const C).obj ((Q e).obj X))
    ((comparisonRight d e).app Y)
  let pre := eHomWhiskerRight SSet ((SimplicialObject.const C).map ((qComparisonRight d e).app X))
    ((commonFrame d e).obj Y)
  calc
    _ = (rightPoint e f ≫ (ResolutionHomComplex.CanonicalEnrichment.rightIso
        ((Q e).obj X) ((rightFrame e).obj Y)).hom) ≫ post ≫ pre :=
      (Category.assoc _ _ _).symm
    _ = eHomEquiv SSet ((SimplicialObject.const C).map ((counit e).app X ≫ f) ≫
        (coaugmentation e).app Y) ≫ post ≫ pre :=
      congrArg (fun h => h ≫ post ≫ pre) (rightPoint_canonical e f)
    _ = centerPoint d e f := by
      dsimp only [post, pre]
      rw [← Category.assoc, eHomEquiv_comp_eHomWhiskerLeft SSet (SimplicialObject C),
        eHomEquiv_comp_eHomWhiskerRight SSet (SimplicialObject C)]
      unfold centerPoint
      apply congrArg (eHomEquiv SSet (C := SimplicialObject C)
        (X := (SimplicialObject.const C).obj ((Q d ⋙ Q e).obj X))
        (Y := (commonFrame d e).obj Y))
      rw [centerCounit_app_right, commonCoaugmentation_eq]
      simp only [NatTrans.comp_app, Functor.map_comp, Category.assoc]

/-- Every scalar structured-Hom coordinate keeps the same entire original center morphism word. -/
theorem centerPoint_coordinate {X Y : C} (f : X ⟶ Y) (n k : SimplexCategoryᵒᵖ)
    (t : (𝟙_ SSet.{v}).obj n) (g : n ⟶ k) :
    ((centerPoint d e f).app n t).app k g =
      (centerCounit d e).app X ≫ f ≫ ((commonCoaugmentation d e).app Y).app k := by
  change ((SimplicialObject.const C).map ((centerCounit d e).app X ≫ f) ≫
    (commonCoaugmentation d e).app Y).app k = _
  exact Category.assoc _ _ _

/-- Every first-branch scalar coordinate retains both original Q and original R/frame comparison
arrows. -/
theorem centerPoint_coordinate_left {X Y : C} (f : X ⟶ Y) (n k : SimplexCategoryᵒᵖ)
    (t : (𝟙_ SSet.{v}).obj n) (g : n ⟶ k) :
    ((centerPoint d e f).app n t).app k g =
      (qComparisonLeft d e).app X ≫ (counit d).app X ≫ f ≫ (unit d).app Y ≫
        ((rightResolution d).app Y).app k ≫ ((comparisonLeft d e).app Y).app k := by
  rw [centerPoint_coordinate, centerCounit_app_left, commonCoaugmentation_app_left]
  simp only [Category.assoc]

/-- Every second-branch scalar coordinate retains the full original alternative Q and R/frame
arrows. -/
theorem centerPoint_coordinate_right {X Y : C} (f : X ⟶ Y) (n k : SimplexCategoryᵒᵖ)
    (t : (𝟙_ SSet.{v}).obj n) (g : n ⟶ k) :
    ((centerPoint d e f).app n t).app k g =
      (qComparisonRight d e).app X ≫ (counit e).app X ≫ f ≫ (unit e).app Y ≫
        ((rightResolution e).app Y).app k ≫ ((comparisonRight d e).app Y).app k := by
  rw [centerPoint_coordinate, centerCounit_app_right, commonCoaugmentation_app_right]
  simp only [Category.assoc]

/-- The entire actual first original right unit maps to the original identity center point. -/
theorem rightUnit_left (X : C) : rightUnit d X ≫ ((left d e).app (.op X)).app X =
    centerPoint d e (𝟙 X) := rightPoint_left d e (𝟙 X)

/-- The entire actual second original right unit maps to that same original identity center point.
-/
theorem rightUnit_right (X : C) : rightUnit e X ≫ ((right d e).app (.op X)).app X =
    centerPoint d e (𝟙 X) := rightPoint_right d e (𝟙 X)

end HomotopicalAlgebra.MappingChoiceUnitCompatibility

end
end
end

section



/-!
# Actual natural localized mapping-choice isomorphisms and entire unit compatibility

Both original weak mapping comparisons become natural isomorphisms under the same
actual simplicial-set localization. Their genuine span constructs the choice iso, with
both complete inverse maps and every original source/target map. Entire represented
point compatibility supplies the complete original transported-unit compatibility.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe wD wE u v

open CategoryTheory
open scoped Simplicial MonoidalCategory SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.MappingChoiceUnitCompatibility

variable {C : Type u} [Category.{v} C] [ModelCategory C]
variable {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
variable {κE : Cardinal.{wE}} [Fact κE.IsRegular] [OrderBot κE.ord.ToType]
variable (d : CofibrantGenerationData C κD) (e : CofibrantGenerationData C κE)

open HomotopyMappingSpaceCategory GeneratedFrameHomComplex GeneratedFrameEnrichmentComparison
open GeneratedMappingChoiceComparisons

/-- The actual comparison center is localized by the same original monoidal localization. -/
def centerHoBifunctor : Cᵒᵖ ⥤ C ⥤ SpaceHo.{v} :=
  centerBifunctor d e ⋙ (Functor.whiskeringRight C SSet.{v} SpaceHo.{v}).obj localize

/-- Every first whole original weak comparison becomes an actual isomorphism. -/
instance left_map_isIso (X Y : C) : IsIso (localize.map (((left d e).app (.op X)).app Y)) := by
  have h : SSet.realizationWeakEquivalences (((left d e).app (.op X)).app Y) := by
    change weakEquivalences SSet.{v} (((left d e).app (.op X)).app Y)
    exact (weakEquivalence_iff _).mp (left_weak d e X Y)
  exact localize_isIso _ h

/-- Every second whole original weak comparison becomes an actual isomorphism. -/
instance right_map_isIso (X Y : C) : IsIso (localize.map (((right d e).app (.op X)).app Y)) := by
  have h : SSet.realizationWeakEquivalences (((right d e).app (.op X)).app Y) := by
    change weakEquivalences SSet.{v} (((right d e).app (.op X)).app Y)
    exact (weakEquivalence_iff _).mp (right_weak d e X Y)
  exact localize_isIso _ h

/-- The actual first localized Hom iso is the same complete original left comparison. -/
def leftHoIso (X Y : C) : GeneratedRightMappingEnrichment.space d X Y ≅
    ((centerHoBifunctor d e).obj (.op X)).obj Y :=
  @asIso SpaceHo.{v} _ (localize.obj (rightSpace d X Y))
    (localize.obj (((centerBifunctor d e).obj (.op X)).obj Y))
    (localize.map (((left d e).app (.op X)).app Y)) (left_map_isIso d e X Y)

/-- The actual second localized Hom iso is the same complete original right comparison. -/
def rightHoIso (X Y : C) : GeneratedRightMappingEnrichment.space e X Y ≅
    ((centerHoBifunctor d e).obj (.op X)).obj Y :=
  @asIso SpaceHo.{v} _ (localize.obj (rightSpace e X Y))
    (localize.obj (((centerBifunctor d e).obj (.op X)).obj Y))
    (localize.map (((right d e).app (.op X)).app Y)) (right_map_isIso d e X Y)

/-- The actual first localized iso retains every source and target naturality square. -/
def leftHoBifunctorIso : GeneratedRightMappingEnrichment.bifunctor d ≅ centerHoBifunctor d e :=
  NatIso.ofComponents (fun X => NatIso.ofComponents (fun Y => leftHoIso d e X.unop Y) (by
    intro Y Y' f
    change localize.map (((rightBifunctor d).obj X).map f) ≫
        localize.map (((left d e).app X).app Y') =
      localize.map (((left d e).app X).app Y) ≫ localize.map (((centerBifunctor d e).obj X).map f)
    rw [← localize.map_comp, ← localize.map_comp]
    exact congrArg localize.map (left_naturality_target d e X.unop f))) (by
      intro X X' f
      apply NatTrans.ext
      funext Y
      change localize.map (((rightBifunctor d).map f).app Y) ≫
          localize.map (((left d e).app X').app Y) =
        localize.map (((left d e).app X).app Y) ≫ localize.map (((centerBifunctor d e).map f).app Y)
      rw [← localize.map_comp, ← localize.map_comp]
      exact congrArg localize.map (left_naturality_source d e f.unop Y))

/-- The actual second localized iso retains every source and target naturality square. -/
def rightHoBifunctorIso : GeneratedRightMappingEnrichment.bifunctor e ≅ centerHoBifunctor d e :=
  NatIso.ofComponents (fun X => NatIso.ofComponents (fun Y => rightHoIso d e X.unop Y) (by
    intro Y Y' f
    change localize.map (((rightBifunctor e).obj X).map f) ≫
        localize.map (((right d e).app X).app Y') =
      localize.map (((right d e).app X).app Y) ≫ localize.map (((centerBifunctor d e).obj X).map f)
    rw [← localize.map_comp, ← localize.map_comp]
    exact congrArg localize.map (right_naturality_target d e X.unop f))) (by
      intro X X' f
      apply NatTrans.ext
      funext Y
      change localize.map (((rightBifunctor e).map f).app Y) ≫
          localize.map (((right d e).app X').app Y) =
        localize.map (((right d e).app X).app Y) ≫
            localize.map (((centerBifunctor d e).map f).app Y)
      rw [← localize.map_comp, ← localize.map_comp]
      exact congrArg localize.map (right_naturality_source d e f.unop Y))

/-- The original localized comparison span gives the actual full natural choice isomorphism. -/
def choiceBifunctorIso : GeneratedRightMappingEnrichment.bifunctor d ≅
    GeneratedRightMappingEnrichment.bifunctor e :=
  leftHoBifunctorIso d e ≪≫ (rightHoBifunctorIso d e).symm

/-- Every original input pair receives the same actual component choice isomorphism. -/
def choiceIso (X Y : C) : GeneratedRightMappingEnrichment.space d X Y ≅
    GeneratedRightMappingEnrichment.space e X Y := leftHoIso d e X Y ≪≫ (rightHoIso d e X Y).symm

/-- The natural choice iso component is exactly the complete original component span. -/
theorem choiceBifunctorIso_app (X Y : C) :
    ((choiceBifunctorIso d e).app (.op X)).app Y = choiceIso d e X Y := rfl

/-- The entire forward choice map uses the original left map and inverse original right map. -/
theorem choiceIso_hom (X Y : C) : (choiceIso d e X Y).hom =
    localize.map (((left d e).app (.op X)).app Y) ≫
      @inv SpaceHo.{v} _ _ _ (localize.map (((right d e).app (.op X)).app Y))
        (right_map_isIso d e X Y) := rfl

/-- The entire inverse choice map uses the original right map and inverse original left map. -/
theorem choiceIso_inv (X Y : C) : (choiceIso d e X Y).inv =
    localize.map (((right d e).app (.op X)).app Y) ≫
      @inv SpaceHo.{v} _ _ _ (localize.map (((left d e).app (.op X)).app Y))
        (left_map_isIso d e X Y) := rfl

/-- The full forward choice map preserves the same entire original localized comparison span. -/
theorem choiceIso_forward_span (X Y : C) :
    (choiceIso d e X Y).hom ≫ (rightHoIso d e X Y).hom = (leftHoIso d e X Y).hom := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (leftHoIso d e X Y).hom ≫ f) (rightHoIso d e X Y).inv_hom_id).trans
      (Category.comp_id _))

/-- The full inverse choice map preserves the same entire original localized comparison span. -/
theorem choiceIso_inverse_span (X Y : C) :
    (choiceIso d e X Y).inv ≫ (leftHoIso d e X Y).hom = (rightHoIso d e X Y).hom := by
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun f => (rightHoIso d e X Y).hom ≫ f) (leftHoIso d e X Y).inv_hom_id).trans
      (Category.comp_id _))

/-- Entire first represented points remain the same entire center point after the actual
localization. -/
theorem localizedPoint_left {X Y : C} (f : X ⟶ Y) :
    localize.map (rightPoint d f) ≫ (leftHoIso d e X Y).hom = localize.map (centerPoint d e f) := by
  change localize.map (rightPoint d f) ≫ localize.map (((left d e).app (.op X)).app Y) = _
  rw [← localize.map_comp]
  exact congrArg localize.map (rightPoint_left d e f)

/-- Entire second represented points remain that same entire center point under the same
localization. -/
theorem localizedPoint_right {X Y : C} (f : X ⟶ Y) :
    localize.map (rightPoint e f) ≫ (rightHoIso d e X Y).hom =
        localize.map (centerPoint d e f) := by
  change localize.map (rightPoint e f) ≫ localize.map (((right d e).app (.op X)).app Y) = _
  rw [← localize.map_comp]
  exact congrArg localize.map (rightPoint_right d e f)

/-- The actual entire forward choice map carries every original represented point to the original
other choice. -/
theorem choiceIso_point {X Y : C} (f : X ⟶ Y) :
    localize.map (rightPoint d f) ≫ (choiceIso d e X Y).hom = localize.map (rightPoint e f) := by
  apply (cancel_mono (rightHoIso d e X Y).hom).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun h => localize.map (rightPoint d f) ≫ h) (choiceIso_forward_span d e X Y)).trans
      ((localizedPoint_left d e f).trans (localizedPoint_right d e f).symm))

/-- The actual entire inverse choice map recovers every original represented point. -/
theorem choiceIso_inv_point {X Y : C} (f : X ⟶ Y) :
    localize.map (rightPoint e f) ≫ (choiceIso d e X Y).inv = localize.map (rightPoint d f) := by
  apply (cancel_mono (leftHoIso d e X Y).hom).mp
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun h => localize.map (rightPoint e f) ≫ h) (choiceIso_inverse_span d e X Y)).trans
      ((localizedPoint_right d e f).trans (localizedPoint_left d e f).symm))

/-- The entire forward choice map preserves the actual original transported Ho(SSet) unit. -/
theorem choiceIso_unit (X : C) :
    GeneratedRightMappingEnrichment.unit d X ≫ (choiceIso d e X X).hom =
      GeneratedRightMappingEnrichment.unit e X := by
  rw [GeneratedRightMappingEnrichment.unit_calculation,
      GeneratedRightMappingEnrichment.unit_calculation]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun f => Functor.LaxMonoidal.ε localize ≫ f) (choiceIso_point d e (𝟙 X)))

/-- The entire inverse choice map recovers the actual original transported Ho(SSet) unit. -/
theorem choiceIso_inv_unit (X : C) :
    GeneratedRightMappingEnrichment.unit e X ≫ (choiceIso d e X X).inv =
      GeneratedRightMappingEnrichment.unit d X := by
  rw [GeneratedRightMappingEnrichment.unit_calculation,
      GeneratedRightMappingEnrichment.unit_calculation]
  exact (Category.assoc _ _ _).trans
    (congrArg (fun f => Functor.LaxMonoidal.ε localize ≫ f) (choiceIso_inv_point d e (𝟙 X)))

/-- Every original source morphism preserves the entire actual forward localized choice map. -/
theorem choiceIso_naturality_source {X X' : C} (f : X ⟶ X') (Y : C) :
    ((GeneratedRightMappingEnrichment.bifunctor d).map f.op).app Y ≫ (choiceIso d e X Y).hom =
      (choiceIso d e X' Y).hom ≫ ((GeneratedRightMappingEnrichment.bifunctor e).map f.op).app Y :=
  congrArg (fun t => t.app Y) ((choiceBifunctorIso d e).hom.naturality f.op)

/-- Every original target morphism preserves the entire actual forward localized choice map. -/
theorem choiceIso_naturality_target (X : C) {Y Y' : C} (f : Y ⟶ Y') :
    ((GeneratedRightMappingEnrichment.bifunctor d).obj (.op X)).map f ≫ (choiceIso d e X Y').hom =
      (choiceIso d e X Y).hom ≫ ((GeneratedRightMappingEnrichment.bifunctor e).obj (.op X)).map f :=
  ((choiceBifunctorIso d e).hom.app (.op X)).naturality f

/-- Every original source morphism preserves the entire actual inverse localized choice map. -/
theorem choiceIso_inv_naturality_source {X X' : C} (f : X ⟶ X') (Y : C) :
    ((GeneratedRightMappingEnrichment.bifunctor e).map f.op).app Y ≫ (choiceIso d e X Y).inv =
      (choiceIso d e X' Y).inv ≫ ((GeneratedRightMappingEnrichment.bifunctor d).map f.op).app Y :=
  congrArg (fun t => t.app Y) ((choiceBifunctorIso d e).inv.naturality f.op)

/-- Every original target morphism preserves the entire actual inverse localized choice map. -/
theorem choiceIso_inv_naturality_target (X : C) {Y Y' : C} (f : Y ⟶ Y') :
    ((GeneratedRightMappingEnrichment.bifunctor e).obj (.op X)).map f ≫ (choiceIso d e X Y').inv =
      (choiceIso d e X Y).inv ≫ ((GeneratedRightMappingEnrichment.bifunctor d).obj (.op X)).map f :=
  ((choiceBifunctorIso d e).inv.app (.op X)).naturality f

end HomotopicalAlgebra.MappingChoiceUnitCompatibility

end
end
end

section



/-!
# The original generated homotopy function complex

The mapping bifunctor uses the original generated `Q`, the actual right frame of
the original `R`, and their original maps. Its Kan property, weak invariance,
component correspondence and coherent composition are constructed from the
original model category. The construction retains every original source,
target and simplex map. Independent generated choices have the actual natural
weak comparison span and its genuine inverse in the same homotopy category of
simplicial sets.

No simplicial enrichment or compatible external action is required here.
The compatible enriched calculation is a separate construction.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe wD wE u v uH vH

open CategoryTheory MonoidalCategory
open scoped Simplicial MonoidalCategory SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.GeneratedHomotopyFunctionComplex

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
  (d : CofibrantGenerationData C κD)

open GeneratedFunctorialReplacements GeneratedFramings GeneratedFrameHomComplex
open GeneratedFrameEnrichmentComparison HomotopyMappingSpaceCategory

/-- Every degree is the original Hom from the same original Q to the same original right frame. -/
theorem rightSpace_degree (X Y : C) (n : SimplexCategoryᵒᵖ) :
    (rightSpace d X Y).obj n = ((Q d).obj X ⟶ ((rightFrame d).obj Y).obj n) := rfl

/-- Every original simplex operator acts by the original right-frame map. -/
theorem rightSpace_operator (X Y : C) {n m : SimplexCategoryᵒᵖ} (g : n ⟶ m)
    (x : (rightSpace d X Y).obj n) :
    (rightSpace d X Y).map g x = x ≫ ((rightFrame d).obj Y).map g :=
  ResolutionHomComplex.right_map_apply ((Q d).obj X) ((rightFrame d).obj Y) g x

/-- Every original source morphism acts by the same original Q map in every degree. -/
theorem rightSpace_source {X X' : C} (f : X ⟶ X') (Y : C) (n : SimplexCategoryᵒᵖ)
    (x : (rightSpace d X' Y).obj n) :
    (((rightBifunctor d).map f.op).app Y).app n x = (Q d).map f ≫ x := rfl

/-- Every original target morphism acts by the same original right-frame map in every degree. -/
theorem rightSpace_target (X : C) {Y Y' : C} (f : Y ⟶ Y') (n : SimplexCategoryᵒᵖ)
    (x : (rightSpace d X Y).obj n) :
    (((rightBifunctor d).obj (.op X)).map f).app n x = x ≫ ((rightFrame d).map f).app n := rfl

variable {H : Type uH} [Category.{vH} H] (L : C ⥤ H) [L.IsLocalization (weakEquivalences C)]

/-- Complete mapping data constructed on the original model and its original localization.
The mapping objects and coherent enrichment are fixed by their original constructions;
the remaining fields retain their complete homotopical and original map contracts. -/
structure Construction where
  /-- The simplicial mapping bifunctor, required to be the original right-frame bifunctor. -/
  mapping : Cᵒᵖ ⥤ C ⥤ SSet.{v}
  mapping_original : mapping = rightBifunctor d
  kan : ∀ X Y : C, SSet.KanComplex (rightSpace d X Y)
  source_weak : ∀ {X X' : C} (f : X ⟶ X'), weakEquivalences C f →
    ∀ Y : C, WeakEquivalence (((rightBifunctor d).map f.op).app Y)
  target_weak : ∀ (X : C) {Y Y' : C} (f : Y ⟶ Y'), weakEquivalences C f →
    WeakEquivalence (((rightBifunctor d).obj (.op X)).map f)
  /-- The equivalence from mapping-space components to morphisms in the selected localization. -/
  components : ∀ X Y : C, SSet.π₀ (rightSpace d X Y) ≃ (L.obj X ⟶ L.obj Y)
  components_original : ∀ X Y : C, components X Y = rightPiZeroEquiv d L X Y
  components_vertex : ∀ (X Y : C) (f : (Q d).obj X ⟶ ((rightFrame d).obj Y).obj (.op ⦋0⦌)),
    components X Y (SSet.π₀.mk f) =
      inv (L.map ((counit d).app X)) ≫ L.map (f ≫ (rightZeroIso d).inv.app Y) ≫
        inv (L.map ((unit d).app Y))
  components_map : ∀ {X Y : C} (f : X ⟶ Y),
    components X Y (SSet.π₀.mk (representedRightVertex d f)) = L.map f
  components_inverse_map : ∀ {X Y : C} (f : X ⟶ Y),
    (components X Y).symm (L.map f) = SSet.π₀.mk (representedRightVertex d f)
  components_source : ∀ {X X' : C} (f : X ⟶ X') (Y : C) (x : SSet.π₀ (rightSpace d X' Y)),
    components X Y (SSet.mapπ₀ (((rightBifunctor d).map f.op).app Y) x) =
      L.map f ≫ components X' Y x
  components_target : ∀ (X : C) {Y Y' : C} (f : Y ⟶ Y') (x : SSet.π₀ (rightSpace d X Y)),
    components X Y' (SSet.mapπ₀ (((rightBifunctor d).obj (.op X)).map f) x) =
      components X Y x ≫ L.map f
  components_inverse_source : ∀ {X X' : C} (f : X ⟶ X') (Y : C) (x : L.obj X' ⟶ L.obj Y),
    (components X Y).symm (L.map f ≫ x) =
      SSet.mapπ₀ (((rightBifunctor d).map f.op).app Y) ((components X' Y).symm x)
  components_inverse_target : ∀ (X : C) {Y Y' : C} (f : Y ⟶ Y') (x : L.obj X ⟶ L.obj Y),
    (components X Y').symm (x ≫ L.map f) =
      SSet.mapπ₀ (((rightBifunctor d).obj (.op X)).map f) ((components X Y).symm x)
  components_comp : ∀ (X Y Z : C) (f : SSet.π₀ (rightSpace d X Y))
      (g : SSet.π₀ (rightSpace d Y Z)),
    components X Z (GeneratedMappingHomComposition.localizedComponentComp d X Y Z f g) =
      components X Y f ≫ components Y Z g
  components_inverse_comp : ∀ (X Y Z : C) (f : L.obj X ⟶ L.obj Y) (g : L.obj Y ⟶ L.obj Z),
    (components X Z).symm (f ≫ g) =
      GeneratedMappingHomComposition.localizedComponentComp d X Y Z
        ((components X Y).symm f) ((components Y Z).symm g)
  components_unit : ∀ (X : C) (t : 𝟙_ (Type v)),
    components X X (GeneratedMappingHomComposition.localizedUnitMap d X t) = 𝟙 (L.obj X)
  /-- The enrichment over the homotopy category of spaces constructed from the original right
  frames. -/
  enrichment : EnrichedCategory SpaceHo.{v} C
  enrichment_original : enrichment = GeneratedRightMappingEnrichment.enrichment d
  enrichment_objects : ∀ X Y : C, enrichment.Hom X Y = localize.obj (rightSpace d X Y)
  enrichment_unit : ∀ X : C,
    GeneratedRightMappingEnrichment.unit d X =
      Functor.LaxMonoidal.ε localize ≫ localize.map (rightUnit d X)
  comp_source : ∀ {X X' : C} (f : X ⟶ X') (Y Z : C),
    GeneratedRightMappingEnrichment.comp d X' Y Z ≫ GeneratedRightMappingEnrichment.precomp d f Z =
      GeneratedRightMappingEnrichment.precomp d f Y ▷ GeneratedRightMappingEnrichment.space d Y Z ≫
        GeneratedRightMappingEnrichment.comp d X Y Z
  comp_middle : ∀ (X : C) {Y Y' : C} (f : Y ⟶ Y') (Z : C),
    GeneratedRightMappingEnrichment.postcomp d X f ▷ GeneratedRightMappingEnrichment.space d Y' Z ≫
        GeneratedRightMappingEnrichment.comp d X Y' Z =
      GeneratedRightMappingEnrichment.space d X Y ◁ GeneratedRightMappingEnrichment.precomp d f Z ≫
        GeneratedRightMappingEnrichment.comp d X Y Z
  comp_target : ∀ (X Y : C) {Z Z' : C} (f : Z ⟶ Z'),
    GeneratedRightMappingEnrichment.comp d X Y Z ≫ GeneratedRightMappingEnrichment.postcomp d X f =
      GeneratedRightMappingEnrichment.space d X Y ◁ GeneratedRightMappingEnrichment.postcomp d Y f ≫
        GeneratedRightMappingEnrichment.comp d X Y Z'
  unit_natural : ∀ {X Y : C} (f : X ⟶ Y),
    GeneratedRightMappingEnrichment.unit d X ≫ GeneratedRightMappingEnrichment.postcomp d X f =
      GeneratedRightMappingEnrichment.unit d Y ≫ GeneratedRightMappingEnrichment.precomp d f Y
  /-- The simplicial point represented by each original coefficient morphism. -/
  point : ∀ {X Y : C}, (X ⟶ Y) → (𝟙_ SSet.{v} ⟶ rightSpace d X Y)
  point_original : ∀ {X Y : C} (f : X ⟶ Y), point f = rightPoint d f
  point_simplex : ∀ {X Y : C} (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ) (t : (𝟙_ SSet.{v}).obj n),
    (point f).app n t = (counit d).app X ≫ f ≫ (unit d).app Y ≫ ((rightResolution d).app Y).app n
  localized_point_comp : ∀ {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z),
    GeneratedMappingHomComposition.point d (f ≫ g) = (λ_ (𝟙_ SpaceHo.{v})).inv ≫
      (GeneratedMappingHomComposition.point d f ⊗ₘ GeneratedMappingHomComposition.point d g) ≫
        GeneratedRightMappingEnrichment.comp d X Y Z

/-- The complete original mapping construction uses the genuine proved frames and all original maps.
-/
def originalConstruction : Construction d L where
  mapping := rightBifunctor d
  mapping_original := rfl
  kan := rightSpace_kanComplex d
  source_weak := right_source_weak d
  target_weak := right_target_weak d
  components := rightPiZeroEquiv d L
  components_original _ _ := rfl
  components_vertex := rightPiZeroEquiv_mk d L
  components_map := rightPiZeroEquiv_original_map d L
  components_inverse_map := rightPiZeroEquiv_symm_original_map d L
  components_source := rightPiZeroEquiv_naturality_source d L
  components_target := rightPiZeroEquiv_naturality_target d L
  components_inverse_source := rightPiZeroEquiv_symm_naturality_source d L
  components_inverse_target := rightPiZeroEquiv_symm_naturality_target d L
  components_comp := GeneratedMappingHomComposition.localizedComponentComp_toHom d L
  components_inverse_comp := GeneratedMappingHomComposition.localizedComponentComp_ofHom d L
  components_unit := GeneratedMappingHomComposition.localizedUnitMap_toHom d L
  enrichment := GeneratedRightMappingEnrichment.enrichment d
  enrichment_original := rfl
  enrichment_objects := GeneratedRightMappingEnrichment.enrichment_hom d
  enrichment_unit := GeneratedRightMappingEnrichment.unit_calculation d
  comp_source := GeneratedRightMappingEnrichment.comp_naturality_source d
  comp_middle := GeneratedRightMappingEnrichment.comp_naturality_middle d
  comp_target := GeneratedRightMappingEnrichment.comp_naturality_target d
  unit_natural := GeneratedRightMappingEnrichment.unit_naturality d
  point := rightPoint d
  point_original _ := rfl
  point_simplex := rightPoint_simplex d
  localized_point_comp := GeneratedMappingHomComposition.point_comp d

/-- Original generated homotopy function complexes have all complete mapping and coherent enrichment
contracts. -/
theorem derivedMappingSpaces : Nonempty (Construction d L) := ⟨originalConstruction d L⟩

section IndependentChoices

variable {κE : Cardinal.{wE}} [Fact κE.IsRegular] [OrderBot κE.ord.ToType]
  (e : CofibrantGenerationData C κE)

/-- Independent original Q/R choices give the actual natural weak mapping comparison and both whole
units. -/
theorem replacementInvariant :
    (∀ X Y : C, WeakEquivalence (((GeneratedMappingChoiceComparisons.left d e).app (.op X)).app Y))
        ∧
    (∀ X Y : C, WeakEquivalence (((GeneratedMappingChoiceComparisons.right d e).app (.op X)).app Y))
        ∧
    ∃ i : GeneratedRightMappingEnrichment.bifunctor d ≅ GeneratedRightMappingEnrichment.bifunctor e,
      i = MappingChoiceUnitCompatibility.choiceBifunctorIso d e ∧
      (∀ X : C, GeneratedRightMappingEnrichment.unit d X ≫ ((i.hom.app (.op X)).app X) =
        GeneratedRightMappingEnrichment.unit e X) ∧
      (∀ X : C, GeneratedRightMappingEnrichment.unit e X ≫ ((i.inv.app (.op X)).app X) =
        GeneratedRightMappingEnrichment.unit d X) :=
  ⟨GeneratedMappingChoiceComparisons.left_weak d e,
      GeneratedMappingChoiceComparisons.right_weak d e,
    MappingChoiceUnitCompatibility.choiceBifunctorIso d e, rfl,
    MappingChoiceUnitCompatibility.choiceIso_unit d e,
        MappingChoiceUnitCompatibility.choiceIso_inv_unit d e⟩

end IndependentChoices

end HomotopicalAlgebra.GeneratedHomotopyFunctionComplex

end
end
end
