/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex

module

public import MathlibExt.AlgebraicTopology.ModelCategory.CompatibleCotensorFraming
public import MathlibExt.AlgebraicTopology.ModelCategory.FiniteResolutionTensor
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedDerivedMapping
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedFramings
public import MathlibExt.AlgebraicTopology.ModelCategory.FunctorialFramings
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedHomotopyFunctionComplex
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedRightMappingEnrichment
public import MathlibExt.AlgebraicTopology.ModelCategory.ResolutionMappingWeakPreservation
public import MathlibExt.CategoryTheory.Enriched.HomTransport

/-!
# Actual common fibrant frames for the compatible right comparison

The original cotensor augmentation is first factored by the actual generated
Reedy J factory. Its genuine trivial-cofibration middle augmentation and the
original RF augmentation form a functorial pushout. The same terminal factory
gives the common fibrant frame, retaining every original augmentation and map.
-/

open HomotopicalAlgebra.GeneratedFunctorialReplacements

section

@[expose] public section

set_option autoImplicit false

noncomputable section

universe wM wD uC vC

open CategoryTheory Limits MorphismProperty

namespace HomotopicalAlgebra.CompatibleRightMappingComparison

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [SimplicialCategory C]
  (a : CompatibleSimplicialMapping.Action C)
  {κM : Cardinal.{wM}} [Fact κM.IsRegular] [OrderBot κM.ord.ToType]
  (m : CofibrantGenerationData C κM)
  {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
  (d : CofibrantGenerationData C κD)

open GeneratedFramingModels

/-- The actual generated J factory factors the whole weak original cotensor augmentation. -/
def cotensorFactor :
    letI := simplicialModel m
    MapFactorizationData ((trivialCofibrations (SimplicialObject C)).functorCategory C)
      ((fibrations (SimplicialObject C)).functorCategory C)
      (CompatibleCotensorFraming.originalAugmentation a d) := by
  let _ := simplicialModel m
  exact ((simplicialFibrantFactorizationData m).functorCategory C).factorizationData
    (CompatibleCotensorFraming.originalAugmentation a d)

/-- The actual intermediate functor retains the full generated original factor record. -/
abbrev middleFrame : C ⥤ SimplicialObject C := by
  let _ := simplicialModel m
  exact (cotensorFactor a m d).Z

/-- The full actual intermediate coaugmentation is the original J factor's left map. -/
def middleAugmentation : SimplicialObject.const C ⟶ middleFrame a m d := by
  let _ := simplicialModel m
  exact (cotensorFactor a m d).i

/-- The full actual map to the original cotensor frame is the same generated right factor. -/
def cotensorProjection : middleFrame a m d ⟶ CompatibleCotensorFraming.originalResolution a d := by
  let _ := simplicialModel m
  exact (cotensorFactor a m d).p

/-- The complete original generated factor equation retains the weak cotensor augmentation. -/
theorem cotensorFactor_fac :
    middleAugmentation a m d ≫ cotensorProjection a m d =
      CompatibleCotensorFraming.originalAugmentation a d := by
  let _ := simplicialModel m
  exact (cotensorFactor a m d).fac

/-- Every actual intermediate coaugmentation is a true model trivial cofibration. -/
theorem middleAugmentation_trivialCofibration (Y : C) :
    letI := simplicialModel m
    trivialCofibrations (SimplicialObject C) ((middleAugmentation a m d).app Y) := by
  let _ := simplicialModel m
  exact (cotensorFactor a m d).hi Y

/-- Every actual original cotensor augmentation is weak in the selected actual Reedy model. -/
theorem cotensorAugmentation_model_weak (Y : C) :
    letI := simplicialModel m
    WeakEquivalence ((CompatibleCotensorFraming.originalAugmentation a d).app Y) := by
  let _ := simplicialModel m
  apply (weakEquivalence_iff _).mpr
  change ∀ j,
      weakEquivalences C (((CompatibleCotensorFraming.originalAugmentation a d).app Y).app j)
  intro j
  let _ : WeakEquivalence (((CompatibleCotensorFraming.originalAugmentation a d).app Y).app j) :=
    CompatibleCotensorFraming.originalAugmentation_weak a d Y j
  exact mem_weakEquivalences _

/-- The same generated projection is weak by the actual factor equation and original augmentation
weakness. -/
theorem cotensorProjection_model_weak (Y : C) :
    letI := simplicialModel m
    WeakEquivalence ((cotensorProjection a m d).app Y) := by
  let _ := simplicialModel m
  let _ : WeakEquivalence ((middleAugmentation a m d).app Y) :=
    (weakEquivalence_iff _).mpr (middleAugmentation_trivialCofibration a m d Y).2
  let _ : WeakEquivalence ((CompatibleCotensorFraming.originalAugmentation a d).app Y) :=
    cotensorAugmentation_model_weak a m d Y
  exact weakEquivalence_of_precomp_of_fac
    (congrArg (fun t ↦ t.app Y) (cotensorFactor_fac a m d))

/-- The original generated projection is an actual model trivial fibration. -/
theorem cotensorProjection_trivialFibration (Y : C) :
    letI := simplicialModel m
    trivialFibrations (SimplicialObject C) ((cotensorProjection a m d).app Y) := by
  let _ := simplicialModel m
  exact
      ⟨(cotensorFactor a m d).hp Y,
      (weakEquivalence_iff _).mp (cotensorProjection_model_weak a m d Y)⟩

/-- The actual intermediate frame is fibrant through its original projection to the genuine cotensor
frame. -/
theorem middleFrame_isFibrant (Y : C) :
    letI := simplicialModel m
    IsFibrant ((middleFrame a m d).obj Y) := by
  let _ := simplicialModel m
  let _ : IsFibrant ((CompatibleCotensorFraming.originalResolution a d).obj Y) :=
    CompatibleCotensorFraming.originalResolution_model_isFibrant a m d Y
  let _ : Fibration ((cotensorProjection a m d).app Y) :=
    (fibration_iff _).mpr ((cotensorFactor a m d).hp Y)
  exact isFibrant_of_fibration ((cotensorProjection a m d).app Y)

/-- The actual original RF augmentation and true intermediate augmentation form the whole functorial
pushout. -/
def center : C ⥤ SimplicialObject C :=
  pushout (FunctorialFramings.coaugmentation (fromGeneration d)) (middleAugmentation a m d)

/-- The first actual pushout leg retains the same original RF functor. -/
abbrev centerRF : FunctorialFramings.rightFrame (fromGeneration d) ⟶ center a m d :=
  pushout.inl (FunctorialFramings.coaugmentation (fromGeneration d)) (middleAugmentation a m d)

/-- The second actual pushout leg retains the same actual intermediate functor. -/
abbrev centerMiddle : middleFrame a m d ⟶ center a m d :=
  pushout.inr (FunctorialFramings.coaugmentation (fromGeneration d)) (middleAugmentation a m d)

/-- Every actual first pushout leg is a model trivial cofibration from the genuine intermediate
augmentation. -/
theorem centerRF_trivialCofibration (Y : C) :
    letI := simplicialModel m
    trivialCofibrations (SimplicialObject C) ((centerRF a m d).app Y) := by
  let _ := simplicialModel m
  have h := ((trivialCofibrations (SimplicialObject C)).functorCategory C).pushout_inl
    (FunctorialFramings.coaugmentation (fromGeneration d)) (middleAugmentation a m d)
    (fun Z ↦ middleAugmentation_trivialCofibration a m d Z)
  exact h Y

/-- Every actual second pushout leg is a model trivial cofibration from the original RF
augmentation. -/
theorem centerMiddle_trivialCofibration (Y : C) :
    letI := simplicialModel m
    trivialCofibrations (SimplicialObject C) ((centerMiddle a m d).app Y) := by
  let _ := simplicialModel m
  have h := ((trivialCofibrations (SimplicialObject C)).functorCategory C).pushout_inr
    (FunctorialFramings.coaugmentation (fromGeneration d)) (middleAugmentation a m d)
    (fun Z ↦ coaugmentation_model_trivialCofibration m d Z)
  exact h Y

/-- The actual original terminal natural map of the full pushout functor. -/
def centerTerminal :
    letI := simplicialModel m
    center a m d ⟶ (Functor.const C).obj (⊤_ (SimplicialObject C)) := by
  let _ := simplicialModel m
  exact { app Y := terminal.from ((center a m d).obj Y), naturality _ _ _ := by simp }

/-- The same actual original generated J factory factors the whole terminal natural map. -/
def terminalFactor :
    letI := simplicialModel m
    MapFactorizationData ((trivialCofibrations (SimplicialObject C)).functorCategory C)
      ((fibrations (SimplicialObject C)).functorCategory C) (centerTerminal a m d) := by
  let _ := simplicialModel m
  exact ((simplicialFibrantFactorizationData m).functorCategory C).factorizationData
      (centerTerminal a m d)

/-- The actual common fibrant frame retains the original full terminal factor middle. -/
abbrev commonFrame : C ⥤ SimplicialObject C := by
  let _ := simplicialModel m
  exact (terminalFactor a m d).Z

/-- The original RF comparison is its actual pushout leg followed by the original terminal factor
map. -/
def fromRF : FunctorialFramings.rightFrame (fromGeneration d) ⟶ commonFrame a m d := by
  let _ := simplicialModel m
  exact centerRF a m d ≫ (terminalFactor a m d).i

/-- The actual intermediate comparison is its original pushout leg followed by the same terminal
factor map. -/
def fromMiddle : middleFrame a m d ⟶ commonFrame a m d := by
  let _ := simplicialModel m
  exact centerMiddle a m d ≫ (terminalFactor a m d).i

/-- Every original RF comparison is a genuine actual model trivial cofibration. -/
theorem fromRF_trivialCofibration (Y : C) :
    letI := simplicialModel m
    trivialCofibrations (SimplicialObject C) ((fromRF a m d).app Y) := by
  let _ := simplicialModel m
  exact (trivialCofibrations (SimplicialObject C)).comp_mem _ _
    (centerRF_trivialCofibration a m d Y) ((terminalFactor a m d).hi Y)

/-- Every actual intermediate comparison is a genuine model trivial cofibration. -/
theorem fromMiddle_trivialCofibration (Y : C) :
    letI := simplicialModel m
    trivialCofibrations (SimplicialObject C) ((fromMiddle a m d).app Y) := by
  let _ := simplicialModel m
  exact (trivialCofibrations (SimplicialObject C)).comp_mem _ _
    (centerMiddle_trivialCofibration a m d Y) ((terminalFactor a m d).hi Y)

/-- Every actual common frame object is genuinely fibrant by its original terminal factor map. -/
theorem commonFrame_isFibrant (Y : C) :
    letI := simplicialModel m
    IsFibrant ((commonFrame a m d).obj Y) := by
  let _ := simplicialModel m
  exact (isFibrant_iff_of_isTerminal ((terminalFactor a m d).p.app Y) terminalIsTerminal).mpr
    ((fibration_iff _).mpr ((terminalFactor a m d).hp Y))

/-- The two actual original augmentations retain the same full common-frame word. -/
theorem commonAugmentation_eq :
    FunctorialFramings.coaugmentation (fromGeneration d) ≫ fromRF a m d =
      middleAugmentation a m d ≫ fromMiddle a m d := by
  let _ := simplicialModel m
  change _ ≫ (_ ≫ (terminalFactor a m d).i) = _ ≫ (_ ≫ (terminalFactor a m d).i)
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (fun t : SimplicialObject.const C ⟶ center a m d ↦ t ≫ (terminalFactor a m d).i)
    (pushout.condition (f := FunctorialFramings.coaugmentation (fromGeneration d)) (g :=
      middleAugmentation a m d))

/-- Every original cotensor augmentation coordinate retains the same generated factor equation and
original rY word. -/
theorem cotensorFactor_fac_app (Y : C) (n : SimplexCategoryᵒᵖ) :
    ((middleAugmentation a m d).app Y).app n ≫ ((cotensorProjection a m d).app Y).app n =
      (GeneratedFunctorialReplacements.unit d).app Y ≫ CompatibleCotensorFraming.zeroUnit a
        ((GeneratedFunctorialReplacements.R d).obj Y) ≫
        (a.cotensor.map (SSet.StandardSimplexWeakMaps.collapse n.unop).op).app
          ((GeneratedFunctorialReplacements.R d).obj Y) := by
  have h := congrArg (fun t ↦ (t.app Y).app n) (cotensorFactor_fac a m d)
  exact h.trans (CompatibleCotensorFraming.originalAugmentation_app a d Y n)

end HomotopicalAlgebra.CompatibleRightMappingComparison

end
end
end

section



/-!
# Actual natural weak mapping zigzag with the original constant Q source

The mapping construction retains every original Q source and every original
target natural map. The three actual frame legs give weak mapping maps from
the fixed genuine constant-Q cofibrant source to fibrant targets. Original
represented-Hom isomorphisms retain both complete simplex functions.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe wM wD uC vC

open CategoryTheory Limits Opposite
open scoped MonoidalCategory SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CompatibleRightMappingComparison

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
  (d : CofibrantGenerationData C κD)

open GeneratedFunctorialReplacements GeneratedFramingModels

/-- The genuine mapping functor keeps the same original constant-Q source in every target diagram.
-/
def mappingFunctor : (C ⥤ SimplicialObject C) ⥤ Cᵒᵖ ⥤ C ⥤ SSet.{vC} :=
  Functor.whiskeringLeft C (SimplicialObject C) SSet.{vC} ⋙
    (Functor.whiskeringLeft Cᵒᵖ (SimplicialObject C ⥤ SSet.{vC}) (C ⥤ SSet.{vC})).obj
      ((Q d ⋙ SimplicialObject.const C).op ⋙ SimplicialCategory.sHomFunctor (SimplicialObject C))

/-- The actual fixed original constant-Q mapping bifunctor of a supplied target functor. -/
abbrev mappingBifunctor (T : C ⥤ SimplicialObject C) : Cᵒᵖ ⥤ C ⥤ SSet.{vC} :=
  (mappingFunctor d).obj T

/-- Every target natural map gives the full original mapping natural transformation. -/
def mappingMap {T T' : C ⥤ SimplicialObject C} (f : T ⟶ T') :
    mappingBifunctor d T ⟶ mappingBifunctor d T' := (mappingFunctor d).map f

/-- Every mapping component is exactly the original native postcomposition map. -/
theorem mappingMap_app {T T' : C ⥤ SimplicialObject C} (f : T ⟶ T') (X Y : C) :
    ((mappingMap d f).app (op X)).app Y =
      ((SimplicialCategory.sHomFunctor (SimplicialObject C)).obj
        (op ((SimplicialObject.const C).obj ((Q d).obj X)))).map (f.app Y) := rfl

/-- Every original target-map composition is retained by the full natural mapping construction. -/
theorem mappingMap_comp {T T' T'' : C ⥤ SimplicialObject C} (f : T ⟶ T') (g : T' ⟶ T'') :
    mappingMap d (f ≫ g) = mappingMap d f ≫ mappingMap d g := (mappingFunctor d).map_comp f g

/-- Every original target identity is retained by the full natural mapping construction. -/
theorem mappingMap_id (T : C ⥤ SimplicialObject C) : mappingMap d (𝟙 T) =
    𝟙 (mappingBifunctor d T) :=
  (mappingFunctor d).map_id T

/-- The actual original represented-Hom isomorphism identifies the entire mapping bifunctor. -/
def representedIso (T : C ⥤ SimplicialObject C) :
    ResolutionHomComplex.ofFunctors (Q d ⋙ CosimplicialObject.const C) T ≅ mappingBifunctor d T :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (Q d).op
        (ResolutionHomComplex.CanonicalEnrichment.rightBifunctorIso (C := C)))
    ((Functor.whiskeringLeft C (SimplicialObject C) SSet.{vC}).obj T)

/-- Each represented comparison is the same original full forward and inverse Hom isomorphism. -/
theorem representedIso_app (T : C ⥤ SimplicialObject C) (X Y : C) :
    ((representedIso d T).app (op X)).app Y =
      ResolutionHomComplex.CanonicalEnrichment.rightIso ((Q d).obj X) (T.obj Y) := rfl

/-- Every original target map retains the whole represented comparison square. -/
theorem representedIso_naturality {T T' : C ⥤ SimplicialObject C} (f : T ⟶ T') (X Y : C) :
    ResolutionHomComplex.postcomp ((CosimplicialObject.const C).obj ((Q d).obj X)) (f.app Y) ≫
        (((representedIso d T').hom.app (op X)).app Y) =
      (((representedIso d T).hom.app (op X)).app Y) ≫ ((mappingMap d f).app (op X)).app Y :=
  ResolutionHomComplex.CanonicalEnrichment.rightIso_natural_target ((Q d).obj X) (f.app Y)

section CompatibleFrames

variable [SimplicialCategory C] (a : CompatibleSimplicialMapping.Action C)
  {κM : Cardinal.{wM}} [Fact κM.IsRegular] [OrderBot κM.ord.ToType]
  (m : CofibrantGenerationData C κM)


/-- The original RF branch of the full actual natural mapping zigzag. -/
def mappingRF (a : CompatibleSimplicialMapping.Action C)
    (m : CofibrantGenerationData C κM) (d : CofibrantGenerationData C κD) :
    mappingBifunctor d (FunctorialFramings.rightFrame (fromGeneration d)) ⟶
    mappingBifunctor d (commonFrame a m d) := mappingMap d (fromRF a m d)

/-- The actual intermediate branch of the full natural mapping zigzag to the common fibrant frame.
-/
def mappingMiddle (a : CompatibleSimplicialMapping.Action C)
    (m : CofibrantGenerationData C κM) (d : CofibrantGenerationData C κD) : mappingBifunctor d
        (middleFrame a m d) ⟶
    mappingBifunctor d (commonFrame a m d) := mappingMap d (fromMiddle a m d)

/-- The actual intermediate projection branch to the original compatible cotensor complex. -/
def mappingCotensor (a : CompatibleSimplicialMapping.Action C)
    (m : CofibrantGenerationData C κM) (d : CofibrantGenerationData C κD) : mappingBifunctor d
        (middleFrame a m d) ⟶
    mappingBifunctor d (CompatibleCotensorFraming.originalResolution a d) :=
  mappingMap d (cotensorProjection a m d)

/-- The original RF mapping branch is weak by the actual fixed-constant-Q target weak law. -/
theorem mappingRF_weak (a : CompatibleSimplicialMapping.Action C)
    (m : CofibrantGenerationData C κM) (d : CofibrantGenerationData C κD) (X Y : C) :
    WeakEquivalence (((mappingRF a m d).app (op X)).app Y) := by
  let _ := simplicialModel m
  have hw : WeakEquivalence ((fromRF a m d).app Y) :=
    (weakEquivalence_iff _).mpr (fromRF_trivialCofibration a m d Y).2
  exact ResolutionMappingWeakPreservation.postcomp_weak m
    ((SimplicialObject.const C).obj ((Q d).obj X)) ((fromRF a m d).app Y)
    (constant_Q_isCofibrant m d X) hw (rightFrame_isFibrant m d Y) (commonFrame_isFibrant a m d Y)

/-- The actual intermediate mapping branch is weak between genuine fibrant target frames. -/
theorem mappingMiddle_weak (a : CompatibleSimplicialMapping.Action C)
    (m : CofibrantGenerationData C κM) (d : CofibrantGenerationData C κD) (X Y : C) :
    WeakEquivalence (((mappingMiddle a m d).app (op X)).app Y) := by
  let _ := simplicialModel m
  have hw : WeakEquivalence ((fromMiddle a m d).app Y) :=
    (weakEquivalence_iff _).mpr (fromMiddle_trivialCofibration a m d Y).2
  exact ResolutionMappingWeakPreservation.postcomp_weak m
    ((SimplicialObject.const C).obj ((Q d).obj X)) ((fromMiddle a m d).app Y)
    (constant_Q_isCofibrant m d X) hw (middleFrame_isFibrant a m d Y)
        (commonFrame_isFibrant a m d Y)

/-- The original intermediate-to-cotensor projection gives the actual weak mapping branch. -/
theorem mappingCotensor_weak (a : CompatibleSimplicialMapping.Action C)
    (m : CofibrantGenerationData C κM) (d : CofibrantGenerationData C κD) (X Y : C) :
    WeakEquivalence (((mappingCotensor a m d).app (op X)).app Y) := by
  let _ := simplicialModel m
  exact ResolutionMappingWeakPreservation.postcomp_weak m
    ((SimplicialObject.const C).obj ((Q d).obj X)) ((cotensorProjection a m d).app Y)
    (constant_Q_isCofibrant m d X) (cotensorProjection_model_weak a m d Y)
    (middleFrame_isFibrant a m d Y)
        (CompatibleCotensorFraming.originalResolution_model_isFibrant a m d Y)

end CompatibleFrames

end HomotopicalAlgebra.CompatibleRightMappingComparison

end
end
end

section



/-!
# Entire original represented points along the actual right-frame weak zigzag

Every represented point uses the same original Q counit, input morphism, and
actual target augmentation. The generated J equation and functorial pushout
condition give whole simplicial-set point equations through all three legs.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe wM wD uC vC

open CategoryTheory Limits Opposite
open scoped MonoidalCategory SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CompatibleRightMappingComparison

open GeneratedFunctorialReplacements

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
  (d : CofibrantGenerationData C κD)

/-- An entire original represented point retains q, the input morphism, and the actual target
augmentation. -/
def augmentationPoint (T : C ⥤ SimplicialObject C) (au : SimplicialObject.const C ⟶ T)
    {X Y : C} (f : X ⟶ Y) : 𝟙_ SSet.{vC} ⟶ ((mappingBifunctor d T).obj (op X)).obj Y :=
  eHomEquiv SSet ((SimplicialObject.const C).map ((counit d).app X ≫ f) ≫ au.app Y)

/-- Every complete actual target map carries the original represented point to the composite
augmentation. -/
theorem augmentationPoint_map {T T' : C ⥤ SimplicialObject C}
    (au : SimplicialObject.const C ⟶ T) (g : T ⟶ T') {X Y : C} (f : X ⟶ Y) :
    augmentationPoint d T au f ≫ ((mappingMap d g).app (op X)).app Y =
      augmentationPoint d T' (au ≫ g) f := by
  change eHomEquiv SSet _ ≫ eHomWhiskerLeft SSet _ (g.app Y) = _
  rw [eHomEquiv_comp_eHomWhiskerLeft SSet (SimplicialObject C)]
  change eHomEquiv SSet _ = eHomEquiv SSet _
  rw [Category.assoc, NatTrans.comp_app]

/-- The whole represented point retains every original target-variable naturality square. -/
theorem augmentationPoint_naturality_target (T : C ⥤ SimplicialObject C)
    (au : SimplicialObject.const C ⟶ T) {X Y Y' : C} (f : X ⟶ Y) (g : Y ⟶ Y') :
    augmentationPoint d T au f ≫ ((mappingBifunctor d T).obj (op X)).map g =
      augmentationPoint d T au (f ≫ g) := by
  change eHomEquiv SSet _ ≫ eHomWhiskerLeft SSet _ (T.map g) = _
  rw [eHomEquiv_comp_eHomWhiskerLeft SSet (SimplicialObject C)]
  change eHomEquiv SSet _ = eHomEquiv SSet _
  congr 1
  change ((SimplicialObject.const C).map ((counit d).app X ≫ f) ≫ au.app Y) ≫ T.map g = _
  rw [Category.assoc, ← au.naturality g, ← Category.assoc, ← Functor.map_comp]
  exact congrArg (fun h ↦ (SimplicialObject.const C).map h ≫ au.app Y')
    (Category.assoc ((counit d).app X) f g)

/-- The whole represented point retains every original Q source-variable naturality square. -/
theorem augmentationPoint_naturality_source (T : C ⥤ SimplicialObject C)
    (au : SimplicialObject.const C ⟶ T) {X X' Y : C} (g : X' ⟶ X) (f : X ⟶ Y) :
    augmentationPoint d T au f ≫ (((mappingBifunctor d T).map g.op).app Y) =
      augmentationPoint d T au (g ≫ f) := by
  change eHomEquiv SSet _ ≫ eHomWhiskerRight SSet ((SimplicialObject.const C).map ((Q d).map g)) _ =
      _
  rw [eHomEquiv_comp_eHomWhiskerRight SSet (SimplicialObject C)]
  change eHomEquiv SSet _ = eHomEquiv SSet _
  congr 1
  rw [← Category.assoc, ← Functor.map_comp]
  exact congrArg (fun h ↦ (SimplicialObject.const C).map h ≫ au.app Y)
    ((counit d).naturality_assoc g f)

/-- Every scalar and operator coordinate is the same original q/input/augmentation arrow. -/
theorem augmentationPoint_simplex (T : C ⥤ SimplicialObject C)
    (au : SimplicialObject.const C ⟶ T) {X Y : C} (f : X ⟶ Y)
    (n k : SimplexCategoryᵒᵖ) (t : (𝟙_ SSet.{vC}).obj n) (g : n ⟶ k) :
    ((augmentationPoint d T au f).app n t).app k g =
      (counit d).app X ≫ f ≫ (au.app Y).app k := by
  change (((SimplicialObject.const C).map ((counit d).app X ≫ f)) ≫ au.app Y).app k = _
  exact Category.assoc _ _ _

/-- The original right-complex point is identified by the entire original represented comparison. -/
theorem rightPoint_represented {X Y : C} (f : X ⟶ Y) :
    GeneratedFrameEnrichmentComparison.rightPoint d f ≫
        (((representedIso d (FunctorialFramings.rightFrame (fromGeneration d))).hom.app (op X)).app
            Y) =
      augmentationPoint d (FunctorialFramings.rightFrame (fromGeneration d))
        (FunctorialFramings.coaugmentation (fromGeneration d)) f := by
  change (eHomEquiv SSet _ ≫
      (ResolutionHomComplex.CanonicalEnrichment.rightIso _ _).inv) ≫
        (ResolutionHomComplex.CanonicalEnrichment.rightIso _ _).hom = eHomEquiv SSet _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [GeneratedFramings.coaugmentation_core]
  with_unfolding_all rfl

section CompatibleFrames

variable [SimplicialCategory C]
  {κM : Cardinal.{wM}} [Fact κM.IsRegular] [OrderBot κM.ord.ToType]

/-- The actual generated common-augmentation triangle identifies the whole original RF and middle
points. -/
theorem point_common (a : CompatibleSimplicialMapping.Action C) (m : CofibrantGenerationData C κM)
    (d : CofibrantGenerationData C κD) {X Y : C} (f : X ⟶ Y) :
    augmentationPoint d (FunctorialFramings.rightFrame (fromGeneration d))
      (FunctorialFramings.coaugmentation (fromGeneration d)) f ≫
        ((mappingRF a m d).app (op X)).app Y =
      augmentationPoint d (middleFrame a m d) (middleAugmentation a m d) f ≫
        ((mappingMiddle a m d).app (op X)).app Y := by
  change _ ≫ ((mappingMap d (fromRF a m d)).app (op X)).app Y =
    _ ≫ ((mappingMap d (fromMiddle a m d)).app (op X)).app Y
  rw [augmentationPoint_map, augmentationPoint_map, commonAugmentation_eq]

/-- The actual original J factor equation carries the whole middle point to the original cotensor
point. -/
theorem point_cotensor (a : CompatibleSimplicialMapping.Action C) (m : CofibrantGenerationData C κM)
    (d : CofibrantGenerationData C κD) {X Y : C} (f : X ⟶ Y) :
    augmentationPoint d (middleFrame a m d) (middleAugmentation a m d) f ≫
        ((mappingCotensor a m d).app (op X)).app Y =
      augmentationPoint d (CompatibleCotensorFraming.originalResolution a d)
        (CompatibleCotensorFraming.originalAugmentation a d) f := by
  change _ ≫ ((mappingMap d (cotensorProjection a m d)).app (op X)).app Y = _
  rw [augmentationPoint_map, cotensorFactor_fac]

end CompatibleFrames

end HomotopicalAlgebra.CompatibleRightMappingComparison

end
end
end

section



/-!
# The original right mapping comparison in the same homotopy category of spaces

The three actual natural weak mapping maps become isomorphisms under the same
original simplicial-set localization. Their composite retains the original
right bifunctor, the generated intermediate and common frames, and the exact
cotensor calculation to the same mixed Q/R mapping bifunctor.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe wM wD uC vC

open CategoryTheory Limits Opposite
open scoped MonoidalCategory SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CompatibleRightMappingComparison

open HomotopyMappingSpaceCategory

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
  (d : CofibrantGenerationData C κD)

/-- The same original space localization acts on all original mapping bifunctors. -/
def localizationFunctor : (Cᵒᵖ ⥤ C ⥤ SSet.{vC}) ⥤ Cᵒᵖ ⥤ C ⥤ SpaceHo.{vC} :=
  (Functor.whiskeringRight Cᵒᵖ (C ⥤ SSet.{vC}) (C ⥤ SpaceHo.{vC})).obj
    ((Functor.whiskeringRight C SSet.{vC} SpaceHo.{vC}).obj localize)

/-- The entire original fixed-constant-Q mapping bifunctor under the same localization. -/
abbrev localMapping (T : C ⥤ SimplicialObject C) : Cᵒᵖ ⥤ C ⥤ SpaceHo.{vC} :=
  (localizationFunctor (C := C)).obj (mappingBifunctor d T)

/-- The same localization retains every complete original target natural map. -/
def localMappingMap {T T' : C ⥤ SimplicialObject C} (f : T ⟶ T') :
    localMapping d T ⟶ localMapping d T' :=
  (localizationFunctor (C := C)).map (mappingMap d f)

/-- Every component is the localization of the same entire original mapping map. -/
theorem localMappingMap_app {T T' : C ⥤ SimplicialObject C} (f : T ⟶ T') (X Y : C) :
    ((localMappingMap d f).app (op X)).app Y =
      localize.map (((mappingMap d f).app (op X)).app Y) := rfl

/-- A proved actual componentwise weak mapping map is inverted as a complete natural transformation.
-/
theorem localMappingMap_isIso {T T' : C ⥤ SimplicialObject C} (f : T ⟶ T')
    (hf : ∀ X Y : C, WeakEquivalence (((mappingMap d f).app (op X)).app Y)) :
    IsIso (localMappingMap d f) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro X
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro Y
  apply localize_isIso
  change weakEquivalences SSet.{vC} (((mappingMap d f).app X).app Y)
  exact (weakEquivalence_iff _).mp (hf X.unop Y)

section CompatibleFrames

variable [SimplicialCategory C]
  {κM : Cardinal.{wM}} [Fact κM.IsRegular] [OrderBot κM.ord.ToType]

/-- The original RF weak map supplies the actual whole localized natural isomorphism. -/
def rfIso (a : CompatibleSimplicialMapping.Action C) (m : CofibrantGenerationData C κM)
    (d : CofibrantGenerationData C κD) :
    localMapping d (FunctorialFramings.rightFrame (fromGeneration d)) ≅
        localMapping d (commonFrame a m d) := by
  let _ := localMappingMap_isIso d (fromRF a m d) (mappingRF_weak a m d)
  exact asIso (localMappingMap d (fromRF a m d))

/-- The actual intermediate weak map supplies the whole localized common-frame isomorphism. -/
def middleIso (a : CompatibleSimplicialMapping.Action C) (m : CofibrantGenerationData C κM)
    (d : CofibrantGenerationData C κD) :
    localMapping d (middleFrame a m d) ≅ localMapping d (commonFrame a m d) := by
  let _ := localMappingMap_isIso d (fromMiddle a m d) (mappingMiddle_weak a m d)
  exact asIso (localMappingMap d (fromMiddle a m d))

/-- The actual weak J projection supplies the entire localized cotensor isomorphism. -/
def cotensorIso (a : CompatibleSimplicialMapping.Action C) (m : CofibrantGenerationData C κM)
    (d : CofibrantGenerationData C κD) :
    localMapping d (middleFrame a m d) ≅
      localMapping d (CompatibleCotensorFraming.originalResolution a d) := by
  let _ := localMappingMap_isIso d (cotensorProjection a m d) (mappingCotensor_weak a m d)
  exact asIso (localMappingMap d (cotensorProjection a m d))

/-- The final target is exactly the same mixed original Q/R mapping bifunctor under the same
localization. -/
abbrev mixedLocalization : Cᵒᵖ ⥤ C ⥤ SpaceHo.{vC} :=
  (localizationFunctor (C := C)).obj (GeneratedDerivedMapping.bifunctor d)

/-- The actual weak zigzag and original cotensor calculation give the full original right
comparison. -/
def comparison (a : CompatibleSimplicialMapping.Action C) (m : CofibrantGenerationData C κM)
    (d : CofibrantGenerationData C κD) :
    GeneratedRightMappingEnrichment.bifunctor d ≅ mixedLocalization d :=
  (localizationFunctor (C := C)).mapIso (GeneratedFrameEnrichmentComparison.rightCanonicalIso d) ≪≫
    rfIso a m d ≪≫ (middleIso a m d).symm ≪≫ cotensorIso a m d ≪≫
      (localizationFunctor (C := C)).mapIso
        ((representedIso d (CompatibleCotensorFraming.originalResolution a d)).symm ≪≫
          CompatibleCotensorFraming.originalCalculation a d)

/-- Every actual RF localized branch retains the exact original full mapping arrow. -/
theorem rfIso_hom (a : CompatibleSimplicialMapping.Action C) (m : CofibrantGenerationData C κM)
    (d : CofibrantGenerationData C κD) :
    (rfIso a m d).hom = localMappingMap d (fromRF a m d) := rfl

/-- Every actual intermediate branch retains the exact original full mapping arrow. -/
theorem middleIso_hom (a : CompatibleSimplicialMapping.Action C) (m : CofibrantGenerationData C κM)
    (d : CofibrantGenerationData C κD) :
    (middleIso a m d).hom = localMappingMap d (fromMiddle a m d) := rfl

/-- Every actual projection branch retains the exact original full mapping arrow. -/
theorem cotensorIso_hom (a : CompatibleSimplicialMapping.Action C)
    (m : CofibrantGenerationData C κM)
    (d : CofibrantGenerationData C κD) :
    (cotensorIso a m d).hom = localMappingMap d (cotensorProjection a m d) := rfl

/-- The final comparison retains all original target maps as complete natural transformations. -/
theorem comparison_naturality_target (a : CompatibleSimplicialMapping.Action C)
    (m : CofibrantGenerationData C κM) (d : CofibrantGenerationData C κD)
    (X : C) {Y Y' : C} (f : Y ⟶ Y') :
    ((GeneratedRightMappingEnrichment.bifunctor d).obj (op X)).map f ≫
        (((comparison a m d).hom.app (op X)).app Y') =
      (((comparison a m d).hom.app (op X)).app Y) ≫
        ((mixedLocalization d).obj (op X)).map f :=
  ((comparison a m d).hom.app (op X)).naturality f

/-- The final inverse comparison retains every original target map. -/
theorem comparison_inverse_naturality_target (a : CompatibleSimplicialMapping.Action C)
    (m : CofibrantGenerationData C κM) (d : CofibrantGenerationData C κD)
    (X : C) {Y Y' : C} (f : Y ⟶ Y') :
    ((mixedLocalization d).obj (op X)).map f ≫
        (((comparison a m d).inv.app (op X)).app Y') =
      (((comparison a m d).inv.app (op X)).app Y) ≫
        ((GeneratedRightMappingEnrichment.bifunctor d).obj (op X)).map f :=
  ((comparison a m d).inv.app (op X)).naturality f

/-- The final comparison retains every original Q source map. -/
theorem comparison_naturality_source (a : CompatibleSimplicialMapping.Action C)
    (m : CofibrantGenerationData C κM) (d : CofibrantGenerationData C κD)
    {X X' : C} (f : X' ⟶ X) (Y : C) :
    (((GeneratedRightMappingEnrichment.bifunctor d).map f.op).app Y) ≫
        (((comparison a m d).hom.app (op X')).app Y) =
      (((comparison a m d).hom.app (op X)).app Y) ≫ (((mixedLocalization d).map f.op).app Y) :=
  congrArg (fun t ↦ t.app Y) ((comparison a m d).hom.naturality f.op)

/-- The final inverse comparison retains every original Q source map. -/
theorem comparison_inverse_naturality_source (a : CompatibleSimplicialMapping.Action C)
    (m : CofibrantGenerationData C κM) (d : CofibrantGenerationData C κD)
    {X X' : C} (f : X' ⟶ X) (Y : C) :
    (((mixedLocalization d).map f.op).app Y) ≫
        (((comparison a m d).inv.app (op X')).app Y) =
      (((comparison a m d).inv.app (op X)).app Y) ≫
        (((GeneratedRightMappingEnrichment.bifunctor d).map f.op).app Y) :=
  congrArg (fun t ↦ t.app Y) ((comparison a m d).inv.naturality f.op)

end CompatibleFrames

end HomotopicalAlgebra.CompatibleRightMappingComparison

end
end
end

section



/-!
# Original maps in both directions of the compatible right comparison

The comparison keeps every generated frame leg, the original represented-Hom
isomorphisms, and the same cotensor Q/R calculation. Both localized directions
and all native scalar/operator/source/target map formulas are retained.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe wM wD uC vC

open CategoryTheory Limits Opposite
open scoped MonoidalCategory SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CompatibleRightMappingComparison

open HomotopyMappingSpaceCategory GeneratedFunctorialReplacements

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
  (d : CofibrantGenerationData C κD)

/-- Every original source map is the native precomposition by the same Q arrow. -/
theorem mappingBifunctor_source (T : C ⥤ SimplicialObject C) {X X' : C}
    (f : X' ⟶ X) (Y : C) :
    (((mappingBifunctor d T).map f.op).app Y) =
      eHomWhiskerRight SSet ((SimplicialObject.const C).map ((Q d).map f)) (T.obj Y) := rfl

/-- Every original target map is native postcomposition by that same target functor arrow. -/
theorem mappingBifunctor_target (T : C ⥤ SimplicialObject C) (X : C) {Y Y' : C}
    (f : Y ⟶ Y') :
    ((mappingBifunctor d T).obj (op X)).map f =
      eHomWhiskerLeft SSet ((SimplicialObject.const C).obj ((Q d).obj X)) (T.map f) := rfl

/-- Each native frame comparison retains every scalar degree and original simplex operator
coordinate. -/
theorem mappingMap_simplex {T T' : C ⥤ SimplicialObject C} (f : T ⟶ T') (X Y : C)
    (n : SimplexCategoryᵒᵖ)
    (h : (Functor.functorHom ((SimplicialObject.const C).obj ((Q d).obj X)) (T.obj Y)).obj n)
    (k : SimplexCategoryᵒᵖ) (g : n ⟶ k) :
    ((((mappingMap d f).app (op X)).app Y).app n h).app k g = h.app k g ≫ (f.app Y).app k :=
  ResolutionHomComplex.CanonicalEnrichment.canonical_postcomp_app (f.app Y) n h k g

/-- Every full native mapping leg retains its actual source-variable naturality. -/
theorem mappingMap_naturality_source {T T' : C ⥤ SimplicialObject C} (f : T ⟶ T')
    {X X' : C} (g : X' ⟶ X) (Y : C) :
    (((mappingBifunctor d T).map g.op).app Y) ≫ (((mappingMap d f).app (op X')).app Y) =
      (((mappingMap d f).app (op X)).app Y) ≫ (((mappingBifunctor d T').map g.op).app Y) :=
  congrArg (fun t ↦ t.app Y) ((mappingMap d f).naturality g.op)

/-- Every full native mapping leg retains its actual target-variable naturality. -/
theorem mappingMap_naturality_target {T T' : C ⥤ SimplicialObject C} (f : T ⟶ T')
    (X : C) {Y Y' : C} (g : Y ⟶ Y') :
    ((mappingBifunctor d T).obj (op X)).map g ≫ (((mappingMap d f).app (op X)).app Y') =
      (((mappingMap d f).app (op X)).app Y) ≫ ((mappingBifunctor d T').obj (op X)).map g :=
  ((mappingMap d f).app (op X)).naturality g

/-- Every full native mapping leg retains each original simplex operator. -/
theorem mappingMap_naturality_simplex {T T' : C ⥤ SimplicialObject C} (f : T ⟶ T')
    (X Y : C) {n k : SimplexCategoryᵒᵖ} (g : n ⟶ k) :
    (((mappingBifunctor d T).obj (op X)).obj Y).map g ≫
        ((((mappingMap d f).app (op X)).app Y).app k) =
      ((((mappingMap d f).app (op X)).app Y).app n) ≫
        (((mappingBifunctor d T').obj (op X)).obj Y).map g :=
  (((mappingMap d f).app (op X)).app Y).naturality g

section CompatibleFrames

variable [SimplicialCategory C]
  {κM : Cardinal.{wM}} [Fact κM.IsRegular] [OrderBot κM.ord.ToType]

/-- The whole forward localized comparison contains precisely the original six comparison legs. -/
theorem comparison_hom (a : CompatibleSimplicialMapping.Action C) (m : CofibrantGenerationData C κM)
    (d : CofibrantGenerationData C κD) (X Y : C) :
    (((comparison a m d).hom.app (op X)).app Y) =
      localize.map
          ((((representedIso d (FunctorialFramings.rightFrame (fromGeneration d))).hom.app
          (op X)).app Y)) ≫
        (((rfIso a m d).hom.app (op X)).app Y) ≫
        (((middleIso a m d).inv.app (op X)).app Y) ≫
        (((cotensorIso a m d).hom.app (op X)).app Y) ≫
        localize.map ((((representedIso d
          (CompatibleCotensorFraming.originalResolution a d)).inv.app (op X)).app Y) ≫
          (((CompatibleCotensorFraming.originalCalculation a d).hom.app (op X)).app Y)) := by
  rfl

/-- The whole inverse localized comparison reverses precisely the same actual six comparison legs.
-/
theorem comparison_inv (a : CompatibleSimplicialMapping.Action C) (m : CofibrantGenerationData C κM)
    (d : CofibrantGenerationData C κD) (X Y : C) :
    (((comparison a m d).inv.app (op X)).app Y) =
      (((localize.map
          ((((CompatibleCotensorFraming.originalCalculation a d).inv.app (op X)).app Y) ≫
        (((representedIso d (CompatibleCotensorFraming.originalResolution a d)).hom.app (op X)).app
            Y)) ≫
        (((cotensorIso a m d).inv.app (op X)).app Y)) ≫
        (((middleIso a m d).hom.app (op X)).app Y)) ≫
        (((rfIso a m d).inv.app (op X)).app Y)) ≫
        localize.map
            ((((representedIso d (FunctorialFramings.rightFrame (fromGeneration d))).inv.app
            (op X)).app Y)) :=
  rfl

/-- The RF whole forward branch is exactly the localization of the original full generated leg. -/
theorem rfIso_hom_app (a : CompatibleSimplicialMapping.Action C) (m : CofibrantGenerationData C κM)
    (d : CofibrantGenerationData C κD) (X Y : C) :
    (((rfIso a m d).hom.app (op X)).app Y) =
      localize.map (((mappingMap d (fromRF a m d)).app (op X)).app Y) := rfl

/-- The middle whole forward branch is exactly the localization of its original full generated leg.
-/
theorem middleIso_hom_app (a : CompatibleSimplicialMapping.Action C)
    (m : CofibrantGenerationData C κM)
    (d : CofibrantGenerationData C κD) (X Y : C) :
    (((middleIso a m d).hom.app (op X)).app Y) =
      localize.map (((mappingMap d (fromMiddle a m d)).app (op X)).app Y) := rfl

/-- The cotensor whole forward branch is exactly the localization of the original full generated
projection. -/
theorem cotensorIso_hom_app (a : CompatibleSimplicialMapping.Action C)
    (m : CofibrantGenerationData C κM)
    (d : CofibrantGenerationData C κD) (X Y : C) :
    (((cotensorIso a m d).hom.app (op X)).app Y) =
      localize.map (((mappingMap d (cotensorProjection a m d)).app (op X)).app Y) := rfl

/-- The same actual RF weak map is inverted on every original localized component. -/
instance rfComponent_isIso (a : CompatibleSimplicialMapping.Action C)
    (m : CofibrantGenerationData C κM)
    (d : CofibrantGenerationData C κD) (X Y : C) :
    IsIso (localize.map (((mappingMap d (fromRF a m d)).app (op X)).app Y)) := by
  apply localize_isIso
  exact (weakEquivalence_iff _).mp (mappingRF_weak a m d X Y)

/-- The same actual middle weak map is inverted on every original localized component. -/
instance middleComponent_isIso (a : CompatibleSimplicialMapping.Action C)
    (m : CofibrantGenerationData C κM)
    (d : CofibrantGenerationData C κD) (X Y : C) :
    IsIso (localize.map (((mappingMap d (fromMiddle a m d)).app (op X)).app Y)) := by
  apply localize_isIso
  exact (weakEquivalence_iff _).mp (mappingMiddle_weak a m d X Y)

/-- The same actual J projection is inverted on every original localized component. -/
instance cotensorComponent_isIso (a : CompatibleSimplicialMapping.Action C)
    (m : CofibrantGenerationData C κM)
    (d : CofibrantGenerationData C κD) (X Y : C) :
    IsIso (localize.map (((mappingMap d (cotensorProjection a m d)).app (op X)).app Y)) := by
  apply localize_isIso
  exact (weakEquivalence_iff _).mp (mappingCotensor_weak a m d X Y)

/-- Every inverse RF component is the actual inverse of that same localized original mapping leg. -/
theorem rfIso_inv_app (a : CompatibleSimplicialMapping.Action C) (m : CofibrantGenerationData C κM)
    (d : CofibrantGenerationData C κD) (X Y : C) :
    (((rfIso a m d).inv.app (op X)).app Y) =
      inv (localize.map (((mappingMap d (fromRF a m d)).app (op X)).app Y)) :=
 by
  exact @IsIso.eq_inv_of_hom_inv_id SpaceHo.{vC} _ _ _
    (localize.map (((mappingMap d (fromRF a m d)).app (op X)).app Y))
    (rfComponent_isIso a m d X Y) _
    ((((rfIso a m d).app (op X)).app Y).hom_inv_id)

/-- Every inverse middle component is the actual inverse of the same localized original mapping leg.
-/
theorem middleIso_inv_app (a : CompatibleSimplicialMapping.Action C)
    (m : CofibrantGenerationData C κM)
    (d : CofibrantGenerationData C κD) (X Y : C) :
    (((middleIso a m d).inv.app (op X)).app Y) =
      inv (localize.map (((mappingMap d (fromMiddle a m d)).app (op X)).app Y)) :=
 by
  exact @IsIso.eq_inv_of_hom_inv_id SpaceHo.{vC} _ _ _
    (localize.map (((mappingMap d (fromMiddle a m d)).app (op X)).app Y))
    (middleComponent_isIso a m d X Y) _
    ((((middleIso a m d).app (op X)).app Y).hom_inv_id)

/-- Every inverse cotensor component is the actual inverse of the same localized original J
projection. -/
theorem cotensorIso_inv_app (a : CompatibleSimplicialMapping.Action C)
    (m : CofibrantGenerationData C κM)
    (d : CofibrantGenerationData C κD) (X Y : C) :
    (((cotensorIso a m d).inv.app (op X)).app Y) =
      inv (localize.map (((mappingMap d (cotensorProjection a m d)).app (op X)).app Y)) :=
 by
  exact @IsIso.eq_inv_of_hom_inv_id SpaceHo.{vC} _ _ _
    (localize.map (((mappingMap d (cotensorProjection a m d)).app (op X)).app Y))
    (cotensorComponent_isIso a m d X Y) _
    ((((cotensorIso a m d).app (op X)).app Y).hom_inv_id)

end CompatibleFrames

end HomotopicalAlgebra.CompatibleRightMappingComparison

end
end
end

section



/-!
# Whole represented-point transport through the actual localized weak zigzag

The generated J factor equation and common-frame pushout equation identify the
entire original represented point through the three actual localized weak
legs. The inverse of the middle branch is the actual inverse from localization.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe wM wD uC vC

open CategoryTheory Limits Opposite
open scoped MonoidalCategory SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CompatibleRightMappingComparison

open HomotopyMappingSpaceCategory

private theorem point_inverse {D : Type*} [Category D] {P A B E : D}
    (s : P ⟶ A) (f : A ⟶ E) (t : P ⟶ B) (e : B ≅ E)
    (h : s ≫ f = t ≫ e.hom) : s ≫ f ≫ e.inv = t := by
  rw [← Category.assoc, h, Category.assoc, e.hom_inv_id, Category.comp_id]

private theorem point_pasting {D : Type*} [Category D] {P A B E F G : D}
    (f₀ : P ⟶ A) (f₁ : A ⟶ B) (f₂ : B ⟶ E) (f₃ : E ⟶ F) (f₄ : F ⟶ G)
    (s : P ⟶ B) (t : P ⟶ F) (u : P ⟶ G)
    (h₀ : f₀ ≫ f₁ = s) (h₁ : s ≫ f₂ ≫ f₃ = t) (h₂ : t ≫ f₄ = u) :
    f₀ ≫ f₁ ≫ f₂ ≫ f₃ ≫ f₄ = u := by
  rw [← Category.assoc f₀ f₁, h₀, ← Category.assoc _ _ f₄,
    ← Category.assoc _ _ f₄, h₁, h₂]

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [SimplicialCategory C]
  (a : CompatibleSimplicialMapping.Action C)
  {κM : Cardinal.{wM}} [Fact κM.IsRegular] [OrderBot κM.ord.ToType]
  (m : CofibrantGenerationData C κM)
  {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
  (d : CofibrantGenerationData C κD)

/-- The actual whole common-frame point square persists under the same original localization. -/
theorem localized_point_common {X Y : C} (f : X ⟶ Y) :
    localize.map (augmentationPoint d (FunctorialFramings.rightFrame (fromGeneration d))
        (FunctorialFramings.coaugmentation (fromGeneration d)) f) ≫
            (((rfIso a m d).hom.app (op X)).app Y) =
      localize.map (augmentationPoint d (middleFrame a m d) (middleAugmentation a m d) f) ≫
        (((middleIso a m d).hom.app (op X)).app Y) := by
  exact (localize.map_comp _ _).symm.trans
    ((congrArg localize.map (point_common a m d f)).trans (localize.map_comp _ _))

/-- Inverting the actual middle weak branch retains the entire original represented point. -/
theorem localized_point_middle {X Y : C} (f : X ⟶ Y) :
    localize.map (augmentationPoint d (FunctorialFramings.rightFrame (fromGeneration d))
        (FunctorialFramings.coaugmentation (fromGeneration d)) f) ≫
            (((rfIso a m d).hom.app (op X)).app Y) ≫
        (((middleIso a m d).inv.app (op X)).app Y) =
      localize.map (augmentationPoint d (middleFrame a m d) (middleAugmentation a m d) f) := by
  exact point_inverse _ _ _ (((middleIso a m d).app (op X)).app Y) (localized_point_common a m d f)

/-- The original J factor triangle persists as the whole localized cotensor point equation. -/
theorem localized_point_cotensor {X Y : C} (f : X ⟶ Y) :
    localize.map (augmentationPoint d (middleFrame a m d) (middleAugmentation a m d) f) ≫
        (((cotensorIso a m d).hom.app (op X)).app Y) =
      localize.map (augmentationPoint d (CompatibleCotensorFraming.originalResolution a d)
        (CompatibleCotensorFraming.originalAugmentation a d) f) := by
  exact (localize.map_comp _ _).symm.trans (congrArg localize.map (point_cotensor a m d f))

/-- All four actual localized original-right-to-cotensor legs preserve the whole represented input
map. -/
theorem localized_rightPoint_to_cotensor {X Y : C} (f : X ⟶ Y) :
    localize.map (GeneratedFrameEnrichmentComparison.rightPoint d f) ≫
        localize.map
            ((((representedIso d (FunctorialFramings.rightFrame (fromGeneration d))).hom.app
            (op X)).app Y)) ≫
        (((rfIso a m d).hom.app (op X)).app Y) ≫
        (((middleIso a m d).inv.app (op X)).app Y) ≫
        (((cotensorIso a m d).hom.app (op X)).app Y) =
      localize.map (augmentationPoint d (CompatibleCotensorFraming.originalResolution a d)
        (CompatibleCotensorFraming.originalAugmentation a d) f) := by
  exact point_pasting _ _ _ _ _ _ _ _
    ((localize.map_comp _ _).symm.trans (congrArg localize.map (rightPoint_represented d f)))
    (localized_point_middle a m d f) (localized_point_cotensor a m d f)

end HomotopicalAlgebra.CompatibleRightMappingComparison

end
end
end

section



/-!
# The actual compatible right mapping comparison preserves entire original units

The actual natural weak zigzag, its genuine localized inverses, and the
original cotensor calculation carry every original q/input/r represented point
to the same mixed mapping point. In particular the entire original Ho(SSet)
enriched unit is carried to the localization of the same original q/r unit.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe wM wD uC vC

open CategoryTheory Limits Opposite
open scoped MonoidalCategory SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CompatibleRightMappingComparison

open HomotopyMappingSpaceCategory GeneratedFunctorialReplacements

private theorem point_final {D : Type*} [Category D] {P A B E F G H : D}
    (f₀ : P ⟶ A) (f₁ : A ⟶ B) (f₂ : B ⟶ E) (f₃ : E ⟶ F) (f₄ : F ⟶ G) (f₅ : G ⟶ H)
    (s : P ⟶ G) (t : P ⟶ H)
    (h₀ : f₀ ≫ f₁ ≫ f₂ ≫ f₃ ≫ f₄ = s) (h₁ : s ≫ f₅ = t) :
    f₀ ≫ f₁ ≫ f₂ ≫ f₃ ≫ f₄ ≫ f₅ = t := by
  rw [← Category.assoc _ _ f₅, ← Category.assoc _ _ f₅,
    ← Category.assoc _ _ f₅, ← Category.assoc _ _ f₅, h₀, h₁]

private theorem point_inverse_original_comparison {D : Type*} [Category D] {P A B : D}
    (s : P ⟶ A) (t : P ⟶ B) (e : A ≅ B) (h : s ≫ e.hom = t) : t ≫ e.inv = s := by
  rw [← h, Category.assoc, e.hom_inv_id, Category.comp_id]

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [SimplicialCategory C]
  (a : CompatibleSimplicialMapping.Action C)
  {κM : Cardinal.{wM}} [Fact κM.IsRegular] [OrderBot κM.ord.ToType]
  (m : CofibrantGenerationData C κM)
  {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
  (d : CofibrantGenerationData C κD)

/-- The endpoint uses exactly the original cotensor point and original represented-Hom inverse. -/
theorem cotensorPoint_represented {X Y : C} (f : X ⟶ Y) :
    augmentationPoint d (CompatibleCotensorFraming.originalResolution a d)
        (CompatibleCotensorFraming.originalAugmentation a d) f ≫
        (((representedIso d (CompatibleCotensorFraming.originalResolution a d)).inv.app (op X)).app
            Y) =
      CompatibleCotensorMappingPoints.point a d f := rfl

/-- The complete actual comparison carries every entire original right point to the same mixed
q/input/r point. -/
theorem comparison_rightPoint {X Y : C} (f : X ⟶ Y) :
    localize.map (GeneratedFrameEnrichmentComparison.rightPoint d f) ≫
        (((comparison a m d).hom.app (op X)).app Y) =
      localize.map (eHomEquiv SSet ((counit d).app X ≫ f ≫ (unit d).app Y)) := by
  have hc : augmentationPoint d (CompatibleCotensorFraming.originalResolution a d)
        (CompatibleCotensorFraming.originalAugmentation a d) f ≫
        ((((representedIso d (CompatibleCotensorFraming.originalResolution a d)).inv.app (op X)).app
            Y) ≫
          (((CompatibleCotensorFraming.originalCalculation a d).hom.app (op X)).app Y)) =
      eHomEquiv SSet ((counit d).app X ≫ f ≫ (unit d).app Y) := by
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun p ↦ p ≫ (((CompatibleCotensorFraming.originalCalculation a d).hom.app
          (op X)).app Y)) (cotensorPoint_represented a d f)).trans
        (CompatibleCotensorMappingPoints.point_calculation a d f))
  exact (congrArg (fun k ↦ localize.map (GeneratedFrameEnrichmentComparison.rightPoint d f) ≫ k)
    (comparison_hom a m d X Y)).trans
    (point_final _ _ _ _ _ _ _ _ (localized_rightPoint_to_cotensor a m d f)
      ((localize.map_comp _ _).symm.trans (congrArg localize.map hc)))

/-- The actual inverse comparison carries the same entire mixed q/input/r point back to the original
right point. -/
theorem comparison_inverse_rightPoint {X Y : C} (f : X ⟶ Y) :
    localize.map (eHomEquiv SSet ((counit d).app X ≫ f ≫ (unit d).app Y)) ≫
        (((comparison a m d).inv.app (op X)).app Y) =
      localize.map (GeneratedFrameEnrichmentComparison.rightPoint d f) :=
  point_inverse_original_comparison _ _ (((comparison a m d).app (op X)).app Y)
      (comparison_rightPoint a m d f)

/-- The complete original enriched Ho-unit maps to the same actual q/r mixed unit under the same
localization. -/
theorem comparison_unit (X : C) :
    GeneratedRightMappingEnrichment.unit d X ≫ (((comparison a m d).hom.app (op X)).app X) =
      Functor.LaxMonoidal.ε localize ≫ localize.map (GeneratedDerivedMapping.mixedUnit d X) := by
  have hm : eHomEquiv SSet ((counit d).app X ≫ (𝟙 X) ≫ (unit d).app X) =
      GeneratedDerivedMapping.mixedUnit d X := by
    exact congrArg (fun h ↦ eHomEquiv SSet ((counit d).app X ≫ h))
      (Category.id_comp ((unit d).app X))
  exact (congrArg (fun p ↦ p ≫ (((comparison a m d).hom.app (op X)).app X))
      (GeneratedRightMappingEnrichment.unit_calculation d X)).trans
    ((Category.assoc (Functor.LaxMonoidal.ε localize)
        (localize.map (GeneratedFrameEnrichmentComparison.rightUnit d X))
        (((comparison a m d).hom.app (op X)).app X)).trans
      (congrArg (fun p ↦ Functor.LaxMonoidal.ε localize ≫ p)
        ((comparison_rightPoint a m d (𝟙 X)).trans (congrArg localize.map hm))))

/-- The true inverse comparison carries the same entire localized mixed unit back to the original
Ho-unit. -/
theorem comparison_inverse_unit (X : C) :
    (Functor.LaxMonoidal.ε localize ≫ localize.map (GeneratedDerivedMapping.mixedUnit d X)) ≫
        (((comparison a m d).inv.app (op X)).app X) = GeneratedRightMappingEnrichment.unit d X :=
  point_inverse_original_comparison _ _ (((comparison a m d).app (op X)).app X)
      (comparison_unit a m d X)

end HomotopicalAlgebra.CompatibleRightMappingComparison

end
end
end

section



/-!
# Compatible enriched calculations of the original homotopy function complex

The compatible external simplicial action identifies the original right
function complexes with the original mixed `Hom(QX, RY)` bifunctor. The genuine
natural isomorphism transports coherent composition to those same enriched
calculation objects, preserving the entire original units. At original
cofibrant/fibrant endpoints the same original `q` and `r` identify ordinary
enriched Hom with the original right function complex. The actual bifibrant
`RQ` presentation retains its original strict simplicial enrichment.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe wD wM u v

open CategoryTheory MonoidalCategory
open scoped Simplicial MonoidalCategory SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.GeneratedHomotopyMappingCalculation

variable {C : Type u} [Category.{v} C] [ModelCategory C] [SimplicialCategory C]
  (a : CompatibleSimplicialMapping.Action C)
  {κM : Cardinal.{wM}} [Fact κM.IsRegular] [OrderBot κM.ord.ToType]
  (m : CofibrantGenerationData C κM)
  {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
  (d : CofibrantGenerationData C κD)

open HomotopyMappingSpaceCategory GeneratedFunctorialReplacements

/-- The original right function complex is naturally the same mixed Q/R enriched calculation. -/
def calculation : GeneratedRightMappingEnrichment.bifunctor d ≅
    CompatibleRightMappingComparison.mixedLocalization d :=
  CompatibleRightMappingComparison.comparison a m d

/-- Coherent composition on the same original mixed enriched calculation objects. -/
@[instance_reducible]
def mixedEnrichment : EnrichedCategory SpaceHo.{v} C := by
  let _ : EnrichedCategory SpaceHo.{v} C := GeneratedRightMappingEnrichment.enrichment d
  exact EnrichedHomTransport.enrichedCategoryOnOriginalObjects
    (fun X Y => localize.obj (GeneratedDerivedMapping.space d X Y))
    (fun X Y => ((calculation a m d).app (.op X)).app Y)

/-- The transported enrichment retains the original mixed Q/R mapping space. -/
theorem mixedEnrichment_hom (X Y : C) :
    (mixedEnrichment a m d).Hom X Y = localize.obj (GeneratedDerivedMapping.space d X Y) := rfl

/-- The coherent mixed composition retains the same calculation objects. -/
def mixedComp (X Y Z : C) :
    localize.obj (GeneratedDerivedMapping.space d X Y) ⊗
        localize.obj (GeneratedDerivedMapping.space d Y Z) ⟶
      localize.obj (GeneratedDerivedMapping.space d X Z) :=
  (mixedEnrichment a m d).comp X Y Z

/-- The coherent mixed identity retains the same calculation object. -/
def mixedUnit (X : C) : 𝟙_ SpaceHo.{v} ⟶ localize.obj (GeneratedDerivedMapping.space d X X) :=
  (mixedEnrichment a m d).id X

/-- Every complete original comparison map is retained in the transported mixed composition. -/
theorem mixedComp_formula (X Y Z : C) : mixedComp a m d X Y Z =
    ((((calculation a m d).inv.app (.op X)).app Y) ⊗ₘ
        (((calculation a m d).inv.app (.op Y)).app Z)) ≫
      GeneratedRightMappingEnrichment.comp d X Y Z ≫
        (((calculation a m d).hom.app (.op X)).app Z) := rfl

/-- The complete original mixed unit is the same localized q/r enriched point. -/
theorem mixedUnit_calculation (X : C) : mixedUnit a m d X =
    Functor.LaxMonoidal.ε localize ≫ localize.map (GeneratedDerivedMapping.mixedUnit d X) :=
  CompatibleRightMappingComparison.comparison_unit a m d X

/-- The whole natural comparison preserves the constructed coherent compositions. -/
theorem calculation_comp (X Y Z : C) :
    ((((calculation a m d).hom.app (.op X)).app Y) ⊗ₘ
        (((calculation a m d).hom.app (.op Y)).app Z)) ≫ mixedComp a m d X Y Z =
      GeneratedRightMappingEnrichment.comp d X Y Z ≫
        (((calculation a m d).hom.app (.op X)).app Z) := by
  have hXY : (((calculation a m d).hom.app (.op X)).app Y) ≫
      (((calculation a m d).inv.app (.op X)).app Y) =
        𝟙 (GeneratedRightMappingEnrichment.space d X Y) :=
    congrArg (fun t : GeneratedRightMappingEnrichment.bifunctor d ⟶
        GeneratedRightMappingEnrichment.bifunctor d => (t.app (.op X)).app Y)
      (calculation a m d).hom_inv_id
  have hYZ : (((calculation a m d).hom.app (.op Y)).app Z) ≫
      (((calculation a m d).inv.app (.op Y)).app Z) =
        𝟙 (GeneratedRightMappingEnrichment.space d Y Z) :=
    congrArg (fun t : GeneratedRightMappingEnrichment.bifunctor d ⟶
        GeneratedRightMappingEnrichment.bifunctor d => (t.app (.op Y)).app Z)
      (calculation a m d).hom_inv_id
  rw [mixedComp_formula, ← Category.assoc, ← Category.assoc, tensorHom_comp_tensorHom]
  rw [hXY, hYZ, id_tensorHom_id, Category.id_comp]

/-- The actual mixed calculation satisfies the coherent left identity law. -/
theorem mixedComp_leftUnit (X Y : C) :
    (λ_ (localize.obj (GeneratedDerivedMapping.space d X Y))).inv ≫
        mixedUnit a m d X ▷ _ ≫ mixedComp a m d X X Y =
      𝟙 (localize.obj (GeneratedDerivedMapping.space d X Y)) :=
  (mixedEnrichment a m d).id_comp X Y

/-- The actual mixed calculation satisfies the coherent right identity law. -/
theorem mixedComp_rightUnit (X Y : C) :
    (ρ_ (localize.obj (GeneratedDerivedMapping.space d X Y))).inv ≫
        _ ◁ mixedUnit a m d Y ≫ mixedComp a m d X Y Y =
      𝟙 (localize.obj (GeneratedDerivedMapping.space d X Y)) :=
  (mixedEnrichment a m d).comp_id X Y

/-- Coherent mixed associativity retains the actual associator and all four original inputs. -/
theorem mixedComp_assoc (W X Y Z : C) :
    (α_ (localize.obj (GeneratedDerivedMapping.space d W X))
        (localize.obj (GeneratedDerivedMapping.space d X Y))
        (localize.obj (GeneratedDerivedMapping.space d Y Z))).inv ≫
        mixedComp a m d W X Y ▷ _ ≫ mixedComp a m d W Y Z =
      _ ◁ mixedComp a m d X Y Z ≫ mixedComp a m d W X Z :=
  (mixedEnrichment a m d).assoc W X Y Z

include a in
/-- The complete original enriched endpoint map is inverted at cofibrant/fibrant endpoints. -/
theorem ordinary_map_isIso (X Y : C) [IsCofibrant X] [IsFibrant Y] :
    IsIso (localize.map (((GeneratedDerivedMapping.ordinaryToMixed d).app (.op X)).app Y)) := by
  apply localize_isIso
  change weakEquivalences SSet.{v} (((GeneratedDerivedMapping.ordinaryToMixed d).app (.op X)).app Y)
  exact (weakEquivalence_iff _).mp (GeneratedDerivedMapping.ordinaryToMixed_weak d a X Y)

/-- Ordinary enriched Hom computes the original function complex at the original suitable endpoints.
-/
def ordinaryCalculation (X Y : C) [IsCofibrant X] [IsFibrant Y] :
    localize.obj (SimplicialCategory.sHom X Y) ≅ GeneratedRightMappingEnrichment.space d X Y :=
  @asIso SpaceHo.{v} _ _ _
    (localize.map (((GeneratedDerivedMapping.ordinaryToMixed d).app (.op X)).app Y))
    (ordinary_map_isIso a d X Y) ≪≫ (((calculation a m d).app (.op X)).app Y).symm

/-- The full endpoint comparison uses the same q/r map and complete inverse compatible comparison.
-/
theorem ordinaryCalculation_hom (X Y : C) [IsCofibrant X] [IsFibrant Y] :
    (ordinaryCalculation a m d X Y).hom =
      localize.map (((GeneratedDerivedMapping.ordinaryToMixed d).app (.op X)).app Y) ≫
        (((calculation a m d).inv.app (.op X)).app Y) := rfl

/-- The genuine endpoint inverse retains the same entire original enriched comparison. -/
theorem ordinaryCalculation_inv (X Y : C) [IsCofibrant X] [IsFibrant Y] :
    (ordinaryCalculation a m d X Y).inv =
      (((calculation a m d).hom.app (.op X)).app Y) ≫
        @inv SpaceHo.{v} _ _ _
          (localize.map (((GeneratedDerivedMapping.ordinaryToMixed d).app (.op X)).app Y))
          (ordinary_map_isIso a d X Y) := rfl

/-- The complete endpoint calculation retains every original map between cofibrant sources. -/
theorem ordinaryCalculation_source {X X' : C} [IsCofibrant X] [IsCofibrant X']
    (f : X ⟶ X') (Y : C) [IsFibrant Y] :
    localize.map (((SimplicialCategory.sHomFunctor C).map f.op).app Y) ≫
        (ordinaryCalculation a m d X Y).hom =
      (ordinaryCalculation a m d X' Y).hom ≫ GeneratedRightMappingEnrichment.precomp d f Y := by
  have h := congrArg localize.map (GeneratedDerivedMapping.ordinaryToMixed_source_naturality d f Y)
  rw [Functor.map_comp, Functor.map_comp] at h
  have k := congrArg (fun t => t.app Y) ((calculation a m d).inv.naturality f.op)
  rw [ordinaryCalculation_hom, ordinaryCalculation_hom, ← Category.assoc, h, Category.assoc]
  exact (congrArg (fun t => localize.map
    (((GeneratedDerivedMapping.ordinaryToMixed d).app (.op X')).app Y) ≫ t) k).trans
      (Category.assoc _ _ _).symm

/-- The complete endpoint calculation retains every original map between fibrant targets. -/
theorem ordinaryCalculation_target (X : C) [IsCofibrant X]
    {Y Y' : C} [IsFibrant Y] [IsFibrant Y'] (f : Y ⟶ Y') :
    localize.map (((SimplicialCategory.sHomFunctor C).obj (.op X)).map f) ≫
        (ordinaryCalculation a m d X Y').hom =
      (ordinaryCalculation a m d X Y).hom ≫ GeneratedRightMappingEnrichment.postcomp d X f := by
  have h := congrArg localize.map (GeneratedDerivedMapping.ordinaryToMixed_target_naturality d X f)
  rw [Functor.map_comp, Functor.map_comp] at h
  have k := ((calculation a m d).inv.app (.op X)).naturality f
  rw [ordinaryCalculation_hom, ordinaryCalculation_hom, ← Category.assoc, h, Category.assoc]
  exact (congrArg (fun t => localize.map
    (((GeneratedDerivedMapping.ordinaryToMixed d).app (.op X)).app Y) ≫ t) k).trans
      (Category.assoc _ _ _).symm

/-- The entire inverse endpoint calculation retains every original cofibrant source map. -/
theorem ordinaryCalculation_inverse_source {X X' : C} [IsCofibrant X] [IsCofibrant X']
    (f : X ⟶ X') (Y : C) [IsFibrant Y] :
    GeneratedRightMappingEnrichment.precomp d f Y ≫ (ordinaryCalculation a m d X Y).inv =
      (ordinaryCalculation a m d X' Y).inv ≫
        localize.map (((SimplicialCategory.sHomFunctor C).map f.op).app Y) := by
  apply (cancel_mono (ordinaryCalculation a m d X Y).hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    ordinaryCalculation_source, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- The entire inverse endpoint calculation retains every original fibrant target map. -/
theorem ordinaryCalculation_inverse_target (X : C) [IsCofibrant X]
    {Y Y' : C} [IsFibrant Y] [IsFibrant Y'] (f : Y ⟶ Y') :
    GeneratedRightMappingEnrichment.postcomp d X f ≫ (ordinaryCalculation a m d X Y').inv =
      (ordinaryCalculation a m d X Y).inv ≫
        localize.map (((SimplicialCategory.sHomFunctor C).obj (.op X)).map f) := by
  apply (cancel_mono (ordinaryCalculation a m d X Y').hom).mp
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id, Category.assoc,
    ordinaryCalculation_target, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

/-- Every original enriched point is retained by the entire original enriched endpoint map. -/
theorem ordinaryPoint_to_mixed {X Y : C} (f : X ⟶ Y) :
    eHomEquiv SSet f ≫ (((GeneratedDerivedMapping.ordinaryToMixed d).app (.op X)).app Y) =
      eHomEquiv SSet ((counit d).app X ≫ f ≫ (unit d).app Y) := by
  rw [GeneratedDerivedMapping.ordinaryToMixed_app, ← Category.assoc,
    eHomEquiv_comp_eHomWhiskerLeft SSet C, eHomEquiv_comp_eHomWhiskerRight SSet C]

/-- The endpoint calculation retains every whole original represented morphism. -/
theorem ordinaryCalculation_point {X Y : C} [IsCofibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    localize.map (eHomEquiv SSet f) ≫ (ordinaryCalculation a m d X Y).hom =
      localize.map (GeneratedFrameEnrichmentComparison.rightPoint d f) := by
  rw [ordinaryCalculation_hom, ← Category.assoc, ← localize.map_comp, ordinaryPoint_to_mixed]
  exact CompatibleRightMappingComparison.comparison_inverse_rightPoint a m d f

/-- The genuine inverse endpoint calculation recovers the same entire original enriched point. -/
theorem ordinaryCalculation_inverse_point {X Y : C} [IsCofibrant X] [IsFibrant Y] (f : X ⟶ Y) :
    localize.map (GeneratedFrameEnrichmentComparison.rightPoint d f) ≫
        (ordinaryCalculation a m d X Y).inv = localize.map (eHomEquiv SSet f) := by
  rw [← ordinaryCalculation_point a m d f, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The whole ordinary enriched identity computes the same original coherent identity. -/
theorem ordinaryCalculation_unit (X : C) [IsCofibrant X] [IsFibrant X] :
    (Functor.LaxMonoidal.ε localize ≫ localize.map (eId SSet X)) ≫
        (ordinaryCalculation a m d X X).hom = GeneratedRightMappingEnrichment.unit d X := by
  rw [GeneratedRightMappingEnrichment.unit_calculation, Category.assoc]
  exact congrArg (fun f => Functor.LaxMonoidal.ε localize ≫ f)
    (by simpa only [eHomEquiv_id] using ordinaryCalculation_point a m d (𝟙 X))

include a in
/-- The actual original strict bifibrant presentation has a natural weak comparison to mixed Hom. -/
theorem strict_map_isIso (X Y : C) :
    IsIso (localize.map (((GeneratedDerivedMapping.strictToMixed d).app (.op X)).app Y)) := by
  apply localize_isIso
  change weakEquivalences SSet.{v} (((GeneratedDerivedMapping.strictToMixed d).app (.op X)).app Y)
  exact (weakEquivalence_iff _).mp (GeneratedDerivedMapping.strictToMixed_weak d a X Y)

/-- The original strict RQ enrichment presents the same original derived function-complex objects.
-/
def strictCalculation (X Y : C) :
    localize.obj (GeneratedDerivedMapping.strictSpace d X Y) ≅
      GeneratedRightMappingEnrichment.space d X Y :=
  @asIso SpaceHo.{v} _ _ _
    (localize.map (((GeneratedDerivedMapping.strictToMixed d).app (.op X)).app Y))
    (strict_map_isIso a d X Y) ≪≫ (((calculation a m d).app (.op X)).app Y).symm

/-- The entire original strict mapping bifunctor under the same genuine localization. -/
def strictHoBifunctor : Cᵒᵖ ⥤ C ⥤ SpaceHo.{v} :=
  (CompatibleRightMappingComparison.localizationFunctor (C := C)).obj
    (GeneratedDerivedMapping.strictBifunctor d)

/-- The original strict presentation compares naturally on all original source and target maps. -/
def strictBifunctorCalculation : strictHoBifunctor d ≅
    GeneratedRightMappingEnrichment.bifunctor d := by
  let t := (CompatibleRightMappingComparison.localizationFunctor (C := C)).map
    (GeneratedDerivedMapping.strictToMixed d)
  have ht : IsIso t := by
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro X
    apply (NatTrans.isIso_iff_isIso_app _).mpr
    intro Y
    exact strict_map_isIso a d X.unop Y
  exact @asIso _ _ _ _ t ht ≪≫ (calculation a m d).symm

/-- Every strict natural comparison component is the same entire original comparison. -/
theorem strictBifunctorCalculation_app (X Y : C) :
    ((strictBifunctorCalculation a m d).app (.op X)).app Y = strictCalculation a m d X Y := by
  apply Iso.ext
  rfl

/-- The strict original unit has exactly the entire original coherent unit as its comparison image.
-/
theorem strictCalculation_unit (X : C) :
    (Functor.LaxMonoidal.ε localize ≫ localize.map (GeneratedDerivedMapping.strictUnit d X)) ≫
        (strictCalculation a m d X X).hom = GeneratedRightMappingEnrichment.unit d X := by
  change (Functor.LaxMonoidal.ε localize ≫ localize.map (GeneratedDerivedMapping.strictUnit d X)) ≫
      (localize.map (((GeneratedDerivedMapping.strictToMixed d).app (.op X)).app X) ≫
        (((calculation a m d).inv.app (.op X)).app X)) = _
  calc
    _ = (Functor.LaxMonoidal.ε localize ≫ localize.map
        (GeneratedDerivedMapping.strictUnit d X ≫
          (((GeneratedDerivedMapping.strictToMixed d).app (.op X)).app X))) ≫
          (((calculation a m d).inv.app (.op X)).app X) := by
      simp only [Functor.map_comp, Category.assoc]
    _ = _ := by
      rw [GeneratedDerivedMapping.strictUnit_comparison]
      exact CompatibleRightMappingComparison.comparison_inverse_unit a m d X

/-- The compatible calculation from the same original source factory needs only that original data.
-/
def originalCalculation : GeneratedRightMappingEnrichment.bifunctor d ≅
    CompatibleRightMappingComparison.mixedLocalization d := calculation a d d

/-- The same original factory gives the compatible coherent enriched calculation. -/
@[instance_reducible]
def originalMixedEnrichment : EnrichedCategory SpaceHo.{v} C := mixedEnrichment a d d

/-- The original compatible endpoint calculation requires only the same original Q/R factory. -/
def originalEndpointCalculation (X Y : C) [IsCofibrant X] [IsFibrant Y] :
    localize.obj (SimplicialCategory.sHom X Y) ≅ GeneratedRightMappingEnrichment.space d X Y :=
  ordinaryCalculation a d d X Y

include a in
/-- Compatible enrichment supplies actual calculations and a genuine strict simplicial presentation.
-/
theorem compatibleDerivedMappingSpaces :
    Nonempty (GeneratedRightMappingEnrichment.bifunctor d ≅
      CompatibleRightMappingComparison.mixedLocalization d) ∧
    (∀ (X Y : C) [IsCofibrant X] [IsFibrant Y],
      Nonempty (localize.obj (SimplicialCategory.sHom X Y) ≅
        GeneratedRightMappingEnrichment.space d X Y)) ∧
    Nonempty (EnrichedCategory SpaceHo.{v} C) ∧ Nonempty (EnrichedCategory SSet.{v} C) :=
  ⟨⟨originalCalculation a d⟩, fun X Y _ _ => ⟨originalEndpointCalculation a d X Y⟩,
    ⟨originalMixedEnrichment a d⟩, ⟨GeneratedDerivedMapping.strictEnrichment d⟩⟩

end HomotopicalAlgebra.GeneratedHomotopyMappingCalculation

end
end
end
