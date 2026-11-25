/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Codex

module

public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedHomotopyFunctionComplex
public import MathlibExt.AlgebraicTopology.ModelCategory.FunctorialFramings
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenBrown
public import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyCategory
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import Mathlib.CategoryTheory.Adjunction.Mates
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.ULiftFibration

/-!
# The original right function complexes of a Quillen adjunction

The coefficient adjunction is applied to every original right-frame degree.
Its Reedy Quillen property is derived through the complete matching-corner
comparison. The common frame uses the original coaugmentations and generated
Reedy factorization, so neither a mapping-complex comparison nor a weak
comparison of frames is supplied as a premise.
-/

open HomotopicalAlgebra.GeneratedFunctorialReplacements

@[expose] public section

set_option autoImplicit false

noncomputable section

universe wC wD uC uD v

open CategoryTheory Limits MorphismProperty
open scoped SSet.modelCategoryQuillen
open scoped Simplicial

namespace HomotopicalAlgebra.QuillenFrameHomComplex

variable {C : Type uC} [Category.{v} C] [ModelCategory C]
  {D : Type uD} [Category.{v} D] [ModelCategory D]
  {κC : Cardinal.{wC}} [Fact κC.IsRegular] [OrderBot κC.ord.ToType]
  {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
  (dC : CofibrantGenerationData C κC) (dD : CofibrantGenerationData D κD)
  {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G) [adj.IsQuillenAdjunction]

open GeneratedFunctorialReplacements GeneratedFramings GeneratedFramingModels

/-- The whole original coefficient adjunction is Quillen on the actual generated right-frame
models. -/
theorem simplicial_isQuillenAdjunction :
    letI := simplicialModel dC
    letI := simplicialModel dD
    (adj.whiskerRight SimplexCategoryᵒᵖ).IsQuillenAdjunction := by
  let _ := simplicialModel dC
  let _ := simplicialModel dD
  let _ : G.IsRightAdjoint := ⟨L, ⟨adj⟩⟩
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesFibrations
  · intro X Y p hp
    rw [simplicial_fibrations_eq dD] at hp
    rw [simplicial_fibrations_eq dC]
    intro j
    exact ((fibrations C).arrow_mk_iso_iff
      (ReedyStructure.PostcomposeCorners.matchingArrowIso SimplexCategory.reedyOp G p j)).mp
        (Adjunction.IsQuillenAdjunction.preservesFibrations (adj := adj) _ (hp j))
  · intro X Y p hp
    rw [simplicial_trivialFibrations_eq dD] at hp
    rw [simplicial_trivialFibrations_eq dC]
    intro j
    exact ((trivialFibrations C).arrow_mk_iso_iff
      (ReedyStructure.PostcomposeCorners.matchingArrowIso SimplexCategory.reedyOp G p j)).mp
        (Adjunction.IsQuillenAdjunction.preservesTrivialFibrations (adj := adj) _ (hp j))

/-- The actual original D right frame after the unchanged right adjoint. -/
def imageRightFrame : D ⥤ SimplicialObject C :=
  FunctorialFramings.rightFrame (fromGeneration dD) ⋙ (Functor.whiskeringRight SimplexCategoryᵒᵖ
    D C).obj G

omit [ModelCategory C] in
/-- Every original image degree retains its actual coefficient object. -/
theorem imageRightFrame_obj (Y : D) (j : SimplexCategoryᵒᵖ) :
    ((imageRightFrame dD (G := G)).obj Y).obj j =
      G.obj (((rightFrame dD).obj Y).obj j) := rfl

omit [ModelCategory C] in
/-- Every original image degree map is the actual right-adjoint image of that frame map. -/
theorem imageRightFrame_map (Y : D) {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j) :
    ((imageRightFrame dD (G := G)).obj Y).map g =
      G.map (((rightFrame dD).obj Y).map g) := rfl

/-- The original full D coaugmentation is mapped degree by degree by the actual right adjoint. -/
def imageCoaugmentation : G ⋙ SimplicialObject.const C ⟶ imageRightFrame dD (G := G) where
  app Y :=
    { app j := G.map (((coaugmentation dD).app Y).app j)
      naturality i j g := by
        change 𝟙 (G.obj Y) ≫ G.map (((coaugmentation dD).app Y).app j) =
          G.map (((coaugmentation dD).app Y).app i) ≫ G.map (((rightFrame dD).obj Y).map g)
        rw [Category.id_comp, ← G.map_comp]
        exact G.congr_map (by simpa using (((coaugmentation dD).app Y).naturality g)) }
  naturality X Y f := by
    ext j
    change G.map f ≫ G.map (((coaugmentation dD).app Y).app j) =
      G.map (((coaugmentation dD).app X).app j) ≫ G.map (((rightFrame dD).map f).app j)
    rw [← G.map_comp, ← G.map_comp]
    exact G.congr_map (congrArg (fun q => q.app j) ((coaugmentation dD).naturality f))

omit [ModelCategory C] in
/-- Every original coaugmentation coordinate retains the original R unit and right-resolution
arrow. -/
theorem imageCoaugmentation_app (Y : D) (j : SimplexCategoryᵒᵖ) :
    ((imageCoaugmentation dD (G := G)).app Y).app j =
      G.map ((unit dD).app Y ≫ ((rightResolution dD).app Y).app j) := by
  change G.map (((coaugmentation dD).app Y).app j) = _
  rw [coaugmentation_app]

include adj in
/-- The original right adjoint sends every actual generated right frame to a Reedy-fibrant
diagram. -/
theorem imageRightFrame_isFibrant (Y : D) :
    letI := simplicialModel dC
    IsFibrant ((imageRightFrame dD (G := G)).obj Y) := by
  let _ := simplicialModel dC
  let _ := simplicialModel dD
  let _ := simplicial_isQuillenAdjunction dC dD adj
  exact Adjunction.IsQuillenAdjunction.preservesFibrantObjects
    (adj := adj.whiskerRight SimplexCategoryᵒᵖ) (rightFrame_isFibrant dD dD Y)

include adj in
/-- At a genuinely fibrant original target every mapped original coaugmentation is weak. -/
theorem imageCoaugmentation_weak (Y : D) [IsFibrant Y] :
    letI := simplicialModel dC
    weakEquivalences (SimplicialObject C) ((imageCoaugmentation dD (G := G)).app Y) := by
  let _ := simplicialModel dC
  rw [simplicial_weakEquivalences_eq dC]
  intro j
  let _ : IsFibrant (((SimplicialObject.const D).obj Y).obj j) := inferInstanceAs (IsFibrant Y)
  let _ : IsFibrant (((rightFrame dD).obj Y).obj j) :=
    RightFrameHornGeometry.degree_isFibrant _ (rightFrame_matching_fibration dD Y) j
  let _ : WeakEquivalence (((coaugmentation dD).app Y).app j) :=
    (weakEquivalence_iff _).mpr (coaugmentation_weak dD Y j)
  exact (weakEquivalence_iff _).mp
    (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := adj)
      (((coaugmentation dD).app Y).app j))

/-- The common frame starts with the actual functorial pushout of the two original
coaugmentations. -/
def center : D ⥤ SimplicialObject C :=
  pushout (Functor.whiskerLeft G (coaugmentation dC)) (imageCoaugmentation dD (G := G))

/-- The original canonical C-frame pushout leg. -/
abbrev centerLeft : G ⋙ rightFrame dC ⟶ center dC dD (G := G) :=
  pushout.inl (Functor.whiskerLeft G (coaugmentation dC)) (imageCoaugmentation dD (G := G))

/-- The original right-adjoint-image pushout leg. -/
abbrev centerRight : imageRightFrame dD (G := G) ⟶ center dC dD (G := G) :=
  pushout.inr (Functor.whiskerLeft G (coaugmentation dC)) (imageCoaugmentation dD (G := G))

/-- The unchanged canonical coaugmentation makes the complete image-frame leg a trivial
cofibration. -/
theorem centerRight_trivialCofibration (Y : D) :
    letI := simplicialModel dC
    trivialCofibrations (SimplicialObject C) ((centerRight dC dD (G := G)).app Y) := by
  let _ := simplicialModel dC
  have h : ((trivialCofibrations (SimplicialObject C)).functorCategory D)
      (centerRight dC dD (G := G)) :=
    ((trivialCofibrations (SimplicialObject C)).functorCategory D).pushout_inr
      (Functor.whiskerLeft G (coaugmentation dC)) (imageCoaugmentation dD (G := G))
      (fun X => coaugmentation_model_trivialCofibration dC dC (G.obj X))
  exact h Y

/-- The terminal natural arrow is factored by the same original generated Reedy factory. -/
def centerTerminal :
    letI := simplicialModel dC
    center dC dD (G := G) ⟶ (Functor.const D).obj (⊤_ (SimplicialObject C)) := by
  let _ := simplicialModel dC
  exact { app Y := terminal.from _, naturality _ _ _ := by simp }

/-- The full original functorial Reedy terminal factor, with every commuting source square
retained. -/
def factor :
    letI := simplicialModel dC
    MapFactorizationData ((trivialCofibrations (SimplicialObject C)).functorCategory D)
      ((fibrations (SimplicialObject C)).functorCategory D) (centerTerminal dC dD (G := G)) := by
  let _ := simplicialModel dC
  exact ((simplicialFibrantFactorizationData dC).functorCategory D).factorizationData
    (centerTerminal dC dD (G := G))

/-- The complete common right-frame functor is the actual middle of that original factor. -/
abbrev commonFrame : D ⥤ SimplicialObject C := by
  let _ := simplicialModel dC
  exact (factor dC dD (G := G)).Z

/-- The whole canonical C-frame comparison retains its actual pushout leg and factor map. -/
def comparisonLeft : G ⋙ rightFrame dC ⟶ commonFrame dC dD (G := G) := by
  let _ := simplicialModel dC
  exact centerLeft dC dD (G := G) ≫ (factor dC dD (G := G)).i

/-- The whole right-adjoint-frame comparison retains its actual pushout leg and factor map. -/
def comparisonRight : imageRightFrame dD (G := G) ⟶ commonFrame dC dD (G := G) := by
  let _ := simplicialModel dC
  exact centerRight dC dD (G := G) ≫ (factor dC dD (G := G)).i

/-- Both original coaugmentations have the same complete comparison word. -/
theorem coaugmentation_comparison :
    Functor.whiskerLeft G (coaugmentation dC) ≫ comparisonLeft dC dD (G := G) =
      imageCoaugmentation dD (G := G) ≫ comparisonRight dC dD (G := G) := by
  let _ := simplicialModel dC
  change _ ≫ (_ ≫ (factor dC dD (G := G)).i) = _ ≫ (_ ≫ (factor dC dD (G := G)).i)
  rw [← Category.assoc, ← Category.assoc]
  exact congrArg (fun q : G ⋙ SimplicialObject.const C ⟶ center dC dD (G := G) =>
    q ≫ (factor dC dD (G := G)).i)
      (pushout.condition (f := Functor.whiskerLeft G (coaugmentation dC))
        (g := imageCoaugmentation dD (G := G)))

/-- The actual image-frame comparison is a trivial cofibration in the original generated C Reedy
model. -/
theorem comparisonRight_trivialCofibration (Y : D) :
    letI := simplicialModel dC
    trivialCofibrations (SimplicialObject C) ((comparisonRight dC dD (G := G)).app Y) := by
  let _ := simplicialModel dC
  exact (trivialCofibrations (SimplicialObject C)).comp_mem _ _
    (centerRight_trivialCofibration dC dD Y) ((factor dC dD (G := G)).hi Y)

include adj in
/-- At each fibrant original target the same canonical C-frame comparison is weak by
two-out-of-three. -/
theorem comparisonLeft_weak (Y : D) [IsFibrant Y] :
    letI := simplicialModel dC
    weakEquivalences (SimplicialObject C) ((comparisonLeft dC dD (G := G)).app Y) := by
  let _ := simplicialModel dC
  apply (weakEquivalences (SimplicialObject C)).of_precomp
    ((Functor.whiskerLeft G (coaugmentation dC)).app Y) _
    (coaugmentation_model_trivialCofibration dC dC (G.obj Y)).2
  have h := congrArg (fun q => q.app Y) (coaugmentation_comparison dC dD (G := G))
  rw [NatTrans.comp_app, NatTrans.comp_app] at h
  rw [h]
  exact (weakEquivalences (SimplicialObject C)).comp_mem _ _
    (imageCoaugmentation_weak dC dD adj Y) (comparisonRight_trivialCofibration dC dD Y).2

/-- The original terminal factor supplies fibrancy of the whole common frame. -/
theorem commonFrame_isFibrant (Y : D) :
    letI := simplicialModel dC
    IsFibrant ((commonFrame dC dD (G := G)).obj Y) := by
  let _ := simplicialModel dC
  exact (isFibrant_iff_of_isTerminal ((factor dC dD (G := G)).p.app Y) terminalIsTerminal).mpr
    ((fibration_iff _).mpr ((factor dC dD (G := G)).hp Y))

variable {G' : D ⥤ C}

/-- A whole original right-adjoint transformation acts on every original right-frame coefficient. -/
def imageRightFrameMap (b : G ⟶ G') :
    imageRightFrame dD (G := G) ⟶ imageRightFrame dD (G := G') :=
  Functor.whiskerLeft (rightFrame dD)
    ((Functor.whiskeringRight SimplexCategoryᵒᵖ D C).map b)

omit [ModelCategory C] in
/-- Every original mate coefficient is retained in the original right-frame map. -/
theorem imageRightFrameMap_app (b : G ⟶ G') (Y : D) (j : SimplexCategoryᵒᵖ) :
    ((imageRightFrameMap dD b).app Y).app j = b.app (((rightFrame dD).obj Y).obj j) := rfl

omit [ModelCategory C] in
/-- The actual original D coaugmentation retains its whole original right-adjoint naturality
square. -/
theorem imageCoaugmentation_naturality (b : G ⟶ G') :
    imageCoaugmentation dD (G := G) ≫ imageRightFrameMap dD b =
      Functor.whiskerRight b (SimplicialObject.const C) ≫ imageCoaugmentation dD (G := G') := by
  ext Y j
  exact b.naturality (((coaugmentation dD).app Y).app j)

/-- The same two original coaugmentation squares induce the full original pushout map. -/
def centerMap (b : G ⟶ G') : center dC dD (G := G) ⟶ center dC dD (G := G') :=
  pushout.map
    (Functor.whiskerLeft G (coaugmentation dC)) (imageCoaugmentation dD (G := G))
    (Functor.whiskerLeft G' (coaugmentation dC)) (imageCoaugmentation dD (G := G'))
    (Functor.whiskerRight b (rightFrame dC)) (imageRightFrameMap dD b)
    (Functor.whiskerRight b (SimplicialObject.const C))
    (by
      ext Y j
      exact congrArg (fun q => q.app j) ((coaugmentation dC).naturality (b.app Y)).symm)
    (imageCoaugmentation_naturality dD b)

/-- The full original pushout map retains every original canonical-frame comparison. -/
theorem centerMap_left (b : G ⟶ G') :
    centerLeft dC dD (G := G) ≫ centerMap dC dD b =
      Functor.whiskerRight b (rightFrame dC) ≫ centerLeft dC dD (G := G') := by
  dsimp only [centerLeft, centerMap, pushout.map]
  exact pushout.inl_desc _ _ _

/-- The full original pushout map retains every original right-adjoint-frame comparison. -/
theorem centerMap_right (b : G ⟶ G') :
    centerRight dC dD (G := G) ≫ centerMap dC dD b =
      imageRightFrameMap dD b ≫ centerRight dC dD (G := G') := by
  dsimp only [centerRight, centerMap, pushout.map]
  exact pushout.inr_desc _ _ _

/-- The same original pushout map is a whole Arrow square of the original terminal maps. -/
def factorSquare (b : G ⟶ G') :
    letI := simplicialModel dC
    Arrow.mk (centerTerminal dC dD (G := G)) ⟶ Arrow.mk (centerTerminal dC dD (G := G')) := by
  let _ := simplicialModel dC
  exact Arrow.homMk (centerMap dC dD b)
    (𝟙 ((Functor.const D).obj (⊤_ (SimplicialObject C)))) (by
    apply NatTrans.ext
    funext Y
    dsimp only [NatTrans.comp_app, centerTerminal, NatTrans.id_app]
    exact terminalIsTerminal.hom_ext _ _)

/-- The original generated Reedy middle functor maps that entire original terminal square. -/
def commonFrameMap (b : G ⟶ G') : commonFrame dC dD (G := G) ⟶ commonFrame dC dD (G := G') := by
  let _ := simplicialModel dC
  exact ((simplicialFibrantFactorizationData dC).functorCategory D).Z.map (factorSquare dC dD b)

/-- Both complete original Reedy source factors retain their actual square map. -/
theorem factorSquare_i (b : G ⟶ G') :
    letI := simplicialModel dC
    centerMap dC dD b ≫ (factor dC dD (G := G')).i =
      (factor dC dD (G := G)).i ≫ commonFrameMap dC dD b := by
  let _ := simplicialModel dC
  exact ((simplicialFibrantFactorizationData dC).functorCategory D).i.naturality (factorSquare
    dC dD b)

/-- All original canonical C-frame comparison maps retain the same complete original mate square. -/
theorem comparisonLeft_naturality (b : G ⟶ G') :
    comparisonLeft dC dD (G := G) ≫ commonFrameMap dC dD b =
      Functor.whiskerRight b (rightFrame dC) ≫ comparisonLeft dC dD (G := G') := by
  let _ := simplicialModel dC
  change (centerLeft dC dD (G := G) ≫ (factor dC dD (G := G)).i) ≫ _ = _ ≫
    (centerLeft dC dD (G := G') ≫ (factor dC dD (G := G')).i)
  rw [Category.assoc, ← factorSquare_i, ← Category.assoc, centerMap_left, Category.assoc]

/-- All original right-adjoint-frame comparison maps retain the same complete original mate
square. -/
theorem comparisonRight_naturality (b : G ⟶ G') :
    comparisonRight dC dD (G := G) ≫ commonFrameMap dC dD b =
      imageRightFrameMap dD b ≫ comparisonRight dC dD (G := G') := by
  let _ := simplicialModel dC
  change (centerRight dC dD (G := G) ≫ (factor dC dD (G := G)).i) ≫ _ = _ ≫
    (centerRight dC dD (G := G') ≫ (factor dC dD (G := G')).i)
  rw [Category.assoc, ← factorSquare_i, ← Category.assoc, centerMap_right, Category.assoc]

end HomotopicalAlgebra.QuillenFrameHomComplex

namespace HomotopicalAlgebra.QuillenFrameHomComplex

section Algebraic

variable {C : Type uC} [Category.{v} C] {D : Type uD} [Category.{v} D]

/-- The original coefficient arrow gives the complete right-complex source map. -/
abbrev rightPrecomp {X X' : C} (f : X ⟶ X') (B : SimplicialObject C) :
    ResolutionHomComplex.right X' B ⟶ ResolutionHomComplex.right X B :=
  ResolutionHomComplex.precomp ((CosimplicialObject.const C).map f) B

/-- The original diagram arrow gives the complete right-complex target map. -/
abbrev rightPostcomp (X : C) {B B' : SimplicialObject C} (b : B ⟶ B') :
    ResolutionHomComplex.right X B ⟶ ResolutionHomComplex.right X B' :=
  ResolutionHomComplex.postcomp ((CosimplicialObject.const C).obj X) b

variable {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G)

/-- Every original right-frame degree is transposed through the same complete coefficient
adjunction. -/
def rightAdjunctionIso (X : C) (B : SimplicialObject D) :
    ResolutionHomComplex.right (L.obj X) B ≅ ResolutionHomComplex.right X (B ⋙ G) :=
  NatIso.ofComponents (fun n => (adj.homEquiv X (B.obj n)).toIso) (by
    intro n m g
    ext f
    change adj.homEquiv X (B.obj m) (𝟙 (L.obj X) ≫ f ≫ B.map g) =
      𝟙 X ≫ adj.homEquiv X (B.obj n) f ≫ G.map (B.map g)
    rw [Category.id_comp, Category.id_comp]
    exact adj.homEquiv_naturality_right f (B.map g))

/-- The complete original forward frame transpose is the actual Hom equivalence in each degree. -/
theorem rightAdjunctionIso_hom_app (X : C) (B : SimplicialObject D) (n : SimplexCategoryᵒᵖ)
    (f : L.obj X ⟶ B.obj n) :
    (rightAdjunctionIso adj X B).hom.app n f = adj.homEquiv X (B.obj n) f := rfl

/-- The complete original inverse frame transpose is the actual inverse Hom equivalence in each
degree. -/
theorem rightAdjunctionIso_inv_app (X : C) (B : SimplicialObject D) (n : SimplexCategoryᵒᵖ)
    (f : X ⟶ G.obj (B.obj n)) :
    (rightAdjunctionIso adj X B).inv.app n f = (adj.homEquiv X (B.obj n)).symm f := rfl

/-- Every original source arrow retains the complete original adjunction naturality square. -/
theorem rightAdjunctionIso_source {X X' : C} (f : X ⟶ X') (B : SimplicialObject D) :
    rightPrecomp (L.map f) B ≫ (rightAdjunctionIso adj X B).hom =
      (rightAdjunctionIso adj X' B).hom ≫ rightPrecomp f (B ⋙ G) := by
  ext n g
  exact adj.homEquiv_naturality_left f g

/-- Every original target-diagram arrow retains the complete original adjunction naturality
square. -/
theorem rightAdjunctionIso_target (X : C) {B B' : SimplicialObject D} (b : B ⟶ B') :
    rightPostcomp (L.obj X) b ≫ (rightAdjunctionIso adj X B').hom =
      (rightAdjunctionIso adj X B).hom ≫ rightPostcomp X (Functor.whiskerRight b G) := by
  ext n g
  exact adj.homEquiv_naturality_right g (b.app n)

variable {L₁ L₂ : C ⥤ D} {G₁ G₂ : D ⥤ C}

/-- The actual original left comparison is transposed to its whole original right mate on every
frame degree. -/
theorem rightMate_square (adj₁ : L₁ ⊣ G₁) (adj₂ : L₂ ⊣ G₂) (a : L₁ ⟶ L₂)
    (X : C) (B : SimplicialObject D) :
    rightPrecomp (a.app X) B ≫ (rightAdjunctionIso adj₁ X B).hom =
      (rightAdjunctionIso adj₂ X B).hom ≫
        rightPostcomp X (Functor.whiskerLeft B (conjugateEquiv adj₂ adj₁ a)) := by
  ext n f
  change L₂.obj X ⟶ B.obj n at f
  change adj₁.unit.app X ≫ G₁.map (a.app X ≫ f) =
    (adj₂.unit.app X ≫ G₂.map f) ≫ (conjugateEquiv adj₂ adj₁ a).app (B.obj n)
  rw [G₁.map_comp]
  conv_rhs =>
    rw [Category.assoc, (conjugateEquiv adj₂ adj₁ a).naturality f, ← Category.assoc]
  rw [unit_conjugateEquiv adj₂ adj₁ a]
  simp only [Category.assoc]

end Algebraic

section WeakPreservation

variable {C : Type uC} [Category.{v} C] [ModelCategory C]
  {κC : Cardinal.{wC}} [Fact κC.IsRegular] [OrderBot κC.ord.ToType]
  (dC : CofibrantGenerationData C κC)

open GeneratedFramingModels ResolutionHomComplex.CanonicalEnrichment

/-- The actual right-complex source map preserves weak maps of cofibrant sources into an original
fibrant frame. -/
theorem rightPrecomp_weak {X X' : C} (f : X ⟶ X') (B : SimplicialObject C) :
    letI := simplicialModel dC
    WeakEquivalence f → IsCofibrant X → IsCofibrant X' → IsFibrant B →
      WeakEquivalence (rightPrecomp f B) := by
  let _ := simplicialModel dC
  intro hf hX hX' hB
  let _ : WeakEquivalence f := hf
  have hnative : WeakEquivalence
      (((SimplicialCategory.sHomFunctor (SimplicialObject C)).map
        ((SimplicialObject.const C).map f).op).app B) :=
    ResolutionMappingWeakPreservation.precomp_weak dC _ _
      (constant_model_weak dC f (mem_weakEquivalences f))
      (constant_isCofibrant dC X hX) (constant_isCofibrant dC X' hX') hB
  exact (weakEquivalence_iff _).mpr
    (((weakEquivalences SSet.{v}).arrow_mk_iso_iff
      (Arrow.isoMk (rightIso X' B) (rightIso X B) (rightIso_natural_source f B).symm)).mpr
        ((weakEquivalence_iff _).mp hnative))

/-- The actual right-complex target map preserves weak maps between original fibrant frames. -/
theorem rightPostcomp_weak (X : C) {B B' : SimplicialObject C} (b : B ⟶ B') :
    letI := simplicialModel dC
    IsCofibrant X → WeakEquivalence b → IsFibrant B → IsFibrant B' →
      WeakEquivalence (rightPostcomp X b) := by
  let _ := simplicialModel dC
  intro hX hb hB hB'
  have hnative : WeakEquivalence
      (((SimplicialCategory.sHomFunctor (SimplicialObject C)).obj
        (.op ((SimplicialObject.const C).obj X))).map b) :=
    ResolutionMappingWeakPreservation.postcomp_weak dC _ b
      (constant_isCofibrant dC X hX) hb hB hB'
  exact (weakEquivalence_iff _).mpr
    (((weakEquivalences SSet.{v}).arrow_mk_iso_iff
      (Arrow.isoMk (rightIso X B) (rightIso X B') (rightIso_natural_target X b).symm)).mpr
        ((weakEquivalence_iff _).mp hnative))

end WeakPreservation

section HornLifting

variable {C : Type uC} [Category.{v} C] [ModelCategory C]

open Opposite RightFrameHornGeometry

/-- A whole original right-Hom horn square has the same complete original coefficient matching
square. -/
theorem coefficientHornSquareOfPrecomp {X X' : C} (i : X ⟶ X') (B : SimplicialObject C)
    (n : ℕ) (k : Fin (n + 2))
    (z : (SSet.horn.{v} (n + 1) k : SSet.{v}) ⟶ ResolutionHomComplex.right X' B)
    (b : (SSet.stdSimplex.obj ⦋n + 1⦌ : SSet.{v}) ⟶ ResolutionHomComplex.right X B)
    (sq : CommSq z (SSet.horn.{v} (n + 1) k).ι (rightPrecomp i B) b) :
    CommSq (SSet.yonedaEquiv b) i (PartialFaceMatching.hornMap B (n + 1) k)
      (hornHomMap X' B (n + 1) k z) := by
  let t : X ⟶ B.obj (op ⦋n + 1⦌) := SSet.yonedaEquiv b
  change CommSq t i (PartialFaceMatching.hornMap B (n + 1) k) (hornHomMap X' B (n + 1) k z)
  constructor
  apply limit.hom_ext
  intro a
  rw [Category.assoc, PartialFaceMatching.hornMap_π, Category.assoc, hornHomMap_π]
  have h := congrArg (fun q => q.app (SimplexCategory.PartialMatching.target a)
    (hornLabel (n + 1) k a)) sq.w
  change i ≫ z.app (SimplexCategory.PartialMatching.target a) (hornLabel (n + 1) k a) =
    b.app (SimplexCategory.PartialMatching.target a)
      (SSet.stdSimplex.objEquiv.symm (SimplexCategory.PartialMatching.arrow a).unop) at h
  have hb := homSimplex_app X B (n + 1) t k a
  have ht : homSimplex X B (n + 1) t = b := SSet.yonedaEquiv.symm_apply_apply b
  rw [ht] at hb
  exact hb.symm.trans h.symm

/-- The actual coefficient horn trivial fibration lifts the entire original right-Hom horn square.
-/
theorem rightPrecomp_horn_hasLift {X X' : C} (i : X ⟶ X') [Cofibration i] (B : SimplicialObject C)
    (hB : ∀ j, fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp B j))
    (hW : ∀ {a b : SimplexCategoryᵒᵖ} (g : a ⟶ b), weakEquivalences C (B.map g))
    (n : ℕ) (k : Fin (n + 2))
    (z : (SSet.horn.{v} (n + 1) k : SSet.{v}) ⟶ ResolutionHomComplex.right X' B)
    (b : (SSet.stdSimplex.obj ⦋n + 1⦌ : SSet.{v}) ⟶ ResolutionHomComplex.right X B)
    (sq : CommSq z (SSet.horn.{v} (n + 1) k).ι (rightPrecomp i B) b) : sq.HasLift := by
  let _ : HasLiftingProperty i (PartialFaceMatching.hornMap B (n + 1) k) :=
    hasLiftingProperty_of_wfs _ _ (mem_cofibrations i) (hornMatchingMap_trivialFibration B hB hW
      n k)
  let t : X ⟶ B.obj (op ⦋n + 1⦌) := SSet.yonedaEquiv b
  let c : CommSq t i (PartialFaceMatching.hornMap B (n + 1) k) (hornHomMap X' B (n + 1) k z) :=
    coefficientHornSquareOfPrecomp i B n k z b sq
  let _ : c.HasLift := inferInstance
  refine CommSq.HasLift.mk' { l := homSimplex X' B (n + 1) c.lift, fac_left := ?_, fac_right := ?_ }
  · exact homSimplex_horn_extension X' B n k z c.lift c.fac_right
  · apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, homSimplex]
    exact (congrArg (fun f : (ResolutionHomComplex.right X' B).obj (op ⦋n + 1⦌) =>
      (rightPrecomp i B).app (op ⦋n + 1⦌) f) (SSet.yonedaEquiv.apply_symm_apply c.lift)).trans
        c.fac_left

/-- Every original cofibration gives a genuine Kan fibration on the whole original right-frame Hom
complex. -/
theorem rightPrecomp_fibration {X X' : C} (i : X ⟶ X') [Cofibration i] (B : SimplicialObject C)
    (hB : ∀ j, fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp B j))
    (hW : ∀ {a b : SimplexCategoryᵒᵖ} (g : a ⟶ b), weakEquivalences C (B.map g)) :
    Fibration (rightPrecomp i B) := by
  apply (SSet.modelCategoryQuillen.fibration_iff _).mpr
  intro A A' j hj
  rw [SSet.modelCategoryQuillen.J, iSup_iff] at hj
  obtain ⟨n, ⟨k⟩⟩ := hj
  refine ⟨?_⟩
  intro z b sq
  exact rightPrecomp_horn_hasLift i B hB hW n k z b sq

variable {κC : Cardinal.{wC}} [Fact κC.IsRegular] [OrderBot κC.ord.ToType]
  (dC : CofibrantGenerationData C κC)

/-- The original generated right frame supplies both actual source hypotheses of the raw mapping
fibration. -/
theorem rightPrecomp_originalFrame_fibration {X X' : C} (i : X ⟶ X') [Cofibration i] (Z : C) :
    Fibration (rightPrecomp i ((FunctorialFramings.rightFrame (fromGeneration dC)).obj Z)) :=
  rightPrecomp_fibration i _ (FunctorialFramings.rightFrame_matching_fibration (fromGeneration
    dC) Z)
    (FunctorialFramings.rightFrame_map_weak (fromGeneration dC) Z)

/-- A weak raw original mapping test of a cofibration is a genuine original simplicial trivial
fibration. -/
theorem rightPrecomp_originalFrame_trivialFibration_iff {X X' : C} (i : X ⟶ X') [Cofibration i]
  (Z : C) :
    trivialFibrations SSet.{v} (rightPrecomp i ((FunctorialFramings.rightFrame (fromGeneration
      dC)).obj Z)) ↔
      weakEquivalences SSet.{v} (rightPrecomp i ((FunctorialFramings.rightFrame (fromGeneration
        dC)).obj Z)) := by
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨(HomotopicalAlgebra.fibration_iff _).mp (rightPrecomp_originalFrame_fibration dC i Z), h⟩

end HornLifting

section CofibrantSourceComparison

variable {C : Type uC} [Category.{v} C] [ModelCategory C]
  {κC : Cardinal.{wC}} [Fact κC.IsRegular] [OrderBot κC.ord.ToType]
  (dC : CofibrantGenerationData C κC)

open GeneratedFunctorialReplacements GeneratedFramings GeneratedFramingModels
open GeneratedFrameHomComplex HomotopyMappingSpaceCategory

/-- The original generated counit compares each actual cofibrant-source right Hom with the same
original HFC. -/
def rightCofibrantSourceIso (X : C) [IsCofibrant X] (Y : C) :
    localize.obj (ResolutionHomComplex.right X ((rightFrame dC).obj Y)) ≅
      GeneratedRightMappingEnrichment.space dC X Y := by
  let _ := simplicialModel dC
  let q : (Q dC).obj X ⟶ X := (counit dC).app X
  let _ : WeakEquivalence q := (weakEquivalence_iff _).mpr (counit_weak dC X)
  have h : WeakEquivalence (rightPrecomp q ((rightFrame dC).obj Y)) :=
    rightPrecomp_weak dC q _ inferInstance (Q_isCofibrant dC X) inferInstance
      (rightFrame_isFibrant dC dC Y)
  let s : localize.obj (ResolutionHomComplex.right X ((rightFrame dC).obj Y)) ⟶
      GeneratedRightMappingEnrichment.space dC X Y :=
    localize.map (rightPrecomp q ((rightFrame dC).obj Y))
  let _ : IsIso s :=
    localize_isIso _ ((weakEquivalence_iff _).mp h)
  exact asIso s

/-- The whole forward cofibrant-source comparison is exactly precomposition by the actual original
Q counit. -/
theorem rightCofibrantSourceIso_hom (X : C) [IsCofibrant X] (Y : C) :
    (rightCofibrantSourceIso dC X Y).hom =
      localize.map (rightPrecomp ((counit dC).app X) ((rightFrame dC).obj Y)) := rfl

/-- Every original map of cofibrant sources retains the full original Q-map/counit comparison
square. -/
theorem rightCofibrantSourceIso_source {X X' : C} [IsCofibrant X] [IsCofibrant X']
    (f : X ⟶ X') (Y : C) :
    localize.map (rightPrecomp f ((rightFrame dC).obj Y)) ≫ (rightCofibrantSourceIso dC X Y).hom =
      (rightCofibrantSourceIso dC X' Y).hom ≫ GeneratedRightMappingEnrichment.precomp dC f Y := by
  let q : (Q dC).obj X ⟶ X := (counit dC).app X
  let q' : (Q dC).obj X' ⟶ X' := (counit dC).app X'
  let B := (rightFrame dC).obj Y
  have h : rightPrecomp f B ≫ rightPrecomp q B =
      rightPrecomp q' B ≫ ((rightBifunctor dC).map f.op).app Y := by
    ext n z
    change X' ⟶ B.obj n at z
    change q ≫ (f ≫ z) = (Q dC).map f ≫ (q' ≫ z)
    have hq : (Q dC).map f ≫ q' = q ≫ f := (counit dC).naturality f
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (fun a => a ≫ z) hq.symm).trans (Category.assoc _ _ _))
  change localize.map (rightPrecomp f B) ≫ localize.map (rightPrecomp q B) =
    localize.map (rightPrecomp q' B) ≫ localize.map (((rightBifunctor dC).map f.op).app Y)
  exact (localize.map_comp _ _).symm.trans ((localize.congr_map h).trans (localize.map_comp _ _))

/-- The complete inverse source comparison retains the same original Q-map/counit naturality. -/
theorem rightCofibrantSourceIso_source_inv {X X' : C} [IsCofibrant X] [IsCofibrant X']
    (f : X ⟶ X') (Y : C) :
    GeneratedRightMappingEnrichment.precomp dC f Y ≫ (rightCofibrantSourceIso dC X Y).inv =
      (rightCofibrantSourceIso dC X' Y).inv ≫
        localize.map (rightPrecomp f ((rightFrame dC).obj Y)) := by
  apply (cancel_mono (rightCofibrantSourceIso dC X Y).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [rightCofibrantSourceIso_source]
  simp only [Iso.inv_hom_id_assoc]

/-- Every original target arrow retains the whole original counit/right-frame comparison square. -/
theorem rightCofibrantSourceIso_target (X : C) [IsCofibrant X] {Y Y' : C} (f : Y ⟶ Y') :
    localize.map (rightPostcomp X ((rightFrame dC).map f)) ≫ (rightCofibrantSourceIso dC X Y').hom =
      (rightCofibrantSourceIso dC X Y).hom ≫ GeneratedRightMappingEnrichment.postcomp dC X f := by
  let q : (Q dC).obj X ⟶ X := (counit dC).app X
  have h : rightPostcomp X ((rightFrame dC).map f) ≫ rightPrecomp q ((rightFrame dC).obj Y') =
      rightPrecomp q ((rightFrame dC).obj Y) ≫ ((rightBifunctor dC).obj (.op X)).map f :=
    (ResolutionHomComplex.precomp_postcomp ((CosimplicialObject.const C).map q) ((rightFrame
      dC).map f)).symm
  change localize.map _ ≫ localize.map _ = localize.map _ ≫ localize.map _
  exact (localize.map_comp _ _).symm.trans ((localize.congr_map h).trans (localize.map_comp _ _))

/-- Every original target arrow retains the full inverse original counit/right-frame comparison
square. -/
theorem rightCofibrantSourceIso_target_inv (X : C) [IsCofibrant X] {Y Y' : C} (f : Y ⟶ Y') :
    GeneratedRightMappingEnrichment.postcomp dC X f ≫ (rightCofibrantSourceIso dC X Y').inv =
      (rightCofibrantSourceIso dC X Y).inv ≫ localize.map (rightPostcomp X ((rightFrame dC).map
        f)) := by
  apply (cancel_mono (rightCofibrantSourceIso dC X Y').hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [rightCofibrantSourceIso_target]
  simp only [Iso.inv_hom_id_assoc]

/-- A same-original generated HFC test is weak exactly when the original raw right-frame test is
weak. -/
theorem generatedPrecomp_iff_raw {X X' : C} [IsCofibrant X] [IsCofibrant X'] (f : X ⟶ X') (Y : C) :
    IsIso (GeneratedRightMappingEnrichment.precomp dC f Y) ↔
      weakEquivalences SSet.{v} (rightPrecomp f ((rightFrame dC).obj Y)) := by
  let _ : localize.{v}.IsLocalization (weakEquivalences SSet.{v}) := by
    change localize.{v}.IsLocalization SSet.realizationWeakEquivalences.{v}
    infer_instance
  have h : IsIso (localize.map (rightPrecomp f ((rightFrame dC).obj Y))) ↔
      IsIso (GeneratedRightMappingEnrichment.precomp dC f Y) :=
    (isomorphisms SpaceHo.{v}).arrow_mk_iso_iff
      (Arrow.isoMk (rightCofibrantSourceIso dC X' Y) (rightCofibrantSourceIso dC X Y)
        (rightCofibrantSourceIso_source dC f Y).symm)
  exact h.symm.trans
    (weakEquivalence_iff_isIso_map_of_isLocalization localize
      (rightPrecomp f ((rightFrame dC).obj Y))).symm

/-- The same generated HFC test of a cofibration is equivalent to a genuine raw mapping trivial
fibration. -/
theorem generatedPrecomp_iff_raw_trivialFibration {X X' : C} [IsCofibrant X] [IsCofibrant X']
    (f : X ⟶ X') [Cofibration f] (Y : C) :
    IsIso (GeneratedRightMappingEnrichment.precomp dC f Y) ↔
      trivialFibrations SSet.{v} (rightPrecomp f ((rightFrame dC).obj Y)) :=
  (generatedPrecomp_iff_raw dC f Y).trans (rightPrecomp_originalFrame_trivialFibration_iff dC f
    Y).symm

end CofibrantSourceComparison

section QuillenMappingComparison

variable {C : Type uC} [Category.{v} C] [ModelCategory C]
  {D : Type uD} [Category.{v} D] [ModelCategory D]
  {κC : Cardinal.{wC}} [Fact κC.IsRegular] [OrderBot κC.ord.ToType]
  {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
  (dC : CofibrantGenerationData C κC) (dD : CofibrantGenerationData D κD)
  {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G) [adj.IsQuillenAdjunction]

open GeneratedFunctorialReplacements GeneratedFramings GeneratedFramingModels
open GeneratedFrameHomComplex HomotopyMappingSpaceCategory

/-- The actual original right-adjoint-frame comparison supplies the full original mapping-space
isomorphism. -/
def rightMappingIso (X : C) (Y : D) :
    localize.obj (ResolutionHomComplex.right ((Q dC).obj X) ((imageRightFrame dD (G := G)).obj Y)) ≅
      localize.obj (ResolutionHomComplex.right ((Q dC).obj X) ((commonFrame dC dD (G := G)).obj
        Y)) := by
  let _ := simplicialModel dC
  let q := (Q dC).obj X
  let r := (comparisonRight dC dD (G := G)).app Y
  let _ : WeakEquivalence r := (weakEquivalence_iff _).mpr (comparisonRight_trivialCofibration
    dC dD Y).2
  have h : WeakEquivalence (rightPostcomp q r) :=
    rightPostcomp_weak dC q r (Q_isCofibrant dC X) inferInstance
      (imageRightFrame_isFibrant dC dD adj Y) (commonFrame_isFibrant dC dD Y)
  let s : localize.obj (ResolutionHomComplex.right q ((imageRightFrame dD (G := G)).obj Y)) ⟶
      localize.obj (ResolutionHomComplex.right q ((commonFrame dC dD (G := G)).obj Y)) :=
    localize.map (rightPostcomp q r)
  let _ : IsIso s := localize_isIso _ ((weakEquivalence_iff _).mp h)
  exact asIso s

/-- The actual original canonical-frame comparison supplies the full original mapping-space
isomorphism. -/
def leftMappingIso (X : C) (Y : D) [IsFibrant Y] :
    GeneratedRightMappingEnrichment.space dC X (G.obj Y) ≅
      localize.obj (ResolutionHomComplex.right ((Q dC).obj X) ((commonFrame dC dD (G := G)).obj
        Y)) := by
  let _ := simplicialModel dC
  let q := (Q dC).obj X
  let r := (comparisonLeft dC dD (G := G)).app Y
  let _ : WeakEquivalence r := (weakEquivalence_iff _).mpr (comparisonLeft_weak dC dD adj Y)
  have h : WeakEquivalence (rightPostcomp q r) :=
    rightPostcomp_weak dC q r (Q_isCofibrant dC X) inferInstance
      (rightFrame_isFibrant dC dC (G.obj Y)) (commonFrame_isFibrant dC dD Y)
  let s : GeneratedRightMappingEnrichment.space dC X (G.obj Y) ⟶
      localize.obj (ResolutionHomComplex.right q ((commonFrame dC dD (G := G)).obj Y)) :=
    localize.map (rightPostcomp q r)
  let _ : IsIso s := localize_isIso _ ((weakEquivalence_iff _).mp h)
  exact asIso s

/-- The complete original image-frame forward map is the localization of its actual original
comparison. -/
theorem rightMappingIso_hom (X : C) (Y : D) :
    (rightMappingIso dC dD adj X Y).hom =
      localize.map (rightPostcomp ((Q dC).obj X) ((comparisonRight dC dD (G := G)).app Y)) := rfl

/-- The complete original canonical-frame forward map is the localization of its actual original
comparison. -/
theorem leftMappingIso_hom (X : C) (Y : D) [IsFibrant Y] :
    (leftMappingIso dC dD adj X Y).hom =
      localize.map (rightPostcomp ((Q dC).obj X) ((comparisonLeft dC dD (G := G)).app Y)) := rfl

/-- The actual original natural comparison span gives the full mapping isomorphism for the
right-adjoint image frame. -/
def imageComparisonIso (X : C) (Y : D) [IsFibrant Y] :
    localize.obj (ResolutionHomComplex.right ((Q dC).obj X) ((imageRightFrame dD (G := G)).obj Y)) ≅
      GeneratedRightMappingEnrichment.space dC X (G.obj Y) :=
  (rightMappingIso dC dD adj X Y).trans (leftMappingIso dC dD adj X Y).symm

/-- The whole original image comparison retains its actual forward span and original inverse
canonical comparison. -/
theorem imageComparisonIso_hom (X : C) (Y : D) [IsFibrant Y] :
    (imageComparisonIso dC dD adj X Y).hom =
      (rightMappingIso dC dD adj X Y).hom ≫ (leftMappingIso dC dD adj X Y).inv := rfl

variable {L' : C ⥤ D} {G' : D ⥤ C} (adj' : L' ⊣ G') [adj'.IsQuillenAdjunction]

/-- Every whole original right-adjoint transformation retains the full image-frame mapping
comparison square. -/
theorem rightMappingIso_naturality (b : G ⟶ G') (X : C) (Y : D) :
    localize.map (rightPostcomp ((Q dC).obj X) ((imageRightFrameMap dD b).app Y)) ≫
        (rightMappingIso dC dD adj' X Y).hom =
      (rightMappingIso dC dD adj X Y).hom ≫
        localize.map (rightPostcomp ((Q dC).obj X) ((commonFrameMap dC dD b).app Y)) := by
  let q := (Q dC).obj X
  have hf : (imageRightFrameMap dD b).app Y ≫ (comparisonRight dC dD (G := G')).app Y =
      (comparisonRight dC dD (G := G)).app Y ≫ (commonFrameMap dC dD b).app Y :=
    (congrArg (fun t => t.app Y) (comparisonRight_naturality dC dD b)).symm
  have h : rightPostcomp q ((imageRightFrameMap dD b).app Y) ≫
      rightPostcomp q ((comparisonRight dC dD (G := G')).app Y) =
    rightPostcomp q ((comparisonRight dC dD (G := G)).app Y) ≫
      rightPostcomp q ((commonFrameMap dC dD b).app Y) :=
    (ResolutionHomComplex.postcomp_comp _ _ _).symm.trans
      ((congrArg (rightPostcomp q) hf).trans (ResolutionHomComplex.postcomp_comp _ _ _))
  change localize.map _ ≫ localize.map _ = localize.map _ ≫ localize.map _
  exact (localize.map_comp _ _).symm.trans ((localize.congr_map h).trans (localize.map_comp _ _))

/-- Every whole original right-adjoint transformation retains the full canonical-frame mapping
comparison square. -/
theorem leftMappingIso_naturality (b : G ⟶ G') (X : C) (Y : D) [IsFibrant Y] :
    GeneratedRightMappingEnrichment.postcomp dC X (b.app Y) ≫ (leftMappingIso dC dD adj' X Y).hom =
      (leftMappingIso dC dD adj X Y).hom ≫
        localize.map (rightPostcomp ((Q dC).obj X) ((commonFrameMap dC dD b).app Y)) := by
  let q := (Q dC).obj X
  have hf : (rightFrame dC).map (b.app Y) ≫ (comparisonLeft dC dD (G := G')).app Y =
      (comparisonLeft dC dD (G := G)).app Y ≫ (commonFrameMap dC dD b).app Y :=
    (congrArg (fun t => t.app Y) (comparisonLeft_naturality dC dD b)).symm
  have h : rightPostcomp q ((rightFrame dC).map (b.app Y)) ≫
      rightPostcomp q ((comparisonLeft dC dD (G := G')).app Y) =
    rightPostcomp q ((comparisonLeft dC dD (G := G)).app Y) ≫
      rightPostcomp q ((commonFrameMap dC dD b).app Y) :=
    (ResolutionHomComplex.postcomp_comp _ _ _).symm.trans
      ((congrArg (rightPostcomp q) hf).trans (ResolutionHomComplex.postcomp_comp _ _ _))
  change localize.map _ ≫ localize.map _ = localize.map _ ≫ localize.map _
  exact (localize.map_comp _ _).symm.trans ((localize.congr_map h).trans (localize.map_comp _ _))

/-- The full original frame comparison span preserves every original right mate as an entire
mapping arrow. -/
theorem imageComparisonIso_naturality (b : G ⟶ G') (X : C) (Y : D) [IsFibrant Y] :
    localize.map (rightPostcomp ((Q dC).obj X) ((imageRightFrameMap dD b).app Y)) ≫
        (imageComparisonIso dC dD adj' X Y).hom =
      (imageComparisonIso dC dD adj X Y).hom ≫ GeneratedRightMappingEnrichment.postcomp dC X
        (b.app Y) := by
  apply (cancel_mono (leftMappingIso dC dD adj' X Y).hom).mp
  rw [imageComparisonIso_hom, imageComparisonIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [leftMappingIso_naturality dC dD adj adj' b X Y]
  simp only [Iso.inv_hom_id_assoc]
  exact rightMappingIso_naturality dC dD adj adj' b X Y

/-- The actual full frame comparison preserves every original source arrow and its same generated
Q map. -/
theorem imageComparisonIso_source {X X' : C} (f : X ⟶ X') (Y : D) [IsFibrant Y] :
    localize.map (rightPrecomp ((Q dC).map f) ((imageRightFrame dD (G := G)).obj Y)) ≫
        (imageComparisonIso dC dD adj X Y).hom =
      (imageComparisonIso dC dD adj X' Y).hom ≫ GeneratedRightMappingEnrichment.precomp dC f
        (G.obj Y) := by
  let q := (Q dC).map f
  let B := (commonFrame dC dD (G := G)).obj Y
  have hL : GeneratedRightMappingEnrichment.precomp dC f (G.obj Y) ≫ (leftMappingIso dC dD adj X
    Y).hom =
      (leftMappingIso dC dD adj X' Y).hom ≫ localize.map (rightPrecomp q B) := by
    have h := ResolutionHomComplex.precomp_postcomp ((CosimplicialObject.const C).map q)
      ((comparisonLeft dC dD (G := G)).app Y)
    change localize.map _ ≫ localize.map _ = localize.map _ ≫ localize.map _
    exact (localize.map_comp _ _).symm.trans ((localize.congr_map h).trans (localize.map_comp _ _))
  have hR : localize.map (rightPrecomp q ((imageRightFrame dD (G := G)).obj Y)) ≫
      (rightMappingIso dC dD adj X Y).hom =
    (rightMappingIso dC dD adj X' Y).hom ≫ localize.map (rightPrecomp q B) := by
    have h := ResolutionHomComplex.precomp_postcomp ((CosimplicialObject.const C).map q)
      ((comparisonRight dC dD (G := G)).app Y)
    change localize.map _ ≫ localize.map _ = localize.map _ ≫ localize.map _
    exact (localize.map_comp _ _).symm.trans ((localize.congr_map h).trans (localize.map_comp _ _))
  apply (cancel_mono (leftMappingIso dC dD adj X Y).hom).mp
  rw [imageComparisonIso_hom, imageComparisonIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hL]
  simp only [Iso.inv_hom_id_assoc]
  exact hR

/-- The actual full frame comparison preserves every original arrow between fibrant targets and
its right-frame map. -/
theorem imageComparisonIso_target (X : C) {Y Y' : D} [IsFibrant Y] [IsFibrant Y'] (f : Y ⟶ Y') :
    localize.map (rightPostcomp ((Q dC).obj X) ((imageRightFrame dD (G := G)).map f)) ≫
        (imageComparisonIso dC dD adj X Y').hom =
      (imageComparisonIso dC dD adj X Y).hom ≫ GeneratedRightMappingEnrichment.postcomp dC X
        (G.map f) := by
  let q := (Q dC).obj X
  let c := (commonFrame dC dD (G := G)).map f
  have hL : GeneratedRightMappingEnrichment.postcomp dC X (G.map f) ≫ (leftMappingIso dC dD adj
    X Y').hom =
      (leftMappingIso dC dD adj X Y).hom ≫ localize.map (rightPostcomp q c) := by
    have hc : (rightFrame dC).map (G.map f) ≫ (comparisonLeft dC dD (G := G)).app Y' =
        (comparisonLeft dC dD (G := G)).app Y ≫ c :=
      (comparisonLeft dC dD (G := G)).naturality f
    have h : rightPostcomp q ((rightFrame dC).map (G.map f)) ≫
          rightPostcomp q ((comparisonLeft dC dD (G := G)).app Y') =
        rightPostcomp q ((comparisonLeft dC dD (G := G)).app Y) ≫ rightPostcomp q c :=
      (ResolutionHomComplex.postcomp_comp _ _ _).symm.trans
        ((congrArg (rightPostcomp q) hc).trans (ResolutionHomComplex.postcomp_comp _ _ _))
    change localize.map _ ≫ localize.map _ = localize.map _ ≫ localize.map _
    exact (localize.map_comp _ _).symm.trans ((localize.congr_map h).trans (localize.map_comp _ _))
  have hR : localize.map (rightPostcomp q ((imageRightFrame dD (G := G)).map f)) ≫
        (rightMappingIso dC dD adj X Y').hom =
      (rightMappingIso dC dD adj X Y).hom ≫ localize.map (rightPostcomp q c) := by
    have hc := (comparisonRight dC dD (G := G)).naturality f
    have h : rightPostcomp q ((imageRightFrame dD (G := G)).map f) ≫
          rightPostcomp q ((comparisonRight dC dD (G := G)).app Y') =
        rightPostcomp q ((comparisonRight dC dD (G := G)).app Y) ≫ rightPostcomp q c :=
      (ResolutionHomComplex.postcomp_comp _ _ _).symm.trans
        ((congrArg (rightPostcomp q) hc).trans (ResolutionHomComplex.postcomp_comp _ _ _))
    change localize.map _ ≫ localize.map _ = localize.map _ ≫ localize.map _
    exact (localize.map_comp _ _).symm.trans ((localize.congr_map h).trans (localize.map_comp _ _))
  apply (cancel_mono (leftMappingIso dC dD adj X Y').hom).mp
  rw [imageComparisonIso_hom, imageComparisonIso_hom]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [hL]
  simp only [Iso.inv_hom_id_assoc]
  exact hR

/-- The original generated Q of the source and the actual Quillen left image give the exact source
comparison. -/
def freeSourceIso (X : C) (Y : D) :
    localize.obj (ResolutionHomComplex.right (L.obj ((Q dC).obj X)) ((rightFrame dD).obj Y)) ≅
      GeneratedRightMappingEnrichment.space dD (L.obj ((Q dC).obj X)) Y := by
  let _ : IsCofibrant (L.obj ((Q dC).obj X)) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := adj) (Q_isCofibrant dC X)
  exact rightCofibrantSourceIso dD _ Y

/-- The original Quillen right-HFC comparison retains both generated Q choices, the full
adjunction and both actual
frame legs. -/
def quillenRightMappingIso (X : C) (Y : D) [IsFibrant Y] :
    GeneratedRightMappingEnrichment.space dD (L.obj ((Q dC).obj X)) Y ≅
      GeneratedRightMappingEnrichment.space dC X (G.obj Y) :=
  (freeSourceIso dC dD adj X Y).symm.trans
    ((localize.mapIso (rightAdjunctionIso adj ((Q dC).obj X) ((rightFrame dD).obj Y))).trans
      (imageComparisonIso dC dD adj X Y))

/-- The complete forward derived adjunction retains the exact original inverse-Q, full frame
transpose and original
comparison span. -/
theorem quillenRightMappingIso_hom (X : C) (Y : D) [IsFibrant Y] :
    (quillenRightMappingIso dC dD adj X Y).hom =
      (freeSourceIso dC dD adj X Y).inv ≫
        localize.map (rightAdjunctionIso adj ((Q dC).obj X) ((rightFrame dD).obj Y)).hom ≫
          (imageComparisonIso dC dD adj X Y).hom := rfl

/-- The complete original derived adjunction is natural in every original source arrow, with its
unchanged Q map. -/
theorem quillenRightMappingIso_source {X X' : C} (f : X ⟶ X') (Y : D) [IsFibrant Y] :
    GeneratedRightMappingEnrichment.precomp dD (L.map ((Q dC).map f)) Y ≫
        (quillenRightMappingIso dC dD adj X Y).hom =
      (quillenRightMappingIso dC dD adj X' Y).hom ≫ GeneratedRightMappingEnrichment.precomp dC f
        (G.obj Y) := by
  let _ : IsCofibrant (L.obj ((Q dC).obj X)) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := adj) (Q_isCofibrant dC X)
  let _ : IsCofibrant (L.obj ((Q dC).obj X')) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := adj) (Q_isCofibrant dC X')
  let q := (Q dC).map f
  let B := (rightFrame dD).obj Y
  let s₁ : CommSq (GeneratedRightMappingEnrichment.precomp dD (L.map q) Y)
      (freeSourceIso dC dD adj X' Y).inv (freeSourceIso dC dD adj X Y).inv
      (localize.map (rightPrecomp (L.map q) B)) :=
    ⟨rightCofibrantSourceIso_source_inv dD (L.map q) Y⟩
  let s₂ : CommSq (localize.map (rightPrecomp (L.map q) B))
      (localize.map (rightAdjunctionIso adj ((Q dC).obj X') B).hom)
      (localize.map (rightAdjunctionIso adj ((Q dC).obj X) B).hom)
      (localize.map (rightPrecomp q ((imageRightFrame dD (G := G)).obj Y))) :=
    ⟨(localize.map_comp _ _).symm.trans
      ((localize.congr_map (rightAdjunctionIso_source adj q B)).trans (localize.map_comp _ _))⟩
  let s₃ : CommSq (localize.map (rightPrecomp q ((imageRightFrame dD (G := G)).obj Y)))
      (imageComparisonIso dC dD adj X' Y).hom (imageComparisonIso dC dD adj X Y).hom
      (GeneratedRightMappingEnrichment.precomp dC f (G.obj Y)) :=
    ⟨imageComparisonIso_source dC dD adj f Y⟩
  exact (s₁.vert_comp (s₂.vert_comp s₃)).w

/-- The complete original derived adjunction is natural in every original fibrant-target arrow and
its right-frame
map. -/
theorem quillenRightMappingIso_target (X : C) {Y Y' : D} [IsFibrant Y] [IsFibrant Y'] (f : Y ⟶ Y') :
    GeneratedRightMappingEnrichment.postcomp dD (L.obj ((Q dC).obj X)) f ≫
        (quillenRightMappingIso dC dD adj X Y').hom =
      (quillenRightMappingIso dC dD adj X Y).hom ≫ GeneratedRightMappingEnrichment.postcomp dC X
        (G.map f) := by
  let _ : IsCofibrant (L.obj ((Q dC).obj X)) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := adj) (Q_isCofibrant dC X)
  let q := (Q dC).obj X
  let b := (rightFrame dD).map f
  let s₁ : CommSq (GeneratedRightMappingEnrichment.postcomp dD (L.obj q) f)
      (freeSourceIso dC dD adj X Y).inv (freeSourceIso dC dD adj X Y').inv
      (localize.map (rightPostcomp (L.obj q) b)) :=
    ⟨rightCofibrantSourceIso_target_inv dD (L.obj q) f⟩
  let s₂ : CommSq (localize.map (rightPostcomp (L.obj q) b))
      (localize.map (rightAdjunctionIso adj q ((rightFrame dD).obj Y)).hom)
      (localize.map (rightAdjunctionIso adj q ((rightFrame dD).obj Y')).hom)
      (localize.map (rightPostcomp q ((imageRightFrame dD (G := G)).map f))) :=
    ⟨(localize.map_comp _ _).symm.trans
      ((localize.congr_map (rightAdjunctionIso_target adj q b)).trans (localize.map_comp _ _))⟩
  let s₃ : CommSq (localize.map (rightPostcomp q ((imageRightFrame dD (G := G)).map f)))
      (imageComparisonIso dC dD adj X Y).hom (imageComparisonIso dC dD adj X Y').hom
      (GeneratedRightMappingEnrichment.postcomp dC X (G.map f)) :=
    ⟨imageComparisonIso_target dC dD adj X f⟩
  exact (s₁.vert_comp (s₂.vert_comp s₃)).w

/-- Every original left comparison retains the complete inverse generated-Q source comparison
square. -/
theorem freeSourceIso_mate (a : L ⟶ L') (X : C) (Y : D) :
    GeneratedRightMappingEnrichment.precomp dD (a.app ((Q dC).obj X)) Y ≫
        (freeSourceIso dC dD adj X Y).inv =
      (freeSourceIso dC dD adj' X Y).inv ≫
        localize.map (rightPrecomp (a.app ((Q dC).obj X)) ((rightFrame dD).obj Y)) := by
  let _ : IsCofibrant (L.obj ((Q dC).obj X)) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := adj) (Q_isCofibrant dC X)
  let _ : IsCofibrant (L'.obj ((Q dC).obj X)) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := adj') (Q_isCofibrant dC X)
  exact rightCofibrantSourceIso_source_inv dD (a.app ((Q dC).obj X)) Y

/-- The full original derived mapping adjunction transposes every actual original comparison to
its same right mate. -/
theorem quillenRightMappingIso_mate (a : L ⟶ L') (X : C) (Y : D) [IsFibrant Y] :
    GeneratedRightMappingEnrichment.precomp dD (a.app ((Q dC).obj X)) Y ≫
        (quillenRightMappingIso dC dD adj X Y).hom =
      (quillenRightMappingIso dC dD adj' X Y).hom ≫
        GeneratedRightMappingEnrichment.postcomp dC X ((conjugateEquiv adj' adj a).app Y) := by
  let q := (Q dC).obj X
  let B := (rightFrame dD).obj Y
  let b := conjugateEquiv adj' adj a
  have hRaw : localize.map (rightPrecomp (a.app q) B) ≫
        localize.map (rightAdjunctionIso adj q B).hom =
      localize.map (rightAdjunctionIso adj' q B).hom ≫
        localize.map (rightPostcomp q ((imageRightFrameMap dD b).app Y)) :=
    (localize.map_comp _ _).symm.trans
      ((localize.congr_map (rightMate_square adj adj' a q B)).trans (localize.map_comp _ _))
  rw [quillenRightMappingIso_hom, quillenRightMappingIso_hom]
  let s₁ : CommSq (GeneratedRightMappingEnrichment.precomp dD (a.app q) Y)
      (freeSourceIso dC dD adj' X Y).inv (freeSourceIso dC dD adj X Y).inv
      (localize.map (rightPrecomp (a.app q) B)) :=
    ⟨freeSourceIso_mate dC dD adj adj' a X Y⟩
  let s₂ : CommSq (localize.map (rightPrecomp (a.app q) B))
      (localize.map (rightAdjunctionIso adj' q B).hom) (localize.map (rightAdjunctionIso adj q
        B).hom)
      (localize.map (rightPostcomp q ((imageRightFrameMap dD b).app Y))) := ⟨hRaw⟩
  let s₃ : CommSq (localize.map (rightPostcomp q ((imageRightFrameMap dD b).app Y)))
      (imageComparisonIso dC dD adj' X Y).hom (imageComparisonIso dC dD adj X Y).hom
      (GeneratedRightMappingEnrichment.postcomp dC X (b.app Y)) :=
    ⟨imageComparisonIso_naturality dC dD adj' adj b X Y⟩
  exact (s₁.vert_comp (s₂.vert_comp s₃)).w

/-- The actual original left comparison and right mate give isomorphic complete derived mapping
arrows. -/
def rightMateArrowIso (a : L ⟶ L') (X : C) (Y : D) [IsFibrant Y] :
    Arrow.mk (GeneratedRightMappingEnrichment.precomp dD (a.app ((Q dC).obj X)) Y) ≅
      Arrow.mk (GeneratedRightMappingEnrichment.postcomp dC X ((conjugateEquiv adj' adj a).app
        Y)) :=
  Arrow.isoMk (quillenRightMappingIso dC dD adj' X Y) (quillenRightMappingIso dC dD adj X Y)
    (quillenRightMappingIso_mate dC dD adj adj' a X Y).symm

/-- Local testing of the same original QA left comparison is exactly original HFC testing of its
actual right mate. -/
theorem generated_precomp_mate_iff (a : L ⟶ L') (X : C) (Y : D) [IsFibrant Y] :
    IsIso (GeneratedRightMappingEnrichment.precomp dD (a.app ((Q dC).obj X)) Y) ↔
      IsIso (GeneratedRightMappingEnrichment.postcomp dC X ((conjugateEquiv adj' adj a).app Y)) :=
  (isomorphisms SpaceHo.{v}).arrow_mk_iso_iff (rightMateArrowIso dC dD adj adj' a X Y)

end QuillenMappingComparison

end HomotopicalAlgebra.QuillenFrameHomComplex
