/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.ModelCategory.CellularSource
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedArrowFactorizations
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedFunctorialReplacements
public import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.GeneratedLocalReplacement
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedFramings
public import MathlibExt.AlgebraicTopology.ModelCategory.QuillenFrameHomComplex
public import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedFrameHomComparison
public import MathlibExt.AlgebraicTopology.ModelCategory.CellularLocalizationSmallness
public import MathlibExt.AlgebraicTopology.ModelCategory.CellularLocalizationFactorizations
public import MathlibExt.AlgebraicTopology.ModelCategory.CofibrantlyGenerated.Colimits
public import MathlibExt.CategoryTheory.SmallObject.Closure

/-!
# Original generated cell approximations of localizing arrows

The auxiliary cofibration approximation first applies the actual generated
Q and then the original I-factorization at its original cardinal. Its full
Arrow functor and comparison to the original Arrow retain every supplied
commuting square. The relative-cell presentation uses the original ordinal
and generating family.

The same original generic homotopy-function-complex tests prove that these
approximations have exactly the original locality tests. This construction
does not assert that the family generates localized fibrations.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe w wS u v

open CategoryTheory Limits MorphismProperty Simplicial Opposite
open scoped SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CellularLocalizingFamilies

variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open GeneratedFunctorialReplacements GeneratedArrowFactorizations

/-- The auxiliary Arrow is constructed by the actual original Q and I factories. -/
def cellApproximation : Arrow C ⥤ Arrow C where
  obj p := Arrow.mk ((cofibrant d).i.app ((Q d).mapArrow.obj p))
  map φ := Arrow.homMk ((Q d).map φ.left)
    ((cofibrant d).Z.map ((Q d).mapArrow.map φ))
    ((cofibrant d).i.naturality ((Q d).mapArrow.map φ))
  map_id p := by
    apply Arrow.hom_ext
    · change (Q d).map (𝟙 p.left) = 𝟙 _
      exact (Q d).map_id p.left
    · change (cofibrant d).Z.map ((Q d).mapArrow.map (𝟙 p)) = 𝟙 _
      rw [(Q d).mapArrow.map_id p, (cofibrant d).Z.map_id]
  map_comp φ ψ := by
    apply Arrow.hom_ext
    · change (Q d).map (φ.left ≫ ψ.left) = (Q d).map φ.left ≫ (Q d).map ψ.left
      exact (Q d).map_comp φ.left ψ.left
    · change (cofibrant d).Z.map ((Q d).mapArrow.map (φ ≫ ψ)) =
        (cofibrant d).Z.map ((Q d).mapArrow.map φ) ≫
          (cofibrant d).Z.map ((Q d).mapArrow.map ψ)
      rw [Functor.map_comp, Functor.map_comp]

/-- Each original source is the original generated-Q source. -/
theorem cellApproximation_left (p : Arrow C) :
    ((cellApproximation d).obj p).left = (Q d).obj p.left := rfl

/-- Each actual middle object uses the same original small-object factory. -/
theorem cellApproximation_right (p : Arrow C) :
    letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
    ((cellApproximation d).obj p).right = SmallObject.obj d.I κ ((Q d).map p.hom) := rfl

/-- Every actual attaching inclusion is the same original I factor. -/
theorem cellApproximation_hom (p : Arrow C) :
    letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
    ((cellApproximation d).obj p).hom = SmallObject.ιObj d.I κ ((Q d).map p.hom) := rfl

/-- Every source square map remains the image under the same original Q functor. -/
theorem cellApproximation_map_left {p q : Arrow C} (φ : p ⟶ q) :
    ((cellApproximation d).map φ).left = (Q d).map φ.left := rfl

/-- Every target square map remains the original I middle-functor square map. -/
theorem cellApproximation_map_right {p q : Arrow C} (φ : p ⟶ q) :
    letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
    ((cellApproximation d).map φ).right = SmallObject.objMap d.I κ ((Q d).mapArrow.map φ) := rfl

/-- The actual whole original Arrow comparison retains both original Q counits. -/
def toOriginal : cellApproximation d ⟶ 𝟭 (Arrow C) where
  app p := Arrow.homMk ((counit d).app p.left)
    ((cofibrant d).p.app ((Q d).mapArrow.obj p) ≫ (counit d).app p.right) (by
      change (counit d).app p.left ≫ p.hom =
        (cofibrant d).i.app ((Q d).mapArrow.obj p) ≫
          ((cofibrant d).p.app ((Q d).mapArrow.obj p) ≫ (counit d).app p.right)
      rw [← Category.assoc, (cofibrant d).fac_app]
      exact ((counit d).naturality p.hom).symm)
  naturality p q φ := by
    apply Arrow.hom_ext
    · exact (counit d).naturality φ.left
    · change (cofibrant d).Z.map ((Q d).mapArrow.map φ) ≫
          ((cofibrant d).p.app ((Q d).mapArrow.obj q) ≫ (counit d).app q.right) =
        ((cofibrant d).p.app ((Q d).mapArrow.obj p) ≫ (counit d).app p.right) ≫ φ.right
      rw [← Category.assoc, (cofibrant d).p.naturality, Category.assoc]
      change (cofibrant d).p.app ((Q d).mapArrow.obj p) ≫
          ((Q d).map φ.right ≫ (counit d).app q.right) =
        ((cofibrant d).p.app ((Q d).mapArrow.obj p) ≫ (counit d).app p.right) ≫ φ.right
      rw [(counit d).naturality φ.right, ← Category.assoc]
      rfl

/-- The entire original source comparison is precisely the original Q counit. -/
theorem toOriginal_left (p : Arrow C) :
    ((toOriginal d).app p).left = (counit d).app p.left := rfl

/-- The entire original target comparison retains the actual I projection and Q counit. -/
theorem toOriginal_right (p : Arrow C) :
    ((toOriginal d).app p).right =
      (cofibrant d).p.app ((Q d).mapArrow.obj p) ≫ (counit d).app p.right := rfl

/-- The same original natural square recovers every original localizing map. -/
@[reassoc]
theorem toOriginal_square (p : Arrow C) :
    ((toOriginal d).app p).left ≫ p.hom =
      ((cellApproximation d).obj p).hom ≫ ((toOriginal d).app p).right :=
  ((toOriginal d).app p).w

/-- The original fixed-cardinal I-cell chain presents each same actual auxiliary map. -/
def cellComplex (p : Arrow C) :
    RelativeCellComplex.{w} (fun _ : κ.ord.ToType => d.I.homFamily)
      ((cellApproximation d).obj p).hom := by
  letI : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
  exact SmallObject.relativeCellComplexιObj d.I κ ((Q d).map p.hom)

/-- Every actual auxiliary arrow is an original base cofibration. -/
theorem cellApproximation_cofibration (p : Arrow C) :
    cofibrations C ((cellApproximation d).obj p).hom :=
  (cofibrant d).hi ((Q d).mapArrow.obj p)

/-- The actual original generated-Q source is cofibrant. -/
theorem cellApproximation_source_cofibrant (p : Arrow C) :
    IsCofibrant ((cellApproximation d).obj p).left := Q_isCofibrant d p.left

/-- The actual target is cofibrant by the same original I attaching inclusion. -/
theorem cellApproximation_target_cofibrant (p : Arrow C) :
    IsCofibrant ((cellApproximation d).obj p).right := by
  let _ : IsCofibrant ((cellApproximation d).obj p).left :=
    cellApproximation_source_cofibrant d p
  let _ : Cofibration ((cellApproximation d).obj p).hom :=
    (cofibration_iff _).mpr (cellApproximation_cofibration d p)
  exact isCofibrant_of_cofibration ((cellApproximation d).obj p).hom

/-- The original source comparison is a base trivial fibration. -/
theorem toOriginal_left_trivialFibration (p : Arrow C) :
    trivialFibrations C ((toOriginal d).app p).left := counit_trivialFibration d p.left

/-- The original target comparison is a base trivial fibration. -/
theorem toOriginal_right_trivialFibration (p : Arrow C) :
    trivialFibrations C ((toOriginal d).app p).right :=
  (trivialFibrations C).comp_mem _ _
    ((cofibrant d).hp ((Q d).mapArrow.obj p)) (counit_trivialFibration d p.right)

/-- Every original generic function-complex test agrees with its same cell approximation. -/
theorem nativePrecomp_iff (p : Arrow C) (Z : C) :
    IsIso (GeneratedRightMappingEnrichment.precomp d ((cellApproximation d).obj p).hom Z) ↔
      IsIso (GeneratedRightMappingEnrichment.precomp d p.hom Z) := by
  let _ : IsIso (GeneratedRightMappingEnrichment.precomp d ((toOriginal d).app p).left Z) :=
    GeneratedLocalReplacement.nativePrecomp_isIso_of_weak d _
      (toOriginal_left_trivialFibration d p).2 Z
  let _ : IsIso (GeneratedRightMappingEnrichment.precomp d ((toOriginal d).app p).right Z) :=
    GeneratedLocalReplacement.nativePrecomp_isIso_of_weak d _
      (toOriginal_right_trivialFibration d p).2 Z
  have h : GeneratedRightMappingEnrichment.precomp d p.hom Z ≫
        GeneratedRightMappingEnrichment.precomp d ((toOriginal d).app p).left Z =
      GeneratedRightMappingEnrichment.precomp d ((toOriginal d).app p).right Z ≫
        GeneratedRightMappingEnrichment.precomp d ((cellApproximation d).obj p).hom Z := by
    rw [← GeneratedLocalReplacement.nativePrecomp_comp,
      ← GeneratedLocalReplacement.nativePrecomp_comp]
    exact congrArg (fun f => GeneratedRightMappingEnrichment.precomp d f Z)
      (toOriginal_square d p)
  constructor
  · intro hf
    let _ := hf
    exact IsIso.of_isIso_fac_right h
  · intro hf
    let _ := hf
    exact IsIso.of_isIso_fac_left h.symm

/-- The original family keeps every label while the auxiliary family uses its actual I cell map. -/
def approximatedFamily {K : Type wS} (S : K → Arrow C) : K → Arrow C :=
  fun k => (cellApproximation d).obj (S k)

/-- All original localizing-arrow tests are retained at every original target. -/
theorem derivedLocal_iff {K : Type wS} (S : K → Arrow C) (Z : C) :
    generatedIsDerivedLocal d (approximatedFamily d S) Z ↔
      generatedIsDerivedLocal d S Z :=
  forall_congr' (fun k => nativePrecomp_iff d (S k) Z)

/-- The complete local-object test retains base fibrancy and all original arrows. -/
theorem localFibrant_iff {K : Type wS} (S : K → Arrow C) (Z : C) :
    generatedLocalFibrant d (approximatedFamily d S) Z ↔ generatedLocalFibrant d S Z :=
  and_congr Iff.rfl (derivedLocal_iff d S Z)

/-- The entire original local weak class is unchanged, at arbitrary arrow endpoints. -/
theorem localEquivalences_eq {K : Type wS} (S : K → Arrow C) :
    generatedLocalEquivalences d (approximatedFamily d S) = generatedLocalEquivalences d S := by
  funext X Y f
  apply propext
  constructor
  · intro hf Z hZ
    exact hf Z ((localFibrant_iff d S Z).mpr hZ)
  · intro hf Z hZ
    exact hf Z ((localFibrant_iff d S Z).mp hZ)

/-- Each actual auxiliary attaching map is local-weak for the original family. -/
theorem approximatedFamily_local {K : Type wS} (S : K → Arrow C) (k : K) :
    generatedLocalEquivalences d S (approximatedFamily d S k).hom := by
  intro Z hZ
  exact (nativePrecomp_iff d (S k) Z).mpr (hZ.2 k)

open GeneratedFramings GeneratedFramingModels

/-- The actual original generated Reedy factory resolves every original source arrow between its same frames. -/
def cosimplicialFactor (p : Arrow C) :
    MapFactorizationData
      (ReedyStructure.latchingClass SimplexCategory.reedy (cofibrations C))
      (ReedyStructure.matchingClass SimplexCategory.reedy (trivialFibrations C))
      ((leftFrame d).map p.hom) := by
  let _ := cosimplicialModel d
  let a := (cosimplicialCofibrantFactorizationData d).factorizationData ((leftFrame d).map p.hom)
  have hi : ReedyStructure.latchingClass SimplexCategory.reedy (cofibrations C) a.i := by
    rw [← cosimplicial_cofibrations_eq d]
    exact a.hi
  have hp : ReedyStructure.matchingClass SimplexCategory.reedy (trivialFibrations C) a.p := by
    rw [← cosimplicial_trivialFibrations_eq d]
    exact a.hp
  exact { Z := a.Z, i := a.i, p := a.p, hi := hi, hp := hp, fac := a.fac }

/-- The original source frame augmentation still targets the same actual original Q source. -/
def sourceResolution (p : Arrow C) :
    (leftFrame d).obj p.left ⟶ (CosimplicialObject.const C).obj ((Q d).obj p.left) :=
  (leftResolution d).app p.left

/-- The actual Reedy middle frame maps to the same original Q target by its original projection. -/
def targetResolution (p : Arrow C) :
    (cosimplicialFactor d p).Z ⟶ (CosimplicialObject.const C).obj ((Q d).obj p.right) :=
  (cosimplicialFactor d p).p ≫ (leftResolution d).app p.right

/-- Both actual frame augmentation routes retain every original source arrow and its same Q map. -/
theorem resolution_square (p : Arrow C) :
    (cosimplicialFactor d p).i ≫ targetResolution d p =
      sourceResolution d p ≫ (CosimplicialObject.const C).map ((Q d).map p.hom) := by
  unfold targetResolution sourceResolution
  rw [← Category.assoc, (cosimplicialFactor d p).fac]
  exact (leftResolution d).naturality p.hom

/-- Every original source resolution component is weak in the same base model. -/
theorem sourceResolution_weak (p : Arrow C) (j : SimplexCategory) :
    weakEquivalences C ((sourceResolution d p).app j) := leftResolution_weak d p.left j

/-- Every actual target resolution component is weak, from the original Reedy trivial-fibration factory. -/
theorem targetResolution_weak (p : Arrow C) (j : SimplexCategory) :
    weakEquivalences C ((targetResolution d p).app j) := by
  have hp : trivialFibrations C (((cosimplicialFactor d p).p).app j) :=
    ReedyModel.component_trivialFibration_of_matchingCorners SimplexCategory.reedy
      (cosimplicialFactor d p).p (cosimplicialFactor d p).hp j
  change weakEquivalences C (((cosimplicialFactor d p).p).app j ≫ ((leftResolution d).app p.right).app j)
  exact (weakEquivalences C).comp_mem _ _ hp.2 (leftResolution_weak d p.right j)

/-- Each actual localizing attaching arrow is the same original latching corner of the constructed resolution. -/
def latchingArrow (p : Arrow C) (n : ℕ) : Arrow C :=
  Arrow.mk (ReedyStructure.latchingCorner SimplexCategory.reedy (cosimplicialFactor d p).i ⦋n⦌)

/-- All actual localizing latching corners are source cofibrations; no simplicial structure on C is required. -/
theorem latchingArrow_cofibration (p : Arrow C) (n : ℕ) :
    cofibrations C (latchingArrow d p n).hom := (cosimplicialFactor d p).hi ⦋n⦌

/-- Every original source-resolution coefficient is cofibrant in the original model. -/
theorem sourceResolution_cofibrant (p : Arrow C) (j : SimplexCategory) :
    IsCofibrant (((leftFrame d).obj p.left).obj j) :=
  LeftFrameHomWeakEquivalence.coefficient_isCofibrant _
    (leftFrame_latching_cofibration d p.left) j

/-- The actual original Reedy projection's middle object has all cofibrant latching boundaries. -/
theorem targetResolution_latching_cofibration (p : Arrow C) (j : SimplexCategory) :
    cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy
      (cosimplicialFactor d p).Z j) := by
  let _ := cosimplicialModel d
  let _ : IsCofibrant ((leftFrame d).obj p.left) := leftFrame_isCofibrant d d p.left
  let _ : Cofibration (cosimplicialFactor d p).i := by
    apply (cofibration_iff _).mpr
    rw [cosimplicial_cofibrations_eq d]
    exact (cosimplicialFactor d p).hi
  let _ : IsCofibrant (cosimplicialFactor d p).Z :=
    isCofibrant_of_cofibration (cosimplicialFactor d p).i
  exact (cofibration_iff _).mp ((cosimplicial_isCofibrant_iff d _).mp inferInstance j)

/-- Every actual original target-resolution coefficient is cofibrant. -/
theorem targetResolution_cofibrant (p : Arrow C) (j : SimplexCategory) :
    IsCofibrant ((cosimplicialFactor d p).Z.obj j) :=
  LeftFrameHomWeakEquivalence.coefficient_isCofibrant _
    (targetResolution_latching_cofibration d p) j

/-- The actual original latching pushout has a cofibrant source, by the base latching comparison. -/
theorem latchingArrow_source_cofibrant (p : Arrow C) (n : ℕ) :
    IsCofibrant (latchingArrow d p n).left := by
  let a := (cosimplicialFactor d p).i
  have hl : cofibrations C
      (colimMap (SimplexCategory.reedy.latchingTransformation a ⦋n⦌)) :=
    ReedyModel.latchingColimMap_cofibration SimplexCategory.reedy a ⦋n⦌
      (fun j _ => (cosimplicialFactor d p).hi j)
  let _ : IsCofibrant (((leftFrame d).obj p.left).obj ⦋n⦌) :=
    sourceResolution_cofibrant d p ⦋n⦌
  let i : ((leftFrame d).obj p.left).obj ⦋n⦌ ⟶ (latchingArrow d p n).left := pushout.inl
    (ReedyStructure.latchingMap SimplexCategory.reedy ((leftFrame d).obj p.left) ⦋n⦌)
    (colimMap (SimplexCategory.reedy.latchingTransformation a ⦋n⦌))
  let _ : Cofibration i := (cofibration_iff _).mpr ((cofibrations C).pushout_inl _ _ hl)
  exact isCofibrant_of_cofibration i

/-- The same actual latching arrow has a cofibrant target, with no endpoint assumption on the original arrow. -/
theorem latchingArrow_target_cofibrant (p : Arrow C) (n : ℕ) :
    IsCofibrant (latchingArrow d p n).right := targetResolution_cofibrant d p ⦋n⦌

/-- The original Reedy factory's complete Arrow functor retains every original source square. -/
def cosimplicialApproximation : Arrow C ⥤ Arrow (CosimplicialObject C) where
  obj p := Arrow.mk (cosimplicialFactor d p).i
  map φ := Arrow.homMk ((leftFrame d).map φ.left)
    ((cosimplicialCofibrantFactorizationData d).Z.map ((leftFrame d).mapArrow.map φ))
    ((cosimplicialCofibrantFactorizationData d).i.naturality ((leftFrame d).mapArrow.map φ))
  map_id p := by
    apply Arrow.hom_ext
    · exact (leftFrame d).map_id p.left
    · change (cosimplicialCofibrantFactorizationData d).Z.map
        ((leftFrame d).mapArrow.map (𝟙 p)) = 𝟙 _
      rw [(leftFrame d).mapArrow.map_id p, (cosimplicialCofibrantFactorizationData d).Z.map_id]
  map_comp φ ψ := by
    apply Arrow.hom_ext
    · exact (leftFrame d).map_comp φ.left ψ.left
    · change (cosimplicialCofibrantFactorizationData d).Z.map
        ((leftFrame d).mapArrow.map (φ ≫ ψ)) = _
      rw [Functor.map_comp, Functor.map_comp]
      rfl

/-- Each latching degree retains all actual original Arrow maps in a complete functor. -/
def latchingFamilyFunctor (n : ℕ) : Arrow C ⥤ Arrow C :=
  cosimplicialApproximation d ⋙ SimplexCategory.reedy.latchingCornerArrow ⦋n⦌

/-- The full attaching-family functor has the same original actual latching corner. -/
theorem latchingFamilyFunctor_obj (p : Arrow C) (n : ℕ) :
    (latchingFamilyFunctor d n).obj p = latchingArrow d p n := rfl

/-- Every original latching-family source square is the same canonical latching pushout map. -/
theorem latchingFamilyFunctor_map_left {p q : Arrow C} (φ : p ⟶ q) (n : ℕ) :
    ((latchingFamilyFunctor d n).map φ).left =
      SimplexCategory.reedy.latchingCornerSourceMap
        ((cosimplicialApproximation d).map φ) ⦋n⦌ := rfl

/-- Every target square retains the original Reedy middle-functor coefficient map. -/
theorem latchingFamilyFunctor_map_right {p q : Arrow C} (φ : p ⟶ q) (n : ℕ) :
    ((latchingFamilyFunctor d n).map φ).right =
      (((cosimplicialCofibrantFactorizationData d).Z.map
        ((leftFrame d).mapArrow.map φ)).app ⦋n⦌) := rfl

private theorem weak_test_iff_of_square {A B A' B' : SSet.{v}}
    (f : A ⟶ B) (g : A' ⟶ B') (a : A ⟶ A') (b : B ⟶ B')
    [WeakEquivalence a] [WeakEquivalence b] (sq : f ≫ b = a ≫ g) :
    WeakEquivalence f ↔ WeakEquivalence g := by
  constructor
  · intro hf
    let _ := hf
    let _ : WeakEquivalence (a ≫ g) := sq ▸ (inferInstance : WeakEquivalence (f ≫ b))
    exact weakEquivalence_of_precomp a g
  · intro hg
    let _ := hg
    let _ : WeakEquivalence (f ≫ b) := sq.symm ▸ (inferInstance : WeakEquivalence (a ≫ g))
    exact weakEquivalence_of_postcomp f b

/-- The constructed resolution's actual left-Hom source test is the complete original derived test. -/
theorem resolutionPrecomp_weak_iff (p : Arrow C) (Z : C) [IsFibrant Z] :
    WeakEquivalence (ResolutionHomComplex.precomp (cosimplicialFactor d p).i
      ((SimplicialObject.const C).obj Z)) ↔
      IsIso (GeneratedRightMappingEnrichment.precomp d p.hom Z) := by
  let A := (leftFrame d).obj p.left
  let B := (cosimplicialFactor d p).Z
  let R := (rightFrame d).obj Z
  let _ : IsCofibrant ((Q d).obj p.left) := Q_isCofibrant d p.left
  let _ : IsCofibrant ((Q d).obj p.right) := Q_isCofibrant d p.right
  let _ : WeakEquivalence (ResolutionHomComplex.fromAugmentation (sourceResolution d p) R) :=
    GeneratedFrameHomComparison.fromAugmentation_weak A R (sourceResolution d p)
      (leftFrame_latching_cofibration d p.left) (rightFrame_matching_fibration d Z)
      (sourceResolution_weak d p)
  let _ : WeakEquivalence (ResolutionHomComplex.fromAugmentation (targetResolution d p) R) :=
    GeneratedFrameHomComparison.fromAugmentation_weak B R (targetResolution d p)
      (targetResolution_latching_cofibration d p) (rightFrame_matching_fibration d Z)
      (targetResolution_weak d p)
  let _ : WeakEquivalence (ResolutionHomComplex.fromCoaugmentation A ((coaugmentation d).app Z)) :=
    GeneratedFrameHomComparison.fromCoaugmentation_weak A R ((coaugmentation d).app Z)
      (leftFrame_latching_cofibration d p.left) (rightFrame_matching_fibration d Z)
      (coaugmentation_weak d Z)
  let _ : WeakEquivalence (ResolutionHomComplex.fromCoaugmentation B ((coaugmentation d).app Z)) :=
    GeneratedFrameHomComparison.fromCoaugmentation_weak B R ((coaugmentation d).app Z)
      (targetResolution_latching_cofibration d p) (rightFrame_matching_fibration d Z)
      (coaugmentation_weak d Z)
  have hleft := weak_test_iff_of_square _ _ _ _
    (ResolutionHomComplex.fromCoaugmentation_naturality_source
      (cosimplicialFactor d p).i ((coaugmentation d).app Z))
  have hright := weak_test_iff_of_square _ _ _ _
    (ResolutionHomComplex.fromAugmentation_naturality_source
      (cosimplicialFactor d p).i ((Q d).map p.hom)
      (sourceResolution d p) (targetResolution d p) (resolution_square d p) R)
  have hraw := (QuillenFrameHomComplex.generatedPrecomp_iff_raw d ((Q d).map p.hom) Z).symm
  have hQ := GeneratedLocalReplacement.nativePrecomp_Q_iff d p.hom Z
  exact hleft.trans (hright.symm.trans ((weakEquivalence_iff _).trans (hraw.trans hQ)))

/-- Every original right-frame coefficient of an actual local-fibrant object retains full original locality. -/
theorem rightFrame_coefficient_localFibrant {K : Type wS} (S : K → Arrow C)
    (Z : C) (hZ : generatedLocalFibrant d S Z) (j : SimplexCategoryᵒᵖ) :
    generatedLocalFibrant d S (((rightFrame d).obj Z).obj j) := by
  let _ : IsFibrant (((rightFrame d).obj Z).obj j) :=
    RightFrameHornGeometry.degree_isFibrant _ (rightFrame_matching_fibration d Z) j
  exact CellularLocalizationFactorizations.localFibrant_of_weak d S
    (((coaugmentation d).app Z).app j) (coaugmentation_weak d Z j) hZ

/-- Every actual local target gives the original weak left-Hom map for each original localizing arrow. -/
theorem resolutionPrecomp_local_weak {K : Type wS} (S : K → Arrow C)
    (k : K) (Z : C) (hZ : generatedLocalFibrant d S Z) :
    WeakEquivalence (ResolutionHomComplex.precomp (cosimplicialFactor d (S k)).i
      ((SimplicialObject.const C).obj Z)) := by
  let _ : IsFibrant Z := hZ.1
  exact (resolutionPrecomp_weak_iff d (S k) Z).mpr (hZ.2 k)

/-- The exact original resolution test is weak at every original right-frame coefficient. -/
theorem resolutionPrecomp_frameCoefficient_local_weak {K : Type wS} (S : K → Arrow C)
    (k : K) (Z : C) (hZ : generatedLocalFibrant d S Z) (j : SimplexCategoryᵒᵖ) :
    WeakEquivalence (ResolutionHomComplex.precomp (cosimplicialFactor d (S k)).i
      ((SimplicialObject.const C).obj (((rightFrame d).obj Z).obj j))) :=
  resolutionPrecomp_local_weak d S k _ (rightFrame_coefficient_localFibrant d S Z hZ j)

/-- Every actual original source-resolution operator is weak by its same augmentation square. -/
theorem sourceResolution_map_weak (p : Arrow C) {j k : SimplexCategory} (a : j ⟶ k) :
    weakEquivalences C (((leftFrame d).obj p.left).map a) := by
  apply (weakEquivalences C).of_postcomp _ _ (sourceResolution_weak d p k)
  have h := (sourceResolution d p).naturality a
  rw [h]
  change weakEquivalences C ((sourceResolution d p).app j ≫ 𝟙 ((Q d).obj p.left))
  exact (weakEquivalences C).comp_mem _ _ (sourceResolution_weak d p j)
    ((weakEquivalences C).id_mem _)

/-- Every actual middle-frame operator remains weak, with its original constant-Q target. -/
theorem targetResolution_map_weak (p : Arrow C) {j k : SimplexCategory} (a : j ⟶ k) :
    weakEquivalences C ((cosimplicialFactor d p).Z.map a) := by
  apply (weakEquivalences C).of_postcomp _ _ (targetResolution_weak d p k)
  have h := (targetResolution d p).naturality a
  rw [h]
  change weakEquivalences C ((targetResolution d p).app j ≫ 𝟙 ((Q d).obj p.right))
  exact (weakEquivalences C).comp_mem _ _ (targetResolution_weak d p j)
    ((weakEquivalences C).id_mem _)

/-- The actual original I factor keeps the original source; it does not replace a J domain by Q. -/
def originalCellFactor : Arrow C ⥤ Arrow C where
  obj p := Arrow.mk ((cofibrant d).i.app p)
  map φ := Arrow.homMk φ.left ((cofibrant d).Z.map φ) ((cofibrant d).i.naturality φ)
  map_id p := by
    apply Arrow.hom_ext
    · rfl
    · exact (cofibrant d).Z.map_id p
  map_comp φ ψ := by
    apply Arrow.hom_ext
    · rfl
    · exact (cofibrant d).Z.map_comp φ ψ

/-- The original I projection is a complete natural Arrow comparison over unchanged original sources. -/
def originalCellProjection : originalCellFactor d ⟶ 𝟭 (Arrow C) where
  app p := Arrow.homMk (𝟙 p.left) ((cofibrant d).p.app p) (by
    change 𝟙 p.left ≫ p.hom = (cofibrant d).i.app p ≫ (cofibrant d).p.app p
    rw [Category.id_comp]
    exact (cofibrant d).fac_app.symm)
  naturality p q φ := by
    apply Arrow.hom_ext
    · change φ.left ≫ 𝟙 q.left = 𝟙 p.left ≫ φ.left
      simp
    · exact (cofibrant d).p.naturality φ

/-- Each factored source is the original actual source, including noncofibrant J domains. -/
theorem originalCellFactor_source (p : Arrow C) :
    ((originalCellFactor d).obj p).left = p.left := rfl

/-- The same fixed original I ordinal presents each factored original arrow. -/
def originalCellFactorComplex (p : Arrow C) :
    RelativeCellComplex.{w} (fun _ : κ.ord.ToType => d.I.homFamily)
      ((originalCellFactor d).obj p).hom := by
  let _ : d.I.IsCardinalForSmallObjectArgument κ := d.I_smallObject
  exact SmallObject.relativeCellComplexιObj d.I κ p.hom

/-- Every actual source-preserving I factor is an original cofibration. -/
theorem originalCellFactor_cofibration (p : Arrow C) :
    cofibrations C ((originalCellFactor d).obj p).hom := (cofibrant d).hi p

/-- The complete original I projection remains a base trivial fibration. -/
theorem originalCellProjection_trivialFibration (p : Arrow C) :
    trivialFibrations C ((originalCellProjection d).app p).right := by
  change trivialFibrations C ((cofibrant d).p.app p)
  exact (cofibrant d).hp p

/-- Original cofibration lifting constructs the actual original Arrow retract into its I factor. -/
def originalCellFactorRetract (p : Arrow C) (hp : cofibrations C p.hom) :
    RetractArrow p.hom ((originalCellFactor d).obj p).hom :=
  CellularCofibrationTransport.originalFactoryRetract d p.hom hp

/-- Every original J arrow is a base trivial cofibration by the original source right-class equality. -/
theorem original_J_trivialCofibration (j : d.J.toSet) : trivialCofibrations C j.1.hom := by
  have h : d.J.rlp.llp j.1.hom := d.J.le_llp_rlp _ j.2
  rwa [d.J_rlp, fibrations_llp] at h

/-- The original source-preserving I factor of an original J arrow remains base trivial. -/
theorem originalCellFactor_J_trivialCofibration (j : d.J.toSet) :
    trivialCofibrations C ((originalCellFactor d).obj j.1).hom := by
  refine ⟨originalCellFactor_cofibration d j.1, ?_⟩
  apply (weakEquivalences C).of_postcomp _ _
    (originalCellProjection_trivialFibration d j.1).2
  change weakEquivalences C ((cofibrant d).i.app j.1 ≫ (cofibrant d).p.app j.1)
  rw [(cofibrant d).fac_app]
  exact (original_J_trivialCofibration d j).2

/-- The augmented attaching family retains all original J labels and all original S labels and degrees. -/
def attachingFamily {K : Type wS} (S : K → Arrow C) : d.J.toSet ⊕ (K × ℕ) → Arrow C :=
  fun a => match a with
  | .inl j => (originalCellFactor d).obj j.1
  | .inr a => (originalCellFactor d).obj (latchingArrow d (S a.1) a.2)

/-- The original J branch still has its exact original source, without a cofibrancy assumption. -/
theorem attachingFamily_J_source {K : Type wS} (S : K → Arrow C) (j : d.J.toSet) :
    (attachingFamily d S (.inl j)).left = j.1.left := rfl

/-- Every actual family map uses its same original fixed-cardinal I cell presentation. -/
def attachingFamilyComplex {K : Type wS} (S : K → Arrow C)
    (a : d.J.toSet ⊕ (K × ℕ)) :
    RelativeCellComplex.{w} (fun _ : κ.ord.ToType => d.I.homFamily)
      (attachingFamily d S a).hom := by
  cases a with
  | inl j => exact originalCellFactorComplex d j.1
  | inr a => exact originalCellFactorComplex d (latchingArrow d (S a.1) a.2)

/-- All source-preserving family maps are original source cofibrations. -/
theorem attachingFamily_cofibration {K : Type wS} (S : K → Arrow C)
    (a : d.J.toSet ⊕ (K × ℕ)) : cofibrations C (attachingFamily d S a).hom := by
  cases a with
  | inl j => exact originalCellFactor_cofibration d j.1
  | inr a => exact originalCellFactor_cofibration d (latchingArrow d (S a.1) a.2)

/-- The generated attaching property keeps the entire same original labelled family. -/
def attachingClass {K : Type wS} (S : K → Arrow C) : MorphismProperty C :=
  ofHoms (fun a : d.J.toSet ⊕ (K × ℕ) => (attachingFamily d S a).hom)

/-- The actual source attaching property lies in the original cofibration class. -/
theorem attachingClass_le_cofibrations {K : Type wS} (S : K → Arrow C) :
    attachingClass d S ≤ cofibrations C := by
  intro X Y f hf
  rcases hf with ⟨a⟩
  exact attachingFamily_cofibration d S a

/-- The same source cofibration bound holds on the actual attaching left lifting class. -/
theorem attachingLeftClass_le_cofibrations {K : Type wS} (S : K → Arrow C) :
    (attachingClass d S).rlp.llp ≤ cofibrations C := by
  have h := MorphismProperty.antitone_llp
    (MorphismProperty.antitone_rlp (attachingClass_le_cofibrations d S))
  rwa [cofibrations_rlp, trivialFibrations_llp] at h

/-- Original J arrows are actual Arrow retracts of their same labelled attaching maps. -/
theorem original_J_le_attaching_retracts {K : Type wS} (S : K → Arrow C) :
    d.J ≤ (attachingClass d S).retracts := by
  intro X Y f hf
  let j : d.J.toSet := ⟨Arrow.mk f, hf⟩
  refine ⟨_, _, (attachingFamily d S (.inl j)).hom,
    originalCellFactorRetract d j.1 (original_J_trivialCofibration d j).1, ?_⟩
  change ofHoms (fun a : d.J.toSet ⊕ (K × ℕ) => (attachingFamily d S a).hom)
    (attachingFamily d S (Sum.inl j)).hom
  exact ofHoms.mk (Sum.inl j)

/-- The same augmented attaching injectives are original base fibrations. -/
theorem attachingRLP_le_fibrations {K : Type wS} (S : K → Arrow C) :
    (attachingClass d S).rlp ≤ fibrations C := by
  rw [← d.J_rlp, ← MorphismProperty.rlp_retracts (attachingClass d S)]
  exact MorphismProperty.antitone_rlp (original_J_le_attaching_retracts d S)

section SourceSmallness

variable {K : Type wS} (S : K → Arrow C) (h : CellularSource d)

local instance : d.J.IsSmall.{w} := d.J_smallObject.isSmall
include h in
/-- Original cellular source hypotheses prove smallness of each exact attaching source. -/
theorem attachingFamily_source_small (a : d.J.toSet ⊕ (K × ℕ)) :
    IsUniformlySmallRelativeTo.{w} d.I (attachingFamily d S a).left := by
  cases a with
  | inl j => exact h.J_domains_small j
  | inr a =>
    change IsUniformlySmallRelativeTo.{w} d.I (latchingArrow d (S a.1) a.2).left
    let _ : IsCofibrant (latchingArrow d (S a.1) a.2).left :=
      latchingArrow_source_cofibrant d (S a.1) a.2
    exact CellularLocalizationSmallness.cofibrant_uniformly_small h _

include h in
/-- The source's same original smallness transfers to every actual original cofibration chain. -/
theorem attachingFamily_cofibration_small (a : d.J.toSet ⊕ (K × ℕ)) :
    ∃ β : Cardinal.{w},
      ∀ (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType], β < μ →
        ∀ (F : μ.ord.ToType ⥤ C) [F.IsWellOrderContinuous],
          (∀ j : μ.ord.ToType, ¬ IsMax j →
            cofibrations C (F.map (homOfLE (Order.le_succ j)))) →
          PreservesColimit F (coyoneda.obj (op (attachingFamily d S a).left)) :=
  CellularCofibrationTransport.uniformOriginalCofibrationChains d
    (attachingFamily_source_small d S h a)

/-- Every original labelled source retains its genuinely earned chosen smallness bound. -/
def attachingSourceBound (a : d.J.toSet ⊕ (K × ℕ)) : Cardinal.{w} :=
  (attachingFamily_cofibration_small d S h a).choose

variable [Small.{w} K]

/-- One common bound is taken over the same small original labels. -/
def commonAttachingSourceBound : Cardinal.{w} :=
  max Cardinal.aleph0 (⨆ a : Shrink.{w} (d.J.toSet ⊕ (K × ℕ)),
    attachingSourceBound d S h ((equivShrink (d.J.toSet ⊕ (K × ℕ))).symm a))

/-- Every original source bound lies below the same actual common bound. -/
theorem attachingSourceBound_le_common (a : d.J.toSet ⊕ (K × ℕ)) :
    attachingSourceBound d S h a ≤ commonAttachingSourceBound d S h := by
  have ha := le_ciSup
    (f := fun k : Shrink.{w} (d.J.toSet ⊕ (K × ℕ)) =>
      attachingSourceBound d S h ((equivShrink (d.J.toSet ⊕ (K × ℕ))).symm k))
    Cardinal.bddAbove_of_small ((equivShrink (d.J.toSet ⊕ (K × ℕ))) a)
  simpa only [commonAttachingSourceBound, Equiv.symm_apply_apply] using
    ha.trans (le_max_right _ _)

/-- Actual original source-Hom preservation verifies the complete attaching small-object dictionary. -/
theorem attachingIsCardinalForSmallObjectArgument
    (μ : Cardinal.{w}) [Fact μ.IsRegular] [OrderBot μ.ord.ToType]
    (hμ : commonAttachingSourceBound d S h < μ) :
    (attachingClass d S).IsCardinalForSmallObjectArgument μ := by
  let _ : HasColimitsOfSize.{w, w} C := d.hasColimitsOfSize
  let _ : (cofibrations C).IsStableUnderCoproducts.{w} := by
    rw [← trivialFibrations_llp]
    infer_instance
  let _ : IsStableUnderTransfiniteComposition.{w} (cofibrations C) := by
    rw [← trivialFibrations_llp]
    infer_instance
  refine { isSmall := ?_, locallySmall := d.I_smallObject.locallySmall, preservesColimit := ?_ }
  · dsimp only [attachingClass]
    infer_instance
  intro A B X Y i hi f c
  rcases hi with ⟨a⟩
  apply (attachingFamily_cofibration_small d S h a).choose_spec μ
    ((attachingSourceBound_le_common d S h a).trans_lt hμ) c.F
  intro j _
  let t := c.transfiniteCompositionOfShape' (I := cofibrations C)
    (fun s => attachingClass_le_cofibrations d S _ s.i.2)
  have hClosure : ((cofibrations C).coproducts.{w}).pushouts ≤ cofibrations C :=
    (MorphismProperty.pushouts_monotone (MorphismProperty.coproducts_le.{w} (cofibrations C))).trans
      (cofibrations C).pushouts_le
  exact (t.ofLE hClosure).mem_map (homOfLE (Order.le_succ j))

/-- The actual attaching factory uses a chosen regular successor above the earned source bounds. -/
def attachingRank : Cardinal.{w} := Order.succ (commonAttachingSourceBound d S h)

/-- The constructed source rank is regular by the ordinary infinite-successor theorem. -/
theorem attachingRank_regular : (attachingRank d S h).IsRegular :=
  Cardinal.isRegular_succ (le_max_left _ _)

/-- The actual chosen original ordinal has its least stage, with no supplied localization dictionary. -/
@[instance_reducible]
def attachingRankOrderBot : OrderBot (attachingRank d S h).ord.ToType := by
  have hn : Nonempty (attachingRank d S h).ord.ToType := by
    apply Cardinal.mk_ne_zero_iff.mp
    rw [Cardinal.mk_toType, Cardinal.card_ord]
    exact ((Cardinal.aleph0_pos).trans_le (attachingRank_regular d S h).aleph0_le).ne'
  let _ := hn
  exact WellFoundedLT.toOrderBot _

/-- The entire horn-only functorial factorization is constructed from actual source smallness. -/
def hornFactorizationData :
    FunctorialFactorizationData (attachingClass d S).rlp.llp (attachingClass d S).rlp := by
  let _ : Fact (attachingRank d S h).IsRegular := ⟨attachingRank_regular d S h⟩
  let _ : OrderBot (attachingRank d S h).ord.ToType := attachingRankOrderBot d S h
  let _ : (attachingClass d S).IsCardinalForSmallObjectArgument (attachingRank d S h) :=
    attachingIsCardinalForSmallObjectArgument d S h _ (Order.lt_succ _)
  exact SmallObject.functorialFactorizationData (attachingClass d S) (attachingRank d S h)

/-- Every caller original Arrow keeps the same actual attaching middle map on its square. -/
theorem hornFactorizationData_map {p q : Arrow C} (φ : p ⟶ q) :
    letI : Fact (attachingRank d S h).IsRegular := ⟨attachingRank_regular d S h⟩
    letI : OrderBot (attachingRank d S h).ord.ToType := attachingRankOrderBot d S h
    letI : (attachingClass d S).IsCardinalForSmallObjectArgument (attachingRank d S h) :=
      attachingIsCardinalForSmallObjectArgument d S h _ (Order.lt_succ _)
    (hornFactorizationData d S h).Z.map φ =
      SmallObject.objMap (attachingClass d S) (attachingRank d S h) φ := rfl

/-- The original terminal arrows retain every original source map as a complete Arrow functor. -/
def terminalArrowFunctor : C ⥤ Arrow C where
  obj X := Arrow.mk (terminal.from X)
  map f := Arrow.homMk f (𝟙 (⊤_ C)) (by simp)
  map_id X := by
    apply Arrow.hom_ext <;> rfl
  map_comp f g := by
    apply Arrow.hom_ext
    · rfl
    · exact (Category.id_comp _).symm

/-- The actual horn-only object approximation is the original source-generated middle functor. -/
def hornObjectFunctor : C ⥤ C :=
  terminalArrowFunctor ⋙ (hornFactorizationData d S h).Z

/-- Each actual horn-only object unit is the original attaching-factory inclusion. -/
def hornUnit : 𝟭 C ⟶ hornObjectFunctor d S h where
  app X := (hornFactorizationData d S h).i.app (terminalArrowFunctor.obj X)
  naturality _ _ f := (hornFactorizationData d S h).i.naturality (terminalArrowFunctor.map f)

/-- The original horn-only factor has an actual projection to the same terminal object. -/
def hornProjection (X : C) : (hornObjectFunctor d S h).obj X ⟶ ⊤_ C :=
  (hornFactorizationData d S h).p.app (terminalArrowFunctor.obj X)

/-- The complete original horn-only unit and projection factor the same original terminal arrow. -/
theorem hornUnit_projection (X : C) :
    (hornUnit d S h).app X ≫ hornProjection d S h X = terminal.from X :=
  (hornFactorizationData d S h).fac_app

/-- The actual original source attaching property proves the same original unit is a cofibration. -/
theorem hornUnit_cofibration (X : C) : cofibrations C ((hornUnit d S h).app X) :=
  attachingLeftClass_le_cofibrations d S _
    ((hornFactorizationData d S h).hi (terminalArrowFunctor.obj X))

/-- Every actual projection lifts against all original labelled attaching maps. -/
theorem hornProjection_rlp (X : C) : (attachingClass d S).rlp (hornProjection d S h X) :=
  (hornFactorizationData d S h).hp (terminalArrowFunctor.obj X)

/-- Original J retracts prove base fibrancy of each actual horn-only approximation. -/
theorem hornObject_isFibrant (X : C) : IsFibrant ((hornObjectFunctor d S h).obj X) := by
  apply (isFibrant_iff_of_isTerminal (hornProjection d S h X) terminalIsTerminal).mpr
  exact (fibration_iff _).mpr (attachingRLP_le_fibrations d S _ (hornProjection_rlp d S h X))

/-- The actual attaching ordinal and original family present the same actual horn-only unit. -/
def hornUnitComplex (X : C) :
    letI : Fact (attachingRank d S h).IsRegular := ⟨attachingRank_regular d S h⟩
    letI : OrderBot (attachingRank d S h).ord.ToType := attachingRankOrderBot d S h
    RelativeCellComplex.{w}
      (fun _ : (attachingRank d S h).ord.ToType => (attachingClass d S).homFamily)
      ((hornUnit d S h).app X) := by
  let _ : Fact (attachingRank d S h).IsRegular := ⟨attachingRank_regular d S h⟩
  let _ : OrderBot (attachingRank d S h).ord.ToType := attachingRankOrderBot d S h
  let _ : (attachingClass d S).IsCardinalForSmallObjectArgument (attachingRank d S h) :=
    attachingIsCardinalForSmallObjectArgument d S h _ (Order.lt_succ _)
  exact SmallObject.relativeCellComplexιObj (attachingClass d S) (attachingRank d S h)
    (terminal.from X)

end SourceSmallness

end HomotopicalAlgebra.CellularLocalizingFamilies
