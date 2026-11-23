/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.GeneratedFrameHomComparison
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenDerivedAdjunction
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenDerivedReplacementComparison
import MathlibExt.AlgebraicTopology.ModelCategory.LeftBousfieldLocalization.CombinatorialEnrichment
import MathlibExt.AlgebraicTopology.SimplicialSet.SSetULiftRealizationWeak

/-!
# Descent of original Quillen adjunctions from their derived localizing images

The target retains an arbitrary original model category, independent object and
Hom universes, and its entire original adjunction. A target right frame is
constructed from ordinary model factorization, without target generation or
enrichment. Genuine bisimplicial comparisons identify its source tests with
the actual source cosimplicial frames. The coefficient universe lifts retain
both original Hom transposes.
-/

set_option autoImplicit false
noncomputable section

universe w wS uC uD vC vD

open CategoryTheory Limits MorphismProperty Opposite
open scoped Simplicial SSet.modelCategoryQuillen

namespace HomotopicalAlgebra.CombinatorialQuillenDescent

open CombinatorialSourceRecognition (localizationData)

section BareFrame

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]

/-- An ordinary original model factorization constructs one complete right frame. -/
def rightFrameFactor (Z : C) :
    MapFactorizationData
      (ReedyStructure.latchingClass SimplexCategory.reedyOp (trivialCofibrations C))
      (ReedyStructure.matchingClass SimplexCategory.reedyOp (fibrations C))
      (RightFrameHornGeometry.terminalProjection ((SimplicialObject.const C).obj Z)) := by
  letI : IsWeakFactorizationSystem
      (ReedyStructure.latchingClass SimplexCategory.reedyOp (trivialCofibrations C))
      (ReedyStructure.matchingClass SimplexCategory.reedyOp (fibrations C)) :=
    ReedyModel.cornerWfs SimplexCategory.reedyOp
      (factorizationData (trivialCofibrations C) (fibrations C))
  exact factorizationData _ _ _

/-- The actual original right frame is the middle of the ordinary complete factor. -/
abbrev rightFrame (Z : C) : SimplicialObject C := (rightFrameFactor Z).Z

/-- The actual original coaugmentation is the entire left natural factor. -/
abbrev rightCoaugmentation (Z : C) : (SimplicialObject.const C).obj Z ⟶ rightFrame Z :=
  (rightFrameFactor Z).i

/-- Every original right-frame matching map is a base fibration. -/
theorem rightFrame_matching (Z : C) (j : SimplexCategoryᵒᵖ) :
    fibrations C (ReedyStructure.matchingMap SimplexCategory.reedyOp (rightFrame Z) j) := by
  have hp : (rightFrameFactor Z).p = RightFrameHornGeometry.terminalProjection (rightFrame Z) := by
    apply NatTrans.ext
    funext k
    exact terminalIsTerminal.hom_ext _ _
  have h := (rightFrameFactor Z).hp j
  rw [hp] at h
  exact ((fibrations C).arrow_mk_iso_iff
    (RightFrameHornGeometry.terminalProjectionMatchingCornerIso (rightFrame Z) j)).mp h

/-- All original coaugmentation coefficients are weak by genuine original latching corners. -/
theorem rightCoaugmentation_weak (Z : C) (j : SimplexCategoryᵒᵖ) :
    weakEquivalences C ((rightCoaugmentation Z).app j) :=
  (ReedyModel.component_trivialCofibration_of_latchingCorners SimplexCategory.reedyOp
    (rightCoaugmentation Z) (rightFrameFactor Z).hi j).2

/-- Weak original source images control the full original left-frame mapping test. -/
theorem framePrecomp_weak
    {A A' : CosimplicialObject C} (t : A ⟶ A')
    (hA : ∀ j, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A j))
    (hA' : ∀ j, cofibrations C (ReedyStructure.latchingMap SimplexCategory.reedy A' j))
    {X X' : C} [IsCofibrant X] [IsCofibrant X']
    (a : A ⟶ (CosimplicialObject.const C).obj X)
    (a' : A' ⟶ (CosimplicialObject.const C).obj X')
    (ha : ∀ j, weakEquivalences C (a.app j))
    (ha' : ∀ j, weakEquivalences C (a'.app j))
    (f : X ⟶ X') [WeakEquivalence f]
    (ht : t ≫ a' = a ≫ (CosimplicialObject.const C).map f)
    (Z : C) [IsFibrant Z] :
    WeakEquivalence (ResolutionHomComplex.precomp t ((SimplicialObject.const C).obj Z)) := by
  let B := rightFrame Z
  let b := rightCoaugmentation Z
  let r := RightFrameHomBoundary.precomp f B
  let q := SSet.simplicialDiagonalFunctor.map (ResolutionHomBisimplicial.precomp t B)
  let ca := ResolutionHomBisimplicial.fromAugmentation a B
  let ca' := ResolutionHomBisimplicial.fromAugmentation a' B
  let cb := ResolutionHomBisimplicial.fromCoaugmentation A b
  let cb' := ResolutionHomBisimplicial.fromCoaugmentation A' b
  let _ : WeakEquivalence r := RightFrameHomBoundary.precomp_weak f B (rightFrame_matching Z)
  let _ : WeakEquivalence ca :=
    GeneratedFrameHomComparison.fromAugmentation_diagonal_weak A B a hA (rightFrame_matching Z) ha
  let _ : WeakEquivalence ca' :=
    GeneratedFrameHomComparison.fromAugmentation_diagonal_weak A' B a' hA' (rightFrame_matching Z) ha'
  let _ : WeakEquivalence cb :=
    GeneratedFrameHomComparison.fromCoaugmentation_diagonal_weak A B b hA
      (rightFrame_matching Z) (rightCoaugmentation_weak Z)
  let _ : WeakEquivalence cb' :=
    GeneratedFrameHomComparison.fromCoaugmentation_diagonal_weak A' B b hA'
      (rightFrame_matching Z) (rightCoaugmentation_weak Z)
  have hr : r ≫ ca = ca' ≫ q :=
    ResolutionHomBisimplicial.fromAugmentation_source_naturality a a' t f ht.symm B
  let _ : WeakEquivalence (ca' ≫ q) := hr ▸ (inferInstance : WeakEquivalence (r ≫ ca))
  let _ : WeakEquivalence q := weakEquivalence_of_precomp ca' q
  have hl : ResolutionHomComplex.precomp t ((SimplicialObject.const C).obj Z) ≫ cb = cb' ≫ q :=
    ResolutionHomBisimplicial.fromCoaugmentation_source_naturality t b
  let _ : WeakEquivalence
      (ResolutionHomComplex.precomp t ((SimplicialObject.const C).obj Z) ≫ cb) :=
    hl.symm ▸ (inferInstance : WeakEquivalence (cb' ≫ q))
  exact weakEquivalence_of_postcomp _ cb

end BareFrame

section OriginalAdjunction

variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)

/-- Both complete original Hom transposes retain independent coefficient universes. -/
def frameAdjunctionIso (A : CosimplicialObject C) (Z : D) :
    SSet.uliftFunctor.{vC, vD}.obj (ResolutionHomComplex.left (A ⋙ F) Z) ≅
      SSet.uliftFunctor.{vD, vC}.obj (ResolutionHomComplex.left A (G.obj Z)) :=
  NatIso.ofComponents
    (fun n =>
      { hom := ↾fun f => ULift.up (adj.homEquiv (A.obj n.unop) Z f.down)
        inv := ↾fun f => ULift.up ((adj.homEquiv (A.obj n.unop) Z).symm f.down)
        hom_inv_id := by ext f; exact congrArg ULift.up ((adj.homEquiv _ _).symm_apply_apply f.down)
        inv_hom_id := by ext f; exact congrArg ULift.up ((adj.homEquiv _ _).apply_symm_apply f.down) })
    (by
      intro n m g
      ext f
      change ULift.{vC} (F.obj (A.obj n.unop) ⟶ Z) at f
      apply ULift.ext
      change adj.homEquiv (A.obj m.unop) Z (F.map (A.map g.unop) ≫ f.down ≫ 𝟙 Z) =
        A.map g.unop ≫ adj.homEquiv (A.obj n.unop) Z f.down ≫ 𝟙 (G.obj Z)
      simpa only [Category.comp_id] using adj.homEquiv_naturality_left (A.map g.unop) f.down)

/-- The comparison retains every actual source frame morphism and its full transpose. -/
theorem frameAdjunctionIso_source {A A' : CosimplicialObject C} (t : A ⟶ A') (Z : D) :
    SSet.uliftFunctor.{vC, vD}.map
        (ResolutionHomComplex.precomp (Functor.whiskerRight t F) ((SimplicialObject.const D).obj Z)) ≫
      (frameAdjunctionIso adj A Z).hom =
    (frameAdjunctionIso adj A' Z).hom ≫
      SSet.uliftFunctor.{vD, vC}.map
        (ResolutionHomComplex.precomp t ((SimplicialObject.const C).obj (G.obj Z))) := by
  ext n f
  apply ULift.ext
  change adj.homEquiv (A.obj n.unop) Z (F.map (t.app n.unop) ≫ f.down) =
    t.app n.unop ≫ adj.homEquiv (A'.obj n.unop) Z f.down
  exact adj.homEquiv_naturality_left (t.app n.unop) f.down

/-- The comparison retains every actual original target morphism. -/
theorem frameAdjunctionIso_target (A : CosimplicialObject C) {Z Z' : D} (p : Z ⟶ Z') :
    SSet.uliftFunctor.{vC, vD}.map
        (ResolutionHomComplex.postcomp (A ⋙ F) ((SimplicialObject.const D).map p)) ≫
      (frameAdjunctionIso adj A Z').hom =
    (frameAdjunctionIso adj A Z).hom ≫
      SSet.uliftFunctor.{vD, vC}.map
        (ResolutionHomComplex.postcomp A ((SimplicialObject.const C).map (G.map p))) := by
  ext n f
  apply ULift.ext
  change adj.homEquiv (A.obj n.unop) Z' (f.down ≫ p) =
    adj.homEquiv (A.obj n.unop) Z f.down ≫ G.map p
  exact adj.homEquiv_naturality_right f.down p

include adj in
/-- The two actual complete frame precomposition tests are weak in their independent Hom universes together. -/
theorem framePrecompAdjunction_weak_iff {A A' : CosimplicialObject C} (t : A ⟶ A') (Z : D) :
    WeakEquivalence (ResolutionHomComplex.precomp (Functor.whiskerRight t F)
      ((SimplicialObject.const D).obj Z)) ↔
    WeakEquivalence (ResolutionHomComplex.precomp t ((SimplicialObject.const C).obj (G.obj Z))) := by
  let f := ResolutionHomComplex.precomp (Functor.whiskerRight t F) ((SimplicialObject.const D).obj Z)
  let g := ResolutionHomComplex.precomp t ((SimplicialObject.const C).obj (G.obj Z))
  let e : CategoryTheory.Arrow.mk (SSet.uliftFunctor.{vC, vD}.map f) ≅
      CategoryTheory.Arrow.mk (SSet.uliftFunctor.{vD, vC}.map g) :=
    CategoryTheory.Arrow.isoMk (frameAdjunctionIso adj A' Z) (frameAdjunctionIso adj A Z)
      (frameAdjunctionIso_source adj t Z).symm
  have h := (weakEquivalences SSet.{max vC vD}).arrow_mk_iso_iff e
  change SSet.realizationWeakEquivalences (SSet.uliftFunctor.{vC, vD}.map f) ↔
    SSet.realizationWeakEquivalences (SSet.uliftFunctor.{vD, vC}.map g) at h
  rw [weakEquivalence_iff, weakEquivalence_iff]
  change SSet.realizationWeakEquivalences f ↔ SSet.realizationWeakEquivalences g
  exact (SSet.realizationWeak_ulift_map_iff f).symm.trans
    (h.trans (SSet.realizationWeak_ulift_map_iff g))

end OriginalAdjunction

section DerivedImages

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [adj.IsQuillenAdjunction]

variable {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ)

open GeneratedFunctorialReplacements

/-- Weakness of a genuine derived image gives weakness of its same original generated-Q image. -/
theorem generatedImage_weak {X Y : C} (f : X ⟶ Y)
    (hf : IsIso ((quillenDerivedAdjunctionData adj).leftDerived.map ((weakEquivalences C).Q.map f))) :
    weakEquivalences D (F.map ((Q d).map f)) := by
  let T := quillenDerivedAdjunctionData adj
  let γC := (weakEquivalences C).Q
  let γD := (weakEquivalences D).Q
  let L := T.leftDerived
  let qX := (counit d).app X
  let qY := (counit d).app Y
  let _ : IsIso (γC.map qX) := Localization.inverts γC (weakEquivalences C) qX (counit_weak d X)
  let _ : IsIso (γC.map qY) := Localization.inverts γC (weakEquivalences C) qY (counit_weak d Y)
  let _ : IsIso (L.map (γC.map f)) := hf
  have hq : L.map (γC.map ((Q d).map f)) ≫ L.map (γC.map qY) =
      L.map (γC.map qX) ≫ L.map (γC.map f) := by
    rw [← L.map_comp, ← L.map_comp, ← γC.map_comp, ← γC.map_comp]
    exact L.congr_map (γC.congr_map ((counit d).naturality f))
  let _ : IsIso (L.map (γC.map ((Q d).map f))) := IsIso.of_isIso_fac_right hq
  let _ : IsCofibrant ((Q d).obj X) := Q_isCofibrant d X
  let _ : IsCofibrant ((Q d).obj Y) := Q_isCofibrant d Y
  let _ : IsIso (T.leftComparison.app ((Q d).obj X)) :=
    quillenDerived_leftComparison_isIso_of_isCofibrant adj _
  let _ : IsIso (T.leftComparison.app ((Q d).obj Y)) :=
    quillenDerived_leftComparison_isIso_of_isCofibrant adj _
  have hn := T.leftComparison.naturality ((Q d).map f)
  change L.map (γC.map ((Q d).map f)) ≫ T.leftComparison.app ((Q d).obj Y) =
    T.leftComparison.app ((Q d).obj X) ≫ γD.map (F.map ((Q d).map f)) at hn
  have hImage : IsIso (γD.map (F.map ((Q d).map f))) := IsIso.of_isIso_fac_left hn.symm
  exact (weakEquivalence_iff_isIso_map_of_isLocalization γD _).mpr hImage

/-- The whole actual original generated source frame after the original left adjoint. -/
def imageFrame (X : C) : CosimplicialObject D := (GeneratedFramings.leftFrame d).obj X ⋙ F

/-- The original full frame map is applied coefficient by coefficient by the same original left adjoint. -/
def imageFrameMap {X Y : C} (f : X ⟶ Y) : imageFrame (F := F) d X ⟶ imageFrame (F := F) d Y :=
  Functor.whiskerRight ((GeneratedFramings.leftFrame d).map f) F

/-- The actual original source augmentation retains every original left-adjoint image map. -/
def imageAugmentation (X : C) :
    imageFrame (F := F) d X ⟶ (CosimplicialObject.const D).obj (F.obj ((Q d).obj X)) where
  app j := F.map (((GeneratedFramings.leftResolution d).app X).app j)
  naturality i j g := by
    change F.map (((GeneratedFramings.leftFrame d).obj X).map g) ≫
      F.map (((GeneratedFramings.leftResolution d).app X).app j) =
        F.map (((GeneratedFramings.leftResolution d).app X).app i) ≫ 𝟙 _
    rw [Category.comp_id, ← F.map_comp]
    have h := (((GeneratedFramings.leftResolution d).app X).naturality g)
    change ((GeneratedFramings.leftFrame d).obj X).map g ≫
        ((GeneratedFramings.leftResolution d).app X).app j =
      ((GeneratedFramings.leftResolution d).app X).app i ≫ 𝟙 _ at h
    rw [Category.comp_id] at h
    exact F.congr_map h

omit [ModelCategory D] in
/-- Both actual original augmentation families retain the same original generated-Q source square. -/
theorem imageAugmentation_naturality {X Y : C} (f : X ⟶ Y) :
    imageFrameMap (F := F) d f ≫ imageAugmentation (F := F) d Y =
      imageAugmentation (F := F) d X ≫ (CosimplicialObject.const D).map (F.map ((Q d).map f)) := by
  ext j
  change F.map (((GeneratedFramings.leftFrame d).map f).app j) ≫
      F.map (((GeneratedFramings.leftResolution d).app Y).app j) =
    F.map (((GeneratedFramings.leftResolution d).app X).app j) ≫ F.map ((Q d).map f)
  rw [← F.map_comp, ← F.map_comp]
  exact F.congr_map (congrArg (fun t => t.app j) ((GeneratedFramings.leftResolution d).naturality f))

include adj in
/-- The original Quillen Brown law makes every unchanged image augmentation coefficient weak. -/
theorem imageAugmentation_weak (X : C) (j : SimplexCategory) :
    weakEquivalences D ((imageAugmentation (F := F) d X).app j) := by
  let _ : IsCofibrant (((GeneratedFramings.leftFrame d).obj X).obj j) :=
    LeftFrameHomWeakEquivalence.coefficient_isCofibrant _ (GeneratedFramings.leftFrame_latching_cofibration d X) j
  let _ : IsCofibrant ((Q d).obj X) := Q_isCofibrant d X
  let _ : IsCofibrant (((Q d ⋙ CosimplicialObject.const C).obj X).obj j) := by
    change IsCofibrant ((Q d).obj X)
    exact Q_isCofibrant d X
  let _ : WeakEquivalence (((GeneratedFramings.leftResolution d).app X).app j) :=
    (weakEquivalence_iff _).mpr (GeneratedFramings.leftResolution_weak d X j)
  exact (weakEquivalence_iff _).mp
    (Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant (adj := adj)
      (((GeneratedFramings.leftResolution d).app X).app j))

include adj in
/-- The original source latching colimit is preserved by the actual left adjoint. -/
theorem imageFrame_latching_cofibration (X : C) (j : SimplexCategory) :
    cofibrations D (ReedyStructure.latchingMap SimplexCategory.reedy (imageFrame (F := F) d X) j) := by
  let _ : F.IsLeftAdjoint := ⟨G, ⟨adj⟩⟩
  let A := (GeneratedFramings.leftFrame d).obj X
  let c : Cocone (SimplexCategory.reedy.latchingDiagram (imageFrame (F := F) d X) j) :=
    F.mapCocone (colimit.cocone (SimplexCategory.reedy.latchingDiagram A j))
  let hc : IsColimit c := isColimitOfPreserves F (colimit.isColimit _)
  have he : SimplexCategory.reedy.latchingMapWith (imageFrame (F := F) d X) j c hc =
      F.map (ReedyStructure.latchingMap SimplexCategory.reedy A j) := by
    apply hc.hom_ext
    intro k
    rw [ReedyStructure.latchingMapWith_ι]
    change _ = F.map (colimit.ι (SimplexCategory.reedy.latchingDiagram A j) k) ≫
      F.map (ReedyStructure.latchingMap SimplexCategory.reedy A j)
    rw [← F.map_comp, ReedyStructure.latchingMap_ι]
    rfl
  have hcof : cofibrations D (SimplexCategory.reedy.latchingMapWith
      (imageFrame (F := F) d X) j c hc) := he.symm ▸
    Adjunction.IsQuillenAdjunction.preservesCofibrations (adj := adj) _
      (GeneratedFramings.leftFrame_latching_cofibration d X j)
  let e := ReedyStructure.latchingColimitIso SimplexCategory.reedy j
    (imageFrame (F := F) d X) c hc
  have hcomp : cofibrations D (e.hom ≫ ReedyStructure.latchingMap SimplexCategory.reedy
      (imageFrame (F := F) d X) j) :=
    (ReedyStructure.latchingMapWith_colimitIso SimplexCategory.reedy j _ c hc) ▸ hcof
  exact ((cofibrations D).cancel_left_of_respectsIso _ _).mp hcomp

/-- Every original fibrant target has an actual generated S-local right-adjoint image from derived S weakness. -/
theorem generatedRight_localFibrant {K : Type wS} (S : K → Arrow C)
    (hS : ∀ k, IsIso ((quillenDerivedAdjunctionData adj).leftDerived.map
      ((weakEquivalences C).Q.map (S k).hom))) (Z : D) [IsFibrant Z] :
    generatedLocalFibrant d S (G.obj Z) := by
  let _ : IsFibrant (G.obj Z) := Adjunction.IsQuillenAdjunction.preservesFibrantObjects (adj := adj) inferInstance
  refine ⟨inferInstance, ?_⟩
  intro k
  let f := (S k).hom
  let _ : IsCofibrant (F.obj ((Q d).obj (S k).left)) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := adj) (Q_isCofibrant d _)
  let _ : IsCofibrant (F.obj ((Q d).obj (S k).right)) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects (adj := adj) (Q_isCofibrant d _)
  let _ : WeakEquivalence (F.map ((Q d).map f)) :=
    (weakEquivalence_iff _).mpr (generatedImage_weak adj d f (hS k))
  have hFrame : WeakEquivalence (ResolutionHomComplex.precomp (imageFrameMap (F := F) d f)
      ((SimplicialObject.const D).obj Z)) :=
    framePrecomp_weak (imageFrameMap (F := F) d f)
      (imageFrame_latching_cofibration adj d (S k).left)
      (imageFrame_latching_cofibration adj d (S k).right)
      (imageAugmentation (F := F) d (S k).left) (imageAugmentation (F := F) d (S k).right)
      (imageAugmentation_weak adj d (S k).left) (imageAugmentation_weak adj d (S k).right)
      (F.map ((Q d).map f)) (imageAugmentation_naturality d f) Z
  have hSource : WeakEquivalence
      (ResolutionHomComplex.precomp ((GeneratedFramings.leftFrame d).map f)
        ((SimplicialObject.const C).obj (G.obj Z))) :=
    (framePrecompAdjunction_weak_iff adj ((GeneratedFramings.leftFrame d).map f) Z).mp hFrame
  exact (GeneratedFrameHomComparison.leftFrame_precomp_weak_iff_generatedRight_isIso d f (G.obj Z)).mp hSource

end DerivedImages

section UniversalDescent

variable {C : Type uC} [Category.{vC} C] [ModelCategory C] [SimplicialCategory C]
  [IsLeftProper C] {κ : Cardinal.{w}} [Fact κ.IsRegular] [OrderBot κ.ord.ToType]
  (d : CofibrantGenerationData C κ) (a : CompatibleSimplicialMapping.Action C)
  {K : Type wS} (S : K → Arrow C) [Small.{w} K]
  (κLP : Cardinal.{w}) [Fact κLP.IsRegular] [IsCardinalLocallyPresentable C κLP]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]

/-- The unchanged original left functor on the actually produced selected source localization. -/
def leftFunctor (F : C ⥤ D) : CombinatorialEnrichment.Localized d a S κLP ⥤ D := by
  letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  exact LeftLocalized.toBase (localizationData d a S κLP) ⋙ F

/-- The unchanged original right functor retains every original object and map with its source tag. -/
def rightFunctor (G : D ⥤ C) : D ⥤ CombinatorialEnrichment.Localized d a S κLP := by
  letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  exact G ⋙ LeftLocalized.ofBase (localizationData d a S κLP)

variable {F : C ⥤ D} {G : D ⥤ C}

/-- The full original adjunction survives with exactly its original unit, counit, and triangle laws. -/
def adjunction (adj : F ⊣ G) : leftFunctor d a S κLP F ⊣ rightFunctor d a S κLP G where
  unit :=
    { app X := InducedCategory.homMk (adj.unit.app X.1)
      naturality _ _ f := by
        apply InducedCategory.hom_ext
        exact adj.unit.naturality f.hom }
  counit :=
    { app Z := adj.counit.app Z
      naturality _ _ f := adj.counit.naturality f }
  left_triangle_components X := adj.left_triangle_components X.1
  right_triangle_components Z := by
    apply InducedCategory.hom_ext
    exact adj.right_triangle_components Z

omit [ModelCategory D] in
/-- Every entire original left-functor map retains its original value. -/
theorem leftFunctor_map {X Y : CombinatorialEnrichment.Localized d a S κLP} (f : X ⟶ Y) :
    (leftFunctor d a S κLP F).map f = F.map f.hom := rfl

omit [ModelCategory D] in
/-- Every entire original right-functor map retains its original value. -/
theorem rightFunctor_map {X Y : D} (f : X ⟶ Y) :
    ((rightFunctor d a S κLP G).map f).hom = G.map f := rfl

omit [ModelCategory D] in
/-- The whole original unit is the same actual component at every original source object. -/
theorem adjunction_unit (adj : F ⊣ G) (X : CombinatorialEnrichment.Localized d a S κLP) :
    ((adjunction d a S κLP adj).unit.app X).hom = adj.unit.app X.1 := rfl

omit [ModelCategory D] in
/-- The whole original counit is the same actual component at every original target object. -/
theorem adjunction_counit (adj : F ⊣ G) (Z : D) :
    (adjunction d a S κLP adj).counit.app Z = adj.counit.app Z := rfl

omit [ModelCategory D] in
/-- Both Hom universes and the entire forward original Hom transpose are retained. -/
theorem adjunction_homEquiv (adj : F ⊣ G) (X : CombinatorialEnrichment.Localized d a S κLP) (Z : D)
    (f : (leftFunctor d a S κLP F).obj X ⟶ Z) :
    (((adjunction d a S κLP adj).homEquiv X Z) f).hom = adj.homEquiv X.1 Z f := rfl

omit [ModelCategory D] in
/-- Both Hom universes and the inverse original Hom transpose are retained. -/
theorem adjunction_homEquiv_symm (adj : F ⊣ G) (X : CombinatorialEnrichment.Localized d a S κLP) (Z : D)
    (f : X ⟶ (rightFunctor d a S κLP G).obj Z) :
    (((adjunction d a S κLP adj).homEquiv X Z).symm f) = (adj.homEquiv X.1 Z).symm f.hom := rfl

variable (adj : F ⊣ G) [baseQuillen : adj.IsQuillenAdjunction]

omit [IsLeftProper C] [Small.{w} K] [Fact κLP.IsRegular] [IsCardinalLocallyPresentable C κLP] in
include a in
/-- Every original fibrant target has its actual original S-local right-adjoint image, from derived S weakness. -/
theorem right_localFibrant
    (hS : ∀ k, IsIso ((quillenDerivedAdjunctionData adj).leftDerived.map
      ((weakEquivalences C).Q.map (S k).hom))) (Z : D) [IsFibrant Z] :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    isLocalFibrant S (G.obj Z) := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  exact (GeneratedLocalReplacement.generatedLocalFibrant_iff_original d a S (G.obj Z)).mp
    (generatedRight_localFibrant adj d S hS Z)

/-- Every original left Quillen adjunction with derived-weak S images descends to the actual localization. -/
theorem isQuillenAdjunction
    (hS : ∀ k, IsIso ((quillenDerivedAdjunctionData adj).leftDerived.map
      ((weakEquivalences C).Q.map (S k).hom))) :
    (adjunction d a S κLP adj).IsQuillenAdjunction := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  let LC := localizationData d a S κLP
  apply Adjunction.IsQuillenAdjunction.mkOfPreservesCofibrationsAndFibrationsBetweenFibrantObjects
  · intro X Y i hi
    change cofibrations C i.hom at hi
    exact baseQuillen.preservesCofibrations i.hom hi
  · intro X Y p hp
    let _ : IsFibrant X := hp.2.1
    let _ : IsFibrant Y := hp.2.2
    have hX := right_localFibrant d a S adj hS X
    have hY := right_localFibrant d a S adj hS Y
    exact (LeftLocalized.fibration_iff_of_local LC ((rightFunctor d a S κLP G).map p) hX hY).mpr
      (Adjunction.IsQuillenAdjunction.preservesFibrations (adj := adj) p hp.1)

/-- Both canonical total derived functors and all their original comparison maps descend together. -/
def derivedAdjunctionData
    (hS : ∀ k, IsIso ((quillenDerivedAdjunctionData adj).leftDerived.map
      ((weakEquivalences C).Q.map (S k).hom))) :
    QuillenDerivedAdjunctionData (adjunction d a S κLP adj) := by
  let _ : (adjunction d a S κLP adj).IsQuillenAdjunction := isQuillenAdjunction d a S κLP adj hS
  exact quillenDerivedAdjunctionData (adjunction d a S κLP adj)

/-- The actual source tag functor retains every original object and arrow. -/
def tagFunctor : C ⥤ CombinatorialEnrichment.Localized d a S κLP := rightFunctor d a S κLP (𝟭 C)

/-- The identity comparison induces the actual functor on the two original weak localizations. -/
def sourceLocalizationFunctor :
    (weakEquivalences C).Localization ⥤
      (weakEquivalences (CombinatorialEnrichment.Localized d a S κLP)).Localization := by
  letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  let LC := localizationData d a S κLP
  let γL := (weakEquivalences (CombinatorialEnrichment.Localized d a S κLP)).Q
  have h : (weakEquivalences C).IsInvertedBy (tagFunctor d a S κLP ⋙ γL) := by
    intro X Y f hf
    exact Localization.inverts γL (weakEquivalences (CombinatorialEnrichment.Localized d a S κLP))
      ((tagFunctor d a S κLP).map f) (by
        change localEquivalences S f
        exact LC.baseWeak_le f hf)
  exact Localization.Construction.lift _ h

/-- The entire original projection diagram commutes, on all objects and all morphisms. -/
theorem sourceLocalization_projection :
    (weakEquivalences C).Q ⋙ sourceLocalizationFunctor d a S κLP =
      tagFunctor d a S κLP ⋙ (weakEquivalences (CombinatorialEnrichment.Localized d a S κLP)).Q :=
  Localization.Construction.fac _ _

/-- Both complete natural directions of the original projection comparison are retained. -/
def sourceLocalizationComparison :
    (weakEquivalences C).Q ⋙ sourceLocalizationFunctor d a S κLP ≅
      tagFunctor d a S κLP ⋙ (weakEquivalences (CombinatorialEnrichment.Localized d a S κLP)).Q :=
  eqToIso (sourceLocalization_projection d a S κLP)

/-- The entire left derived comparison uses the original source projection and descended counit comparison. -/
def leftDescentComparison
    (hS : ∀ k, IsIso ((quillenDerivedAdjunctionData adj).leftDerived.map
      ((weakEquivalences C).Q.map (S k).hom))) :
    (weakEquivalences C).Q ⋙
        (sourceLocalizationFunctor d a S κLP ⋙ (derivedAdjunctionData d a S κLP adj hS).leftDerived) ⟶
      F ⋙ (weakEquivalences D).Q :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (sourceLocalizationComparison d a S κLP).hom _ ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (tagFunctor d a S κLP) (derivedAdjunctionData d a S κLP adj hS).leftComparison

/-- The entire right derived comparison uses the same source projection and original unit comparison. -/
def rightDescentComparison :
    rightFunctor d a S κLP G ⋙ (weakEquivalences (CombinatorialEnrichment.Localized d a S κLP)).Q ⟶
      (weakEquivalences D).Q ⋙
        ((quillenDerivedAdjunctionData adj).rightDerived ⋙ sourceLocalizationFunctor d a S κLP) :=
  Functor.whiskerLeft G (sourceLocalizationComparison d a S κLP).inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (quillenDerivedAdjunctionData adj).rightComparison _ ≫
    (Functor.associator _ _ _).hom

/-- The original cofibrant derivability structure proves the full descended left composite derived. -/
theorem leftDescentComparison_isDerived
    (hS : ∀ k, IsIso ((quillenDerivedAdjunctionData adj).leftDerived.map
      ((weakEquivalences C).Q.map (S k).hom))) :
    Functor.IsLeftDerivedFunctor
      (sourceLocalizationFunctor d a S κLP ⋙ (derivedAdjunctionData d a S κLP adj hS).leftDerived)
      (leftDescentComparison d a S κLP adj hS) (weakEquivalences C) := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  let LC := localizationData d a S κLP
  let _ : (adjunction d a S κLP adj).IsQuillenAdjunction := isQuillenAdjunction d a S κLP adj hS
  let _ : (LeftLocalized.equivalence LC).toAdjunction.IsQuillenAdjunction := LeftLocalized.ofBase_isLeftQuillen LC
  let Φ := CofibrantObject.localizerMorphism C
  have h : Φ.Derives (F ⋙ (weakEquivalences D).Q) := by
    intro A B f hf
    let _ : WeakEquivalence f.hom := by
      rw [← weakEquivalence_iff_of_objectProperty, weakEquivalence_iff]
      exact hf
    let _ : WeakEquivalence (F.map f.hom) :=
      Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_cofibrant (adj := adj) f.hom
    exact Localization.inverts (weakEquivalences D).Q (weakEquivalences D) (F.map f.hom)
      (mem_weakEquivalences _)
  apply h.isLeftDerivedFunctor_of_isIso (leftDescentComparison d a S κLP adj hS)
  intro X
  let _ : IsCofibrant ((tagFunctor d a S κLP).obj (Φ.functor.obj X)) :=
    Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := (LeftLocalized.equivalence LC).toAdjunction) (inferInstance : IsCofibrant X.obj)
  let _ : IsIso ((derivedAdjunctionData d a S κLP adj hS).leftComparison.app
      ((tagFunctor d a S κLP).obj (Φ.functor.obj X))) :=
    quillenDerived_leftComparison_isIso_of_isCofibrant (adjunction d a S κLP adj) _
  change IsIso
    ((Functor.associator (weakEquivalences C).Q (sourceLocalizationFunctor d a S κLP)
        (derivedAdjunctionData d a S κLP adj hS).leftDerived).inv.app (Φ.functor.obj X) ≫
      (derivedAdjunctionData d a S κLP adj hS).leftDerived.map
        ((sourceLocalizationComparison d a S κLP).hom.app (Φ.functor.obj X)) ≫
      (Functor.associator (tagFunctor d a S κLP)
        (weakEquivalences (CombinatorialEnrichment.Localized d a S κLP)).Q
        (derivedAdjunctionData d a S κLP adj hS).leftDerived).hom.app (Φ.functor.obj X) ≫
      (derivedAdjunctionData d a S κLP adj hS).leftComparison.app
        ((tagFunctor d a S κLP).obj (Φ.functor.obj X)))
  infer_instance

/-- The original fibrant derivability structure proves the full original right composite derived. -/
theorem rightDescentComparison_isDerived :
    Functor.IsRightDerivedFunctor
      ((quillenDerivedAdjunctionData adj).rightDerived ⋙ sourceLocalizationFunctor d a S κLP)
      (rightDescentComparison d a S κLP adj) (weakEquivalences D) := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  let LC := localizationData d a S κLP
  let γL := (weakEquivalences (CombinatorialEnrichment.Localized d a S κLP)).Q
  let Φ := FibrantObject.localizerMorphism D
  have h : Φ.Derives (rightFunctor d a S κLP G ⋙ γL) := by
    intro A B f hf
    let _ : WeakEquivalence f.hom := by
      rw [← weakEquivalence_iff_of_objectProperty, weakEquivalence_iff]
      exact hf
    let _ : WeakEquivalence (G.map f.hom) :=
      Adjunction.IsQuillenAdjunction.map_weakEquivalence_of_fibrant (adj := adj) f.hom
    exact Localization.inverts γL (weakEquivalences (CombinatorialEnrichment.Localized d a S κLP))
      ((rightFunctor d a S κLP G).map f.hom) (by
        change localEquivalences S (G.map f.hom)
        exact LC.baseWeak_le _ (mem_weakEquivalences _))
  apply h.isRightDerivedFunctor_of_isIso (rightDescentComparison d a S κLP adj)
  intro Y
  let _ : IsFibrant (Φ.functor.obj Y) := (inferInstance : IsFibrant Y.obj)
  let _ : IsIso ((quillenDerivedAdjunctionData adj).rightComparison.app (Φ.functor.obj Y)) :=
    quillenDerived_rightComparison_isIso_of_isFibrant adj _
  change IsIso
    ((sourceLocalizationComparison d a S κLP).inv.app (G.obj (Φ.functor.obj Y)) ≫
      (Functor.associator G (weakEquivalences C).Q (sourceLocalizationFunctor d a S κLP)).inv.app
        (Φ.functor.obj Y) ≫
      (sourceLocalizationFunctor d a S κLP).map
        ((quillenDerivedAdjunctionData adj).rightComparison.app (Φ.functor.obj Y)) ≫
      (Functor.associator (weakEquivalences D).Q (quillenDerivedAdjunctionData adj).rightDerived
        (sourceLocalizationFunctor d a S κLP)).hom.app (Φ.functor.obj Y))
  infer_instance

/-- The full original and descended total left derived functors have their actual natural comparison. -/
def leftDerivedComparison
    (hS : ∀ k, IsIso ((quillenDerivedAdjunctionData adj).leftDerived.map
      ((weakEquivalences C).Q.map (S k).hom))) :
    sourceLocalizationFunctor d a S κLP ⋙ (derivedAdjunctionData d a S κLP adj hS).leftDerived ≅
      (quillenDerivedAdjunctionData adj).leftDerived := by
  let _ := leftDescentComparison_isDerived d a S κLP adj hS
  let _ := (quillenDerivedAdjunctionData adj).leftIsDerived
  exact Functor.leftDerivedUnique _ _ (leftDescentComparison d a S κLP adj hS)
    (quillenDerivedAdjunctionData adj).leftComparison (weakEquivalences C)

/-- The full original and descended total right derived functors retain their actual natural comparison. -/
def rightDerivedComparison
    (hS : ∀ k, IsIso ((quillenDerivedAdjunctionData adj).leftDerived.map
      ((weakEquivalences C).Q.map (S k).hom))) :
    (quillenDerivedAdjunctionData adj).rightDerived ⋙ sourceLocalizationFunctor d a S κLP ≅
      (derivedAdjunctionData d a S κLP adj hS).rightDerived := by
  let _ := rightDescentComparison_isDerived d a S κLP adj
  let _ := (derivedAdjunctionData d a S κLP adj hS).rightIsDerived
  exact Functor.rightDerivedUnique _ _ (rightDescentComparison d a S κLP adj)
    (derivedAdjunctionData d a S κLP adj hS).rightComparison (weakEquivalences D)

/-- The entire left comparison recovers the original full derived counit comparison. -/
theorem leftDerivedComparison_fac
    (hS : ∀ k, IsIso ((quillenDerivedAdjunctionData adj).leftDerived.map
      ((weakEquivalences C).Q.map (S k).hom))) :
    Functor.whiskerLeft (weakEquivalences C).Q (leftDerivedComparison d a S κLP adj hS).hom ≫
        (quillenDerivedAdjunctionData adj).leftComparison = leftDescentComparison d a S κLP adj hS := by
  simp [leftDerivedComparison, Functor.leftDerivedUnique, Functor.leftDerivedNatIso]

/-- The entire right comparison recovers the full descended derived unit comparison. -/
theorem rightDerivedComparison_fac
    (hS : ∀ k, IsIso ((quillenDerivedAdjunctionData adj).leftDerived.map
      ((weakEquivalences C).Q.map (S k).hom))) :
    rightDescentComparison d a S κLP adj ≫
      Functor.whiskerLeft (weakEquivalences D).Q (rightDerivedComparison d a S κLP adj hS).hom =
        (derivedAdjunctionData d a S κLP adj hS).rightComparison := by
  simp [rightDerivedComparison, Functor.rightDerivedUnique, Functor.rightDerivedNatIso]

/-- The complete source-produced enriched localization and universal derived-image Quillen descent. -/
theorem constructs
    (hS : ∀ k, IsIso ((quillenDerivedAdjunctionData adj).leftDerived.map
      ((weakEquivalences C).Q.map (S k).hom))) :
    letI : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
      ⟨⟨d.cofibrantFactorizationData⟩⟩
    letI : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
      ⟨⟨d.fibrantFactorizationData⟩⟩
    let LC := localizationData d a S κLP
    ∃ (aL : CompatibleSimplicialMapping.Action (CombinatorialEnrichment.Localized d a S κLP))
      (rL : GeneratedFunctorialReplacements.Data (C := CombinatorialEnrichment.Localized d a S κLP)),
      (∃ m : ModelCategory (CombinatorialEnrichment.Localized d a S κLP),
        m = CombinatorialEnrichment.modelCategory d a S κLP) ∧
      IsCombinatorialModelCategory.{w} (CombinatorialEnrichment.Localized d a S κLP) ∧
      aL = CombinatorialEnrichment.action d a S κLP ∧
      rL = CombinatorialEnrichment.replacementData d a S κLP ∧
      (weakEquivalences (CombinatorialEnrichment.Localized d a S κLP) =
          (localEquivalences S).inverseImage (LeftLocalized.toBase LC) ∧
        cofibrations (CombinatorialEnrichment.Localized d a S κLP) =
          (cofibrations C).inverseImage (LeftLocalized.toBase LC) ∧
        fibrations (CombinatorialEnrichment.Localized d a S κLP) =
          (localizedFibrations S).inverseImage (LeftLocalized.toBase LC) ∧
        trivialCofibrations (CombinatorialEnrichment.Localized d a S κLP) =
          (cofibrations C ⊓ localEquivalences S).inverseImage (LeftLocalized.toBase LC) ∧
        trivialFibrations (CombinatorialEnrichment.Localized d a S κLP) =
          (trivialFibrations C).inverseImage (LeftLocalized.toBase LC)) ∧
      (∀ X : CombinatorialEnrichment.Localized d a S κLP, IsFibrant X ↔ isLocalFibrant S X.1) ∧
      (∀ {X Y : CombinatorialEnrichment.Localized d a S κLP} (f : X ⟶ Y),
        isLocalFibrant S X.1 → isLocalFibrant S Y.1 →
          (weakEquivalences (CombinatorialEnrichment.Localized d a S κLP) f ↔ weakEquivalences C f.hom)) ∧
      (∃ (χ : Cardinal.{w}) (hχ : Fact χ.IsRegular) (hbot : OrderBot χ.ord.ToType),
        letI : Fact χ.IsRegular := hχ
        letI : OrderBot χ.ord.ToType := hbot
        κLP ≤ χ ∧ κ ≤ χ ∧ IsCardinalLocallyPresentable C χ ∧
          IsCardinalLocallyPresentable (CombinatorialEnrichment.Localized d a S κLP) χ ∧
          (localEquivalences S).IsCardinalAccessible χ ∧
          ∃ g : CofibrantGenerationData (CombinatorialEnrichment.Localized d a S κLP) χ,
            g.I = d.I.strictMap (LeftLocalized.ofBase LC) ∧
              g.J = (CombinatorialSourceRecognition.smithData d a S κLP).J.strictMap (LeftLocalized.ofBase LC)) ∧
      (adjunction d a S κLP adj).IsQuillenAdjunction ∧
      Nonempty (QuillenDerivedAdjunctionData (adjunction d a S κLP adj)) ∧
      Nonempty (sourceLocalizationFunctor d a S κLP ⋙
        (derivedAdjunctionData d a S κLP adj hS).leftDerived ≅
          (quillenDerivedAdjunctionData adj).leftDerived) ∧
      Nonempty ((quillenDerivedAdjunctionData adj).rightDerived ⋙ sourceLocalizationFunctor d a S κLP ≅
        (derivedAdjunctionData d a S κLP adj hS).rightDerived) := by
  let : HasFunctorialFactorization (cofibrations C) (trivialFibrations C) :=
    ⟨⟨d.cofibrantFactorizationData⟩⟩
  let : HasFunctorialFactorization (trivialCofibrations C) (fibrations C) :=
    ⟨⟨d.fibrantFactorizationData⟩⟩
  refine ⟨CombinatorialEnrichment.action d a S κLP, CombinatorialEnrichment.replacementData d a S κLP,
    ⟨CombinatorialEnrichment.modelCategory d a S κLP, rfl⟩, inferInstance,
    rfl, rfl, CombinatorialEnrichment.fiveClasses d a S κLP,
    CombinatorialEnrichment.fibrant_iff d a S κLP, ?_,
    CombinatorialEnrichment.generationAtCommonRank d a S κLP,
    isQuillenAdjunction d a S κLP adj hS, ⟨derivedAdjunctionData d a S κLP adj hS⟩,
    ⟨leftDerivedComparison d a S κLP adj hS⟩, ⟨rightDerivedComparison d a S κLP adj hS⟩⟩
  intro X Y f hX hY
  exact CombinatorialEnrichment.weakEquivalence_iff_of_local d a S κLP f hX hY

end UniversalDescent

end HomotopicalAlgebra.CombinatorialQuillenDescent
