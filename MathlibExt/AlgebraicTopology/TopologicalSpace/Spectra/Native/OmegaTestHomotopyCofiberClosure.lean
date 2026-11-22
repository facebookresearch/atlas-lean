/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.DerivedStableClasses
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.Replacement
import MathlibExt.AlgebraicTopology.ModelCategory.HomotopyPushout
import MathlibExt.Topology.Category.PointedCGWH.NativeMappingPushout
import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.BasedHomotopyExtension
import MathlibExt.AlgebraicTopology.TopologicalSpace.ModelCategory.PointedCGWHBasedHomotopyExtension
import MathlibExt.AlgebraicTopology.Spectra.Sequential.MappingTelescope.ClosedStages

/-!
# Original native coherent span approximations

The original I factorization, at the caller's realized-generator cardinal and
bottom, supplies a coherent cofibrant approximation of every native walking
span. All three endpoint maps and both actual span squares are retained.
The colimit comparison is constructed as a map, without asserting that it is
level weak for arbitrary badly based homotopy cofibrations. That comparison is
the subsequent mathematical obligation for arbitrary Omega-test cobase change.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open MonoidalCategory
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.NativeOmegaWeakClosure

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective

private abbrev D := EnrichedFunctorCat PointedCGWH.{u, v} I

private def originalFstArrow : (WalkingSpan ⥤ D (I := I)) ⥤ Arrow (D (I := I)) where
  obj F := Arrow.mk ((Replacement.cofibrantReplacementCounit (B := B)).app
    (F.obj WalkingSpan.zero) ≫ F.map WalkingSpan.Hom.fst)
  map {F G} η := Arrow.homMk
    ((Replacement.cofibrantReplacement (B := B)).map (η.app WalkingSpan.zero))
    (η.app WalkingSpan.left) (by
      calc
        _ = ((Replacement.cofibrantReplacement (B := B)).map
            (η.app WalkingSpan.zero) ≫
            (Replacement.cofibrantReplacementCounit (B := B)).app
              (G.obj WalkingSpan.zero)) ≫ G.map WalkingSpan.Hom.fst :=
          (Category.assoc _ _ _).symm
        _ = ((Replacement.cofibrantReplacementCounit (B := B)).app
            (F.obj WalkingSpan.zero) ≫ η.app WalkingSpan.zero) ≫
              G.map WalkingSpan.Hom.fst := by
          rw [Replacement.cofibrantReplacementCounit_naturality]
        _ = _ := by
          rw [Category.assoc, ← η.naturality WalkingSpan.Hom.fst, ← Category.assoc]
          rfl)
  map_id F := by
    apply Arrow.hom_ext
    · exact (Replacement.cofibrantReplacement (B := B)).map_id _
    · rfl
  map_comp η θ := by
    apply Arrow.hom_ext
    · exact (Replacement.cofibrantReplacement (B := B)).map_comp _ _
    · rfl

private def originalSndArrow : (WalkingSpan ⥤ D (I := I)) ⥤ Arrow (D (I := I)) where
  obj F := Arrow.mk ((Replacement.cofibrantReplacementCounit (B := B)).app
    (F.obj WalkingSpan.zero) ≫ F.map WalkingSpan.Hom.snd)
  map {F G} η := Arrow.homMk
    ((Replacement.cofibrantReplacement (B := B)).map (η.app WalkingSpan.zero))
    (η.app WalkingSpan.right) (by
      calc
        _ = ((Replacement.cofibrantReplacement (B := B)).map
            (η.app WalkingSpan.zero) ≫
            (Replacement.cofibrantReplacementCounit (B := B)).app
              (G.obj WalkingSpan.zero)) ≫ G.map WalkingSpan.Hom.snd :=
          (Category.assoc _ _ _).symm
        _ = ((Replacement.cofibrantReplacementCounit (B := B)).app
            (F.obj WalkingSpan.zero) ≫ η.app WalkingSpan.zero) ≫
              G.map WalkingSpan.Hom.snd := by
          rw [Replacement.cofibrantReplacementCounit_naturality]
        _ = _ := by
          rw [Category.assoc, ← η.naturality WalkingSpan.Hom.snd, ← Category.assoc]
          rfl)
  map_id F := by
    apply Arrow.hom_ext
    · exact (Replacement.cofibrantReplacement (B := B)).map_id _
    · rfl
  map_comp η θ := by
    apply Arrow.hom_ext
    · exact (Replacement.cofibrantReplacement (B := B)).map_comp _ _
    · rfl

/-- The original I algorithm applied to both complete Q-source span arrows. -/
def originalSpanFunctor : (WalkingSpan ⥤ D (I := I)) ⥤ WalkingSpan ⥤ D (I := I) where
  obj F := span
    ((Native.cofibrantFactorizationData (B := B)).i.app ((originalFstArrow (B := B)).obj F))
    ((Native.cofibrantFactorizationData (B := B)).i.app ((originalSndArrow (B := B)).obj F))
  map {F G} η := spanHomMk
    ((Replacement.cofibrantReplacement (B := B)).map (η.app WalkingSpan.zero))
    ((Native.cofibrantFactorizationData (B := B)).Z.map
      ((originalFstArrow (B := B)).map η))
    ((Native.cofibrantFactorizationData (B := B)).Z.map
      ((originalSndArrow (B := B)).map η))
    ((Native.cofibrantFactorizationData (B := B)).i.naturality
      ((originalFstArrow (B := B)).map η)).symm
    ((Native.cofibrantFactorizationData (B := B)).i.naturality
      ((originalSndArrow (B := B)).map η)).symm
  map_id F := by
    apply NatTrans.ext
    funext j
    rcases j with (_ | _ | _)
    · exact (Replacement.cofibrantReplacement (B := B)).map_id _
    · change (Native.cofibrantFactorizationData (B := B)).Z.map
        ((originalFstArrow (B := B)).map (𝟙 F)) = 𝟙 _
      rw [(originalFstArrow (B := B)).map_id]
      exact (Native.cofibrantFactorizationData (B := B) (A := I)).Z.map_id _
    · change (Native.cofibrantFactorizationData (B := B)).Z.map
        ((originalSndArrow (B := B)).map (𝟙 F)) = 𝟙 _
      rw [(originalSndArrow (B := B)).map_id]
      exact (Native.cofibrantFactorizationData (B := B) (A := I)).Z.map_id _
  map_comp η θ := by
    apply NatTrans.ext
    funext j
    rcases j with (_ | _ | _)
    · exact (Replacement.cofibrantReplacement (B := B)).map_comp _ _
    · change (Native.cofibrantFactorizationData (B := B)).Z.map
        ((originalFstArrow (B := B)).map (η ≫ θ)) = _
      rw [(originalFstArrow (B := B)).map_comp]
      exact (Native.cofibrantFactorizationData (B := B) (A := I)).Z.map_comp _ _
    · change (Native.cofibrantFactorizationData (B := B)).Z.map
        ((originalSndArrow (B := B)).map (η ≫ θ)) = _
      rw [(originalSndArrow (B := B)).map_comp]
      exact (Native.cofibrantFactorizationData (B := B) (A := I)).Z.map_comp _ _

/-- All original replacement endpoint maps form the actual coherent span counit. -/
def originalSpanCounit : originalSpanFunctor (B := B) (I := I) ⟶
    𝟭 (WalkingSpan ⥤ D (I := I)) where
  app F := spanHomMk
    ((Replacement.cofibrantReplacementCounit (B := B)).app (F.obj WalkingSpan.zero))
    ((Native.cofibrantFactorizationData (B := B)).p.app ((originalFstArrow (B := B)).obj F))
    ((Native.cofibrantFactorizationData (B := B)).p.app ((originalSndArrow (B := B)).obj F))
    (Native.cofibrantFactorizationData (B := B)).fac_app
    (Native.cofibrantFactorizationData (B := B)).fac_app
  naturality F G η := by
    apply NatTrans.ext
    funext j
    rcases j with (_ | _ | _)
    · exact (Replacement.cofibrantReplacementCounit (B := B)).naturality _
    · exact (Native.cofibrantFactorizationData (B := B)).p.naturality
        ((originalFstArrow (B := B)).map η)
    · exact (Native.cofibrantFactorizationData (B := B)).p.naturality
        ((originalSndArrow (B := B)).map η)

/-- The constructed source is the caller's original Q applied to the original span source. -/
theorem originalSpan_zero (F : WalkingSpan ⥤ D (I := I)) :
    ((originalSpanFunctor (B := B)).obj F).obj WalkingSpan.zero =
      (Replacement.cofibrantReplacement (B := B)).obj (F.obj WalkingSpan.zero) := rfl

/-- Every endpoint of the actual coherent counit is an original level trivial fibration. -/
theorem originalSpanCounit_trivialFibration (F : WalkingSpan ⥤ D (I := I))
    (j : WalkingSpan) :
    trivialFibrations (D (I := I)) (((originalSpanCounit (B := B)).app F).app j) := by
  rcases j with (_ | _ | _)
  · exact Replacement.cofibrantReplacementCounit_mem_trivialFibrations _
  · exact (Native.cofibrantFactorizationData (B := B)).hp _
  · exact (Native.cofibrantFactorizationData (B := B)).hp _

/-- All original source objects in the coherent approximation are genuinely cofibrant. -/
theorem originalSpan_zero_cofibrant (F : WalkingSpan ⥤ D (I := I)) :
    IsCofibrant (((originalSpanFunctor (B := B)).obj F).obj WalkingSpan.zero) :=
  Replacement.isCofibrant_cofibrantReplacement _

/-- The entire first span arrow is the actual original I cofibration factor. -/
theorem originalSpan_fst_cofibration (F : WalkingSpan ⥤ D (I := I)) :
    Cofibration (((originalSpanFunctor (B := B)).obj F).map WalkingSpan.Hom.fst) :=
  (HomotopicalAlgebra.cofibration_iff _).mpr
    ((Native.cofibrantFactorizationData (B := B) (A := I)).hi _)

/-- The entire second span arrow is the other actual original I cofibration factor. -/
theorem originalSpan_snd_cofibration (F : WalkingSpan ⥤ D (I := I)) :
    Cofibration (((originalSpanFunctor (B := B)).obj F).map WalkingSpan.Hom.snd) :=
  (HomotopicalAlgebra.cofibration_iff _).mpr
    ((Native.cofibrantFactorizationData (B := B) (A := I)).hi _)

/-- The constructed span data is a genuine cofibrant replacement, with no supplied outcome. -/
def originalCofibrantSpanReplacement (F : WalkingSpan ⥤ D (I := I)) :
    CofibrantSpanReplacement F where
  Q := (originalSpanFunctor (B := B)).obj F
  counit := (originalSpanCounit (B := B)).app F
  isCofibrant_zero := originalSpan_zero_cofibrant F
  cofibration_fst := originalSpan_fst_cofibration F
  cofibration_snd := originalSpan_snd_cofibration F
  counit_app_mem_trivialFibrations := originalSpanCounit_trivialFibration F

end PointedCGWH.Spectra.NativeOmegaWeakClosure
namespace PointedCGWH.Spectra.NativeOmegaWeakClosure
variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]

attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

open CategoryTheory.EnrichedFunctorCat
open PointedCGWH.EnrichedIntervalContraction

/-- Every actual native time object and map is preserved by original evaluation. -/
def evaluationTimeIso (a : I) :
    timeFunctor ⋙ evaluation (V := PointedCGWH.{u, v}) a ≅
      evaluation (V := PointedCGWH.{u, v}) a ⋙
        PointedCGWH.BasedTimeHomotopyExtension.timeFunctor :=
  NatIso.ofComponents (fun X => Iso.refl _) (by
    intro X Y f
    change component (tensorLeftMap PointedCGWH.RealizedIntervalContraction.time f) a ≫ 𝟙 _ =
      𝟙 _ ≫ PointedCGWH.RealizedIntervalContraction.time ◁ component f a
    rw [Category.comp_id, Category.id_comp]
    exact tensorLeftMap_component PointedCGWH.RealizedIntervalContraction.time f a)

/-- The complete original native time-zero endpoint is the actual pointed endpoint after
evaluation, with the same time comparison. -/
theorem evaluationTimeIso_endpoint (a : I) (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (evaluation (V := PointedCGWH.{u, v}) a).map ((timeInclusionNatTrans 0).app X) ≫
        ((evaluationTimeIso a).app X).hom =
      (PointedCGWH.BasedTimeHomotopyExtension.inclusionNatTrans 0).app
        ((evaluation (V := PointedCGWH.{u, v}) a).obj X) := by
  change component (timeInclusion 0 X) a ≫ 𝟙 _ = _
  rw [Category.comp_id, timeInclusion_component,
    PointedCGWH.BasedTimeHomotopyExtension.inclusionNatTrans_app]
  rfl

end PointedCGWH.Spectra.NativeOmegaWeakClosure

namespace CGWH
open CategoryTheory Topology

/-- A genuine section in the native compactly generated weak-Hausdorff category has a closed
image. Closedness is tested on actual compact Hausdorff probes of the original universe. -/
theorem section_isClosed_range {A X : CGWH.{u, v}} (s : A ⟶ X) (r : X ⟶ A)
    (h : s ≫ r = 𝟙 A) : IsClosed (Set.range (ConcreteCategory.hom s)) := by
  have hFixed : Set.range (ConcreteCategory.hom s) =
      {x : X | (ConcreteCategory.hom s) ((ConcreteCategory.hom r) x) = x} := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact congrArg (ConcreteCategory.hom s) (ConcreteCategory.congr_hom h a)
    · intro hx
      exact ⟨(ConcreteCategory.hom r) x, hx⟩
  rw [hFixed]
  apply UCompactlyGeneratedSpace.isClosed
  intro K f
  let g : C(K, X) := (ConcreteCategory.hom s).comp ((ConcreteCategory.hom r).comp f)
  exact (uWeakHausdorffSpace_iff_isClosed_equalizer.mp
    (inferInstance : UWeakHausdorffSpace.{u} X)) K g f

/-- Every actual section in native CGWH is a closed embedding, with both original maps and
the strict retraction equation retained. No Hausdorff or model-cofibration assumption enters. -/
theorem section_isClosedEmbedding {A X : CGWH.{u, v}} (s : A ⟶ X) (r : X ⟶ A)
    (h : s ≫ r = 𝟙 A) : IsClosedEmbedding (ConcreteCategory.hom s) := by
  refine ⟨IsEmbedding.of_leftInverse
    (fun a => ConcreteCategory.congr_hom h a)
    (ConcreteCategory.hom r).continuous (ConcreteCategory.hom s).continuous,
    section_isClosed_range s r h⟩

end CGWH

namespace CategoryTheory.IntervalHomotopyExtension

universe uC vC uD vD
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  [HasPushouts C] [HasPushouts D]

omit [HasPushouts D] in
/-- A full time comparison and actual pushout preservation transport genuine
all-target homotopy extension through a functor, without an adjoint hypothesis. -/
theorem map_mem_of_preserved_universal (F : C ⥤ D)
    [PreservesColimitsOfShape WalkingSpan F]
    (TC : C ⥤ C) (eC : 𝟭 C ⟶ TC) (TD : D ⥤ D) (eD : 𝟭 D ⟶ TD)
    (a : TC ⋙ F ≅ F ⋙ TD)
    (ha : ∀ X : C, F.map (eC.app X) ≫ (a.app X).hom = eD.app (F.obj X))
    {A X : C} (i : A ⟶ X) (hi : property TC eC i) : property TD eD (F.map i) := by
  obtain ⟨r, hr0, hri⟩ := (universal_iff TC eC i).mp hi
  change TC.obj X ⟶ pushout (eC.app A) i at r
  change eC.app X ≫ r = pushout.inr (eC.app A) i at hr0
  change TC.map i ≫ r = pushout.inl (eC.app A) i at hri
  let sq := (IsPushout.of_hasPushout (eC.app A) i).map F
  intro Y f H h0
  have hSource : F.map (eC.app A) ≫ ((a.app A).hom ≫ H) = F.map i ≫ f := by
    rw [← Category.assoc, ha]
    exact h0
  let d : F.obj (pushout (eC.app A) i) ⟶ Y := sq.desc ((a.app A).hom ≫ H) f hSource
  have hdT : F.map (pushout.inl (eC.app A) i) ≫ d = (a.app A).hom ≫ H :=
    sq.inl_desc _ _ _
  have hdX : F.map (pushout.inr (eC.app A) i) ≫ d = f := sq.inr_desc _ _ _
  have hEndpoint : eD.app (F.obj X) ≫ (a.app X).inv = F.map (eC.app X) := by
    rw [← ha, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have hTime : TD.map (F.map i) ≫ (a.app X).inv =
      (a.app A).inv ≫ F.map (TC.map i) := a.inv.naturality i
  refine ⟨(a.app X).inv ≫ F.map r ≫ d, ?_, ?_⟩
  · calc
      _ = (eD.app (F.obj X) ≫ (a.app X).inv) ≫ F.map r ≫ d := by
        rw [Category.assoc]
      _ = F.map (eC.app X) ≫ F.map r ≫ d := congrArg (fun q => q ≫ F.map r ≫ d) hEndpoint
      _ = F.map (eC.app X ≫ r) ≫ d := by rw [F.map_comp, Category.assoc]
      _ = F.map (pushout.inr (eC.app A) i) ≫ d :=
        congrArg (fun q : X ⟶ pushout (eC.app A) i => F.map q ≫ d) hr0
      _ = f := hdX
  · calc
      _ = (TD.map (F.map i) ≫ (a.app X).inv) ≫ F.map r ≫ d := by
        rw [Category.assoc]
      _ = ((a.app A).inv ≫ F.map (TC.map i)) ≫ F.map r ≫ d :=
        congrArg (fun q => q ≫ F.map r ≫ d) hTime
      _ = (a.app A).inv ≫ F.map (TC.map i ≫ r) ≫ d := by
        rw [F.map_comp, Category.assoc, Category.assoc]
      _ = (a.app A).inv ≫ F.map (pushout.inl (eC.app A) i) ≫ d :=
        congrArg (fun q : TC.obj A ⟶ pushout (eC.app A) i =>
          (a.app A).inv ≫ F.map q ≫ d) hri
      _ = (a.app A).inv ≫ (a.app A).hom ≫ H := by rw [hdT]
      _ = H := by rw [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end CategoryTheory.IntervalHomotopyExtension

namespace PointedCGWH.Spectra.NativeOmegaWeakClosure

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf
open PointedCGWH.EnrichedIntervalContraction

/-- Every actual evaluation of an arbitrary genuine native homotopy cofibration has the
full pointed all-target homotopy-extension property. No native cofibrancy is required. -/
theorem nativeHEP_evaluation {A X : EnrichedFunctorCat PointedCGWH.{u, v} I} (i : A ⟶ X)
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i) (a : I) :
    PointedCGWH.BasedTimeHomotopyExtension.property
      ((evaluation (V := PointedCGWH.{u, v}) a).map i) := by
  exact IntervalHomotopyExtension.map_mem_of_preserved_universal
    (evaluation (V := PointedCGWH.{u, v}) a)
    timeFunctor (timeInclusionNatTrans 0)
    PointedCGWH.BasedTimeHomotopyExtension.timeFunctor
    (PointedCGWH.BasedTimeHomotopyExtension.inclusionNatTrans 0)
    (evaluationTimeIso a) (evaluationTimeIso_endpoint a) i hi

end PointedCGWH.Spectra.NativeOmegaWeakClosure

/-!
These declarations append to the original coherent span producer after its
first normal build. They retain complete chosen maps, and assert no arbitrary
HEP comparison weakness.
-/

namespace PointedCGWH.Spectra.NativeOmegaWeakClosure

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective

private abbrev C := EnrichedFunctorCat PointedCGWH.{u, v} I

/-- The original coherent I span colimit as a full functor. -/
def originalSpanColimit : (WalkingSpan ⥤ C (I := I)) ⥤ C (I := I) :=
  originalSpanFunctor (B := B) ⋙ colim

/-- The actual I counit induces the complete comparison to the original ordinary colimit. -/
def originalSpanColimitComparison : originalSpanColimit (B := B) (I := I) ⟶ colim :=
  Functor.whiskerRight (originalSpanCounit (B := B)) colim

/-- Every component is the original colimit map of the complete native counit span. -/
theorem originalSpanColimitComparison_app (F : WalkingSpan ⥤ C (I := I)) :
    (originalSpanColimitComparison (B := B)).app F =
      colim.map ((originalSpanCounit (B := B)).app F) := rfl

/-- Every original span endpoint keeps its full source comparison square. -/
@[reassoc]
theorem originalSpanColimitComparison_ι (F : WalkingSpan ⥤ C (I := I)) (j : WalkingSpan) :
    colimit.ι ((originalSpanFunctor (B := B)).obj F) j ≫
        (originalSpanColimitComparison (B := B)).app F =
      ((originalSpanCounit (B := B)).app F).app j ≫ colimit.ι F j :=
  ι_colimMap ((originalSpanCounit (B := B)).app F) j

/-- All original span arrows retain the entire colimit comparison naturality. -/
@[reassoc]
theorem originalSpanColimitComparison_naturality
    {F G : WalkingSpan ⥤ C (I := I)} (η : F ⟶ G) :
    (originalSpanColimit (B := B)).map η ≫
        (originalSpanColimitComparison (B := B)).app G =
      (originalSpanColimitComparison (B := B)).app F ≫ colim.map η :=
  (originalSpanColimitComparison (B := B)).naturality η

/-- The constructed I span has a weak comparison to the actual framework homotopy pushout,
over the same original ordinary colimit. -/
theorem originalSpanColimit_toHomotopyPushout
    (F : WalkingSpan ⥤ C (I := I)) :
    ∃ a : (originalSpanColimit (B := B)).obj F ⟶
        (homotopyPushout (C := C (I := I))).obj F,
      WeakEquivalence a ∧ a ≫ (homotopyPushoutComparison (C := C (I := I))).app F =
        (originalSpanColimitComparison (B := B)).app F :=
  (originalCofibrantSpanReplacement (B := B) F).exists_weakEquivalence_to_homotopyPushout

/-- Every other genuine cofibrant span replacement has a weak comparison over the caller's
same original colimit. This result retains that actual chosen replacement. -/
theorem originalSpanColimit_choiceComparison (F : WalkingSpan ⥤ C (I := I))
    (R : CofibrantSpanReplacement F) :
    ∃ a : (originalSpanColimit (B := B)).obj F ⟶ R.pushoutObj,
      WeakEquivalence a ∧ a ≫ R.toPushout =
        (originalSpanColimitComparison (B := B)).app F :=
  CofibrantSpanReplacement.exists_weakEquivalence_pushoutObj
    (originalCofibrantSpanReplacement (B := B) F) R

/-- Level weakness of the actual comparison is independent of the original I choice,
without claiming weakness for an arbitrary HEP span. -/
theorem originalSpanColimit_comparisonWeak_iff (F : WalkingSpan ⥤ C (I := I))
    (R : CofibrantSpanReplacement F) :
    WeakEquivalence ((originalSpanColimitComparison (B := B)).app F) ↔
      WeakEquivalence R.toPushout :=
  CofibrantSpanReplacement.weakEquivalence_toPushout_iff
    (originalCofibrantSpanReplacement (B := B) F) R

end PointedCGWH.Spectra.NativeOmegaWeakClosure

namespace CGWH

open CategoryTheory MonoidalCategory

/-- The literal native lifted interval reflected by the actual unit-interval involution. -/
def literalTimeReflection : homotopyInterval.{u, v} ≅ homotopyInterval.{u, v} where
  hom := ofHom
    { toFun := fun x => ULift.up (unitInterval.symm x.down)
      continuous_toFun := continuous_uliftUp.comp
        (unitInterval.continuous_symm.comp continuous_uliftDown) }
  inv := ofHom
    { toFun := fun x => ULift.up (unitInterval.symm x.down)
      continuous_toFun := continuous_uliftUp.comp
        (unitInterval.continuous_symm.comp continuous_uliftDown) }
  hom_inv_id := by
    ext x
    exact congrArg ULift.up (unitInterval.symm_symm x.down)
  inv_hom_id := by
    ext x
    exact congrArg ULift.up (unitInterval.symm_symm x.down)

/-- Reflection keeps the complete original endpoint family, with its actual reflected time. -/
theorem literalTimeReflection_endpoint (t : unitInterval) :
    homotopyIntervalEndpoint.{u, v} t ≫ literalTimeReflection.hom =
      homotopyIntervalEndpoint.{u, v} (unitInterval.symm t) := by
  ext x
  rfl

end CGWH

namespace PointedCGWH.Spectra.NativeOmegaWeakClosure

open CategoryTheory MonoidalCategory

/-- The full literal time coefficient is identified with the original realized interval
using reflection before the original native realization comparison. -/
def originalTimeCoefficientIso : PointedCGWH.RealizedIntervalContraction.time.{u, v} ≅
    PointedCGWH.IntervalCoefficient.interval.{u, v} :=
  (Under.costar CGWH.point.{u, v}).mapIso
    (CGWH.literalTimeReflection.{u, v} ≪≫ CGWH.homotopyIntervalIsoInterval.{u, v})

/-- Literal time zero is the original realized delta-zero endpoint under the actual full
coefficient comparison; the whole original unit map is retained. -/
theorem originalTimeCoefficientIso_zero :
    PointedCGWH.freePointIntervalEndpoint.{u, v} 0 ≫ originalTimeCoefficientIso.hom =
      PointedCGWH.IntervalCoefficient.endpoint.{u, v} 0 := by
  let F := Under.costar CGWH.point.{u, v}
  let hF : F.CoreMonoidal := CategoryTheory.Pointed.costarCoreMonoidal
    CGWH.point CGWH.point_isTerminal
  change (hF.εIso.hom ≫ F.map (CGWH.homotopyIntervalEndpoint 0)) ≫
    F.map (CGWH.literalTimeReflection.hom ≫ CGWH.homotopyIntervalIsoInterval.hom) = _
  rw [Category.assoc, ← F.map_comp, ← Category.assoc,
    CGWH.literalTimeReflection_endpoint, unitInterval.symm_zero,
    CGWH.homotopyIntervalIsoInterval_one, F.map_comp, ← Category.assoc]
  rw [PointedCGWH.RealizedIntervalContraction.endpoint_zero_eq]
  have hInverse : F.map (CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v})) =
      hF.εIso.inv := by
    change F.map (CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v})) =
      ((Under.costarAdjForget CGWH.point).homEquiv
        (𝟙_ CGWH) (F.obj CGWH.point)).symm
          (CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v}) ≫ coprod.inr)
    apply ((Under.costarAdjForget CGWH.point).homEquiv
      (𝟙_ CGWH) (F.obj CGWH.point)).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    have hu : (Under.costarAdjForget CGWH.point.{u, v}).unit.app (𝟙_ CGWH) =
        (coprod.inr : (𝟙_ CGWH) ⟶ CGWH.point ⨿ (𝟙_ CGWH)) := by
      rfl
    rw [hu]
    change coprod.inr ≫ coprod.map (𝟙 CGWH.point)
      (CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v})) = _
    exact coprod.inr_map _ _
  rw [hInverse]
  exact hF.εIso.hom_inv_id_assoc _

end PointedCGWH.Spectra.NativeOmegaWeakClosure

namespace PointedCGWH.Spectra.NativeOmegaWeakClosure

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat MonoidalCategory
open PointedCGWH.EnrichedIntervalContraction

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
attribute [local instance] MonoidalClosed.enrichedCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits

/-- The complete scalar action of the genuine time coefficient comparison is a full
natural isomorphism on the original native carrier. -/
def nativeOriginalTimeIso : timeFunctor (I := I) ≅
    PointedCGWH.EnrichedIntervalCylinder.functor (I := I) :=
  (EnrichedFunctorCat.tensorBifunctor (V := PointedCGWH.{u, v}) (A := I)).mapIso
    originalTimeCoefficientIso

/-- Both full original maps of the scalar time comparison are retained. -/
theorem nativeOriginalTimeIso_hom (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (nativeOriginalTimeIso (I := I)).hom.app X =
      scalarTensorMap originalTimeCoefficientIso.hom X := rfl

/-- Literal time zero becomes the actual original first realized interval inclusion. -/
theorem nativeOriginalTimeIso_zero (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    timeInclusion 0 X ≫ (nativeOriginalTimeIso (I := I)).hom.app X =
      PointedCGWH.EnrichedIntervalCylinder.inclusion 0 X := by
  change ((scalarUnitIso X).inv ≫
    scalarTensorMap (PointedCGWH.freePointIntervalEndpoint 0) X) ≫
      scalarTensorMap originalTimeCoefficientIso.hom X =
        (scalarUnitIso X).inv ≫ scalarTensorMap (PointedCGWH.IntervalCoefficient.endpoint 0) X
  rw [Category.assoc, ← scalarTensorMap_comp]
  exact congrArg (fun q : (𝟙_ PointedCGWH.{u, v}) ⟶ PointedCGWH.IntervalCoefficient.interval =>
    (scalarUnitIso X).inv ≫ scalarTensorMap q X) originalTimeCoefficientIso_zero

/-- The original literal time-zero HEP gives the full realized-endpoint HEP on the same
actual native arrow, retaining every target and original homotopy. -/
theorem nativeHEP_originalInterval {A X : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (i : A ⟶ X) (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i) :
    PointedCGWH.EnrichedIntervalBasedHomotopyExtension.property i := by
  exact IntervalHomotopyExtension.map_mem_of_preserved_universal
    (𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} I))
    timeFunctor (timeInclusionNatTrans 0)
    PointedCGWH.EnrichedIntervalCylinder.functor
    (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
    (nativeOriginalTimeIso (I := I)) nativeOriginalTimeIso_zero i hi

end PointedCGWH.Spectra.NativeOmegaWeakClosure

namespace CategoryTheory.IntervalHomotopyExtension

universe uE vE
variable {C : Type uE} [Category.{vE} C] [HasPushouts C]
  (T : C ⥤ C) (e₀ e₁ : 𝟭 C ⟶ T)

/-- Both actual interval endpoints retain the universal source/comparison factor equation
before choosing a native carrier or evaluating its maps. -/
theorem secondEndpoint_comparison {A X : C} (i : A ⟶ X) :
    (e₁.app A ≫ pushout.inl (e₀.app A) i) ≫ comparison T e₀ i = i ≫ e₁.app X := by
  change (e₁.app A ≫ pushout.inl (e₀.app A) i) ≫
    pushout.desc (T.map i) (e₀.app X) (e₀.naturality i).symm = i ≫ e₁.app X
  rw [Category.assoc, pushout.inl_desc]
  exact (e₁.naturality i).symm

end CategoryTheory.IntervalHomotopyExtension

namespace PointedCGWH.Spectra.NativeOmegaWeakClosure

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat Topology
open PointedCGWH.EnrichedIntervalCylinder PointedCGWH.EnrichedIntervalMappingCylinder

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
attribute [local instance] PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf

/-- The entire original endpoint pushout comparison is a section under genuine realized
all-target HEP, hence its actual underlying component is closed in native kWH. -/
theorem originalHEP_comparison_component_closed
    (F : Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I))
    (hF : PointedCGWH.EnrichedIntervalBasedHomotopyExtension.property F.hom) (a : I) :
    IsClosedEmbedding (ConcreteCategory.hom
      (component (PointedCGWH.EnrichedIntervalBasedHomotopyExtension.comparison F) a).right) := by
  obtain ⟨r, hr⟩ :=
    (PointedCGWH.EnrichedIntervalBasedHomotopyExtension.originalRetraction_iff F).mp hF
  have h : (component (PointedCGWH.EnrichedIntervalBasedHomotopyExtension.comparison F) a).right ≫
      (component r a).right = 𝟙 (((object F).toEnrichedFunctor.obj a).right) := by
    have h0 := congrArg (fun g : object F ⟶ object F => (component g a).right) hr
    simpa only [component_comp, component_id, Under.comp_right, Under.id_right] using h0
  exact CGWH.section_isClosedEmbedding _ _ h

/-- Every original realized HEP arrow is a closed embedding at every native level.
The proof uses the actual second endpoint and the genuine universal comparison section. -/
theorem originalHEP_component_closed
    {A X : EnrichedFunctorCat PointedCGWH.{u, v} I} (i : A ⟶ X)
    (hi : PointedCGWH.EnrichedIntervalBasedHomotopyExtension.property i) (a : I) :
    IsClosedEmbedding (ConcreteCategory.hom (component i a).right) := by
  let F := Arrow.mk i
  let q := PointedCGWH.EnrichedIntervalBasedHomotopyExtension.comparison F
  let j := PointedCGWH.EnrichedIntervalMappingCylinder.source F
  let U : EnrichedFunctorCat PointedCGWH.{u, v} I ⥤ CGWH.{u, v} :=
    evaluation a ⋙ PointedCGWH.pointedToCGWH
  have hJ :=
    PointedCGWH.EnrichedIntervalMappingCylinderClosed.source_component_isClosedEmbedding F a
  have hQ := originalHEP_comparison_component_closed F hi a
  have hComp : IsClosedEmbedding
      (ConcreteCategory.hom (U.map (j ≫ q))) := by
    rw [U.map_comp]
    exact hQ.comp hJ
  have hFac : j ≫ q = i ≫ inclusion 1 X :=
    IntervalHomotopyExtension.secondEndpoint_comparison
      PointedCGWH.EnrichedIntervalCylinder.functor
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
      (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 1) i
  have hMapped : U.map (j ≫ q) = U.map i ≫ U.map (inclusion 1 X) :=
    (U.congr_map hFac).trans (U.map_comp _ _)
  have hEndpoint : IsEmbedding (ConcreteCategory.hom (U.map (inclusion 1 X))) := by
    have hRet : U.map (inclusion 1 X) ≫ U.map (projection X) = 𝟙 (U.obj X) :=
      (U.map_comp _ _).symm.trans
        ((U.congr_map (inclusion_projection 1 X)).trans (U.map_id X))
    exact IsEmbedding.of_leftInverse (fun x => ConcreteCategory.congr_hom hRet x)
      (ConcreteCategory.hom (U.map (projection X))).continuous
      (ConcreteCategory.hom (U.map (inclusion 1 X))).continuous
  have hComp' : IsClosedEmbedding (ConcreteCategory.hom (U.map i ≫ U.map (inclusion 1 X))) :=
    hMapped ▸ hComp
  exact IsClosedEmbedding.of_comp hEndpoint hComp'

/-- The actual original literal based native HEP implies the same complete level closed
inclusion property, through the proved full original time comparison. -/
theorem nativeHEP_component_closed
    {A X : EnrichedFunctorCat PointedCGWH.{u, v} I} (i : A ⟶ X)
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i) (a : I) :
    IsClosedEmbedding (ConcreteCategory.hom (component i a).right) :=
  originalHEP_component_closed i (nativeHEP_originalInterval i hi) a

end PointedCGWH.Spectra.NativeOmegaWeakClosure
namespace PointedCGWH.Spectra.NativeOmegaWeakClosure

open CategoryTheory MonoidalCategory

/-- The freely based original terminal-unit inverse is the actual mapped native terminal
map, with the original strong-monoidal factory kept fixed. -/
private theorem originalFreePointUnitInverse :
    (Under.costar CGWH.point.{u, v}).map
        (CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v})) =
      (CategoryTheory.Pointed.costarCoreMonoidal CGWH.point.{u, v}
        CGWH.point_isTerminal).εIso.inv := by
  let F := Under.costar CGWH.point.{u, v}
  change F.map (CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v})) =
    ((Under.costarAdjForget CGWH.point).homEquiv
      (𝟙_ CGWH) (F.obj CGWH.point)).symm
        (CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v}) ≫ coprod.inr)
  apply ((Under.costarAdjForget CGWH.point).homEquiv
    (𝟙_ CGWH) (F.obj CGWH.point)).injective
  rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
  have hu : (Under.costarAdjForget CGWH.point.{u, v}).unit.app (𝟙_ CGWH) =
      (coprod.inr : (𝟙_ CGWH) ⟶ CGWH.point ⨿ (𝟙_ CGWH)) := rfl
  rw [hu]
  change coprod.inr ≫ coprod.map (𝟙 CGWH.point)
    (CGWH.point_isTerminal.from (𝟙_ CGWH.{u, v})) = _
  exact coprod.inr_map _ _

/-- Literal time one is the original second realized endpoint under the same reflected
native coefficient isomorphism, retaining the entire original unit map. -/
theorem originalTimeCoefficientIso_one :
    PointedCGWH.freePointIntervalEndpoint.{u, v} 1 ≫ originalTimeCoefficientIso.hom =
      PointedCGWH.IntervalCoefficient.endpoint.{u, v} 1 := by
  let F := Under.costar CGWH.point.{u, v}
  let hF : F.CoreMonoidal := CategoryTheory.Pointed.costarCoreMonoidal
    CGWH.point CGWH.point_isTerminal
  change (hF.εIso.hom ≫ F.map (CGWH.homotopyIntervalEndpoint 1)) ≫
    F.map (CGWH.literalTimeReflection.hom ≫ CGWH.homotopyIntervalIsoInterval.hom) = _
  rw [Category.assoc, ← F.map_comp, ← Category.assoc,
    CGWH.literalTimeReflection_endpoint, unitInterval.symm_one,
    CGWH.homotopyIntervalIsoInterval_zero, F.map_comp, ← Category.assoc,
    PointedCGWH.RealizedIntervalContraction.endpoint_one_eq,
    originalFreePointUnitInverse]
  exact hF.εIso.hom_inv_id_assoc _

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
attribute [local instance] MonoidalClosed.enrichedCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits
open CategoryTheory.EnrichedFunctorCat PointedCGWH.EnrichedIntervalContraction

/-- The complete inverse scalar time comparison is the original inverse coefficient map. -/
theorem nativeOriginalTimeIso_inv (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    (nativeOriginalTimeIso (I := I)).inv.app X =
      scalarTensorMap originalTimeCoefficientIso.inv X := rfl

/-- Literal time one is exactly the second original realized inclusion on every native
diagram, under the same whole time comparison. -/
theorem nativeOriginalTimeIso_one (X : EnrichedFunctorCat PointedCGWH.{u, v} I) :
    timeInclusion 1 X ≫ (nativeOriginalTimeIso (I := I)).hom.app X =
      PointedCGWH.EnrichedIntervalCylinder.inclusion 1 X := by
  change ((scalarUnitIso X).inv ≫
    scalarTensorMap (PointedCGWH.freePointIntervalEndpoint 1) X) ≫
      scalarTensorMap originalTimeCoefficientIso.hom X =
        (scalarUnitIso X).inv ≫ scalarTensorMap (PointedCGWH.IntervalCoefficient.endpoint 1) X
  rw [Category.assoc, ← scalarTensorMap_comp]
  exact congrArg (fun q : (𝟙_ PointedCGWH.{u, v}) ⟶ PointedCGWH.IntervalCoefficient.interval =>
    (scalarUnitIso X).inv ≫ scalarTensorMap q X) originalTimeCoefficientIso_one

/-- The actual original realized HEP implies literal time-zero HEP on the same full
native arrow, using the inverse of the proved whole time comparison. -/
theorem originalIntervalHEP_native {A X : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (i : A ⟶ X) (hi : PointedCGWH.EnrichedIntervalBasedHomotopyExtension.property i) :
    PointedCGWH.EnrichedBasedHomotopyExtension.property i := by
  have hEndpoint (Y : EnrichedFunctorCat PointedCGWH.{u, v} I) :
      PointedCGWH.EnrichedIntervalCylinder.inclusion 0 Y ≫
        (nativeOriginalTimeIso (I := I)).inv.app Y = timeInclusion 0 Y := by
    let e := nativeOriginalTimeIso (I := I)
    let e0 : Y ⟶ timeFunctor.obj Y := (timeInclusionNatTrans 0).app Y
    change PointedCGWH.EnrichedIntervalCylinder.inclusion 0 Y ≫ e.inv.app Y = e0
    have hz : e0 ≫ e.hom.app Y =
        PointedCGWH.EnrichedIntervalCylinder.inclusion 0 Y := nativeOriginalTimeIso_zero Y
    have h := congrArg (fun f : Y ⟶ PointedCGWH.EnrichedIntervalCylinder.functor.obj Y =>
      f ≫ e.inv.app Y) hz
    calc
      _ = (e0 ≫ e.hom.app Y) ≫ e.inv.app Y := h.symm
      _ = e0 ≫ (e.hom.app Y ≫ e.inv.app Y) := Category.assoc _ _ _
      _ = e0 := by
        rw [Iso.hom_inv_id_app, Category.comp_id]
  exact IntervalHomotopyExtension.map_mem_of_preserved_universal
    (𝟭 (EnrichedFunctorCat PointedCGWH.{u, v} I))
    PointedCGWH.EnrichedIntervalCylinder.functor
    (PointedCGWH.EnrichedIntervalCylinder.inclusionNatTrans 0)
    timeFunctor (timeInclusionNatTrans 0)
    (nativeOriginalTimeIso (I := I)).symm hEndpoint i hi

/-- Both genuine HEP endpoint conventions agree through the actual proved native time
comparison; neither original all-target property is replaced by a cofibration predicate. -/
theorem nativeHEP_iff_originalInterval {A X : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (i : A ⟶ X) :
    PointedCGWH.EnrichedBasedHomotopyExtension.property i ↔
      PointedCGWH.EnrichedIntervalBasedHomotopyExtension.property i :=
  ⟨nativeHEP_originalInterval i, originalIntervalHEP_native i⟩

end PointedCGWH.Spectra.NativeOmegaWeakClosure
