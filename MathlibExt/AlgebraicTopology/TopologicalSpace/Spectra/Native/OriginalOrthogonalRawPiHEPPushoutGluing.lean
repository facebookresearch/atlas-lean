/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import
  MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalRawPiHomotopyPushoutGluing
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OmegaTestHomotopyCofiberClosure
import
  MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.OriginalContinuousSourceApproximation
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SpectrumIndexMaps
import MathlibExt.CategoryTheory.Enriched.PointwiseColimitReflection
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.StableHomotopy.IntegerGroups

/-!
# Original orthogonal restriction and raw homotopy pushout gluing

Full enriched restriction retains the original evaluated objects and maps,
caller colimit cocones, scalar interval actions and universal HEP retractions.
These comparisons transport raw integer homotopy gluing to the original
orthogonal spectra before the all-Omega weak-equivalence comparison.
-/

set_option autoImplicit false
noncomputable section
universe u v uV vV uA uB uJ vJ uC vC uD vD
open CategoryTheory CategoryTheory.Limits MonoidalCategory HomotopicalAlgebra
open CategoryTheory.EnrichedFunctorCat
open scoped MonoidalClosed CGWH.modelCategory

namespace CategoryTheory.EnrichedFunctorCat

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [BraidedCategory V] [MonoidalClosed V]
  {A : Type uA} [EnrichedCategory V A] {B : Type uB} [EnrichedCategory V B]

/-- Original restriction followed by evaluation is the literal original target evaluation. -/
theorem originalRestriction_evaluation_eq (j : EnrichedFunctor V A B) (a : A) :
    restriction j ⋙ evaluation a = evaluation (j.obj a) := by
  refine Functor.ext (fun _ => rfl) ?_
  intro X Y f
  change component (restrictionMap j f) a = 𝟙 _ ≫ component f (j.obj a) ≫ 𝟙 _
  rw [restrictionMap_component, Category.id_comp, Category.comp_id]

/-- Every original caller colimit cocone remains an actual colimit under full enriched
restriction. -/
def originalRestrictionCoconeIsColimit
    {J : Type uJ} [Category.{vJ} J] [HasColimitsOfShape J V]
    (j : EnrichedFunctor V A B) {F : J ⥤ EnrichedFunctorCat V B}
    (c : Cocone F) (hc : IsColimit c) : IsColimit ((restriction j).mapCocone c) := by
  apply evaluationJointlyReflectsColimits
  intro a
  change IsColimit ((restriction j ⋙ evaluation a).mapCocone c)
  rw [originalRestriction_evaluation_eq]
  exact isColimitOfPreserves (evaluation (j.obj a)) hc

/-- The genuine original restriction preserves arbitrary colimit shapes present in the base. -/
theorem originalRestriction_preservesColimit
    {J : Type uJ} [Category.{vJ} J] [HasColimitsOfShape J V]
    (j : EnrichedFunctor V A B) (F : J ⥤ EnrichedFunctorCat V B) :
    PreservesColimit F (restriction j) :=
  preservesColimit_of_preserves_colimit_cocone (colimit.isColimit F)
    (originalRestrictionCoconeIsColimit j (colimit.cocone F) (colimit.isColimit F))

/-- All original caller pushout squares remain the actual restricted squares with both legs. -/
theorem originalRestriction_isPushout [HasPushouts V]
    (j : EnrichedFunctor V A B) {X Y Z P : EnrichedFunctorCat V B}
    (i : X ⟶ Y) (z : X ⟶ Z) (kY : Y ⟶ P) (kZ : Z ⟶ P)
    (sq : IsPushout i z kY kZ) :
    IsPushout ((restriction j).map i) ((restriction j).map z)
      ((restriction j).map kY) ((restriction j).map kZ) := by
  apply (isPushout_iff_evaluation (V := V) (A := A)
    ((restriction j).map_comp _ _ |>.symm.trans
      (((restriction j).congr_map sq.w).trans ((restriction j).map_comp _ _)))).mpr
  intro a
  change IsPushout (component (restrictionMap j i) a)
    (component (restrictionMap j z) a) (component (restrictionMap j kY) a)
    (component (restrictionMap j kZ) a)
  have h := sq.map (evaluation (j.obj a))
  change IsPushout (component i (j.obj a)) (component z (j.obj a))
    (component kY (j.obj a)) (component kZ (j.obj a)) at h
  rw [restrictionMap_component, restrictionMap_component, restrictionMap_component,
    restrictionMap_component]
  exact h

/-- The original restriction and scalar tensor preserve both full natural input functors. -/
def originalRestrictionScalarNatIso (j : EnrichedFunctor V A B) (M : V) :
    restriction j ⋙ tensorLeft M ≅ tensorLeft M ⋙ restriction j :=
  NatIso.ofComponents (tensorLeftRestrictionIso M j)
    (fun f => tensorLeftRestrictionIso_naturality M j f)

end CategoryTheory.EnrichedFunctorCat



namespace PointedCGWH.EnrichedBasedHomotopyExtension

attribute [local instance] MonoidalClosed.enrichedCategorySelf
variable {A : Type} [EnrichedCategory PointedCGWH.{u, v} A]
  {B : Type} [EnrichedCategory PointedCGWH.{u, v} B]
open PointedCGWH.EnrichedIntervalContraction

/-- The genuine free-time comparison retains both original full input functors. -/
def originalRestrictionTimeNatIso (j : EnrichedFunctor PointedCGWH.{u, v} A B) :
    timeFunctor ⋙ restriction j ≅ restriction j ⋙ timeFunctor :=
  (originalRestrictionScalarNatIso j PointedCGWH.RealizedIntervalContraction.time).symm

/-- Every physical free-time endpoint is unchanged under original restriction. -/
theorem originalRestriction_timeEndpoint
    (j : EnrichedFunctor PointedCGWH.{u, v} A B) (t : unitInterval)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} B) :
    (restriction j).map (timeInclusion t X) ≫
      (originalRestrictionTimeNatIso j).hom.app X =
        timeInclusion t ((restriction j).obj X) := by
  apply EnrichedFunctorCat.hom_ext
  intro a
  change component (restrictionMap j (timeInclusion t X) ≫
    (tensorLeftRestrictionIso PointedCGWH.RealizedIntervalContraction.time j X).inv) a = _
  rw [component_comp]
  let V := X.toEnrichedFunctor.obj (j.obj a)
  let T := PointedCGWH.RealizedIntervalContraction.time.{u, v}
  have hR : (component (restrictionMap j (timeInclusion t X)) a : V ⟶ T ⊗ V) =
      component (timeInclusion t X) (j.obj a) := restrictionMap_component j _ a
  have hI : (component (tensorLeftRestrictionIso T j X).inv a : T ⊗ V ⟶ T ⊗ V) =
      𝟙 (T ⊗ V) := tensorLeftRestrictionIso_inv_component T j X a
  change (component (restrictionMap j (timeInclusion t X)) a : V ⟶ T ⊗ V) ≫
    (component (tensorLeftRestrictionIso T j X).inv a : T ⊗ V ⟶ T ⊗ V) =
      (component (timeInclusion t ((restriction j).obj X)) a : V ⟶ T ⊗ V)
  let f : V ⟶ T ⊗ V := component (restrictionMap j (timeInclusion t X)) a
  let g : T ⊗ V ⟶ T ⊗ V := component (tensorLeftRestrictionIso T j X).inv a
  let z : V ⟶ T ⊗ V := component (timeInclusion t ((restriction j).obj X)) a
  have hfg : f ≫ g = f ≫ 𝟙 (T ⊗ V) := congrArg (fun k => f ≫ k) hI
  have hfz : f = z := hR.trans ((timeInclusion_component t X (j.obj a)).trans
    (timeInclusion_component t ((restriction j).obj X) a).symm)
  exact hfg.trans ((Category.comp_id f).trans hfz)

/-- The original projection retains its whole native map under restriction. -/
theorem originalRestriction_timeProjection
    (j : EnrichedFunctor PointedCGWH.{u, v} A B)
    (X : EnrichedFunctorCat PointedCGWH.{u, v} B) :
    (originalRestrictionTimeNatIso j).hom.app X ≫
      timeProjection ((restriction j).obj X) = (restriction j).map (timeProjection X) := by
  apply EnrichedFunctorCat.hom_ext
  intro a
  change component ((tensorLeftRestrictionIso PointedCGWH.RealizedIntervalContraction.time j X).inv
    ≫ timeProjection ((restriction j).obj X)) a = _
  rw [component_comp]
  let V := X.toEnrichedFunctor.obj (j.obj a)
  let T := PointedCGWH.RealizedIntervalContraction.time.{u, v}
  have hI : (component (tensorLeftRestrictionIso T j X).inv a : T ⊗ V ⟶ T ⊗ V) =
      𝟙 (T ⊗ V) := tensorLeftRestrictionIso_inv_component T j X a
  have hR : (component (restrictionMap j (timeProjection X)) a : T ⊗ V ⟶ V) =
      component (timeProjection X) (j.obj a) := restrictionMap_component j _ a
  change (component (tensorLeftRestrictionIso T j X).inv a : T ⊗ V ⟶ T ⊗ V) ≫
    (component (timeProjection ((restriction j).obj X)) a : T ⊗ V ⟶ V) =
      (component (restrictionMap j (timeProjection X)) a : T ⊗ V ⟶ V)
  let f : T ⊗ V ⟶ T ⊗ V := component (tensorLeftRestrictionIso T j X).inv a
  let g : T ⊗ V ⟶ V := component (timeProjection ((restriction j).obj X)) a
  let z : T ⊗ V ⟶ V := component (restrictionMap j (timeProjection X)) a
  have hfg : f ≫ g = 𝟙 (T ⊗ V) ≫ g := congrArg (fun k => k ≫ g) hI
  have hgz : g = z := ((timeProjection_component ((restriction j).obj X) a).trans
    (timeProjection_component X (j.obj a)).symm).trans hR.symm
  exact hfg.trans ((Category.id_comp g).trans hgz)

/-- The actual universal HEP retraction restricts to every original native target. -/
theorem originalRestriction_mem (j : EnrichedFunctor PointedCGWH.{u, v} A B)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} B} (i : X ⟶ Y)
    (hi : property i) : property ((restriction j).map i) := by
  let _ : PreservesColimitsOfShape WalkingSpan (restriction j) :=
    { preservesColimit := fun {F} => originalRestriction_preservesColimit j F }
  exact IntervalHomotopyExtension.map_mem_of_preserved_universal
    (restriction j) timeFunctor (timeInclusionNatTrans 0)
    timeFunctor (timeInclusionNatTrans 0) (originalRestrictionTimeNatIso j)
    (fun X => originalRestriction_timeEndpoint j 0 X) i hi

/-- All actual target maps and time homotopies retain both extension equations. -/
theorem originalRestriction_extension
    (j : EnrichedFunctor PointedCGWH.{u, v} A B)
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} B} (i : X ⟶ Y) (hi : property i)
    (Z : EnrichedFunctorCat PointedCGWH.{u, v} A)
    (f : (restriction j).obj Y ⟶ Z)
    (H : timeObject ((restriction j).obj X) ⟶ Z)
    (hH : timeInclusion 0 ((restriction j).obj X) ≫ H = (restriction j).map i ≫ f) :
    ∃ K : timeObject ((restriction j).obj Y) ⟶ Z,
      timeInclusion 0 ((restriction j).obj Y) ≫ K = f ∧
        tensorLeftMap PointedCGWH.RealizedIntervalContraction.time
          ((restriction j).map i) ≫ K = H :=
  (property_iff ((restriction j).map i)).mp (originalRestriction_mem j i hi) Z f H hH

end PointedCGWH.EnrichedBasedHomotopyExtension

namespace HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
namespace OrthogonalIntegerHomotopy

open CategoryTheory.Spectra.SpectrumIndexMaps
attribute [local instance] CategoryTheory.SequentialSpectrum.EnrichedIndex.enrichedCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
  PointedCGWH.copowerUnderlyingEnrichedOrdinary PointedCGWH.copowerUnderlyingMonoidal

/-- Every caller cocone is an actual colimit after the original orthogonal restriction. -/
def underlyingSequentialCoconeIsColimit
    {J : Type uJ} [Category.{vJ} J] [HasColimitsOfShape J PointedCGWH.{u, v}]
    {F : J ⥤ OrthogonalCarrier.{u, v}} (c : Cocone F) (hc : IsColimit c) :
    IsColimit (underlyingSequential.mapCocone c) :=
  originalRestrictionCoconeIsColimit sequentialOrthogonalOperatorIndexFunctor c hc

/-- The original native pushout keeps its complete caller maps under sequential restriction. -/
theorem underlyingSequential_isPushout
    {A X Z P : OrthogonalCarrier.{u, v}}
    (i : A ⟶ X) (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P)
    (sq : IsPushout i z kX kZ) :
    IsPushout (underlyingSequential.map i) (underlyingSequential.map z)
      (underlyingSequential.map kX) (underlyingSequential.map kZ) :=
  originalRestriction_isPushout sequentialOrthogonalOperatorIndexFunctor i z kX kZ sq

/-- Arbitrary original orthogonal HEP maps restrict with all native target quantifiers. -/
theorem underlyingSequential_HEP
    {A X : OrthogonalCarrier.{u, v}} (i : A ⟶ X)
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i) :
    PointedCGWH.EnrichedBasedHomotopyExtension.property (underlyingSequential.map i) :=
  PointedCGWH.EnrichedBasedHomotopyExtension.originalRestriction_mem
    sequentialOrthogonalOperatorIndexFunctor i hi

/-- Full original orthogonal raw integer gluing retains both actual pushouts,
both HEP legs, all four comparison maps and all original integer groups. -/
theorem originalOrthogonalRawPiHEPpushoutGluing
    [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]
    {A X Z P A' X' Z' P' : OrthogonalCarrier.{u, v}}
    (i : A ⟶ X) (z : A ⟶ Z) (kX : X ⟶ P) (kZ : Z ⟶ P)
    (i' : A' ⟶ X') (z' : A' ⟶ Z') (kX' : X' ⟶ P') (kZ' : Z' ⟶ P')
    (sq : IsPushout i z kX kZ) (sq' : IsPushout i' z' kX' kZ')
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property i)
    (hi' : PointedCGWH.EnrichedBasedHomotopyExtension.property i')
    (a : A ⟶ A') (b : X ⟶ X') (c : Z ⟶ Z') (d : P ⟶ P')
    (hI : a ≫ i' = i ≫ b) (hZ : a ≫ z' = z ≫ c)
    (hX : b ≫ kX' = kX ≫ d) (hP : c ≫ kZ' = kZ ≫ d)
    (ha : integerPiStarEquivalences a) (hb : integerPiStarEquivalences b)
    (hc : integerPiStarEquivalences c) : integerPiStarEquivalences d := by
  let R := underlyingSequential.{u, v}
  have hRi : R.map a ≫ R.map i' = R.map i ≫ R.map b :=
    (R.map_comp _ _).symm.trans ((R.congr_map hI).trans (R.map_comp _ _))
  have hRz : R.map a ≫ R.map z' = R.map z ≫ R.map c :=
    (R.map_comp _ _).symm.trans ((R.congr_map hZ).trans (R.map_comp _ _))
  have hRx : R.map b ≫ R.map kX' = R.map kX ≫ R.map d :=
    (R.map_comp _ _).symm.trans ((R.congr_map hX).trans (R.map_comp _ _))
  have hRp : R.map c ≫ R.map kZ' = R.map kZ ≫ R.map d :=
    (R.map_comp _ _).symm.trans ((R.congr_map hP).trans (R.map_comp _ _))
  apply (integerPiStarEquivalences_iff_underlying d).mpr
  exact PointedCGWH.Spectra.OriginalRawPiHomotopyPushoutGluing.originalRawPiHEPpushoutGluing
    (R.map i) (R.map z) (R.map kX) (R.map kZ)
    (R.map i') (R.map z') (R.map kX') (R.map kZ')
    (underlyingSequential_isPushout i z kX kZ sq)
    (underlyingSequential_isPushout i' z' kX' kZ' sq')
    (underlyingSequential_HEP i hi) (underlyingSequential_HEP i' hi')
    (R.map a) (R.map b) (R.map c) (R.map d) hRi hRz hRx hRp
    ((integerPiStarEquivalences_iff_underlying a).mp ha)
    ((integerPiStarEquivalences_iff_underlying b).mp hb)
    ((integerPiStarEquivalences_iff_underlying c).mp hc)

end OrthogonalIntegerHomotopy
end HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual

namespace PointedCGWH.Spectra.OriginalOrthogonalRawPiHEPPushoutGluing

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf
variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- Every complete original span is retained as the input to the original I source factory. -/
abbrev OriginalSpanInput := WalkingSpan ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I

/-- The bottom functor is the exact original same-cardinal Q on the span source. -/
def originalSpanSource : OriginalSpanInput (I := I) ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I :=
  (CategoryTheory.evaluation WalkingSpan
    (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
    WalkingSpan.zero ⋙ Replacement.cofibrantReplacement (B := B)

/-- The bottom counit is the complete actual original Q counit. -/
def originalSpanSourceCounit : originalSpanSource (B := B) (I := I) ⟶
    (CategoryTheory.evaluation WalkingSpan
    (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
      WalkingSpan.zero :=
  Functor.whiskerLeft
    ((CategoryTheory.evaluation WalkingSpan (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj
      WalkingSpan.zero) (Replacement.cofibrantReplacementCounit (B := B))

/-- Each original span leg composes the whole same-Q counit with the caller's literal leg. -/
def originalSpanLegInput (j : WalkingSpan) (h : WalkingSpan.zero ⟶ j) :
    OriginalSpanInput (I := I) ⥤ Arrow (EnrichedFunctorCat PointedCGWH.{u, v} I) where
  obj D := Arrow.mk ((originalSpanSourceCounit (B := B)).app D ≫ D.map h)
  map a := Arrow.homMk ((originalSpanSource (B := B)).map a) (a.app j) (by
    change (originalSpanSource (B := B)).map a ≫
      ((originalSpanSourceCounit (B := B)).app _ ≫ _) =
        ((originalSpanSourceCounit (B := B)).app _ ≫ _) ≫ a.app j
    have he := (originalSpanSourceCounit (B := B)).naturality a
    have hn := a.naturality h
    calc
      _ = ((originalSpanSource (B := B)).map a ≫
          (originalSpanSourceCounit (B := B)).app _) ≫ _ :=
        (Category.assoc _ _ _).symm
      _ = ((originalSpanSourceCounit (B := B)).app _ ≫ a.app WalkingSpan.zero) ≫ _ :=
        congrArg (fun f => f ≫ _) he
      _ = (originalSpanSourceCounit (B := B)).app _ ≫ (_ ≫ a.app j) :=
        (Category.assoc _ _ _).trans (congrArg (fun f => _ ≫ f) hn.symm)
      _ = _ := (Category.assoc _ _ _).symm)
  map_id D := by
    apply Arrow.hom_ext
    · exact (originalSpanSource (B := B)).map_id D
    · exact NatTrans.id_app D j
  map_comp a b := by
    apply Arrow.hom_ext
    · exact (originalSpanSource (B := B)).map_comp a b
    · rfl

/-- Both resolved target functors use the same original I intermediate functor. -/
def originalSpanLegTarget (j : WalkingSpan) (h : WalkingSpan.zero ⟶ j) :
    OriginalSpanInput (I := I) ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I :=
  originalSpanLegInput (B := B) j h ⋙ (Native.cofibrantFactorizationData (B := B)).Z

/-- The actual resolved leg is the first original I factor, on all input spans. -/
def originalSpanLegInclusion (j : WalkingSpan) (h : WalkingSpan.zero ⟶ j) :
    originalSpanSource (B := B) (I := I) ⟶ originalSpanLegTarget (B := B) j h :=
  Functor.whiskerLeft (originalSpanLegInput (B := B) j h)
    (Native.cofibrantFactorizationData (B := B)).i

/-- The actual target counit is the second original I factor, on all input spans. -/
def originalSpanLegCounit (j : WalkingSpan) (h : WalkingSpan.zero ⟶ j) :
    originalSpanLegTarget (B := B) (I := I) j h ⟶
      (CategoryTheory.evaluation WalkingSpan
    (EnrichedFunctorCat PointedCGWH.{u, v} I)).obj j :=
  Functor.whiskerLeft (originalSpanLegInput (B := B) j h)
    (Native.cofibrantFactorizationData (B := B)).p

/-- The entire resolved leg retains the original source counit and caller leg. -/
theorem originalSpanLeg_fac (j : WalkingSpan) (h : WalkingSpan.zero ⟶ j)
    (D : OriginalSpanInput (I := I)) :
    (originalSpanLegInclusion (B := B) j h).app D ≫
      (originalSpanLegCounit (B := B) j h).app D =
        (originalSpanSourceCounit (B := B)).app D ≫ D.map h :=
  (Native.cofibrantFactorizationData (B := B)).fac_app

/-- Every full original span source is genuinely cofibrant. -/
theorem originalSpanSource_cofibrant (D : OriginalSpanInput (I := I)) :
    IsCofibrant ((originalSpanSource (B := B)).obj D) :=
  NativeOmegaWeakClosure.originalSpan_zero_cofibrant (B := B) D

/-- Both actual original resolved legs are genuine same-I cofibrations. -/
theorem originalSpanLeg_cofibration (j : WalkingSpan) (h : WalkingSpan.zero ⟶ j)
    (D : OriginalSpanInput (I := I)) :
    cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I)
      ((originalSpanLegInclusion (B := B) j h).app D) :=
  (Native.cofibrantFactorizationData (B := B)).hi _

/-- Both actual original resolved legs have native HEP with all target quantifiers. -/
theorem originalSpanLeg_HEP (j : WalkingSpan) (h : WalkingSpan.zero ⟶ j)
    (D : OriginalSpanInput (I := I)) :
    PointedCGWH.EnrichedBasedHomotopyExtension.property
      ((originalSpanLegInclusion (B := B) j h).app D) := by
  have hi := originalSpanLeg_cofibration (B := B) j h D
  rw [Native.cofibrations_eq] at hi
  exact OriginalContinuousSourceApproximation.originalNativeILeft_le_HEP _ hi

/-- Every original target counit is an actual level trivial fibration. -/
theorem originalSpanLegCounit_trivialFibration (j : WalkingSpan)
    (h : WalkingSpan.zero ⟶ j) (D : OriginalSpanInput (I := I)) :
    trivialFibrations (EnrichedFunctorCat PointedCGWH.{u, v} I)
      ((originalSpanLegCounit (B := B) j h).app D) :=
  (Native.cofibrantFactorizationData (B := B)).hp _

/-- The native span targets are cofibrant because their genuine source is cofibrant. -/
theorem originalSpanLegTarget_cofibrant (j : WalkingSpan)
    (h : WalkingSpan.zero ⟶ j) (D : OriginalSpanInput (I := I)) :
    IsCofibrant ((originalSpanLegTarget (B := B) j h).obj D) := by
  let _ : IsCofibrant ((originalSpanSource (B := B)).obj D) :=
    originalSpanSource_cofibrant D
  let _ : Cofibration ((originalSpanLegInclusion (B := B) j h).app D) :=
    (HomotopicalAlgebra.cofibration_iff _).mpr
      (originalSpanLeg_cofibration j h D)
  exact isCofibrant_of_cofibration ((originalSpanLegInclusion (B := B) j h).app D)

end PointedCGWH.Spectra.OriginalOrthogonalRawPiHEPPushoutGluing

namespace PointedCGWH.Spectra.OriginalOrthogonalRawPiHEPPushoutGluing

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf
variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The whole same-I source span retains the two genuine resolved leg functors. -/
def originalSpanDiagram (D : OriginalSpanInput (I := I)) : OriginalSpanInput (I := I) :=
  (NativeOmegaWeakClosure.originalSpanFunctor (B := B)).obj D

/-- Every original span transformation induces the complete original three-stage map. -/
def originalSpanMap {D E : OriginalSpanInput (I := I)} (a : D ⟶ E) :
    originalSpanDiagram (B := B) D ⟶ originalSpanDiagram (B := B) E :=
  (NativeOmegaWeakClosure.originalSpanFunctor (B := B)).map a

/-- The actual resolved diagram acts functorially on every original span and map. -/
def originalSpanFunctor : OriginalSpanInput (I := I) ⥤ OriginalSpanInput (I := I) :=
  NativeOmegaWeakClosure.originalSpanFunctor (B := B)

/-- The full original span counit uses its original Q and both I right factors. -/
def originalSpanCounit (D : OriginalSpanInput (I := I)) :
    originalSpanDiagram (B := B) D ⟶ D :=
  (NativeOmegaWeakClosure.originalSpanCounit (B := B)).app D

/-- The complete same-I span counit is natural on every full original input map. -/
def originalSpanCounitNatTrans : originalSpanFunctor (B := B) (I := I) ⟶
    𝟭 (OriginalSpanInput (I := I)) :=
  NativeOmegaWeakClosure.originalSpanCounit (B := B)

/-- The same original span counit is level weak at all three actual stages. -/
theorem originalSpanCounit_levelWeak (D : OriginalSpanInput (I := I)) (j : WalkingSpan) :
    weakEquivalences (EnrichedFunctorCat PointedCGWH.{u, v} I)
      ((originalSpanCounit (B := B) D).app j) :=
  (NativeOmegaWeakClosure.originalSpanCounit_trivialFibration (B := B) D j).2

/-- Both actual same-I resolved span legs satisfy native HEP. -/
theorem originalSpanDiagram_HEP (D : OriginalSpanInput (I := I)) :
    PointedCGWH.EnrichedBasedHomotopyExtension.property
      ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst) ∧
    PointedCGWH.EnrichedBasedHomotopyExtension.property
      ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd) :=
  ⟨originalSpanLeg_HEP WalkingSpan.left WalkingSpan.Hom.fst D,
    originalSpanLeg_HEP WalkingSpan.right WalkingSpan.Hom.snd D⟩

/-- The actual comparison descends the original counit followed by both caller legs. -/
def originalSpanCallerComparison (D : OriginalSpanInput (I := I))
    {Q P : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (lQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.left ⟶ Q)
    (rQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.right ⟶ Q)
    (sqQ : IsPushout ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst)
      ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd) lQ rQ)
    (lP : D.obj WalkingSpan.left ⟶ P) (rP : D.obj WalkingSpan.right ⟶ P)
    (sqP : IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lP rP) : Q ⟶ P :=
  sqQ.desc ((originalSpanCounit (B := B) D).app WalkingSpan.left ≫ lP)
    ((originalSpanCounit (B := B) D).app WalkingSpan.right ≫ rP) (by
      rw [← Category.assoc, (originalSpanCounit (B := B) D).naturality WalkingSpan.Hom.fst,
        Category.assoc, sqP.w, ← Category.assoc,
        ← (originalSpanCounit (B := B) D).naturality WalkingSpan.Hom.snd, Category.assoc])

/-- The comparison preserves the actual full left caller pushout leg. -/
theorem originalSpanCallerComparison_left (D : OriginalSpanInput (I := I))
    {Q P : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (lQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.left ⟶ Q)
    (rQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.right ⟶ Q)
    (sqQ : IsPushout ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst)
      ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd) lQ rQ)
    (lP : D.obj WalkingSpan.left ⟶ P) (rP : D.obj WalkingSpan.right ⟶ P)
    (sqP : IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lP rP) :
    lQ ≫ originalSpanCallerComparison D lQ rQ sqQ lP rP sqP =
      (originalSpanCounit (B := B) D).app WalkingSpan.left ≫ lP :=
  sqQ.inl_desc _ _ _

/-- The comparison preserves the actual full right caller pushout leg. -/
theorem originalSpanCallerComparison_right (D : OriginalSpanInput (I := I))
    {Q P : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (lQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.left ⟶ Q)
    (rQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.right ⟶ Q)
    (sqQ : IsPushout ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst)
      ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd) lQ rQ)
    (lP : D.obj WalkingSpan.left ⟶ P) (rP : D.obj WalkingSpan.right ⟶ P)
    (sqP : IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lP rP) :
    rQ ≫ originalSpanCallerComparison D lQ rQ sqQ lP rP sqP =
      (originalSpanCounit (B := B) D).app WalkingSpan.right ≫ rP :=
  sqQ.inr_desc _ _ _

end PointedCGWH.Spectra.OriginalOrthogonalRawPiHEPPushoutGluing

namespace PointedCGWH.Spectra.OriginalOrthogonalRawPiHEPPushoutGluing

open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open OrthogonalIntegerHomotopy
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
variable [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- Genuine original HEP span comparison is an all-integer equivalence
for every caller resolved and ordinary pushout, with every counit leg retained. -/
theorem originalOrthogonalSpanCallerComparison_integerPi
    (D : WalkingSpan ⥤ OrthogonalCarrier.{u, v}) {Q P : OrthogonalCarrier.{u, v}}
    (lQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.left ⟶ Q)
    (rQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.right ⟶ Q)
    (sqQ : IsPushout ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst)
      ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd) lQ rQ)
    (lP : D.obj WalkingSpan.left ⟶ P) (rP : D.obj WalkingSpan.right ⟶ P)
    (sqP : IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lP rP)
    (hi : PointedCGWH.EnrichedBasedHomotopyExtension.property (D.map WalkingSpan.Hom.fst)) :
    integerPiStarEquivalences (originalSpanCallerComparison D lQ rQ sqQ lP rP sqP) := by
  let e := originalSpanCounit (B := B) D
  exact originalOrthogonalRawPiHEPpushoutGluing
    ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst)
    ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd) lQ rQ
    (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lP rP sqQ sqP
    (originalSpanDiagram_HEP D).1 hi
    (e.app WalkingSpan.zero) (e.app WalkingSpan.left) (e.app WalkingSpan.right)
    (originalSpanCallerComparison D lQ rQ sqQ lP rP sqP)
    (e.naturality WalkingSpan.Hom.fst).symm
    (e.naturality WalkingSpan.Hom.snd).symm
    (originalSpanCallerComparison_left D lQ rQ sqQ lP rP sqP).symm
    (originalSpanCallerComparison_right D lQ rQ sqQ lP rP sqP).symm
    (levelWeak_le_integerPiStarEquivalences _ (originalSpanCounit_levelWeak D WalkingSpan.zero))
    (levelWeak_le_integerPiStarEquivalences _ (originalSpanCounit_levelWeak D WalkingSpan.left))
    (levelWeak_le_integerPiStarEquivalences _ (originalSpanCounit_levelWeak D WalkingSpan.right))

end PointedCGWH.Spectra.OriginalOrthogonalRawPiHEPPushoutGluing

namespace PointedCGWH.Spectra.OriginalOrthogonalRawPiHEPPushoutGluing

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf
variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- Original all-Omega tests of a caller span leg transfer to the actual same-I resolved leg. -/
theorem originalSpanLeg_omegaTests (s : NativeStabilizationFamily.{u, v} I L)
    (j : WalkingSpan) (h : WalkingSpan.zero ⟶ j) (D : OriginalSpanInput (I := I))
    (hD : NativeK.omegaTests s (D.map h)) :
    NativeK.omegaTests s ((originalSpanLegInclusion (B := B) j h).app D) := by
  let e0 := (originalSpanSourceCounit (B := B)).app D
  let ej := (originalSpanLegCounit (B := B) j h).app D
  let ij := (originalSpanLegInclusion (B := B) j h).app D
  have h0 : NativeK.omegaTests s e0 := NativeK.levelWeak_le_omegaTests s _
    (Replacement.cofibrantReplacementCounit_mem_weakEquivalences (D.obj WalkingSpan.zero))
  have hj : NativeK.omegaTests s ej := NativeK.levelWeak_le_omegaTests s _
    (originalSpanLegCounit_trivialFibration j h D).2
  have hComp : NativeK.omegaTests s (e0 ≫ D.map h) :=
    (NativeK.omegaTests s).comp_mem _ _ h0 hD
  have hfac : ij ≫ ej = e0 ≫ D.map h := originalSpanLeg_fac j h D
  exact (NativeK.omegaTests s).of_postcomp ij ej hj (hfac.symm ▸ hComp)

end PointedCGWH.Spectra.OriginalOrthogonalRawPiHEPPushoutGluing

namespace PointedCGWH.Spectra.OriginalOrthogonalRawPiHEPPushoutGluing

open HomotopicalAlgebra.EnrichedProjective.Native
open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open PointedCGWH.EnrichedMapping
open NativeK
attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits
  MonoidalClosed.enrichedCategorySelf
variable {I L : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The actual cofibrant source span pushes an original Omega-test leg
through every resolved caller pushout and every genuine Omega target. -/
theorem originalResolvedSpanPushout_omegaTests (s : NativeStabilizationFamily.{u, v} I L)
    (D : OriginalSpanInput (I := I)) {Q : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (lQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.left ⟶ Q)
    (rQ : (originalSpanDiagram (B := B) D).obj WalkingSpan.right ⟶ Q)
    (sqQ : IsPushout ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst)
      ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd) lQ rQ)
    (hD : NativeK.omegaTests s (D.map WalkingSpan.Hom.fst)) : NativeK.omegaTests s rQ := by
  let A := (originalSpanDiagram (B := B) D).obj WalkingSpan.zero
  let X := (originalSpanDiagram (B := B) D).obj WalkingSpan.left
  let Z := (originalSpanDiagram (B := B) D).obj WalkingSpan.right
  let i : A ⟶ X := (originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst
  let z : A ⟶ Z := (originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd
  let _ : IsCofibrant A := originalSpanSource_cofibrant D
  let _ : IsCofibrant X := originalSpanLegTarget_cofibrant WalkingSpan.left WalkingSpan.Hom.fst D
  let _ : IsCofibrant Z := originalSpanLegTarget_cofibrant WalkingSpan.right WalkingSpan.Hom.snd D
  have hi : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) i :=
    originalSpanLeg_cofibration WalkingSpan.left WalkingSpan.Hom.fst D
  have hrQ : cofibrations (EnrichedFunctorCat PointedCGWH.{u, v} I) rQ :=
    MorphismProperty.of_isPushout sqQ.flip hi
  let _ : Cofibration rQ := (HomotopicalAlgebra.cofibration_iff _).mpr hrQ
  let _ : IsCofibrant Q := isCofibrant_of_cofibration rQ
  have hiTests : NativeK.omegaTests s i :=
    originalSpanLeg_omegaTests s WalkingSpan.left WalkingSpan.Hom.fst D hD
  apply DerivedLocalMapping.omegaTests_of_mappingPre_weak s rQ
  intro E hE
  have hMap : trivialFibrations PointedCGWH.{u, v} (WeightedEndVariance.pre i E) :=
    ⟨NativeK.mapSource_fibration i hi E,
      DerivedLocalMapping.mappingPre_weak_of_omegaTests s i hiTests E hE⟩
  have hPullback := PointedCGWH.NativeMappingPushout.sourceSquare i z lQ rQ sqQ E
  have hLeg : trivialFibrations PointedCGWH.{u, v} (WeightedEndVariance.pre rQ E) :=
    MorphismProperty.of_isPullback hPullback hMap
  exact hLeg.2

end PointedCGWH.Spectra.OriginalOrthogonalRawPiHEPPushoutGluing

namespace PointedCGWH.Spectra.OriginalOrthogonalRawPiHEPPushoutGluing

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- The actual same-I resolved pushout functor retains all original span input maps. -/
def originalSpanPushout : OriginalSpanInput (I := I) ⥤ EnrichedFunctorCat PointedCGWH.{u, v} I :=
  NativeOmegaWeakClosure.originalSpanColimit (B := B)

/-- The full original span-to-caller colimit comparison retains its natural counit. -/
def originalSpanPushoutCounit : originalSpanPushout (B := B) (I := I) ⟶ colim :=
  NativeOmegaWeakClosure.originalSpanColimitComparison (B := B)

/-- Every actual original span transformation retains the entire colimit counit square. -/
theorem originalSpanPushoutCounit_naturality {D E : OriginalSpanInput (I := I)} (a : D ⟶ E) :
    (originalSpanPushout (B := B)).map a ≫ (originalSpanPushoutCounit (B := B)).app E =
      (originalSpanPushoutCounit (B := B)).app D ≫ colim.map a :=
  NativeOmegaWeakClosure.originalSpanColimitComparison_naturality a

/-- All three actual colimit legs retain the original I span counit component. -/
theorem originalSpanPushoutCounit_leg (D : OriginalSpanInput (I := I)) (j : WalkingSpan) :
    colimit.ι (originalSpanDiagram (B := B) D) j ≫
      (originalSpanPushoutCounit (B := B)).app D =
        (originalSpanCounit (B := B) D).app j ≫ colimit.ι D j :=
  NativeOmegaWeakClosure.originalSpanColimitComparison_ι D j

end PointedCGWH.Spectra.OriginalOrthogonalRawPiHEPPushoutGluing

namespace PointedCGWH.Spectra.OriginalOrthogonalRawPiHEPPushoutGluing

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory
  PointedCGWH.EnrichedMapping.hasSmallLimits MonoidalClosed.enrichedCategorySelf
variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

/-- Every actual input span map and all chosen caller pushouts retain the complete
natural counit comparison square, without changing either colimit choice. -/
theorem originalSpanCallerComparison_naturality
    {D E : OriginalSpanInput (I := I)} (a : D ⟶ E)
    {QD PD QE PE : EnrichedFunctorCat PointedCGWH.{u, v} I}
    (lQD : (originalSpanDiagram (B := B) D).obj WalkingSpan.left ⟶ QD)
    (rQD : (originalSpanDiagram (B := B) D).obj WalkingSpan.right ⟶ QD)
    (sQD : IsPushout ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.fst)
      ((originalSpanDiagram (B := B) D).map WalkingSpan.Hom.snd) lQD rQD)
    (lPD : D.obj WalkingSpan.left ⟶ PD) (rPD : D.obj WalkingSpan.right ⟶ PD)
    (sPD : IsPushout (D.map WalkingSpan.Hom.fst) (D.map WalkingSpan.Hom.snd) lPD rPD)
    (lQE : (originalSpanDiagram (B := B) E).obj WalkingSpan.left ⟶ QE)
    (rQE : (originalSpanDiagram (B := B) E).obj WalkingSpan.right ⟶ QE)
    (sQE : IsPushout ((originalSpanDiagram (B := B) E).map WalkingSpan.Hom.fst)
      ((originalSpanDiagram (B := B) E).map WalkingSpan.Hom.snd) lQE rQE)
    (lPE : E.obj WalkingSpan.left ⟶ PE) (rPE : E.obj WalkingSpan.right ⟶ PE)
    (sPE : IsPushout (E.map WalkingSpan.Hom.fst) (E.map WalkingSpan.Hom.snd) lPE rPE)
    (q : QD ⟶ QE) (p : PD ⟶ PE)
    (hQL : lQD ≫ q = (originalSpanMap (B := B) a).app WalkingSpan.left ≫ lQE)
    (hQR : rQD ≫ q = (originalSpanMap (B := B) a).app WalkingSpan.right ≫ rQE)
    (hPL : lPD ≫ p = a.app WalkingSpan.left ≫ lPE)
    (hPR : rPD ≫ p = a.app WalkingSpan.right ≫ rPE) :
    q ≫ originalSpanCallerComparison E lQE rQE sQE lPE rPE sPE =
      originalSpanCallerComparison D lQD rQD sQD lPD rPD sPD ≫ p := by
  have hN := (originalSpanCounitNatTrans (B := B)).naturality a
  have hNL := congrArg (fun f => f.app WalkingSpan.left) hN
  change (originalSpanMap (B := B) a).app WalkingSpan.left ≫
    (originalSpanCounit (B := B) E).app WalkingSpan.left =
      (originalSpanCounit (B := B) D).app WalkingSpan.left ≫ a.app WalkingSpan.left at hNL
  have hNR := congrArg (fun f => f.app WalkingSpan.right) hN
  change (originalSpanMap (B := B) a).app WalkingSpan.right ≫
    (originalSpanCounit (B := B) E).app WalkingSpan.right =
      (originalSpanCounit (B := B) D).app WalkingSpan.right ≫ a.app WalkingSpan.right at hNR
  let cD : QD ⟶ PD := originalSpanCallerComparison D lQD rQD sQD lPD rPD sPD
  let cE : QE ⟶ PE := originalSpanCallerComparison E lQE rQE sQE lPE rPE sPE
  have hDL : lQD ≫ cD = (originalSpanCounit (B := B) D).app WalkingSpan.left ≫ lPD :=
    originalSpanCallerComparison_left D lQD rQD sQD lPD rPD sPD
  have hDR : rQD ≫ cD = (originalSpanCounit (B := B) D).app WalkingSpan.right ≫ rPD :=
    originalSpanCallerComparison_right D lQD rQD sQD lPD rPD sPD
  have hEL : lQE ≫ cE = (originalSpanCounit (B := B) E).app WalkingSpan.left ≫ lPE :=
    originalSpanCallerComparison_left E lQE rQE sQE lPE rPE sPE
  have hER : rQE ≫ cE = (originalSpanCounit (B := B) E).app WalkingSpan.right ≫ rPE :=
    originalSpanCallerComparison_right E lQE rQE sQE lPE rPE sPE
  change q ≫ cE = cD ≫ p
  apply sQD.hom_ext
  · rw [← Category.assoc, hQL, Category.assoc, hEL, ← Category.assoc, hNL,
      Category.assoc, ← hPL, ← Category.assoc, ← hDL, Category.assoc]
  · rw [← Category.assoc, hQR, Category.assoc, hER, ← Category.assoc, hNR,
      Category.assoc, ← hPR, ← Category.assoc, ← hDR, Category.assoc]

end PointedCGWH.Spectra.OriginalOrthogonalRawPiHEPPushoutGluing
