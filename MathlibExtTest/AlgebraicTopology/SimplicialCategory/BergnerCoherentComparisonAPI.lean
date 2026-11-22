/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalBergnerNativeFunctorialFactorization
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentLocalizationEquivalence
import MathlibExt.AlgebraicTopology.SimplicialCategory.OrdinaryCoherentNervePostcomposition

/-!
# Bergner model and coherent comparison clients

The named varying-object Bergner model supplies both factorizations and
lifting systems. Empty objects, colliding object images and a non-Kan Hom
coefficient exercise the distinction between weak maps and fibrations.
The coherent comparison retains the actual adjunct, replacement unit and
localized realization maps, and its nerve agrees with Mathlib's simplicial
nerve on the same enrichment.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w

open CategoryTheory Limits HomotopicalAlgebra MonoidalCategory Opposite
open CategoryTheory.SimplicialEnrichment CategoryTheory.CoherentRealization
open scoped Simplicial SSet.modelCategoryQuillen

namespace MathlibExtTest.AlgebraicTopology.SimplicialCategory.BergnerCoherentComparisonAPI

attribute [local instance] Bergner.modelCategory JoyalSSet.modelCategory

open OriginalBergnerIntervalFamily

/-- The selected model has the full Hom and component classes on every enriched functor. -/
theorem namedModelClasses {C D : Carrier.{u}} (F : C ⟶ D) :
    (WeakEquivalence F ↔ EnrichedDwyerKan.weakEquivalences F) ∧
      (Fibration F ↔ Bergner.localFibrations F) ∧
        (Cofibration F ↔ Bergner.generatingCofibrations.rlp.llp F) :=
  ⟨Bergner.weakEquivalence_iff_original F,
    Bergner.fibration_iff_original F, Bergner.cofibration_iff_original F⟩

/-- The boundary construction factors every changing-object functor in the first model system. -/
theorem boundaryFactorization {C D : Carrier.{u}} (F : C ⟶ D) :
    ∃ (Z : Carrier.{u}) (i : C ⟶ Z) (p : Z ⟶ D),
      Cofibration i ∧ Fibration p ∧ WeakEquivalence p ∧ i ≫ p = F := by
  let d := Bergner.BoundaryFactorization.data F
  have hp := Bergner.BoundaryFactorization.right_original_classes F
  exact ⟨d.Z, d.i, d.p, (Bergner.cofibration_iff_original _).mpr d.hi,
    (Bergner.fibration_iff_original _).mpr hp.1,
    (Bergner.weakEquivalence_iff_original _).mpr hp.2, d.fac⟩

/-- The combined horn and interval construction gives the second model factorization. -/
theorem nativeFactorization {C D : Carrier.{u}} (F : C ⟶ D) :
    ∃ (Z : Carrier.{u}) (i : C ⟶ Z) (p : Z ⟶ D),
      Cofibration i ∧ WeakEquivalence i ∧ Fibration p ∧ i ≫ p = F := by
  let d := NativeFactorization.data F
  exact ⟨d.Z, d.i, d.p, (Bergner.cofibration_iff_original _).mpr d.hi.1,
    (Bergner.weakEquivalence_iff_original _).mpr d.hi.2,
    (Bergner.fibration_iff_original _).mpr d.hp, d.fac⟩

/-- Both equations of a first-system diagonal follow from the named model. -/
theorem boundarySquareLift {A B X Y : Carrier.{u}} (i : A ⟶ B) (p : X ⟶ Y)
    [Cofibration i] [Fibration p] [WeakEquivalence p]
    (a : A ⟶ X) (b : B ⟶ Y) (sq : CommSq a i p b) :
    ∃ l : B ⟶ X, i ≫ l = a ∧ l ≫ p = b :=
  ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- The constructed second-system maps lift without a supplied lifting certificate. -/
theorem nativeSquareLift {C D E H : Carrier.{u}} (F : C ⟶ D) (G : E ⟶ H)
    (a : C ⟶ (NativeFactorization.data G).Z)
    (b : (NativeFactorization.data F).Z ⟶ H)
    (sq : CommSq a (NativeFactorization.data F).i (NativeFactorization.data G).p b) :
    ∃ l : (NativeFactorization.data F).Z ⟶ (NativeFactorization.data G).Z,
      (NativeFactorization.data F).i ≫ l = a ∧ l ≫ (NativeFactorization.data G).p = b := by
  let _ : Cofibration (NativeFactorization.data F).i :=
    (Bergner.cofibration_iff_original _).mpr (NativeFactorization.data F).hi.1
  let _ : WeakEquivalence (NativeFactorization.data F).i :=
    (Bergner.weakEquivalence_iff_original _).mpr (NativeFactorization.data F).hi.2
  let _ : Fibration (NativeFactorization.data G).p :=
    (Bergner.fibration_iff_original _).mpr (NativeFactorization.data G).hp
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

/-- Native factorization retains the full Hom composite and both endpoint transports. -/
theorem nativeHomFactorization {C D : Carrier.{u}} (F : C ⟶ D) (x y : C) :
    ((NativeFactorization.data F).i.map x y ≫
      (NativeFactorization.data F).p.map
        ((NativeFactorization.data F).i.obj x) ((NativeFactorization.data F).i.obj y)) ≫
      eqToHom (congrArg₂ (fun a b : D => a ⟶[SSet.{u}] b)
        (NativeFactorization.object_fac F x) (NativeFactorization.object_fac F y)) =
      F.map x y := NativeFactorization.hom_fac F x y

/-- The empty-to-point functor fails the component essential-surjectivity condition. -/
theorem emptyToPointNotWeak :
    ¬ EnrichedDwyerKan.weakEquivalences BergnerObjects.inclusion.{u} := by
  intro h
  let _ : (ComponentCategory.mapFunctor BergnerObjects.inclusion.{u}).EssSurj := h.2
  obtain ⟨x, _⟩ := Functor.EssSurj.mem_essImage
    (ComponentCategory.mapFunctor BergnerObjects.inclusion.{u})
      (ComponentCategory.objectOf.{u} BergnerObjects.point PUnit.unit)
  exact PEmpty.elim (ComponentCategory.originalObject.{u} BergnerObjects.empty x)

/-- The named model also detects failure of weakness at this empty input. -/
theorem emptyToPointNotModelWeak : ¬ WeakEquivalence BergnerObjects.inclusion.{u} := by
  intro h
  exact emptyToPointNotWeak ((Bergner.weakEquivalence_iff_original _).mp h)

/-- The boundary factorization really adds objects to an empty source. -/
theorem emptyBoundaryIntermediateNonempty :
    Nonempty (Bergner.BoundaryFactorization.data BergnerObjects.inclusion.{u}).Z := by
  obtain ⟨x, _⟩ := Bergner.BoundaryFactorization.right_objects_surjective
    BergnerObjects.inclusion.{u} PUnit.unit
  exact ⟨x⟩

/-- A second-system projection need not be weak when the original input is not weak. -/
theorem emptyNativeProjectionNotWeak :
    ¬ EnrichedDwyerKan.weakEquivalences
      (NativeFactorization.data BergnerObjects.inclusion.{u}).p := by
  intro h
  have hw := EnrichedDwyerKan.comp_weak _ _
    (NativeFactorization.data BergnerObjects.inclusion.{u}).hi.2 h
  exact emptyToPointNotWeak (NativeFactorization.fac BergnerObjects.inclusion ▸ hw)

/-- Two distinct original objects can have the same image under an enriched functor. -/
def twoObjects : Carrier.{u} := CodiscreteEnrichment.object (ULift.{u} (Fin 2))

def collapse : twoObjects.{u} ⟶ BergnerObjects.point.{u} :=
  CodiscreteEnrichment.map (↾fun _ => PUnit.unit)

theorem collapseNotInjective : ¬ Function.Injective collapse.{u}.obj := by
  intro h
  have bad := h (show collapse.{u}.obj (ULift.up (0 : Fin 2)) =
    collapse.{u}.obj (ULift.up 1) from rfl)
  exact Fin.zero_ne_one (congrArg ULift.down bad)

/-- The same object collapse has weak full Hom maps and is essentially surjective. -/
theorem collapseWeak : EnrichedDwyerKan.weakEquivalences collapse.{u} := by
  constructor
  · intro x y
    exact SSet.realizationWeakEquivalences.id_mem _
  · exact Functor.essSurj_of_surj (fun _ => ⟨ULift.up (0 : Fin 2), rfl⟩)

/-- Both native factors retain the complete colliding-object input. -/
theorem collapseNativeFactorization :
    (NativeFactorization.data collapse.{u}).i ≫
      (NativeFactorization.data collapse.{u}).p = collapse.{u} :=
  NativeFactorization.fac collapse

/-- The standard ordered interval is not Kan: its forward edge cannot have a reverse edge. -/
theorem orderedIntervalNotKan : ¬ SSet.KanComplex (Δ[1] : SSet.{u}) := by
  intro h
  let _ := h
  let e := SSet.Edge.mk' (SSet.stdSimplex.objMk₁.{u} (1 : Fin 3))
  obtain ⟨I⟩ := (SSet.Edge.isEquivalence_of_kanComplex e).nonempty_invStruct
  have hs := congrArg (fun v : (Δ[1] : SSet.{u}) _⦋0⦌ => v 0) I.inv.src_eq
  have ht := congrArg (fun v : (Δ[1] : SSet.{u}) _⦋0⦌ => v 0) I.inv.tgt_eq
  change I.inv.edge 0 = 1 at hs
  change I.inv.edge 1 = 0 at ht
  have hm : (1 : Fin 2) ≤ 0 := by
    have hmono : I.inv.edge 0 ≤ I.inv.edge 1 :=
      I.inv.edge.down.toOrderHom.monotone (show (0 : Fin 2) ≤ 1 from by decide)
    exact (congrArg₂ (fun x y : Fin 2 => x ≤ y) hs ht).mp hmono
  exact (by decide : ¬ (1 : Fin 2) ≤ 0) hm

def nonKanCarrier : Carrier.{u} := BergnerTwoObject.object (Δ[1] : SSet.{u})

/-- Fibrancy detects the genuinely non-Kan forward Hom. -/
theorem nonKanCarrierNotFibrant : ¬ IsFibrant nonKanCarrier.{u} := by
  intro h
  have hKan := (Bergner.isFibrant_iff_original_homKan nonKanCarrier.{u}).mp h
    (BergnerTwoObject.source (Δ[1] : SSet.{u}))
    (BergnerTwoObject.target (Δ[1] : SSet.{u}))
  exact orderedIntervalNotKan hKan

/-- Identity fibrations and full boundary factorizations do not require fibrant input objects. -/
theorem nonKanIdentityAndBoundaryProjection :
    Fibration (𝟙 nonKanCarrier.{u}) ∧
      Fibration (Bergner.BoundaryFactorization.data (𝟙 nonKanCarrier.{u})).p ∧
        WeakEquivalence (Bergner.BoundaryFactorization.data (𝟙 nonKanCarrier.{u})).p := by
  have h := Bergner.BoundaryFactorization.right_original_classes (𝟙 nonKanCarrier.{u})
  exact ⟨inferInstance, (Bergner.fibration_iff_original _).mpr h.1,
    (Bergner.weakEquivalence_iff_original _).mpr h.2⟩

/-- The original native replacement is fibrant even for a non-Kan input. -/
theorem nonKanReplacement :
    IsFibrant (OriginalBergnerFibrantReplacement.functor.obj nonKanCarrier.{u}) ∧
      Cofibration (OriginalBergnerFibrantReplacement.inclusion.app nonKanCarrier.{u}) ∧
        WeakEquivalence (OriginalBergnerFibrantReplacement.inclusion.app nonKanCarrier.{u}) :=
  ⟨OriginalBergnerFibrantReplacement.isFibrant _,
    OriginalBergnerFibrantReplacement.inclusion_model_classes _⟩

/-- The actual coherent adjunction is Quillen equivalent at independent raised universes. -/
theorem namedQuillenEquivalence :
    OriginalQuillenComparison.adjunction.{u + 3}.IsQuillenEquivalence ∧
      OriginalQuillenComparison.adjunction.{v + 5}.IsQuillenEquivalence :=
  ⟨OriginalQuillenComparison.isQuillenEquivalence,
    OriginalQuillenComparison.isQuillenEquivalence⟩

/-- The full adjunct criterion needs target fibrancy and permits every simplicial source. -/
theorem allSourceAdjunctCriterion (K : JoyalSSet.{u}) (C : Carrier.{u}) [IsFibrant C]
    (F : OriginalQuillenComparison.left.obj K ⟶ C) :
    WeakEquivalence F ↔
      WeakEquivalence (OriginalQuillenComparison.adjunction.homEquiv K C F) :=
  OriginalQuillenComparison.allSource_homEquiv_weak_iff K C F

/-- Realization reflects and preserves categorical weakness for arbitrary simplicial maps. -/
theorem realizationWeakReflection {K L : SSet.{u}} (f : K ⟶ L) :
    EnrichedDwyerKan.weakEquivalences (realizationMap f) ↔ SSet.categoricalEquivalences f :=
  OriginalQuillenComparison.realizationMap_weak_iff f

/-- The nerve of a Bergner-fibrant enrichment is the same quasicategorical Mathlib nerve. -/
theorem pinnedMathlibNerve (C : Carrier.{u}) [IsFibrant C] :
    coherentNerveFunctor.obj C = SimplicialNerve (ForgetEnrichment SSet.{u} C) ∧
      SSet.Quasicategory (SimplicialNerve (ForgetEnrichment SSet.{u} C)) :=
  ⟨coherentNerve_eq_mathlib C,
    mathlibCoherentNerve_quasicategory C (Bergner.homKan_of_isFibrant C)⟩

/-- The weak replacement unit retains its actual counit factorization on every input. -/
theorem replacementUnitAndCounit (K : SSet.{u}) :
    SSet.categoricalEquivalences (OriginalQuillenComparison.replacementUnit.app K) ∧
      realizationMap (OriginalQuillenComparison.replacementUnit.app K) ≫
        counit (OriginalQuillenComparison.replacedRealization.obj K) =
          OriginalBergnerFibrantReplacement.inclusion.app (realization K) :=
  ⟨OriginalQuillenComparison.replacementUnit_weak K,
    OriginalQuillenComparison.replacementUnit_counit K⟩

/-- The ordinary localization equivalence uses the original realized map as its left image. -/
theorem localizationRealizationMap {K L : SSet.{u}} (f : K ⟶ L) :
    OriginalCoherentLocalization.equivalence.functor.map
        (OriginalCoherentLocalization.simplicialProjection.map f) =
      OriginalCoherentLocalization.enrichmentProjection.map (realizationMap f) :=
  OriginalCoherentLocalization.left_map_projection f

/-- The localized unit is the projection of the actual categorical weak replacement unit. -/
theorem localizationUnit (K : SSet.{u}) :
    OriginalCoherentLocalization.equivalence.unitIso.hom.app
        (OriginalCoherentLocalization.simplicialProjection.obj K) =
      OriginalCoherentLocalization.simplicialProjection.map
        (OriginalQuillenComparison.replacementUnit.app K) :=
  OriginalCoherentLocalization.unitIso_hom_projection K

/-- The localized counit retains the evaluation map and formal inverse of the native inclusion. -/
theorem localizationCounit (C : Carrier.{u}) :
    OriginalCoherentLocalization.equivalence.counitIso.hom.app
        (OriginalCoherentLocalization.enrichmentProjection.obj C) =
      OriginalCoherentLocalization.enrichmentProjection.map
          (counit (OriginalBergnerFibrantReplacement.functor.obj C)) ≫
        Localization.Construction.wInv (OriginalBergnerFibrantReplacement.inclusion.app C)
          (OriginalBergnerFibrantReplacement.inclusion_original_classes C).2 :=
  OriginalCoherentLocalization.counitIso_hom_projection C

/-- A weak functor with colliding object images becomes an isomorphism after DK localization. -/
theorem localizedCollapseIsIso :
    IsIso (OriginalCoherentLocalization.enrichmentProjection.map collapse.{u}) :=
  EnrichedDwyerKan.weakEquivalences.Q_inverts collapse collapseWeak

/-- The ordinary nerve adapter commutes with full enriched postcomposition. -/
theorem ordinaryNervePostcomposition {A : Type v} [Category.{w} A]
    (C D : Carrier.{max v w}) (F : A ⥤ ForgetEnrichment SSet.{max v w} C) (G : C ⟶ D) :
    OrdinaryNerveMap.map C F ≫ coherentNerveFunctor.map G =
      OrdinaryNerveMap.map D (F ⋙ G.forget) :=
  OrdinaryNerveMap.map_postcompose C D F G

end MathlibExtTest.AlgebraicTopology.SimplicialCategory.BergnerCoherentComparisonAPI
