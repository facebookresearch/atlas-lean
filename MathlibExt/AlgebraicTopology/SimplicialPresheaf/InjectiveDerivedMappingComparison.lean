/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialPresheaf.InjectiveMappingSupport
import MathlibExt.AlgebraicTopology.ModelCategory.DerivedMapping.StrictComparison
import MathlibExt.CategoryTheory.MorphismProperty.FunctorialFactorizationEquivalence
import Mathlib.AlgebraicTopology.ModelCategory.Transport

/-!
# Chosen derived mapping objects on the original injective presheaf category

The actual scalar enrichment supplies a lower-Hom carrier in the value universe.
We transport the established injective model and its full functorial factorizations
to that carrier, use its native replacements once, and pull those same choices back
to the original presheaves. Raw Brown invariance compares every original arrow with
the resulting chosen-derived map at a fibrant target.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open HomotopicalAlgebra Opposite MonoidalCategory
open scoped SSet.modelCategoryQuillen

attribute [local instance] SimplicialPresheaf.scalarEnrichment
attribute [local instance] SimplicialPresheaf.InjectiveKan.modelCategory

namespace SimplicialPresheaf.InjectiveKan

variable (D : Type w) [Category.{v} D] [Small.{u} D] [LocallySmall.{u} D]

/-- The genuine enriched carrier has the original objects and scalar-u morphisms. -/
abbrev MappingCarrier := ForgetEnrichment SSet.{u} (SimplicialPresheaf.{u} D)

/-- The original injective model is transported by the actual enriched carrier equivalence. -/
@[instance_reducible]
def mappingCarrierModel : ModelCategory (MappingCarrier.{u} D) := by
  let E := enrichedCarrierEquivalence (D := D)
  letI : CategoryWithCofibrations (MappingCarrier.{u} D) :=
    ⟨(cofibrations (SimplicialPresheaf.{u} D)).inverseImage E.inverse⟩
  letI : CategoryWithFibrations (MappingCarrier.{u} D) :=
    ⟨(fibrations (SimplicialPresheaf.{u} D)).inverseImage E.inverse⟩
  letI : CategoryWithWeakEquivalences (MappingCarrier.{u} D) :=
    ⟨(weakEquivalences (SimplicialPresheaf.{u} D)).inverseImage E.inverse⟩
  exact ModelCategory.transport E.symm rfl rfl rfl

attribute [local instance] mappingCarrierModel enrichedCarrierSimplicialCategory

/-- Both lower-Hom factor classes are literal inverse images of the original classes. -/
theorem mappingCarrier_classes :
    cofibrations (MappingCarrier.{u} D) =
        (cofibrations (SimplicialPresheaf.{u} D)).inverseImage
          (enrichedCarrierEquivalence (D := D)).inverse ∧
      fibrations (MappingCarrier.{u} D) =
        (fibrations (SimplicialPresheaf.{u} D)).inverseImage
          (enrichedCarrierEquivalence (D := D)).inverse ∧
      weakEquivalences (MappingCarrier.{u} D) =
        (weakEquivalences (SimplicialPresheaf.{u} D)).inverseImage
          (enrichedCarrierEquivalence (D := D)).inverse :=
  ⟨rfl, rfl, rfl⟩

/-- The original model's complete cofibration/trivial-fibration data. -/
def originalCofibrationFactorization : FunctorialFactorizationData
    (cofibrations (SimplicialPresheaf.{u} D))
    (trivialFibrations (SimplicialPresheaf.{u} D)) := by
  have hc : cofibrations (SimplicialPresheaf.{u} D) =
      monomorphisms (SimplicialPresheaf.{u} D) := (data D).cofibrations_eq
  exact (data D).cofibrationFactorization.ofLE hc.ge (data D).trivialFibrations_eq.ge

/-- The original model's complete trivial-cofibration/fibration data. -/
def originalTrivialCofibrationFactorization : FunctorialFactorizationData
    (trivialCofibrations (SimplicialPresheaf.{u} D))
    (fibrations (SimplicialPresheaf.{u} D)) := by
  have hf : fibrations (SimplicialPresheaf.{u} D) = injectiveFibrations D :=
    (data D).fibrations_eq
  exact (data D).trivialCofibrationFactorization.ofLE
    (data D).trivialCofibrations_eq.ge hf.ge

/-- Transport the full first factorization, retaining its native unit/counit legs. -/
def mappingCarrierCofibrationFactorization : FunctorialFactorizationData
    (cofibrations (MappingCarrier.{u} D)) (trivialFibrations (MappingCarrier.{u} D)) := by
  have h := (originalCofibrationFactorization.{u} D).ofEquivalence
    (enrichedCarrierEquivalence (D := D)).symm
  exact h.ofLE (by rw [(mappingCarrier_classes D).1]; exact le_rfl) (by
    intro X Y f hf
    change fibrations (SimplicialPresheaf.{u} D)
        ((enrichedCarrierEquivalence (D := D)).inverse.map f) ∧
      weakEquivalences (SimplicialPresheaf.{u} D)
        ((enrichedCarrierEquivalence (D := D)).inverse.map f) at hf ⊢
    exact hf)

/-- Transport the full second factorization, retaining its native unit/counit legs. -/
def mappingCarrierTrivialCofibrationFactorization : FunctorialFactorizationData
    (trivialCofibrations (MappingCarrier.{u} D)) (fibrations (MappingCarrier.{u} D)) := by
  have h := (originalTrivialCofibrationFactorization.{u} D).ofEquivalence
    (enrichedCarrierEquivalence (D := D)).symm
  exact h.ofLE (by
    intro X Y f hf
    change cofibrations (SimplicialPresheaf.{u} D)
        ((enrichedCarrierEquivalence (D := D)).inverse.map f) ∧
      weakEquivalences (SimplicialPresheaf.{u} D)
        ((enrichedCarrierEquivalence (D := D)).inverse.map f) at hf ⊢
    exact hf)
    (by rw [(mappingCarrier_classes D).2.1]; exact le_rfl)

/-- Native functorial replacement availability comes from the actual first transported data. -/
theorem mappingCarrierHasCofibrationFactorization :
    HasFunctorialFactorization (cofibrations (MappingCarrier.{u} D))
      (trivialFibrations (MappingCarrier.{u} D)) :=
  ⟨⟨mappingCarrierCofibrationFactorization D⟩⟩

/-- Native functorial replacement availability comes from the actual second transported data. -/
theorem mappingCarrierHasTrivialCofibrationFactorization :
    HasFunctorialFactorization (trivialCofibrations (MappingCarrier.{u} D))
      (fibrations (MappingCarrier.{u} D)) :=
  ⟨⟨mappingCarrierTrivialCofibrationFactorization D⟩⟩

attribute [local instance] mappingCarrierHasCofibrationFactorization
  mappingCarrierHasTrivialCofibrationFactorization

variable {D}

/-- The enriched carrier's original precomposition is the fixed-u presheaf end map. -/
theorem mappingCarrier_precomp {A B : MappingCarrier.{u} D} (f : A ⟶ B)
    (Z : MappingCarrier.{u} D) :
    eHomWhiskerRight SSet.{u} f Z =
      innerHomPre ((enrichedCarrierEquivalence (D := D)).inverse.map f)
        ((enrichedCarrierEquivalence (D := D)).inverse.obj Z) := by
  change (MonoidalCategory.leftUnitor _).inv ≫
      ForgetEnrichment.homTo SSet.{u} f ▷ _ ≫ eComp SSet.{u} _ _ _ =
    (MonoidalCategory.leftUnitor _).inv ≫
      eHomEquiv SSet.{u} ((eHomEquiv SSet.{u}).symm
        (ForgetEnrichment.homTo SSet.{u} f)) ▷ _ ≫ eComp SSet.{u} _ _ _
  rw [Equiv.apply_symm_apply]

/-- The enriched carrier's original postcomposition is the fixed-u presheaf end map. -/
theorem mappingCarrier_postcomp (A : MappingCarrier.{u} D)
    {X Y : MappingCarrier.{u} D} (f : X ⟶ Y) :
    eHomWhiskerLeft SSet.{u} A f =
      innerHomPost ((enrichedCarrierEquivalence (D := D)).inverse.obj A)
        ((enrichedCarrierEquivalence (D := D)).inverse.map f) := by
  change (MonoidalCategory.rightUnitor _).inv ≫
      _ ◁ ForgetEnrichment.homTo SSet.{u} f ≫ eComp SSet.{u} _ _ _ =
    (MonoidalCategory.rightUnitor _).inv ≫
      _ ◁ eHomEquiv SSet.{u} ((eHomEquiv SSet.{u}).symm
        (ForgetEnrichment.homTo SSet.{u} f)) ≫ eComp SSet.{u} _ _ _
  rw [Equiv.apply_symm_apply]

private theorem mappingCarrier_roundtrip_property
    (P : MorphismProperty (SimplicialPresheaf.{u} D)) :
    (P.inverseImage (enrichedCarrierEquivalence (D := D)).inverse).inverseImage
      (enrichedCarrierEquivalence (D := D)).functor = P := by
  ext A B f
  change P ((eHomEquiv SSet.{u}).symm (eHomEquiv SSet.{u} f)) ↔ P f
  rw [Equiv.symm_apply_apply]

/-- Fibrancy is transported through the actual arbitrary-terminal comparison. -/
theorem mappingCarrier_fibrant_iff (Z : MappingCarrier.{u} D) :
    IsFibrant Z ↔ IsFibrant ((enrichedCarrierEquivalence (D := D)).inverse.obj Z) := by
  let E := enrichedCarrierEquivalence (D := D)
  have ht := terminalIsTerminal.isTerminalObj E.inverse (⊤_ MappingCarrier.{u} D)
  rw [isFibrant_iff, fibration_iff, (mappingCarrier_classes D).2.1]
  change fibrations (SimplicialPresheaf.{u} D)
      (E.inverse.map (terminal.from Z)) ↔ IsFibrant (E.inverse.obj Z)
  simpa only [fibration_iff] using
    (isFibrant_iff_of_isTerminal (E.inverse.map (terminal.from Z)) ht).symm

variable (D)

/-- The selected native lower-Hom cofibration/trivial-fibration choice used by Q. -/
def chosenCarrierCofibrationFactorization : FunctorialFactorizationData
    (cofibrations (MappingCarrier.{u} D)) (trivialFibrations (MappingCarrier.{u} D)) :=
  cofFactData (C := MappingCarrier.{u} D)

/-- The selected native lower-Hom trivial-cofibration/fibration choice used by R. -/
def chosenCarrierTrivialCofibrationFactorization : FunctorialFactorizationData
    (trivialCofibrations (MappingCarrier.{u} D)) (fibrations (MappingCarrier.{u} D)) :=
  fibFactData (C := MappingCarrier.{u} D)

/-- Pull the very same selected Q factorization to every original Arrow. -/
def chosenOriginalCofibrationFactorization : FunctorialFactorizationData
    (cofibrations (SimplicialPresheaf.{u} D))
    (trivialFibrations (SimplicialPresheaf.{u} D)) := by
  have h := (chosenCarrierCofibrationFactorization.{u} D).ofEquivalence
    (enrichedCarrierEquivalence (D := D))
  exact h.ofLE (by
    rw [(mappingCarrier_classes D).1, mappingCarrier_roundtrip_property]) (by
    rw [trivialFibrations, (mappingCarrier_classes D).2.1,
      (mappingCarrier_classes D).2.2, inverseImage_inf,
      mappingCarrier_roundtrip_property, mappingCarrier_roundtrip_property]
    exact le_rfl)

/-- Pull the very same selected R factorization to every original Arrow. -/
def chosenOriginalTrivialCofibrationFactorization : FunctorialFactorizationData
    (trivialCofibrations (SimplicialPresheaf.{u} D))
    (fibrations (SimplicialPresheaf.{u} D)) := by
  have h := (chosenCarrierTrivialCofibrationFactorization.{u} D).ofEquivalence
    (enrichedCarrierEquivalence (D := D))
  exact h.ofLE (by
    rw [trivialCofibrations, (mappingCarrier_classes D).1,
      (mappingCarrier_classes D).2.2, inverseImage_inf,
      mappingCarrier_roundtrip_property, mappingCarrier_roundtrip_property]
    exact le_rfl) (by
    rw [(mappingCarrier_classes D).2.1, mappingCarrier_roundtrip_property])

/-- Both selected original factorizations retain their two actual unit/counit legs. -/
theorem chosenFactorization_transport (f : Arrow (SimplicialPresheaf.{u} D)) :
    let E := enrichedCarrierEquivalence (D := D)
    let QF := chosenCarrierCofibrationFactorization D
    let RF := chosenCarrierTrivialCofibrationFactorization D
    let QP := chosenOriginalCofibrationFactorization D
    let RP := chosenOriginalTrivialCofibrationFactorization D
    QP.i.app f = E.unitIso.hom.app f.left ≫
        E.inverse.map (QF.i.app (E.functor.mapArrow.obj f)) ∧
      QP.p.app f = E.inverse.map (QF.p.app (E.functor.mapArrow.obj f)) ≫
        E.unitIso.inv.app f.right ∧
      E.functor.map (QP.i.app f) ≫ E.counitIso.hom.app
        (QF.Z.obj (E.functor.mapArrow.obj f)) = QF.i.app (E.functor.mapArrow.obj f) ∧
      E.counitIso.hom.app (QF.Z.obj (E.functor.mapArrow.obj f)) ≫
        QF.p.app (E.functor.mapArrow.obj f) = E.functor.map (QP.p.app f) ∧
      QP.i.app f ≫ QP.p.app f = f.hom ∧
      RP.i.app f = E.unitIso.hom.app f.left ≫
        E.inverse.map (RF.i.app (E.functor.mapArrow.obj f)) ∧
      RP.p.app f = E.inverse.map (RF.p.app (E.functor.mapArrow.obj f)) ≫
        E.unitIso.inv.app f.right ∧
      E.functor.map (RP.i.app f) ≫ E.counitIso.hom.app
        (RF.Z.obj (E.functor.mapArrow.obj f)) = RF.i.app (E.functor.mapArrow.obj f) ∧
      E.counitIso.hom.app (RF.Z.obj (E.functor.mapArrow.obj f)) ≫
        RF.p.app (E.functor.mapArrow.obj f) = E.functor.map (RP.p.app f) ∧
      RP.i.app f ≫ RP.p.app f = f.hom := by
  dsimp only
  exact ⟨rfl, rfl, (chosenCarrierCofibrationFactorization D).ofEquivalence_mapped_i _ f,
    (chosenCarrierCofibrationFactorization D).ofEquivalence_mapped_p _ f,
    (chosenOriginalCofibrationFactorization D).fac_app,
    rfl, rfl, (chosenCarrierTrivialCofibrationFactorization D).ofEquivalence_mapped_i _ f,
    (chosenCarrierTrivialCofibrationFactorization D).ofEquivalence_mapped_p _ f,
    (chosenOriginalTrivialCofibrationFactorization D).fac_app⟩

/-- Every original Arrow square retains both selected middle maps and both natural legs. -/
theorem chosenFactorization_map {f g : Arrow (SimplicialPresheaf.{u} D)} (φ : f ⟶ g) :
    let E := enrichedCarrierEquivalence (D := D)
    let QF := chosenCarrierCofibrationFactorization D
    let RF := chosenCarrierTrivialCofibrationFactorization D
    let QP := chosenOriginalCofibrationFactorization D
    let RP := chosenOriginalTrivialCofibrationFactorization D
    QP.Z.map φ = E.inverse.map (QF.Z.map (E.functor.mapArrow.map φ)) ∧
      φ.left ≫ QP.i.app g = QP.i.app f ≫ QP.Z.map φ ∧
      QP.Z.map φ ≫ QP.p.app g = QP.p.app f ≫ φ.right ∧
      RP.Z.map φ = E.inverse.map (RF.Z.map (E.functor.mapArrow.map φ)) ∧
      φ.left ≫ RP.i.app g = RP.i.app f ≫ RP.Z.map φ ∧
      RP.Z.map φ ≫ RP.p.app g = RP.p.app f ≫ φ.right := by
  dsimp only
  exact ⟨rfl, (chosenOriginalCofibrationFactorization D).i.naturality φ,
    (chosenOriginalCofibrationFactorization D).p.naturality φ,
    rfl, (chosenOriginalTrivialCofibrationFactorization D).i.naturality φ,
    (chosenOriginalTrivialCofibrationFactorization D).p.naturality φ⟩

/-- Original Q is the pullback of the one native enriched-carrier cofibrant replacement. -/
def originalQ : SimplicialPresheaf.{u} D ⥤ SimplicialPresheaf.{u} D :=
  (enrichedCarrierEquivalence (D := D)).functor ⋙
    cofibrantReplacement (C := MappingCarrier.{u} D) ⋙
      (enrichedCarrierEquivalence (D := D)).inverse

/-- Original R is the pullback of the one native enriched-carrier fibrant replacement. -/
def originalR : SimplicialPresheaf.{u} D ⥤ SimplicialPresheaf.{u} D :=
  (enrichedCarrierEquivalence (D := D)).functor ⋙
    fibrantReplacement (C := MappingCarrier.{u} D) ⋙
      (enrichedCarrierEquivalence (D := D)).inverse

/-- The original natural Q counit uses the same native counit and actual inverse unit. -/
def originalQCounit : originalQ.{u} D ⟶ 𝟭 (SimplicialPresheaf.{u} D) :=
  CategoryTheory.Functor.whiskerRight (CategoryTheory.Functor.whiskerLeft
      (enrichedCarrierEquivalence (D := D)).functor
    (cofibrantReplacementCounit (C := MappingCarrier.{u} D)))
      (enrichedCarrierEquivalence (D := D)).inverse ≫
    (enrichedCarrierEquivalence (D := D)).unitIso.inv

/-- The original natural R unit uses the actual unit and the same native replacement unit. -/
def originalRUnit : 𝟭 (SimplicialPresheaf.{u} D) ⟶ originalR.{u} D :=
  (enrichedCarrierEquivalence (D := D)).unitIso.hom ≫
    CategoryTheory.Functor.whiskerRight (CategoryTheory.Functor.whiskerLeft
        (enrichedCarrierEquivalence (D := D)).functor
      (fibrantReplacementUnit (C := MappingCarrier.{u} D)))
        (enrichedCarrierEquivalence (D := D)).inverse

variable {D}

/-- The original counit retains the exact native replacement map and actual inverse unit. -/
theorem originalQCounit_app (A : SimplicialPresheaf.{u} D) :
    (originalQCounit D).app A =
      (enrichedCarrierEquivalence (D := D)).inverse.map
        ((cofibrantReplacementCounit (C := MappingCarrier.{u} D)).app
          ((enrichedCarrierEquivalence (D := D)).functor.obj A)) ≫
        (enrichedCarrierEquivalence (D := D)).unitIso.inv.app A := rfl

/-- The original unit retains the actual unit and exact native replacement map. -/
theorem originalRUnit_app (Z : SimplicialPresheaf.{u} D) :
    (originalRUnit D).app Z =
      (enrichedCarrierEquivalence (D := D)).unitIso.hom.app Z ≫
        (enrichedCarrierEquivalence (D := D)).inverse.map
          ((fibrantReplacementUnit (C := MappingCarrier.{u} D)).app
            ((enrichedCarrierEquivalence (D := D)).functor.obj Z)) := rfl

/-- The same original Q counit is an actual trivial fibration and hence weak. -/
theorem originalQCounit_trivialFibration (A : SimplicialPresheaf.{u} D) :
    trivialFibrations (SimplicialPresheaf.{u} D) ((originalQCounit D).app A) := by
  have h : trivialFibrations (MappingCarrier.{u} D)
      ((cofibrantReplacementCounit (C := MappingCarrier.{u} D)).app
        ((enrichedCarrierEquivalence (D := D)).functor.obj A)) := mem_trivialFibrations _
  change trivialFibrations (SimplicialPresheaf.{u} D)
    ((enrichedCarrierEquivalence (D := D)).inverse.map
      ((cofibrantReplacementCounit (C := MappingCarrier.{u} D)).app
        ((enrichedCarrierEquivalence (D := D)).functor.obj A))) at h
  rw [originalQCounit_app]
  exact (trivialFibrations (SimplicialPresheaf.{u} D)).comp_mem _ _ h
    ((trivialFibrations (SimplicialPresheaf.{u} D)).of_isIso _)

/-- The same original R unit is an actual trivial cofibration and hence weak. -/
theorem originalRUnit_trivialCofibration (Z : SimplicialPresheaf.{u} D) :
    trivialCofibrations (SimplicialPresheaf.{u} D) ((originalRUnit D).app Z) := by
  have h : trivialCofibrations (MappingCarrier.{u} D)
      ((fibrantReplacementUnit (C := MappingCarrier.{u} D)).app
        ((enrichedCarrierEquivalence (D := D)).functor.obj Z)) := mem_trivialCofibrations _
  change trivialCofibrations (SimplicialPresheaf.{u} D)
    ((enrichedCarrierEquivalence (D := D)).inverse.map
      ((fibrantReplacementUnit (C := MappingCarrier.{u} D)).app
        ((enrichedCarrierEquivalence (D := D)).functor.obj Z))) at h
  rw [originalRUnit_app]
  exact (trivialCofibrations (SimplicialPresheaf.{u} D)).comp_mem _ _
    ((trivialCofibrations (SimplicialPresheaf.{u} D)).of_isIso _) h

/-- Every original R image is fibrant in the actual named injective model. -/
theorem originalR_isFibrant (Z : SimplicialPresheaf.{u} D) :
    IsFibrant ((originalR D).obj Z) :=
  (mappingCarrier_fibrant_iff _).mp (inferInstance :
    IsFibrant ((fibrantReplacement (C := MappingCarrier.{u} D)).obj
      ((enrichedCarrierEquivalence (D := D)).functor.obj Z)))

/-- Both native replacement legs and their original factorization equations use the same choices.
The pulled initial and terminal objects are retained; they are not replaced judgmentally by
independently chosen original limits. -/
theorem originalReplacement_factorization (A Z : SimplicialPresheaf.{u} D) :
    let E := enrichedCarrierEquivalence (D := D)
    let i := E.inverse.map (initialToCofibrantReplacement (C := MappingCarrier.{u} D)
      (E.functor.obj A))
    let p := E.inverse.map (fibrantReplacementToTerminal (C := MappingCarrier.{u} D)
      (E.functor.obj Z))
    Nonempty (IsInitial (E.inverse.obj (⊥_ MappingCarrier.{u} D))) ∧
      Nonempty (IsTerminal (E.inverse.obj (⊤_ MappingCarrier.{u} D))) ∧
      cofibrations (SimplicialPresheaf.{u} D) i ∧
      fibrations (SimplicialPresheaf.{u} D) p ∧
      i ≫ (originalQCounit D).app A =
        E.inverse.map (initial.to (E.functor.obj A)) ≫ E.unitIso.inv.app A ∧
      (originalRUnit D).app Z ≫ p =
        E.unitIso.hom.app Z ≫ E.inverse.map (terminal.from (E.functor.obj Z)) := by
  dsimp only
  refine ⟨⟨initialIsInitial.isInitialObj (enrichedCarrierEquivalence (D := D)).inverse _⟩,
    ⟨terminalIsTerminal.isTerminalObj (enrichedCarrierEquivalence (D := D)).inverse _⟩,
    ?_, ?_, ?_, ?_⟩
  · change cofibrations (MappingCarrier.{u} D)
      (initialToCofibrantReplacement ((enrichedCarrierEquivalence (D := D)).functor.obj A))
    exact mem_cofibrations _
  · change fibrations (MappingCarrier.{u} D)
      (fibrantReplacementToTerminal ((enrichedCarrierEquivalence (D := D)).functor.obj Z))
    exact mem_fibrations _
  · rw [originalQCounit_app, ← Category.assoc, ← CategoryTheory.Functor.map_comp,
      cofibrantReplacement_fac]
  · let E := enrichedCarrierEquivalence (D := D)
    let z : MappingCarrier.{u} D := E.functor.obj Z
    let η : z ⟶ (fibrantReplacement (C := MappingCarrier.{u} D)).obj z :=
      (fibrantReplacementUnit (C := MappingCarrier.{u} D)).app z
    let p := fibrantReplacementToTerminal (C := MappingCarrier.{u} D) z
    have hm : E.inverse.map η ≫ E.inverse.map p = E.inverse.map (terminal.from z) :=
      (E.inverse.map_comp η p).symm.trans
        (congrArg E.inverse.map (fibrantReplacement_fac z))
    have hu : (originalRUnit D).app Z ≫ E.inverse.map p =
        (E.unitIso.hom.app Z ≫ E.inverse.map η) ≫ E.inverse.map p :=
      congrArg (fun (f : Z ⟶ (originalR D).obj Z) => f ≫ E.inverse.map p)
        (originalRUnit_app Z)
    exact hu.trans ((Category.assoc _ _ _).trans
      (congrArg (fun (f : E.inverse.obj z ⟶ E.inverse.obj (⊤_ MappingCarrier.{u} D)) =>
        E.unitIso.hom.app Z ≫ f) hm))

variable (D)

/-- Pull the one genuine native chosen-derived bifunctor back to original presheaves. -/
def originalDerivedMappingObject : (SimplicialPresheaf.{u} D)ᵒᵖ ⥤
    SimplicialPresheaf.{u} D ⥤ SSet.{u} :=
  (enrichedCarrierEquivalence (D := D)).functor.op ⋙
    derivedMappingObject (C := MappingCarrier.{u} D) ⋙
      (CategoryTheory.Functor.whiskeringLeft (SimplicialPresheaf.{u} D)
        (MappingCarrier.{u} D) SSet.{u}).obj
          (enrichedCarrierEquivalence (D := D)).functor

/-- The actual end with those very same original Q and R choices. -/
def originalDerivedEnd : (SimplicialPresheaf.{u} D)ᵒᵖ ⥤
    SimplicialPresheaf.{u} D ⥤ SSet.{u} :=
  (originalQ D).op ⋙ innerHomFunctor ⋙
    (CategoryTheory.Functor.whiskeringLeft (SimplicialPresheaf.{u} D)
      (SimplicialPresheaf.{u} D) SSet.{u}).obj (originalR D)

/-- Every original source map acts in the one native chosen-derived bifunctor. -/
def originalDerivedPrecomp {A B : SimplicialPresheaf.{u} D}
    (f : A ⟶ B) (Z : SimplicialPresheaf.{u} D) :
    ((originalDerivedMappingObject D).obj (op B)).obj Z ⟶
      ((originalDerivedMappingObject D).obj (op A)).obj Z :=
  ((originalDerivedMappingObject D).map f.op).app Z

/-- Every original target map acts in the one native chosen-derived bifunctor. -/
def originalDerivedPostcomp (A : SimplicialPresheaf.{u} D)
    {X Y : SimplicialPresheaf.{u} D} (g : X ⟶ Y) :
    ((originalDerivedMappingObject D).obj (op A)).obj X ⟶
      ((originalDerivedMappingObject D).obj (op A)).obj Y :=
  ((originalDerivedMappingObject D).obj (op A)).map g

/-- The actual chosen-derived maps retain both identities, both compositions and exchange. -/
theorem originalDerivedMapping_laws :
    (∀ A Z : SimplicialPresheaf.{u} D, originalDerivedPrecomp D (𝟙 A) Z = 𝟙 _) ∧
      (∀ {A B C : SimplicialPresheaf.{u} D} (f : A ⟶ B) (g : B ⟶ C)
        (Z : SimplicialPresheaf.{u} D), originalDerivedPrecomp D (f ≫ g) Z =
          originalDerivedPrecomp D g Z ≫ originalDerivedPrecomp D f Z) ∧
      (∀ A Z : SimplicialPresheaf.{u} D, originalDerivedPostcomp D A (𝟙 Z) = 𝟙 _) ∧
      (∀ (A : SimplicialPresheaf.{u} D) {X Y Z : SimplicialPresheaf.{u} D}
        (f : X ⟶ Y) (g : Y ⟶ Z), originalDerivedPostcomp D A (f ≫ g) =
          originalDerivedPostcomp D A f ≫ originalDerivedPostcomp D A g) ∧
      (∀ {A B X Y : SimplicialPresheaf.{u} D} (f : A ⟶ B) (g : X ⟶ Y),
        originalDerivedPrecomp D f X ≫ originalDerivedPostcomp D A g =
          originalDerivedPostcomp D B g ≫ originalDerivedPrecomp D f Y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro A Z
    simp [originalDerivedPrecomp]
  · intro A B C f g Z
    simp [originalDerivedPrecomp]
  · intro A Z
    simp [originalDerivedPostcomp]
  · intro A X Y Z f g
    simp [originalDerivedPostcomp]
  · intro A B X Y f g
    exact (((originalDerivedMappingObject D).map f.op).naturality g).symm

variable {D}

/-- Every chosen-derived source map is the end's actual Q-map into the same R target. -/
theorem originalDerivedPrecomp_eq {A B : SimplicialPresheaf.{u} D}
    (f : A ⟶ B) (Z : SimplicialPresheaf.{u} D) :
    originalDerivedPrecomp D f Z =
      innerHomPre ((originalQ D).map f) ((originalR D).obj Z) :=
  mappingCarrier_precomp
    ((cofibrantReplacement (C := MappingCarrier.{u} D)).map
      ((enrichedCarrierEquivalence (D := D)).functor.map f))
    ((fibrantReplacement (C := MappingCarrier.{u} D)).obj
      ((enrichedCarrierEquivalence (D := D)).functor.obj Z))

/-- Every chosen-derived target map is the end's actual R-map out of the same Q source. -/
theorem originalDerivedPostcomp_eq (A : SimplicialPresheaf.{u} D)
    {X Y : SimplicialPresheaf.{u} D} (g : X ⟶ Y) :
    originalDerivedPostcomp D A g =
      innerHomPost ((originalQ D).obj A) ((originalR D).map g) :=
  mappingCarrier_postcomp
    ((cofibrantReplacement (C := MappingCarrier.{u} D)).obj
      ((enrichedCarrierEquivalence (D := D)).functor.obj A))
    ((fibrantReplacement (C := MappingCarrier.{u} D)).map
      ((enrichedCarrierEquivalence (D := D)).functor.map g))

variable (D)

/-- The full native chosen-derived bifunctor is the end with precisely the pulled-back choices. -/
def originalDerivedEndIso : originalDerivedMappingObject.{u} D ≅ originalDerivedEnd D :=
  NatIso.ofComponents (fun A => NatIso.ofComponents (fun Z => Iso.refl _) (by
    intro X Y g
    change originalDerivedPostcomp D A.unop g ≫ 𝟙 _ =
      𝟙 _ ≫ innerHomPost ((originalQ D).obj A.unop) ((originalR D).map g)
    simpa only [Category.comp_id, Category.id_comp] using originalDerivedPostcomp_eq A.unop g))
    (by
      intro A B f
      ext Z : 2
      change originalDerivedPrecomp D f.unop Z ≫ 𝟙 _ =
        𝟙 _ ≫ innerHomPre ((originalQ D).map f.unop) ((originalR D).obj Z)
      simpa only [Category.comp_id, Category.id_comp] using originalDerivedPrecomp_eq f.unop Z)

private theorem original_carrier_map {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B) :
    (enrichedCarrierEquivalence (D := D)).inverse.map
      ((enrichedCarrierEquivalence (D := D)).functor.map f) = f :=
  Equiv.symm_apply_apply (eHomEquiv SSet.{u}) f

set_option backward.isDefEq.respectTransparency false in
private def originalRawCarrierIso : innerHomFunctor (D := D) ≅
    (enrichedCarrierEquivalence (D := D)).functor.op ⋙
      SimplicialCategory.sHomFunctor (MappingCarrier.{u} D) ⋙
        (CategoryTheory.Functor.whiskeringLeft (SimplicialPresheaf.{u} D)
          (MappingCarrier.{u} D) SSet.{u}).obj
            (enrichedCarrierEquivalence (D := D)).functor :=
  NatIso.ofComponents (fun A => NatIso.ofComponents (fun Z => Iso.refl _) (by
    intro X Y g
    change innerHomPost A.unop g ≫ 𝟙 (innerHom A.unop Y) =
      𝟙 (innerHom A.unop X) ≫ eHomWhiskerLeft SSet.{u}
        ((enrichedCarrierEquivalence (D := D)).functor.obj A.unop)
        ((enrichedCarrierEquivalence (D := D)).functor.map g)
    rw [mappingCarrier_postcomp, original_carrier_map]
    simp only [Category.comp_id, Category.id_comp]
    rfl)) (by
      intro A B f
      ext Z : 2
      change innerHomPre f.unop Z ≫ 𝟙 (innerHom B.unop Z) =
        𝟙 (innerHom A.unop Z) ≫ eHomWhiskerRight SSet.{u}
          ((enrichedCarrierEquivalence (D := D)).functor.map f.unop)
          ((enrichedCarrierEquivalence (D := D)).functor.obj Z)
      rw [mappingCarrier_precomp, original_carrier_map]
      simp only [Category.comp_id, Category.id_comp]
      rfl)

/-- The original two-variable comparison is the actual native strict-to-derived transformation. -/
def originalMappingComparison : innerHomFunctor (D := D) ⟶ originalDerivedMappingObject.{u} D :=
  (originalRawCarrierIso D).hom ≫
    CategoryTheory.Functor.whiskerLeft (enrichedCarrierEquivalence (D := D)).functor.op
      (CategoryTheory.Functor.whiskerRight
        (strictToDerivedMappingObject (C := MappingCarrier.{u} D))
        ((CategoryTheory.Functor.whiskeringLeft (SimplicialPresheaf.{u} D)
          (MappingCarrier.{u} D) SSet.{u}).obj
            (enrichedCarrierEquivalence (D := D)).functor))

/-- The first original θ factor is precomposition by the same Q counit. -/
def originalMappingSigma (A Z : SimplicialPresheaf.{u} D) :
    innerHom A Z ⟶ innerHom ((originalQ D).obj A) Z :=
  innerHomPre ((originalQCounit D).app A) Z

/-- The second original θ factor is postcomposition by the same R unit. -/
def originalMappingGamma (A Z : SimplicialPresheaf.{u} D) :
    innerHom ((originalQ D).obj A) Z ⟶
      innerHom ((originalQ D).obj A) ((originalR D).obj Z) :=
  innerHomPost ((originalQ D).obj A) ((originalRUnit D).app Z)

variable {D}

private theorem originalQCounit_normalized (A : SimplicialPresheaf.{u} D) :
    (originalQCounit D).app A = (enrichedCarrierEquivalence (D := D)).inverse.map
      ((cofibrantReplacementCounit (C := MappingCarrier.{u} D)).app
        ((enrichedCarrierEquivalence (D := D)).functor.obj A)) := by
  rw [originalQCounit_app]
  change _ ≫ 𝟙 A = _
  exact Category.comp_id _

private theorem originalRUnit_normalized (Z : SimplicialPresheaf.{u} D) :
    (originalRUnit D).app Z = (enrichedCarrierEquivalence (D := D)).inverse.map
      ((fibrantReplacementUnit (C := MappingCarrier.{u} D)).app
        ((enrichedCarrierEquivalence (D := D)).functor.obj Z)) := by
  rw [originalRUnit_app]
  change 𝟙 Z ≫ _ = _
  exact Category.id_comp _

/-- The original comparison's alternate factorization retains exactly q and η. -/
theorem originalMappingComparison_app (A Z : SimplicialPresheaf.{u} D) :
    ((originalMappingComparison D).app (op A)).app Z =
      innerHomPost A ((originalRUnit D).app Z) ≫
        innerHomPre ((originalQCounit D).app A) ((originalR D).obj Z) := by
  change 𝟙 (innerHom A Z) ≫
      (eHomWhiskerLeft SSet.{u} ((enrichedCarrierEquivalence (D := D)).functor.obj A)
          ((fibrantReplacementUnit (C := MappingCarrier.{u} D)).app
            ((enrichedCarrierEquivalence (D := D)).functor.obj Z)) ≫
        eHomWhiskerRight SSet.{u}
          ((cofibrantReplacementCounit (C := MappingCarrier.{u} D)).app
            ((enrichedCarrierEquivalence (D := D)).functor.obj A))
          ((fibrantReplacement (C := MappingCarrier.{u} D)).obj
            ((enrichedCarrierEquivalence (D := D)).functor.obj Z))) = _
  rw [Category.id_comp, originalRUnit_normalized, originalQCounit_normalized]
  exact congrArg₂
    (fun (p : innerHom A Z ⟶ innerHom A ((originalR D).obj Z))
      (q : innerHom A ((originalR D).obj Z) ⟶
        innerHom ((originalQ D).obj A) ((originalR D).obj Z)) => p ≫ q)
    (mappingCarrier_postcomp
      ((enrichedCarrierEquivalence (D := D)).functor.obj A)
      ((fibrantReplacementUnit (C := MappingCarrier.{u} D)).app
        ((enrichedCarrierEquivalence (D := D)).functor.obj Z)))
    (mappingCarrier_precomp
      ((cofibrantReplacementCounit (C := MappingCarrier.{u} D)).app
        ((enrichedCarrierEquivalence (D := D)).functor.obj A))
      ((fibrantReplacement (C := MappingCarrier.{u} D)).obj
        ((enrichedCarrierEquivalence (D := D)).functor.obj Z)))

/-- The same original comparison is σ followed by γ, with both factors visible. -/
theorem originalMappingComparison_factors (A Z : SimplicialPresheaf.{u} D) :
    ((originalMappingComparison D).app (op A)).app Z =
      originalMappingSigma D A Z ≫ originalMappingGamma D A Z := by
  rw [originalMappingComparison_app]
  exact (innerHom_exchange ((originalQCounit D).app A) ((originalRUnit D).app Z)).symm

/-- Original θ source naturality applies to every original natural transformation. -/
theorem originalMappingComparison_source {A B : SimplicialPresheaf.{u} D}
    (f : A ⟶ B) (Z : SimplicialPresheaf.{u} D) :
    innerHomPre f Z ≫ ((originalMappingComparison D).app (op A)).app Z =
      ((originalMappingComparison D).app (op B)).app Z ≫ originalDerivedPrecomp D f Z :=
  NatTrans.congr_app ((originalMappingComparison D).naturality f.op) Z

/-- Original θ target naturality applies to every original natural transformation. -/
theorem originalMappingComparison_target (A : SimplicialPresheaf.{u} D)
    {X Y : SimplicialPresheaf.{u} D} (g : X ⟶ Y) :
    innerHomPost A g ≫ ((originalMappingComparison D).app (op A)).app Y =
      ((originalMappingComparison D).app (op A)).app X ≫ originalDerivedPostcomp D A g :=
  ((originalMappingComparison D).app (op A)).naturality g

/-- Both original replacement maps remain natural, with no fibrancy restriction. -/
theorem originalReplacement_naturality {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B) :
    (originalQ D).map f ≫ (originalQCounit D).app B =
        (originalQCounit D).app A ≫ f ∧
      f ≫ (originalRUnit D).app B = (originalRUnit D).app A ≫ (originalR D).map f :=
  ⟨(originalQCounit D).naturality f, (originalRUnit D).naturality f⟩

/-- The intermediate σ comparison preserves the entire original source square. -/
theorem originalMappingSigma_source {A B : SimplicialPresheaf.{u} D}
    (f : A ⟶ B) (Z : SimplicialPresheaf.{u} D) :
    innerHomPre f Z ≫ originalMappingSigma D A Z =
      originalMappingSigma D B Z ≫ innerHomPre ((originalQ D).map f) Z := by
  dsimp only [originalMappingSigma]
  rw [innerHomPre_comp, innerHomPre_comp, (originalReplacement_naturality f).1]

/-- The intermediate γ comparison preserves the entire original source square. -/
theorem originalMappingGamma_source {A B : SimplicialPresheaf.{u} D}
    (f : A ⟶ B) (Z : SimplicialPresheaf.{u} D) :
    innerHomPre ((originalQ D).map f) Z ≫ originalMappingGamma D A Z =
      originalMappingGamma D B Z ≫ originalDerivedPrecomp D f Z := by
  rw [originalDerivedPrecomp_eq]
  exact innerHom_exchange ((originalQ D).map f) ((originalRUnit D).app Z)

/-- The intermediate σ comparison retains the original target square. -/
theorem originalMappingSigma_target (A : SimplicialPresheaf.{u} D)
    {X Y : SimplicialPresheaf.{u} D} (g : X ⟶ Y) :
    innerHomPost A g ≫ originalMappingSigma D A Y =
      originalMappingSigma D A X ≫ innerHomPost ((originalQ D).obj A) g :=
  (innerHom_exchange ((originalQCounit D).app A) g).symm

/-- The intermediate γ comparison retains the original R-unit target square. -/
theorem originalMappingGamma_target (A : SimplicialPresheaf.{u} D)
    {X Y : SimplicialPresheaf.{u} D} (g : X ⟶ Y) :
    innerHomPost ((originalQ D).obj A) g ≫ originalMappingGamma D A Y =
      originalMappingGamma D A X ≫ originalDerivedPostcomp D A g := by
  rw [originalDerivedPostcomp_eq]
  change innerHomPost ((originalQ D).obj A) g ≫
      innerHomPost ((originalQ D).obj A) ((originalRUnit D).app Y) =
    innerHomPost ((originalQ D).obj A) ((originalRUnit D).app X) ≫
      innerHomPost ((originalQ D).obj A) ((originalR D).map g)
  rw [innerHomPost_comp, innerHomPost_comp, (originalReplacement_naturality g).2]

/-- Both actual θ endpoint factors are weak at any original fibrant target. -/
theorem originalMappingFactors_weak (A Z : SimplicialPresheaf.{u} D) (hZ : IsFibrant Z) :
    SSet.realizationWeakEquivalences (originalMappingSigma D A Z) ∧
      SSet.realizationWeakEquivalences (originalMappingGamma D A Z) := by
  exact ⟨innerHomPre_weak_of_weakEquivalence ((originalQCounit D).app A) Z
      (originalQCounit_trivialFibration A).2 hZ,
    innerHomPost_weak_of_weakEquivalence ((originalQ D).obj A) ((originalRUnit D).app Z)
      (originalRUnit_trivialCofibration Z).2 hZ (originalR_isFibrant Z)⟩

/-- The original θ component is weak at every original source and fibrant target. -/
theorem originalMappingComparison_weak (A Z : SimplicialPresheaf.{u} D) (hZ : IsFibrant Z) :
    SSet.realizationWeakEquivalences (((originalMappingComparison D).app (op A)).app Z) := by
  rw [originalMappingComparison_factors]
  exact SSet.realizationWeakEquivalences.comp_mem _ _
    (originalMappingFactors_weak A Z hZ).1 (originalMappingFactors_weak A Z hZ).2

/-- The σ square compares Qf with every original f, including arbitrary nonmonic arrows. -/
theorem originalQPrecomp_weak_iff {A B : SimplicialPresheaf.{u} D}
    (f : A ⟶ B) (Z : SimplicialPresheaf.{u} D) (hZ : IsFibrant Z) :
    SSet.realizationWeakEquivalences (innerHomPre ((originalQ D).map f) Z) ↔
      SSet.realizationWeakEquivalences (innerHomPre f Z) := by
  have hA := (originalMappingFactors_weak A Z hZ).1
  have hB := (originalMappingFactors_weak B Z hZ).1
  have hleft := SSet.realizationWeakEquivalences.postcomp_iff
    (innerHomPre f Z) (originalMappingSigma D A Z) hA
  have hright := SSet.realizationWeakEquivalences.precomp_iff
    (originalMappingSigma D B Z) (innerHomPre ((originalQ D).map f) Z) hB
  rw [originalMappingSigma_source f Z] at hleft
  exact hright.symm.trans hleft

/-- The γ square compares the chosen-derived map with the raw Qf map without a condition on f. -/
theorem originalDerivedPrecomp_weak_iff_Q {A B : SimplicialPresheaf.{u} D}
    (f : A ⟶ B) (Z : SimplicialPresheaf.{u} D) (hZ : IsFibrant Z) :
    SSet.realizationWeakEquivalences (originalDerivedPrecomp D f Z) ↔
      SSet.realizationWeakEquivalences (innerHomPre ((originalQ D).map f) Z) := by
  have hA := (originalMappingFactors_weak A Z hZ).2
  have hB := (originalMappingFactors_weak B Z hZ).2
  have hleft := SSet.realizationWeakEquivalences.postcomp_iff
    (innerHomPre ((originalQ D).map f) Z) (originalMappingGamma D A Z) hA
  have hright := SSet.realizationWeakEquivalences.precomp_iff
    (originalMappingGamma D B Z) (originalDerivedPrecomp D f Z) hB
  rw [originalMappingGamma_source f Z] at hleft
  exact hright.symm.trans hleft

/-- The actual chosen-derived and raw maps are weak together for every original arrow. -/
theorem originalDerivedPrecomp_weak_iff {A B : SimplicialPresheaf.{u} D}
    (f : A ⟶ B) (Z : SimplicialPresheaf.{u} D) (hZ : IsFibrant Z) :
    SSet.realizationWeakEquivalences (originalDerivedPrecomp D f Z) ↔
      SSet.realizationWeakEquivalences (innerHomPre f Z) :=
  (originalDerivedPrecomp_weak_iff_Q f Z hZ).trans (originalQPrecomp_weak_iff f Z hZ)

/-- Original Q preserves weak arrows by the actual weak counit's naturality square. -/
theorem originalQ_map_weak {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B)
    (hf : weakEquivalences (SimplicialPresheaf.{u} D) f) :
    weakEquivalences (SimplicialPresheaf.{u} D) ((originalQ D).map f) := by
  apply (weakEquivalences (SimplicialPresheaf.{u} D)).of_postcomp
    ((originalQ D).map f) ((originalQCounit D).app B)
    (originalQCounit_trivialFibration B).2
  rw [(originalReplacement_naturality f).1]
  exact (weakEquivalences (SimplicialPresheaf.{u} D)).comp_mem _ _
    (originalQCounit_trivialFibration A).2 hf

/-- Original R preserves weak arrows by the actual weak unit's naturality square. -/
theorem originalR_map_weak {X Y : SimplicialPresheaf.{u} D} (g : X ⟶ Y)
    (hg : weakEquivalences (SimplicialPresheaf.{u} D) g) :
    weakEquivalences (SimplicialPresheaf.{u} D) ((originalR D).map g) := by
  apply (weakEquivalences (SimplicialPresheaf.{u} D)).of_precomp
    ((originalRUnit D).app X) ((originalR D).map g)
    (originalRUnit_trivialCofibration X).2
  rw [← (originalReplacement_naturality g).2]
  exact (weakEquivalences (SimplicialPresheaf.{u} D)).comp_mem _ _ hg
    (originalRUnit_trivialCofibration Y).2

/-- Chosen-derived precomposition carries every original weak arrow to a weak map at all targets. -/
theorem originalDerivedPrecomp_weak_of_weak {A B : SimplicialPresheaf.{u} D}
    (f : A ⟶ B) (Z : SimplicialPresheaf.{u} D)
    (hf : weakEquivalences (SimplicialPresheaf.{u} D) f) :
    SSet.realizationWeakEquivalences (originalDerivedPrecomp D f Z) := by
  rw [originalDerivedPrecomp_eq]
  exact innerHomPre_weak_of_weakEquivalence ((originalQ D).map f) ((originalR D).obj Z)
    (originalQ_map_weak f hf) (originalR_isFibrant Z)

/-- Chosen-derived postcomposition carries every original weak arrow to a weak map at all
targets. -/
theorem originalDerivedPostcomp_weak_of_weak (A : SimplicialPresheaf.{u} D)
    {X Y : SimplicialPresheaf.{u} D} (g : X ⟶ Y)
    (hg : weakEquivalences (SimplicialPresheaf.{u} D) g) :
    SSet.realizationWeakEquivalences (originalDerivedPostcomp D A g) := by
  rw [originalDerivedPostcomp_eq]
  exact innerHomPost_weak_of_weakEquivalence ((originalQ D).obj A) ((originalR D).map g)
    (originalR_map_weak g hg) (originalR_isFibrant X) (originalR_isFibrant Y)

/-- The complete original comparison and both all-arrow weak-invariance clauses, from I_D alone. -/
theorem originalChosenDerivedMappingComparison (D : Type w) [Category.{v} D]
    [Small.{u} D] [LocallySmall.{u} D] :
    (∀ A Z : SimplicialPresheaf.{u} D,
      trivialFibrations (SimplicialPresheaf.{u} D) ((originalQCounit D).app A) ∧
        trivialCofibrations (SimplicialPresheaf.{u} D) ((originalRUnit D).app Z) ∧
        IsFibrant ((originalR D).obj Z)) ∧
      (∀ A Z : SimplicialPresheaf.{u} D,
        ((originalMappingComparison D).app (op A)).app Z =
            originalMappingSigma D A Z ≫ originalMappingGamma D A Z ∧
          ((originalMappingComparison D).app (op A)).app Z =
            innerHomPost A ((originalRUnit D).app Z) ≫
              innerHomPre ((originalQCounit D).app A) ((originalR D).obj Z)) ∧
      (∀ {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B) (Z : SimplicialPresheaf.{u} D),
        innerHomPre f Z ≫ ((originalMappingComparison D).app (op A)).app Z =
          ((originalMappingComparison D).app (op B)).app Z ≫ originalDerivedPrecomp D f Z) ∧
      (∀ (A : SimplicialPresheaf.{u} D) {X Y : SimplicialPresheaf.{u} D} (g : X ⟶ Y),
        innerHomPost A g ≫ ((originalMappingComparison D).app (op A)).app Y =
          ((originalMappingComparison D).app (op A)).app X ≫ originalDerivedPostcomp D A g) ∧
      (∀ A Z : SimplicialPresheaf.{u} D, IsFibrant Z →
        SSet.realizationWeakEquivalences (originalMappingSigma D A Z) ∧
          SSet.realizationWeakEquivalences (originalMappingGamma D A Z) ∧
          SSet.realizationWeakEquivalences (((originalMappingComparison D).app (op A)).app Z)) ∧
      (∀ {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B) (Z : SimplicialPresheaf.{u} D),
        IsFibrant Z →
          (SSet.realizationWeakEquivalences (originalDerivedPrecomp D f Z) ↔
            SSet.realizationWeakEquivalences (innerHomPre ((originalQ D).map f) Z)) ∧
          (SSet.realizationWeakEquivalences (innerHomPre ((originalQ D).map f) Z) ↔
            SSet.realizationWeakEquivalences (innerHomPre f Z))) ∧
      (∀ {A B : SimplicialPresheaf.{u} D} (f : A ⟶ B) (Z : SimplicialPresheaf.{u} D),
        weakEquivalences (SimplicialPresheaf.{u} D) f →
          SSet.realizationWeakEquivalences (originalDerivedPrecomp D f Z)) ∧
      (∀ (A : SimplicialPresheaf.{u} D) {X Y : SimplicialPresheaf.{u} D} (g : X ⟶ Y),
        weakEquivalences (SimplicialPresheaf.{u} D) g →
          SSet.realizationWeakEquivalences (originalDerivedPostcomp D A g)) := by
  refine ⟨?_, ?_, originalMappingComparison_source, originalMappingComparison_target,
    ?_, ?_, originalDerivedPrecomp_weak_of_weak, originalDerivedPostcomp_weak_of_weak⟩
  · intro A Z
    exact ⟨originalQCounit_trivialFibration A, originalRUnit_trivialCofibration Z,
      originalR_isFibrant Z⟩
  · intro A Z
    exact ⟨originalMappingComparison_factors A Z, originalMappingComparison_app A Z⟩
  · intro A Z hZ
    exact ⟨(originalMappingFactors_weak A Z hZ).1, (originalMappingFactors_weak A Z hZ).2,
      originalMappingComparison_weak A Z hZ⟩
  · intro A B f Z hZ
    exact ⟨originalDerivedPrecomp_weak_iff_Q f Z hZ, originalQPrecomp_weak_iff f Z hZ⟩

end SimplicialPresheaf.InjectiveKan
