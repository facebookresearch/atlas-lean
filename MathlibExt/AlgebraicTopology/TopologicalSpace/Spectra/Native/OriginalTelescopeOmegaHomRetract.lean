/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.EnrichedProjectiveNative.CoaugmentationTelescopeGroups
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.MMSSStabilization.OmegaUnit
import MathlibExt.CategoryTheory.Functor.CoaugmentedLocalization
import MathlibExt.CategoryTheory.Functor.CoaugmentedTestRetract
import MathlibExt.CategoryTheory.Functor.CoaugmentationHomEquivalence

/-!
# The original native telescope in level Ho and its Omega-target Hom retract

The actual original input-coaugmentation telescope preserves level weak
maps by the all-point homotopy-colimit proof. Its complete functor and its
stage-zero unit descend to the original level homotopy category. Every
native map, weak inverse, stage leg and source naturality is retained.

At an actual Omega target the original shifted-loop coaugmentation is
level weak. Hence its actual telescope unit is level weak at that target.
Only this target unit is inverted in the full Hom retraction. Neither
source unit is assumed invertible and no arbitrary telescope is declared
Omega. Both source and Omega-target naturalities hold for every original
level-Ho morphism.

Consequently a native map whose actual telescope map is level weak passes
all original Omega Hom tests, with the explicit inverse precomposition
function. The separate unrestricted integer-pi-to-telescope-level-weak
calculation is still needed for the unrestricted detector.
-/

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory CategoryTheory.Limits CategoryTheory.EnrichedFunctorCat HomotopicalAlgebra
open scoped CGWH.modelCategory MonoidalClosed

namespace PointedCGWH.Spectra.OriginalTelescopeOmegaHomRetract

universe uC vC

private theorem inverse_eq_of_original_iso
    {C : Type uC} [Category.{vC} C] {X Y : C} (f : X ⟶ Y) [IsIso f]
    (e : X ≅ Y) (h : f = e.hom) : CategoryTheory.inv f = e.inv := by
  apply IsIso.inv_eq_of_hom_inv_id
  exact (congrArg (fun k => k ≫ e.inv) h).trans e.hom_inv_id


open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK
open CategoryTheory.Functor.CoaugmentedLocalization
open CategoryTheory.Functor.CoaugmentedTestRetract

attribute [local instance] MonoidalClosed.enrichedCategorySelf
  PointedCGWH.EnrichedMapping.hasSmallLimits

variable {I : Type} [EnrichedCategory PointedCGWH.{u, v} I]
  [B : OrderBot realizedGeneratorCardinal.{v}.ord.ToType]

attribute [local instance] HomotopicalAlgebra.EnrichedProjective.Native.modelCategory

/-- The complete original native enriched carrier. -/
abbrev Carrier := EnrichedFunctorCat PointedCGWH.{u, v} I

section General

variable {F : Carrier (I := I) ⥤ Carrier (I := I)} (η : 𝟭 (Carrier (I := I)) ⟶ F)

/-- This is the actual original mapping-cylinder homotopy-colimit functor. -/
abbrev originalTelescope : Carrier (I := I) ⥤ Carrier (I := I) :=
  EnrichedCoaugmentationTelescope.telescopeFunctor η

/-- Its entire original coaugmentation is the chosen stage-zero colimit leg. -/
abbrev originalUnit : 𝟭 (Carrier (I := I)) ⟶ originalTelescope η :=
  EnrichedCoaugmentationTelescope.unit η

/-- Actual all-point homotopy-colimit comparison proves preservation of every level weak map. -/
theorem originalTelescope_preservesWeak
    (hF : ∀ ⦃A X : Carrier (I := I)⦄ (f : A ⟶ X),
      weakEquivalences (Carrier (I := I)) f → weakEquivalences (Carrier (I := I)) (F.map f))
    {X Y : Carrier (I := I)} (f : X ⟶ Y)
    (hf : weakEquivalences (Carrier (I := I)) f) :
    weakEquivalences (Carrier (I := I)) ((originalTelescope η).map f) :=
  PointedCGWH.EnrichedCoaugmentationTelescope.telescopeFunctor_map_mem_weak_of_preserves
    η (fun {A X} f hf => hF (A := A) (X := X) f hf) f hf

variable (hF : ∀ ⦃A X : Carrier (I := I)⦄ (f : A ⟶ X),
  weakEquivalences (Carrier (I := I)) f → weakEquivalences (Carrier (I := I)) (F.map f))

include hF in
/-- The actual original telescope descends on every original level-Ho object and map. -/
def originalTelescopeHo : HomotopyCategory (Carrier (I := I)) ⥤
    HomotopyCategory (Carrier (I := I)) :=
  localizedFunctor (weakEquivalences (Carrier (I := I))) (originalTelescope η)
    (fun {X Y} f hf => originalTelescope_preservesWeak η hF (X := X) (Y := Y) f hf)

include hF in
/-- Every projected original object remains the actual original telescope object. -/
theorem originalTelescopeHo_obj (X : Carrier (I := I)) :
    (originalTelescopeHo η hF).obj ((toHomotopyCategory (Carrier (I := I))).obj X) =
      (toHomotopyCategory (Carrier (I := I))).obj ((originalTelescope η).obj X) := rfl

include hF in
/-- Every projected original map remains the original actual telescope map. -/
theorem originalTelescopeHo_map {X Y : Carrier (I := I)} (f : X ⟶ Y) :
    (originalTelescopeHo η hF).map ((toHomotopyCategory (Carrier (I := I))).map f) =
      (toHomotopyCategory (Carrier (I := I))).map ((originalTelescope η).map f) :=
  localizedFunctor_map (weakEquivalences (Carrier (I := I))) (originalTelescope η)
    (fun {X Y} f hf => originalTelescope_preservesWeak η hF (X := X) (Y := Y) f hf) f

include hF in
/-- The entire projected original telescope functor is the same complete composite. -/
theorem originalTelescopeHo_factorization :
    toHomotopyCategory (Carrier (I := I)) ⋙ originalTelescopeHo η hF =
      originalTelescope η ⋙ toHomotopyCategory (Carrier (I := I)) :=
  Localization.Construction.fac _
    (inverts (weakEquivalences (Carrier (I := I))) (originalTelescope η)
      (fun {X Y} f hf => originalTelescope_preservesWeak η hF (X := X) (Y := Y) f hf))

include hF in
/-- Both original natural comparison directions come from that entire functor equality. -/
def originalTelescopeHoComparison :
    toHomotopyCategory (Carrier (I := I)) ⋙ originalTelescopeHo η hF ≅
      originalTelescope η ⋙ toHomotopyCategory (Carrier (I := I)) :=
  eqToIso (originalTelescopeHo_factorization η hF)

include hF in
/-- The complete forward comparison at each original input is the canonical identity. -/
theorem originalTelescopeHoComparison_hom (X : Carrier (I := I)) :
    (originalTelescopeHoComparison η hF).hom.app X =
      𝟙 ((originalTelescopeHo η hF).obj ((toHomotopyCategory (Carrier (I := I))).obj X)) := rfl

include hF in
/-- The inverse comparison retains that same original identity on the actual telescope. -/
theorem originalTelescopeHoComparison_inv (X : Carrier (I := I)) :
    (originalTelescopeHoComparison η hF).inv.app X =
      𝟙 ((originalTelescopeHo η hF).obj ((toHomotopyCategory (Carrier (I := I))).obj X)) := rfl

include hF in
/-- The actual original stage-zero unit descends on all original level-Ho morphisms. -/
def originalUnitHo : 𝟭 (HomotopyCategory (Carrier (I := I))) ⟶ originalTelescopeHo η hF :=
  localizedUnit (weakEquivalences (Carrier (I := I))) (originalTelescope η) (originalUnit η)
    (fun {X Y} f hf => originalTelescope_preservesWeak η hF (X := X) (Y := Y) f hf)

include hF in
/-- Its complete projected component is literally the original stage-zero unit map. -/
theorem originalUnitHo_app (X : Carrier (I := I)) :
    (originalUnitHo η hF).app ((toHomotopyCategory (Carrier (I := I))).obj X) =
      (toHomotopyCategory (Carrier (I := I))).map ((originalUnit η).app X) :=
  localizedUnit_app (weakEquivalences (Carrier (I := I))) (originalTelescope η)
    (originalUnit η) (fun {X Y} f hf => originalTelescope_preservesWeak η hF (X := X) (Y := Y) f hf) X

include hF in
/-- Every original level-Ho source arrow keeps the full actual unit naturality square. -/
theorem originalUnitHo_naturality
    {X Y : HomotopyCategory (Carrier (I := I))} (f : X ⟶ Y) :
    f ≫ (originalUnitHo η hF).app Y =
      (originalUnitHo η hF).app X ≫ (originalTelescopeHo η hF).map f :=
  (originalUnitHo η hF).naturality f

include hF in
/-- Original weak arrows keep their actual inverse under the descended telescope. -/
theorem originalTelescopeHo_map_inverse {X Y : Carrier (I := I)} (f : X ⟶ Y)
    (hf : weakEquivalences (Carrier (I := I)) f) :
    (originalTelescopeHo η hF).map
        (Localization.Construction.wIso f hf).inv =
      (Localization.Construction.wIso ((originalTelescope η).map f)
        (originalTelescope_preservesWeak η hF f hf)).inv := by
  let e := Localization.Construction.wIso f hf
  let t := Localization.Construction.wIso ((originalTelescope η).map f)
    (originalTelescope_preservesWeak η hF f hf)
  have hIso : (originalTelescopeHo η hF).mapIso e = t := by
    apply Iso.ext
    exact originalTelescopeHo_map η hF f
  exact congrArg Iso.inv hIso

include hF in
/-- The actual unit is weak when the original input coaugmentation is weak at this object. -/
theorem originalUnit_weak (E : Carrier (I := I))
    (hηE : weakEquivalences (Carrier (I := I)) (η.app E)) :
    weakEquivalences (Carrier (I := I)) ((originalUnit η).app E) :=
  EnrichedCoaugmentationTelescope.unit_mem_weak_of_preserves η
    (fun {A X} f hf => hF (A := A) (X := X) f hf) E hηE

include hF in
/-- The exact original weak unit supplies both original localization-Iso maps. -/
def originalTargetUnitIso (E : Carrier (I := I))
    (hηE : weakEquivalences (Carrier (I := I)) (η.app E)) :
    (toHomotopyCategory (Carrier (I := I))).obj E ≅
      (originalTelescopeHo η hF).obj ((toHomotopyCategory (Carrier (I := I))).obj E) :=
  Localization.Construction.wIso ((originalUnit η).app E) (originalUnit_weak η hF E hηE)

include hF in
/-- The complete target-unit hom is the actual projected original stage-zero map. -/
theorem originalTargetUnitIso_hom (E : Carrier (I := I))
    (hηE : weakEquivalences (Carrier (I := I)) (η.app E)) :
    (originalTargetUnitIso η hF E hηE).hom =
      (toHomotopyCategory (Carrier (I := I))).map ((originalUnit η).app E) := rfl

include hF in
/-- The descended target unit is exactly that same weak-unit Iso hom. -/
theorem originalTargetUnitIso_unit (E : Carrier (I := I))
    (hηE : weakEquivalences (Carrier (I := I)) (η.app E)) :
    (originalUnitHo η hF).app ((toHomotopyCategory (Carrier (I := I))).obj E) =
      (originalTargetUnitIso η hF E hηE).hom := originalUnitHo_app η hF E

include hF in
/-- Both target-unit inverse equations keep the actual descended target map. -/
theorem originalTargetUnitIso_inverse_laws (E : Carrier (I := I))
    (hηE : weakEquivalences (Carrier (I := I)) (η.app E)) :
    (originalUnitHo η hF).app ((toHomotopyCategory (Carrier (I := I))).obj E) ≫
        (originalTargetUnitIso η hF E hηE).inv = 𝟙 _ ∧
      (originalTargetUnitIso η hF E hηE).inv ≫
        (originalUnitHo η hF).app ((toHomotopyCategory (Carrier (I := I))).obj E) = 𝟙 _ := by
  rw [originalTargetUnitIso_unit η hF E hηE]
  exact ⟨(originalTargetUnitIso η hF E hηE).hom_inv_id,
    (originalTargetUnitIso η hF E hηE).inv_hom_id⟩

include hF in
private theorem originalTargetUnitIsIso (E : Carrier (I := I))
    (hηE : weakEquivalences (Carrier (I := I)) (η.app E)) :
    IsIso ((originalUnitHo η hF).app ((toHomotopyCategory (Carrier (I := I))).obj E)) := by
  rw [originalTargetUnitIso_unit η hF E hηE]
  exact (originalTargetUnitIso η hF E hηE).isIso_hom

include hF in
/-- The full original Hom retraction keeps the source unit and only inverts the target unit. -/
def originalHomRetraction (X E : Carrier (I := I))
    (hηE : weakEquivalences (Carrier (I := I)) (η.app E))
    (g : (originalTelescopeHo η hF).obj ((toHomotopyCategory (Carrier (I := I))).obj X) ⟶
      (originalTelescopeHo η hF).obj ((toHomotopyCategory (Carrier (I := I))).obj E)) :
    (toHomotopyCategory (Carrier (I := I))).obj X ⟶
      (toHomotopyCategory (Carrier (I := I))).obj E := by
  letI := originalTargetUnitIsIso η hF E hηE
  exact Functor.CoaugmentedTestRetract.homRetraction (originalTelescopeHo η hF) (originalUnitHo η hF)
    ((toHomotopyCategory (Carrier (I := I))).obj X) ((toHomotopyCategory (Carrier (I := I))).obj E) g

include hF in
/-- Both original source and target maps are retained by the complete retraction formula. -/
theorem originalHomRetraction_formula (X E : Carrier (I := I))
    (hηE : weakEquivalences (Carrier (I := I)) (η.app E))
    (g : (originalTelescopeHo η hF).obj ((toHomotopyCategory (Carrier (I := I))).obj X) ⟶
      (originalTelescopeHo η hF).obj ((toHomotopyCategory (Carrier (I := I))).obj E)) :
    originalHomRetraction η hF X E hηE g =
      (toHomotopyCategory (Carrier (I := I))).map ((originalUnit η).app X) ≫
        g ≫ (originalTargetUnitIso η hF E hηE).inv := by
  let := originalTargetUnitIsIso η hF E hηE
  change (originalUnitHo η hF).app ((toHomotopyCategory (Carrier (I := I))).obj X) ≫ g ≫
    CategoryTheory.inv ((originalUnitHo η hF).app ((toHomotopyCategory (Carrier (I := I))).obj E)) = _
  have hInv : CategoryTheory.inv
      ((originalUnitHo η hF).app ((toHomotopyCategory (Carrier (I := I))).obj E)) =
      (originalTargetUnitIso η hF E hηE).inv :=
    inverse_eq_of_original_iso _ (originalTargetUnitIso η hF E hηE)
      (originalTargetUnitIso_unit η hF E hηE)
  rw [hInv, originalUnitHo_app η hF X]
  rfl

include hF in
/-- The actual full telescope Hom map has its original target-specific Hom retraction. -/
theorem originalHomRetraction_map (X E : Carrier (I := I))
    (hηE : weakEquivalences (Carrier (I := I)) (η.app E))
    (g : (toHomotopyCategory (Carrier (I := I))).obj X ⟶
      (toHomotopyCategory (Carrier (I := I))).obj E) :
    originalHomRetraction η hF X E hηE ((originalTelescopeHo η hF).map g) = g := by
  let := originalTargetUnitIsIso η hF E hηE
  exact Functor.CoaugmentedTestRetract.homRetraction_map (originalTelescopeHo η hF) (originalUnitHo η hF)
    ((toHomotopyCategory (Carrier (I := I))).obj X) ((toHomotopyCategory (Carrier (I := I))).obj E) g

include hF in
/-- All original level-Ho source arrows commute with the whole retraction, in both families. -/
theorem originalHomRetraction_source {X Y E : Carrier (I := I)}
    (hηE : weakEquivalences (Carrier (I := I)) (η.app E))
    (f : (toHomotopyCategory (Carrier (I := I))).obj X ⟶
      (toHomotopyCategory (Carrier (I := I))).obj Y)
    (g : (originalTelescopeHo η hF).obj ((toHomotopyCategory (Carrier (I := I))).obj Y) ⟶
      (originalTelescopeHo η hF).obj ((toHomotopyCategory (Carrier (I := I))).obj E)) :
    originalHomRetraction η hF X E hηE ((originalTelescopeHo η hF).map f ≫ g) =
      f ≫ originalHomRetraction η hF Y E hηE g := by
  let := originalTargetUnitIsIso η hF E hηE
  exact Functor.CoaugmentedTestRetract.homRetraction_source (originalTelescopeHo η hF) (originalUnitHo η hF) f g

include hF in
/-- Every original map between targets with weak coaugmentation preserves the inverse units. -/
theorem originalTargetUnitIso_naturality {E E' : Carrier (I := I)}
    (hηE : weakEquivalences (Carrier (I := I)) (η.app E))
    (hηE' : weakEquivalences (Carrier (I := I)) (η.app E'))
    (p : (toHomotopyCategory (Carrier (I := I))).obj E ⟶
      (toHomotopyCategory (Carrier (I := I))).obj E') :
    (originalTelescopeHo η hF).map p ≫ (originalTargetUnitIso η hF E' hηE').inv =
      (originalTargetUnitIso η hF E hηE).inv ≫ p := by
  let := originalTargetUnitIsIso η hF E hηE
  let := originalTargetUnitIsIso η hF E' hηE'
  have h := Functor.CoaugmentedTestRetract.homRetraction_target (originalTelescopeHo η hF) (originalUnitHo η hF)
    ((toHomotopyCategory (Carrier (I := I))).obj E) p (𝟙 _)
  apply (cancel_epi ((originalUnitHo η hF).app ((toHomotopyCategory (Carrier (I := I))).obj E))).mp
  have hInv : CategoryTheory.inv
      ((originalUnitHo η hF).app ((toHomotopyCategory (Carrier (I := I))).obj E)) =
      (originalTargetUnitIso η hF E hηE).inv :=
    inverse_eq_of_original_iso _ (originalTargetUnitIso η hF E hηE)
      (originalTargetUnitIso_unit η hF E hηE)
  have hInv' : CategoryTheory.inv
      ((originalUnitHo η hF).app ((toHomotopyCategory (Carrier (I := I))).obj E')) =
      (originalTargetUnitIso η hF E' hηE').inv :=
    inverse_eq_of_original_iso _ (originalTargetUnitIso η hF E' hηE')
      (originalTargetUnitIso_unit η hF E' hηE')
  simpa only [Functor.CoaugmentedTestRetract.homRetraction, Category.id_comp,
    Category.assoc, hInv, hInv'] using h

include hF in
/-- All original level-Ho target maps preserve the complete source/target Hom retraction. -/
theorem originalHomRetraction_target (X : Carrier (I := I)) {E E' : Carrier (I := I)}
    (hηE : weakEquivalences (Carrier (I := I)) (η.app E))
    (hηE' : weakEquivalences (Carrier (I := I)) (η.app E'))
    (p : (toHomotopyCategory (Carrier (I := I))).obj E ⟶
      (toHomotopyCategory (Carrier (I := I))).obj E')
    (g : (originalTelescopeHo η hF).obj ((toHomotopyCategory (Carrier (I := I))).obj X) ⟶
      (originalTelescopeHo η hF).obj ((toHomotopyCategory (Carrier (I := I))).obj E)) :
    originalHomRetraction η hF X E' hηE' (g ≫ (originalTelescopeHo η hF).map p) =
      originalHomRetraction η hF X E hηE g ≫ p := by
  let := originalTargetUnitIsIso η hF E hηE
  let := originalTargetUnitIsIso η hF E' hηE'
  exact Functor.CoaugmentedTestRetract.homRetraction_target (originalTelescopeHo η hF) (originalUnitHo η hF)
    ((toHomotopyCategory (Carrier (I := I))).obj X) p g

include hF in
/-- A telescope-inverted native map has its genuine typed original level-Ho isomorphism. -/
def originalMapIso {X Y : Carrier (I := I)} (f : X ⟶ Y)
    (hf : weakEquivalences (Carrier (I := I)) ((originalTelescope η).map f)) :
    (originalTelescopeHo η hF).obj ((toHomotopyCategory (Carrier (I := I))).obj X) ≅
      (originalTelescopeHo η hF).obj ((toHomotopyCategory (Carrier (I := I))).obj Y) := by
  let q := (originalTelescopeHo η hF).map ((toHomotopyCategory (Carrier (I := I))).map f)
  have hq : IsIso q := by
    change IsIso ((originalTelescopeHo η hF).map
      ((toHomotopyCategory (Carrier (I := I))).map f))
    rw [originalTelescopeHo_map η hF f]
    exact (weakEquivalence_iff_isIso_toHomotopyCategory_map _).mp hf
  let _ : IsIso q := hq
  exact asIso q

include hF in
/-- The original typed map Iso has exactly the actual descended native map as its hom. -/
theorem originalMapIso_hom {X Y : Carrier (I := I)} (f : X ⟶ Y)
    (hf : weakEquivalences (Carrier (I := I)) ((originalTelescope η).map f)) :
    (originalMapIso η hF f hf).hom =
      (originalTelescopeHo η hF).map ((toHomotopyCategory (Carrier (I := I))).map f) := rfl

include hF in
private theorem originalMapIsIso {X Y : Carrier (I := I)} (f : X ⟶ Y)
    (hf : weakEquivalences (Carrier (I := I)) ((originalTelescope η).map f)) :
    IsIso ((originalTelescopeHo η hF).map ((toHomotopyCategory (Carrier (I := I))).map f)) := by
  rw [← originalMapIso_hom η hF f hf]
  exact (originalMapIso η hF f hf).isIso_hom

include hF in
/-- The full explicit inverse to source precomposition uses the actual telescope map inverse. -/
def originalPrecompInverse {X Y : Carrier (I := I)} (f : X ⟶ Y)
    (hf : weakEquivalences (Carrier (I := I)) ((originalTelescope η).map f))
    (E : Carrier (I := I)) (hηE : weakEquivalences (Carrier (I := I)) (η.app E))
    (g : (toHomotopyCategory (Carrier (I := I))).obj X ⟶
      (toHomotopyCategory (Carrier (I := I))).obj E) :
    (toHomotopyCategory (Carrier (I := I))).obj Y ⟶
      (toHomotopyCategory (Carrier (I := I))).obj E := by
  letI := originalMapIsIso η hF f hf
  letI := originalTargetUnitIsIso η hF E hηE
  exact Functor.CoaugmentationHomTests.liftHom (originalUnitHo η hF) ((toHomotopyCategory (Carrier (I := I))).map f) g

include hF in
/-- Every original source Hom input is restored by the same full inverse function. -/
theorem originalPrecompInverse_section {X Y : Carrier (I := I)} (f : X ⟶ Y)
    (hf : weakEquivalences (Carrier (I := I)) ((originalTelescope η).map f))
    (E : Carrier (I := I)) (hηE : weakEquivalences (Carrier (I := I)) (η.app E))
    (g : (toHomotopyCategory (Carrier (I := I))).obj X ⟶
      (toHomotopyCategory (Carrier (I := I))).obj E) :
    (toHomotopyCategory (Carrier (I := I))).map f ≫ originalPrecompInverse η hF f hf E hηE g = g := by
  let := originalMapIsIso η hF f hf
  let := originalTargetUnitIsIso η hF E hηE
  exact Functor.CoaugmentationHomTests.comp_liftHom (originalUnitHo η hF)
    ((toHomotopyCategory (Carrier (I := I))).map f) g

include hF in
/-- Every original target-side Hom input is restored by the other complete inverse law. -/
theorem originalPrecompInverse_retract {X Y : Carrier (I := I)} (f : X ⟶ Y)
    (hf : weakEquivalences (Carrier (I := I)) ((originalTelescope η).map f))
    (E : Carrier (I := I)) (hηE : weakEquivalences (Carrier (I := I)) (η.app E))
    (g : (toHomotopyCategory (Carrier (I := I))).obj Y ⟶
      (toHomotopyCategory (Carrier (I := I))).obj E) :
    originalPrecompInverse η hF f hf E hηE
      ((toHomotopyCategory (Carrier (I := I))).map f ≫ g) = g := by
  let := originalMapIsIso η hF f hf
  let := originalTargetUnitIsIso η hF E hηE
  exact Functor.CoaugmentationHomTests.liftHom_comp (originalUnitHo η hF)
    ((toHomotopyCategory (Carrier (I := I))).map f) g

include hF in
/-- The actual telescope-inverted map has bijective complete original Hom precomposition. -/
theorem originalPrecomp_bijective {X Y : Carrier (I := I)} (f : X ⟶ Y)
    (hf : weakEquivalences (Carrier (I := I)) ((originalTelescope η).map f))
    (E : Carrier (I := I)) (hηE : weakEquivalences (Carrier (I := I)) (η.app E)) :
    Function.Bijective (fun g : (toHomotopyCategory (Carrier (I := I))).obj Y ⟶
      (toHomotopyCategory (Carrier (I := I))).obj E =>
      (toHomotopyCategory (Carrier (I := I))).map f ≫ g) := by
  let := originalMapIsIso η hF f hf
  let := originalTargetUnitIsIso η hF E hηE
  exact (Functor.CoaugmentationHomTests.homEquiv (originalUnitHo η hF)
    ((toHomotopyCategory (Carrier (I := I))).map f)).bijective

include hF in
/-- Both full source Hom functions form the actual original precomposition equivalence. -/
def originalPrecompEquiv {X Y : Carrier (I := I)} (f : X ⟶ Y)
    (hf : weakEquivalences (Carrier (I := I)) ((originalTelescope η).map f))
    (E : Carrier (I := I)) (hηE : weakEquivalences (Carrier (I := I)) (η.app E)) :
    ((toHomotopyCategory (Carrier (I := I))).obj Y ⟶
      (toHomotopyCategory (Carrier (I := I))).obj E) ≃
      ((toHomotopyCategory (Carrier (I := I))).obj X ⟶
      (toHomotopyCategory (Carrier (I := I))).obj E) := by
  letI := originalMapIsIso η hF f hf
  letI := originalTargetUnitIsIso η hF E hηE
  exact Functor.CoaugmentationHomTests.homEquiv (originalUnitHo η hF) ((toHomotopyCategory (Carrier (I := I))).map f)

include hF in
/-- Every original target-Ho map preserves the actual full precomposition inverse. -/
theorem originalPrecompInverse_target {X Y E E' : Carrier (I := I)} (f : X ⟶ Y)
    (hf : weakEquivalences (Carrier (I := I)) ((originalTelescope η).map f))
    (hηE : weakEquivalences (Carrier (I := I)) (η.app E))
    (hηE' : weakEquivalences (Carrier (I := I)) (η.app E'))
    (p : (toHomotopyCategory (Carrier (I := I))).obj E ⟶
      (toHomotopyCategory (Carrier (I := I))).obj E')
    (g : (toHomotopyCategory (Carrier (I := I))).obj X ⟶
      (toHomotopyCategory (Carrier (I := I))).obj E) :
    originalPrecompInverse η hF f hf E' hηE' (g ≫ p) =
      originalPrecompInverse η hF f hf E hηE g ≫ p := by
  let := originalMapIsIso η hF f hf
  let := originalTargetUnitIsIso η hF E hηE
  let := originalTargetUnitIsIso η hF E' hηE'
  exact Functor.CoaugmentationHomTests.liftHom_target (originalUnitHo η hF)
    ((toHomotopyCategory (Carrier (I := I))).map f) g p

include hF in
/-- An actual square preserves the entire original inverse precomposition function. -/
theorem originalPrecompInverse_sourceSquare
    {X Y X' Y' E : Carrier (I := I)} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (hf : weakEquivalences (Carrier (I := I)) ((originalTelescope η).map f))
    (hf' : weakEquivalences (Carrier (I := I)) ((originalTelescope η).map f'))
    (a : X' ⟶ X) (b : Y' ⟶ Y) (w : f' ≫ b = a ≫ f)
    (hηE : weakEquivalences (Carrier (I := I)) (η.app E))
    (g : (toHomotopyCategory (Carrier (I := I))).obj X ⟶
      (toHomotopyCategory (Carrier (I := I))).obj E) :
    originalPrecompInverse η hF f' hf' E hηE
        ((toHomotopyCategory (Carrier (I := I))).map a ≫ g) =
      (toHomotopyCategory (Carrier (I := I))).map b ≫
        originalPrecompInverse η hF f hf E hηE g := by
  let := originalMapIsIso η hF f hf
  let := originalMapIsIso η hF f' hf'
  let := originalTargetUnitIsIso η hF E hηE
  have hw : (toHomotopyCategory (Carrier (I := I))).map f' ≫ (toHomotopyCategory (Carrier (I := I))).map b =
      (toHomotopyCategory (Carrier (I := I))).map a ≫ (toHomotopyCategory (Carrier (I := I))).map f := by
    rw [← (toHomotopyCategory (Carrier (I := I))).map_comp, ← (toHomotopyCategory (Carrier (I := I))).map_comp, w]
  exact (Functor.CoaugmentationHomTests.liftHom_source (originalUnitHo η hF)
    ((toHomotopyCategory (Carrier (I := I))).map f)
    ((toHomotopyCategory (Carrier (I := I))).map f')
    ((toHomotopyCategory (Carrier (I := I))).map a)
    ((toHomotopyCategory (Carrier (I := I))).map b) hw g).symm

include hF in
/-- The typed original map inverse is the full weak-Iso inverse of the actual telescope map. -/
theorem originalMapIso_raw_inverse {X Y : Carrier (I := I)} (f : X ⟶ Y)
    (hf : weakEquivalences (Carrier (I := I)) ((originalTelescope η).map f)) :
    (originalMapIso η hF f hf).inv =
      (Localization.Construction.wIso ((originalTelescope η).map f) hf).inv := by
  let e := originalMapIso η hF f hf
  let r := Localization.Construction.wIso ((originalTelescope η).map f) hf
  have hIso : e = r := by
    apply Iso.ext
    exact (originalMapIso_hom η hF f hf).trans (originalTelescopeHo_map η hF f)
  exact congrArg Iso.inv hIso

include hF in
/-- The complete original inverse formula retains the actual unit, raw weak map and target unit. -/
theorem originalPrecompInverse_formula {X Y : Carrier (I := I)} (f : X ⟶ Y)
    (hf : weakEquivalences (Carrier (I := I)) ((originalTelescope η).map f))
    (E : Carrier (I := I)) (hηE : weakEquivalences (Carrier (I := I)) (η.app E))
    (g : (toHomotopyCategory (Carrier (I := I))).obj X ⟶
      (toHomotopyCategory (Carrier (I := I))).obj E) :
    originalPrecompInverse η hF f hf E hηE g =
      (toHomotopyCategory (Carrier (I := I))).map ((originalUnit η).app Y) ≫
        (originalMapIso η hF f hf).inv ≫ (originalTelescopeHo η hF).map g ≫
          (originalTargetUnitIso η hF E hηE).inv := by
  let := originalMapIsIso η hF f hf
  let := originalTargetUnitIsIso η hF E hηE
  change Functor.CoaugmentationHomTests.liftHom (originalUnitHo η hF)
    ((toHomotopyCategory (Carrier (I := I))).map f) g = _
  have hInv : CategoryTheory.inv
      ((originalTelescopeHo η hF).map ((toHomotopyCategory (Carrier (I := I))).map f)) =
      (originalMapIso η hF f hf).inv :=
    inverse_eq_of_original_iso _ (originalMapIso η hF f hf)
      (originalMapIso_hom η hF f hf).symm
  have hTargetInv : CategoryTheory.inv
      ((originalUnitHo η hF).app ((toHomotopyCategory (Carrier (I := I))).obj E)) =
      (originalTargetUnitIso η hF E hηE).inv :=
    inverse_eq_of_original_iso _ (originalTargetUnitIso η hF E hηE)
      (originalTargetUnitIso_unit η hF E hηE)
  rw [Functor.CoaugmentationHomTests.liftHom_formula, hInv, hTargetInv,
    originalUnitHo_app η hF Y]
  rfl

end General

section OriginalOrthogonal

open HomotopicalAlgebra.EnrichedProjective.Native.OperatorStabilizationK.Actual
open PointedCGWH.Spectra.Orthogonal.MMSSStabilization
open PointedCGWH.Spectra.Orthogonal.FunctionSpectrum

/-- The original shifted-loop/D.delta telescope descends through actual level weak preservation. -/
def orthogonalTelescopeHo : HomotopyCategory OrthogonalCarrier.{u, v} ⥤
    HomotopyCategory OrthogonalCarrier.{u, v} :=
  originalTelescopeHo Delooping.delta (fun {X Y} f hf => OmegaUnit.shiftedLoop_preserves_weak (X := X) (Y := Y) f hf)

/-- The complete original orthogonal telescope unit is the actual projected stage-zero leg. -/
def orthogonalUnitHo : 𝟭 (HomotopyCategory OrthogonalCarrier.{u, v}) ⟶ orthogonalTelescopeHo :=
  originalUnitHo Delooping.delta (fun {X Y} f hf => OmegaUnit.shiftedLoop_preserves_weak (X := X) (Y := Y) f hf)

/-- Every actual native original orthogonal map keeps its full telescope map in level Ho. -/
theorem orthogonalTelescopeHo_map {X Y : OrthogonalCarrier.{u, v}} (f : X ⟶ Y) :
    orthogonalTelescopeHo.map ((toHomotopyCategory OrthogonalCarrier.{u, v}).map f) =
      (toHomotopyCategory OrthogonalCarrier.{u, v}).map (OmegaUnit.telescopeFunctor.map f) :=
  originalTelescopeHo_map Delooping.delta
    (fun {X Y} f hf => OmegaUnit.shiftedLoop_preserves_weak (X := X) (Y := Y) f hf) f

/-- The original Omega-target telescope unit is genuinely level weak, with all paired tests. -/
theorem orthogonalOmegaUnit_weak (E : OrthogonalCarrier.{u, v})
    (hE : NativeK.IsOmega orthogonalFamily E) :
    weakEquivalences OrthogonalCarrier.{u, v} (OmegaUnit.unit.app E) :=
  originalUnit_weak Delooping.delta (fun {X Y} f hf => OmegaUnit.shiftedLoop_preserves_weak (X := X) (Y := Y) f hf) E
    (Delooping.delta_weak E hE)

/-- Only the actual original Omega test target supplies this entire unit isomorphism. -/
def orthogonalOmegaUnitIso (E : OrthogonalCarrier.{u, v})
    (hE : NativeK.IsOmega orthogonalFamily E) :
    (toHomotopyCategory OrthogonalCarrier.{u, v}).obj E ≅
      orthogonalTelescopeHo.obj ((toHomotopyCategory OrthogonalCarrier.{u, v}).obj E) :=
  originalTargetUnitIso Delooping.delta
    (fun {X Y} f hf => OmegaUnit.shiftedLoop_preserves_weak (X := X) (Y := Y) f hf) E
    (Delooping.delta_weak E hE)

/-- Its original hom is the actual projected unit, with no arbitrary input-unit assumption. -/
theorem orthogonalOmegaUnitIso_hom (E : OrthogonalCarrier.{u, v})
    (hE : NativeK.IsOmega orthogonalFamily E) :
    (orthogonalOmegaUnitIso E hE).hom =
      (toHomotopyCategory OrthogonalCarrier.{u, v}).map (OmegaUnit.unit.app E) := rfl

/-- The original full telescope Hom map retracts into every actual original Omega target. -/
def orthogonalOmegaHomRetraction (X E : OrthogonalCarrier.{u, v})
    (hE : NativeK.IsOmega orthogonalFamily E)
    (g : orthogonalTelescopeHo.obj ((toHomotopyCategory OrthogonalCarrier.{u, v}).obj X) ⟶
      orthogonalTelescopeHo.obj ((toHomotopyCategory OrthogonalCarrier.{u, v}).obj E)) :
    (toHomotopyCategory OrthogonalCarrier.{u, v}).obj X ⟶
      (toHomotopyCategory OrthogonalCarrier.{u, v}).obj E :=
  originalHomRetraction Delooping.delta (fun {X Y} f hf => OmegaUnit.shiftedLoop_preserves_weak (X := X) (Y := Y) f hf)
    X E (Delooping.delta_weak E hE) g

/-- Every original Ho input has the same full original target-specific Hom retraction. -/
theorem orthogonalOmegaHomRetraction_map (X E : OrthogonalCarrier.{u, v})
    (hE : NativeK.IsOmega orthogonalFamily E)
    (g : (toHomotopyCategory OrthogonalCarrier.{u, v}).obj X ⟶
      (toHomotopyCategory OrthogonalCarrier.{u, v}).obj E) :
    orthogonalOmegaHomRetraction X E hE (orthogonalTelescopeHo.map g) = g :=
  originalHomRetraction_map Delooping.delta
    (fun {X Y} f hf => OmegaUnit.shiftedLoop_preserves_weak (X := X) (Y := Y) f hf)
    X E (Delooping.delta_weak E hE) g

/-- Every map inverted by this actual original telescope passes all original Omega Hom tests. -/
theorem orthogonalTelescopeMap_weak_implies_omegaTests {X Y : OrthogonalCarrier.{u, v}}
    (f : X ⟶ Y)
    (hf : weakEquivalences OrthogonalCarrier.{u, v} (OmegaUnit.telescopeFunctor.map f)) :
    NativeK.omegaTests orthogonalFamily f := by
  intro E hE
  exact originalPrecomp_bijective Delooping.delta
    (fun {X Y} f hf => OmegaUnit.shiftedLoop_preserves_weak (X := X) (Y := Y) f hf) f hf E (Delooping.delta_weak E hE)

/-- The full original inverse of those all-target Hom tests keeps each actual input arrow. -/
def orthogonalOmegaPrecompEquiv {X Y : OrthogonalCarrier.{u, v}} (f : X ⟶ Y)
    (hf : weakEquivalences OrthogonalCarrier.{u, v} (OmegaUnit.telescopeFunctor.map f))
    (E : OrthogonalCarrier.{u, v}) (hE : NativeK.IsOmega orthogonalFamily E) :
    ((toHomotopyCategory OrthogonalCarrier.{u, v}).obj Y ⟶
      (toHomotopyCategory OrthogonalCarrier.{u, v}).obj E) ≃
      ((toHomotopyCategory OrthogonalCarrier.{u, v}).obj X ⟶
      (toHomotopyCategory OrthogonalCarrier.{u, v}).obj E) :=
  originalPrecompEquiv Delooping.delta (fun {X Y} f hf => OmegaUnit.shiftedLoop_preserves_weak (X := X) (Y := Y) f hf)
    f hf E (Delooping.delta_weak E hE)

/-- Every original Omega-target Ho map commutes with the actual inverse Hom precomposition. -/
theorem orthogonalOmegaPrecompEquiv_target {X Y E E' : OrthogonalCarrier.{u, v}}
    (f : X ⟶ Y)
    (hf : weakEquivalences OrthogonalCarrier.{u, v} (OmegaUnit.telescopeFunctor.map f))
    (hE : NativeK.IsOmega orthogonalFamily E) (hE' : NativeK.IsOmega orthogonalFamily E')
    (p : (toHomotopyCategory OrthogonalCarrier.{u, v}).obj E ⟶
      (toHomotopyCategory OrthogonalCarrier.{u, v}).obj E')
    (g : (toHomotopyCategory OrthogonalCarrier.{u, v}).obj X ⟶
      (toHomotopyCategory OrthogonalCarrier.{u, v}).obj E) :
    (orthogonalOmegaPrecompEquiv f hf E' hE').symm (g ≫ p) =
      (orthogonalOmegaPrecompEquiv f hf E hE).symm g ≫ p :=
  originalPrecompInverse_target Delooping.delta
    (fun {X Y} f hf => OmegaUnit.shiftedLoop_preserves_weak (X := X) (Y := Y) f hf)
    f hf (Delooping.delta_weak E hE) (Delooping.delta_weak E' hE') p g

/-- The original source square commutes with every actual Omega-target inverse Hom map. -/
theorem orthogonalOmegaPrecompEquiv_sourceSquare
    {X Y X' Y' E : OrthogonalCarrier.{u, v}} (f : X ⟶ Y) (f' : X' ⟶ Y')
    (hf : weakEquivalences OrthogonalCarrier.{u, v} (OmegaUnit.telescopeFunctor.map f))
    (hf' : weakEquivalences OrthogonalCarrier.{u, v} (OmegaUnit.telescopeFunctor.map f'))
    (a : X' ⟶ X) (b : Y' ⟶ Y) (w : f' ≫ b = a ≫ f)
    (hE : NativeK.IsOmega orthogonalFamily E)
    (g : (toHomotopyCategory OrthogonalCarrier.{u, v}).obj X ⟶
      (toHomotopyCategory OrthogonalCarrier.{u, v}).obj E) :
    (orthogonalOmegaPrecompEquiv f' hf' E hE).symm
        ((toHomotopyCategory OrthogonalCarrier.{u, v}).map a ≫ g) =
      (toHomotopyCategory OrthogonalCarrier.{u, v}).map b ≫
        (orthogonalOmegaPrecompEquiv f hf E hE).symm g :=
  originalPrecompInverse_sourceSquare Delooping.delta
    (fun {X Y} f hf => OmegaUnit.shiftedLoop_preserves_weak (X := X) (Y := Y) f hf)
    f f' hf hf' a b w (Delooping.delta_weak E hE) g

end OriginalOrthogonal

end PointedCGWH.Spectra.OriginalTelescopeOmegaHomRetract
