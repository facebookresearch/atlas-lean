/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OneStepModuleEquivalence
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.GenericSphereModules
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OperatorReconstructionEquivalence
import MathlibExt.AlgebraicTopology.Spectra.Symmetric.SphereDayMonoidClosed
import MathlibExt.CategoryTheory.Enriched.WholeRepresentationFreeComparison

/-!
# Original generic symmetric spectra as genuine enriched operator functors

This is an equivalence on the existing ordinary `SymmetricSpectrum S(T)`
carrier. Both the sphere monoid and the whole operator coends are produced
from the original tensor powers and finite labels. No reconstruction law
or tensor-unit separator is an input.
-/

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory

local notation "I" => Operad.SmallFinBijGroupoid

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V] [HasColimitsOfSize.{0, 0} V]

/-- Actual genuine enriched functors from the full original generic sphere operator. -/
abbrev GenericSphereOperatorSpectra (T : V) :=
  letI : EnrichedCategory V I := Spectra.Symmetric.OperatorCoend.enrichedCategory T
  EnrichedFunctorCat V I

/-- The whole-action representation and the actual original enriched functor category agree. -/
def genericSphereOperatorRepresentationEquivalence (T : V) :
    Spectra.Symmetric.OperatorCoend.Representation T ≌ GenericSphereOperatorSpectra T := by
  letI : EnrichedCategory V I := Spectra.Symmetric.OperatorCoend.enrichedCategory T
  exact WholeRepresentation.genuineEquivalence

/-- The existing ordinary sphere-module carrier is the actual genuine enriched operator carrier. -/
def genericSphereModuleOperatorEquivalence (T : V) :
    SymmetricSpectrum (genericSphereDayMonoid T) ≌ GenericSphereOperatorSpectra T :=
  ((DayFunctor.ExternalModule.equivalence (genericSphereDayMonoid T).X).symm.trans
    (Spectra.Symmetric.OperatorCoend.externalRepresentationEquivalence T)).trans
      (genericSphereOperatorRepresentationEquivalence T)

/-- Full compatible one-step spectra are the same actual genuine enriched operator functors. -/
def genericOneStepOperatorEquivalence (T : V) :
    Spectra.Symmetric.OneStepSpectrum T ≌ GenericSphereOperatorSpectra T :=
  (Spectra.Symmetric.OneStepSpectrum.moduleEquivalence T).trans (genericSphereModuleOperatorEquivalence T)

/-- Every original value object of a genuine generic sphere operator spectrum. -/
def genericSphereOperatorObject (T : V) (F : GenericSphereOperatorSpectra T) (n : I) : V := by
  letI : EnrichedCategory V I := Spectra.Symmetric.OperatorCoend.enrichedCategory T
  exact F.toEnrichedFunctor.obj n

/-- The actual enriched map on the entire original coefficient Hom coend. -/
def genericSphereOperatorHomMap (T : V) (F : GenericSphereOperatorSpectra T) (n k : I) :
    Spectra.Symmetric.OperatorCoend.Hom T n k ⟶
      (ihom (genericSphereOperatorObject T F n)).obj (genericSphereOperatorObject T F k) := by
  letI : EnrichedCategory V I := Spectra.Symmetric.OperatorCoend.enrichedCategory T
  exact F.toEnrichedFunctor.map n k

/-- Every original component of a genuine whole enriched operator transformation. -/
def genericSphereOperatorComponent (T : V) {F G : GenericSphereOperatorSpectra T} (f : F ⟶ G) (n : I) :
    genericSphereOperatorObject T F n ⟶ genericSphereOperatorObject T G n := by
  letI : EnrichedCategory V I := Spectra.Symmetric.OperatorCoend.enrichedCategory T
  exact EnrichedFunctorCat.component f n

/-- The full ordinary-to-enriched functor preserves every original module level. -/
theorem genericSphereModuleOperatorEquivalence_obj (T : V)
    (M : SymmetricSpectrum (genericSphereDayMonoid T)) (n : I) :
    genericSphereOperatorObject T ((genericSphereModuleOperatorEquivalence T).functor.obj M) n =
      M.X.functor.obj n := rfl

/-- The full ordinary-to-enriched functor preserves every original spectrum morphism component. -/
theorem genericSphereModuleOperatorEquivalence_map (T : V)
    {M N : SymmetricSpectrum (genericSphereDayMonoid T)} (f : M ⟶ N) (n : I) :
    genericSphereOperatorComponent T ((genericSphereModuleOperatorEquivalence T).functor.map f) n =
      f.hom.natTrans.app n := by
  let _ : EnrichedCategory V I := Spectra.Symmetric.OperatorCoend.enrichedCategory T
  exact WholeRepresentation.toGenuineFunctors_map_component
    (Spectra.Symmetric.OperatorCoend.toRepresentationMap
      ((DayFunctor.ExternalModule.fromModules (genericSphereDayMonoid T).X).map f)) n

/-- Every original operator label retains the entire original module coefficient and target action. -/
theorem genericSphereModuleOperatorEquivalence_generator (T : V)
    (M : SymmetricSpectrum (genericSphereDayMonoid T)) (a n k : I) (f : a ⊗ n ⟶ k) :
    (M.X.functor.obj n ◁ Spectra.Symmetric.OperatorCoend.generator T a n k f) ≫
      MonoidalClosed.uncurry (genericSphereOperatorHomMap T
        ((genericSphereModuleOperatorEquivalence T).functor.obj M) n k) =
    (β_ (M.X.functor.obj n) ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a)).hom ≫
      genericSpectrumPairAction T M a n ≫ M.X.functor.map f := by
  let d := (DayFunctor.ExternalModule.fromModules (genericSphereDayMonoid T).X).obj M
  let z : M.X.functor.obj n ⊗ Spectra.Symmetric.OperatorCoend.Hom T n k ⟶ M.X.functor.obj k :=
    Spectra.Symmetric.OperatorCoend.operatorAction d n k
  change (M.X.functor.obj n ◁ Spectra.Symmetric.OperatorCoend.generator T a n k f) ≫
    MonoidalClosed.uncurry (MonoidalClosed.curry z) = _
  rw [MonoidalClosed.uncurry_curry]
  have hg : (M.X.functor.obj n ◁ Spectra.Symmetric.OperatorCoend.generator T a n k f) ≫ z =
      Spectra.Symmetric.OperatorCoend.actionLeg d a n k f :=
    Spectra.Symmetric.OperatorCoend.generator_operatorAction d a n k f
  exact hg.trans (Category.assoc _ _ _)

/-- Reconstruction preserves every original operator value object on the existing module carrier. -/
theorem genericSphereModuleOperatorEquivalence_inverse_obj (T : V) (F : GenericSphereOperatorSpectra T) (n : I) :
    ((genericSphereModuleOperatorEquivalence T).inverse.obj F).X.functor.obj n =
      genericSphereOperatorObject T F n := rfl

/-- Reconstruction retains each original index arrow's complete empty-coefficient action. -/
theorem genericSphereModuleOperatorEquivalence_inverse_map (T : V) (F : GenericSphereOperatorSpectra T)
    {n k : I} (f : n ⟶ k) :
    ((genericSphereModuleOperatorEquivalence T).inverse.obj F).X.functor.map f =
      (ρ_ (genericSphereOperatorObject T F n)).inv ≫
        (genericSphereOperatorObject T F n ◁ Spectra.Symmetric.OperatorCoend.arrow T f) ≫
        MonoidalClosed.uncurry (genericSphereOperatorHomMap T F n k) := by
  let _ : EnrichedCategory V I := Spectra.Symmetric.OperatorCoend.enrichedCategory T
  exact Spectra.Symmetric.OperatorCoend.ordinaryDiagram_map
    (WholeRepresentation.fromGenuineFunctors.obj F) f

/-- Reconstruction retains every original entire identity-labelled tensor-power coefficient. -/
theorem genericSphereModuleOperatorEquivalence_inverse_coefficient (T : V) (F : GenericSphereOperatorSpectra T)
    (a n : I) :
    genericSpectrumPairAction T ((genericSphereModuleOperatorEquivalence T).inverse.obj F) a n =
      (β_ ((Operad.SmallFinBijGroupoid.tensorPowerFunctor T).obj a) (genericSphereOperatorObject T F n)).hom ≫
        (genericSphereOperatorObject T F n ◁
          Spectra.Symmetric.OperatorCoend.generator T a n (a ⊗ n) (𝟙 (a ⊗ n))) ≫
        MonoidalClosed.uncurry (genericSphereOperatorHomMap T F n (a ⊗ n)) := by
  let _ : EnrichedCategory V I := Spectra.Symmetric.OperatorCoend.enrichedCategory T
  let d := Spectra.Symmetric.OperatorCoend.fromRepresentation (WholeRepresentation.fromGenuineFunctors.obj F)
  exact d.smul_generator a n

end CategoryTheory
