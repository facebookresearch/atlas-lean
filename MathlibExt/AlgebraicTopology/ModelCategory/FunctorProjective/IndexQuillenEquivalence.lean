/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.CategoryTheory.Functor.KanExtension.IndexAdjunctionProperties
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.KanExtensions
import MathlibExt.AlgebraicTopology.ModelCategory.QuillenEquivalence
import Mathlib.CategoryTheory.EssentiallySmall

/-!
# Quillen equivalence of the existing native Lan along an index equivalence

The adjunction is the existing e.functor.lanAdjunction M. Fixed entries
derive the actual cross-size Hom bound and comma dictionaries from the
given equivalence and source generation datum. Both original diagram
models, cardinals and bottom instances remain independent.
-/

set_option autoImplicit false
noncomputable section
universe uD vD uE vE uM vM wD wE
open CategoryTheory Functor

namespace HomotopicalAlgebra.FunctorProjective.IndexQuillenEquivalence

variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  {M : Type uM} [Category.{vM} M] [ModelCategory M]

section ExistingModels

variable [ModelCategory (D ⥤ M)] [ModelCategory (E ⥤ M)]
  (e : D ≌ E) [∀ F : D ⥤ M, e.functor.HasLeftKanExtension F]

/-- The actual native forward adjunct detects weak arrows in the original models. -/
theorem homEquiv_weakEquivalence_iff_of_pointwise
    (hWD : weakEquivalences (D ⥤ M) = (weakEquivalences M).functorCategory D)
    (hWE : weakEquivalences (E ⥤ M) = (weakEquivalences M).functorCategory E)
    {X : D ⥤ M} {Y : E ⥤ M} (f : e.functor.lan.obj X ⟶ Y) :
    weakEquivalences (E ⥤ M) f ↔
      weakEquivalences (D ⥤ M) ((e.functor.lanAdjunction M).homEquiv X Y f) := by
  rw [hWE, hWD]
  exact Functor.IndexAdjunctionProperties.homEquiv_property_iff e (weakEquivalences M) f

/-- The inverse of the same native Hom equivalence retains the weak-map criterion. -/
theorem inverse_weakEquivalence_iff_of_pointwise
    (hWD : weakEquivalences (D ⥤ M) = (weakEquivalences M).functorCategory D)
    (hWE : weakEquivalences (E ⥤ M) = (weakEquivalences M).functorCategory E)
    {X : D ⥤ M} {Y : E ⥤ M} (c : X ⟶ e.functor ⋙ Y) :
    weakEquivalences (D ⥤ M) c ↔
      weakEquivalences (E ⥤ M) (((e.functor.lanAdjunction M).homEquiv X Y).symm c) := by
  rw [hWD, hWE]
  exact Functor.IndexAdjunctionProperties.inverse_property_iff e (weakEquivalences M) c

/-- Original pointwise right classes give QE for the given native Lan adjunction. -/
theorem isQuillenEquivalence_of_pointwise_classes
    (hWD : weakEquivalences (D ⥤ M) = (weakEquivalences M).functorCategory D)
    (hWE : weakEquivalences (E ⥤ M) = (weakEquivalences M).functorCategory E)
    (hFD : fibrations (D ⥤ M) = (fibrations M).functorCategory D)
    (hFE : fibrations (E ⥤ M) = (fibrations M).functorCategory E)
    (hTD : trivialFibrations (D ⥤ M) = (trivialFibrations M).functorCategory D)
    (hTE : trivialFibrations (E ⥤ M) = (trivialFibrations M).functorCategory E) :
    (e.functor.lanAdjunction M).IsQuillenEquivalence where
  toIsQuillenAdjunction :=
    KanExtensions.isQuillen_of_pointwise_right_classes e.functor hFD hFE hTD hTE
  homEquiv_weakEquivalence_iff f :=
    homEquiv_weakEquivalence_iff_of_pointwise e hWD hWE f

end ExistingModels

section FixedData

variable {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
  {κE : Cardinal.{wE}} [Fact κE.IsRegular] [OrderBot κE.ord.ToType]
  [Small.{wD} D] [LocallySmall.{wD} D] [Small.{wE} E] [LocallySmall.{wE} E]
  (dD : CofibrantGenerationData M κD) (dE : CofibrantGenerationData M κE)
  (e : D ≌ E)

/-- The two original independent data give QE of the same existing native Lan adjunction. -/
theorem isQuillenEquivalence :
    letI : LocallySmall.{wD} E := locallySmall_of_faithful e.inverse
    letI : ∀ F : D ⥤ M, e.functor.HasLeftKanExtension F :=
      fun F => dD.hasLeftKanExtension e.functor F
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    (e.functor.lanAdjunction M).IsQuillenEquivalence := by
  let _ : LocallySmall.{wD} E := locallySmall_of_faithful e.inverse
  let _ : ∀ F : D ⥤ M, e.functor.HasLeftKanExtension F :=
    fun F => dD.hasLeftKanExtension e.functor F
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
  let _ : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
  exact isQuillenEquivalence_of_pointwise_classes e
    (FunctorProjective.weakEquivalences_eq.{wD} dD)
    (FunctorProjective.weakEquivalences_eq.{wE} dE)
    (FunctorProjective.fibrations_eq.{wD} dD) (FunctorProjective.fibrations_eq.{wE} dE)
    (FunctorProjective.trivialFibrations_eq.{wD} dD)
    (FunctorProjective.trivialFibrations_eq.{wE} dE)

/-- The original fixed-model Hovey criterion uses the full actual forward Hom function. -/
theorem homEquiv_weakEquivalence_iff
    (X : D ⥤ M) (Y : E ⥤ M) :
    letI : LocallySmall.{wD} E := locallySmall_of_faithful e.inverse
    letI : ∀ F : D ⥤ M, e.functor.HasLeftKanExtension F :=
      fun F => dD.hasLeftKanExtension e.functor F
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    IsCofibrant X → IsFibrant Y → ∀ f : e.functor.lan.obj X ⟶ Y,
      (weakEquivalences (E ⥤ M) f ↔
        weakEquivalences (D ⥤ M) ((e.functor.lanAdjunction M).homEquiv X Y f)) := by
  let _ : LocallySmall.{wD} E := locallySmall_of_faithful e.inverse
  let _ : ∀ F : D ⥤ M, e.functor.HasLeftKanExtension F :=
    fun F => dD.hasLeftKanExtension e.functor F
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
  let _ : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
  intro hX hY f
  let _ : IsCofibrant X := hX
  let _ : IsFibrant Y := hY
  let _ : (e.functor.lanAdjunction M).IsQuillenEquivalence := isQuillenEquivalence dD dE e
  exact Adjunction.IsQuillenEquivalence.homEquiv_weakEquivalence_iff
    (adj := e.functor.lanAdjunction M) f

/-- The inverse criterion keeps the same original data, objects and inverse Hom function. -/
theorem inverse_weakEquivalence_iff
    (X : D ⥤ M) (Y : E ⥤ M) :
    letI : LocallySmall.{wD} E := locallySmall_of_faithful e.inverse
    letI : ∀ F : D ⥤ M, e.functor.HasLeftKanExtension F :=
      fun F => dD.hasLeftKanExtension e.functor F
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    IsCofibrant X → IsFibrant Y → ∀ c : X ⟶ e.functor ⋙ Y,
      (weakEquivalences (D ⥤ M) c ↔
        weakEquivalences (E ⥤ M)
          (((e.functor.lanAdjunction M).homEquiv X Y).symm c)) := by
  let _ : LocallySmall.{wD} E := locallySmall_of_faithful e.inverse
  let _ : ∀ F : D ⥤ M, e.functor.HasLeftKanExtension F :=
    fun F => dD.hasLeftKanExtension e.functor F
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
  let _ : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
  intro hX hY c
  let _ : IsCofibrant X := hX
  let _ : IsFibrant Y := hY
  let _ : (e.functor.lanAdjunction M).IsQuillenEquivalence := isQuillenEquivalence dD dE e
  simpa only [Equiv.apply_symm_apply] using
    (Adjunction.IsQuillenEquivalence.homEquiv_weakEquivalence_iff
      (adj := e.functor.lanAdjunction M)
      (((e.functor.lanAdjunction M).homEquiv X Y).symm c)).symm

end FixedData

end HomotopicalAlgebra.FunctorProjective.IndexQuillenEquivalence
