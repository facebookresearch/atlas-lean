/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorProjective.IndexQuillenEquivalence
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.SingleObj
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.Algebra.Group.TypeTags.Basic
import Mathlib.Algebra.Group.Nat.Defs

/-!
# Original fixed-data projective index Quillen-equivalence clients

The models are exactly the two original fixed-data constructors. Every
native Kan dictionary is produced from dD with the actual e-derived
cross-size local-smallness witness. No data or cardinal is reselected.
-/

set_option autoImplicit false
noncomputable section
universe uD vD uE vE uM vM wD wE
open CategoryTheory Functor HomotopicalAlgebra

namespace MathlibExtTest.FunctorProjectiveIndexQuillenEquivalence

variable {D : Type uD} [Category.{vD} D] {E : Type uE} [Category.{vE} E]
  {M : Type uM} [Category.{vM} M] [ModelCategory M]

section ExistingModels

variable [ModelCategory (D ⥤ M)] [ModelCategory (E ⥤ M)]
  (e : D ≌ E) [∀ F : D ⥤ M, e.functor.HasLeftKanExtension F]
  (hWD : weakEquivalences (D ⥤ M) = (weakEquivalences M).functorCategory D)
  (hWE : weakEquivalences (E ⥤ M) = (weakEquivalences M).functorCategory E)
  (hFD : fibrations (D ⥤ M) = (fibrations M).functorCategory D)
  (hFE : fibrations (E ⥤ M) = (fibrations M).functorCategory E)
  (hTD : trivialFibrations (D ⥤ M) = (trivialFibrations M).functorCategory D)
  (hTE : trivialFibrations (E ⥤ M) = (trivialFibrations M).functorCategory E)

example : (e.functor.lanAdjunction M).IsQuillenEquivalence :=
  FunctorProjective.IndexQuillenEquivalence.isQuillenEquivalence_of_pointwise_classes
    e hWD hWE hFD hFE hTD hTE

example {X : D ⥤ M} {Y : E ⥤ M} (f : e.functor.lan.obj X ⟶ Y) :
    weakEquivalences (E ⥤ M) f ↔
      weakEquivalences (D ⥤ M) ((e.functor.lanAdjunction M).homEquiv X Y f) :=
  FunctorProjective.IndexQuillenEquivalence.homEquiv_weakEquivalence_iff_of_pointwise
    e hWD hWE f

example {X : D ⥤ M} {Y : E ⥤ M} (c : X ⟶ e.functor ⋙ Y) :
    weakEquivalences (D ⥤ M) c ↔
      weakEquivalences (E ⥤ M) (((e.functor.lanAdjunction M).homEquiv X Y).symm c) :=
  FunctorProjective.IndexQuillenEquivalence.inverse_weakEquivalence_iff_of_pointwise
    e hWD hWE c

end ExistingModels

section FixedData

variable {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
  {κE : Cardinal.{wE}} [Fact κE.IsRegular] [OrderBot κE.ord.ToType]
  [Small.{wD} D] [LocallySmall.{wD} D] [Small.{wE} E] [LocallySmall.{wE} E]
  (dD : CofibrantGenerationData M κD) (dE : CofibrantGenerationData M κE)
  (e : D ≌ E)

example :
    letI : LocallySmall.{wD} E := locallySmall_of_faithful e.inverse
    letI : ∀ F : D ⥤ M, e.functor.HasLeftKanExtension F :=
      fun F => dD.hasLeftKanExtension e.functor F
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    (e.functor.lanAdjunction M).IsQuillenEquivalence :=
  FunctorProjective.IndexQuillenEquivalence.isQuillenEquivalence dD dE e

example (X : D ⥤ M) (Y : E ⥤ M) :
    letI : LocallySmall.{wD} E := locallySmall_of_faithful e.inverse
    letI : ∀ F : D ⥤ M, e.functor.HasLeftKanExtension F :=
      fun F => dD.hasLeftKanExtension e.functor F
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    IsCofibrant X → IsFibrant Y → ∀ f : e.functor.lan.obj X ⟶ Y,
      (weakEquivalences (E ⥤ M) f ↔
        weakEquivalences (D ⥤ M) ((e.functor.lanAdjunction M).homEquiv X Y f)) :=
  FunctorProjective.IndexQuillenEquivalence.homEquiv_weakEquivalence_iff dD dE e X Y

example (X : D ⥤ M) (Y : E ⥤ M) :
    letI : LocallySmall.{wD} E := locallySmall_of_faithful e.inverse
    letI : ∀ F : D ⥤ M, e.functor.HasLeftKanExtension F :=
      fun F => dD.hasLeftKanExtension e.functor F
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    IsCofibrant X → IsFibrant Y → ∀ c : X ⟶ e.functor ⋙ Y,
      (weakEquivalences (D ⥤ M) c ↔
        weakEquivalences (E ⥤ M) (((e.functor.lanAdjunction M).homEquiv X Y).symm c)) :=
  FunctorProjective.IndexQuillenEquivalence.inverse_weakEquivalence_iff dD dE e X Y

example {X X' : D ⥤ M} (a : X ⟶ X') :
    letI : LocallySmall.{wD} E := locallySmall_of_faithful e.inverse
    letI : ∀ F : D ⥤ M, e.functor.HasLeftKanExtension F :=
      fun F => dD.hasLeftKanExtension e.functor F
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    cofibrations (D ⥤ M) a → cofibrations (E ⥤ M) (e.functor.lan.map a) := by
  let _ : LocallySmall.{wD} E := locallySmall_of_faithful e.inverse
  let _ : ∀ F : D ⥤ M, e.functor.HasLeftKanExtension F :=
    fun F => dD.hasLeftKanExtension e.functor F
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
  let _ : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
  let _ : (e.functor.lanAdjunction M).IsQuillenEquivalence :=
    FunctorProjective.IndexQuillenEquivalence.isQuillenEquivalence dD dE e
  exact (inferInstance : (e.functor.lanAdjunction M).IsQuillenAdjunction).preservesCofibrations a

example {X X' : D ⥤ M} (a : X ⟶ X') :
    letI : LocallySmall.{wD} E := locallySmall_of_faithful e.inverse
    letI : ∀ F : D ⥤ M, e.functor.HasLeftKanExtension F :=
      fun F => dD.hasLeftKanExtension e.functor F
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    trivialCofibrations (D ⥤ M) a →
      trivialCofibrations (E ⥤ M) (e.functor.lan.map a) := by
  let _ : LocallySmall.{wD} E := locallySmall_of_faithful e.inverse
  let _ : ∀ F : D ⥤ M, e.functor.HasLeftKanExtension F :=
    fun F => dD.hasLeftKanExtension e.functor F
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
  let _ : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
  let _ : (e.functor.lanAdjunction M).IsQuillenEquivalence :=
    FunctorProjective.IndexQuillenEquivalence.isQuillenEquivalence dD dE e
  exact (inferInstance : (e.functor.lanAdjunction M).IsQuillenAdjunction).preservesTrivialCofibrations a

example {Y Y' : E ⥤ M} (a : Y ⟶ Y') :
    letI : LocallySmall.{wD} E := locallySmall_of_faithful e.inverse
    letI : ∀ F : D ⥤ M, e.functor.HasLeftKanExtension F :=
      fun F => dD.hasLeftKanExtension e.functor F
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    fibrations (E ⥤ M) a → fibrations (D ⥤ M)
      (((Functor.whiskeringLeft D E M).obj e.functor).map a) := by
  let _ : LocallySmall.{wD} E := locallySmall_of_faithful e.inverse
  let _ : ∀ F : D ⥤ M, e.functor.HasLeftKanExtension F :=
    fun F => dD.hasLeftKanExtension e.functor F
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
  let _ : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
  let _ : (e.functor.lanAdjunction M).IsQuillenEquivalence :=
    FunctorProjective.IndexQuillenEquivalence.isQuillenEquivalence dD dE e
  exact Adjunction.IsQuillenAdjunction.preservesFibrations
    (adj := e.functor.lanAdjunction M) a

example {Y Y' : E ⥤ M} (a : Y ⟶ Y') :
    letI : LocallySmall.{wD} E := locallySmall_of_faithful e.inverse
    letI : ∀ F : D ⥤ M, e.functor.HasLeftKanExtension F :=
      fun F => dD.hasLeftKanExtension e.functor F
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    trivialFibrations (E ⥤ M) a → trivialFibrations (D ⥤ M)
      (((Functor.whiskeringLeft D E M).obj e.functor).map a) := by
  let _ : LocallySmall.{wD} E := locallySmall_of_faithful e.inverse
  let _ : ∀ F : D ⥤ M, e.functor.HasLeftKanExtension F :=
    fun F => dD.hasLeftKanExtension e.functor F
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
  let _ : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
  let _ : (e.functor.lanAdjunction M).IsQuillenEquivalence :=
    FunctorProjective.IndexQuillenEquivalence.isQuillenEquivalence dD dE e
  exact Adjunction.IsQuillenAdjunction.preservesTrivialFibrations
    (adj := e.functor.lanAdjunction M) a

example (X : D ⥤ M) :
    letI : LocallySmall.{wD} E := locallySmall_of_faithful e.inverse
    letI : ∀ F : D ⥤ M, e.functor.HasLeftKanExtension F :=
      fun F => dD.hasLeftKanExtension e.functor F
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    IsCofibrant X → IsFibrant (e.functor.lan.obj X) →
      weakEquivalences (D ⥤ M) ((e.functor.lanAdjunction M).unit.app X) := by
  let _ : LocallySmall.{wD} E := locallySmall_of_faithful e.inverse
  let _ : ∀ F : D ⥤ M, e.functor.HasLeftKanExtension F :=
    fun F => dD.hasLeftKanExtension e.functor F
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
  let _ : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
  intro hX hLX
  let _ : IsCofibrant X := hX
  let _ : IsFibrant (e.functor.lan.obj X) := hLX
  let _ : (e.functor.lanAdjunction M).IsQuillenEquivalence :=
    FunctorProjective.IndexQuillenEquivalence.isQuillenEquivalence dD dE e
  exact (weakEquivalence_iff _).1
    (Adjunction.IsQuillenEquivalence.weakEquivalence_unit (adj := e.functor.lanAdjunction M) X)

example (Y : E ⥤ M) :
    letI : LocallySmall.{wD} E := locallySmall_of_faithful e.inverse
    letI : ∀ F : D ⥤ M, e.functor.HasLeftKanExtension F :=
      fun F => dD.hasLeftKanExtension e.functor F
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
    letI : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
    IsFibrant Y → IsCofibrant (e.functor ⋙ Y) →
      weakEquivalences (E ⥤ M) ((e.functor.lanAdjunction M).counit.app Y) := by
  let _ : LocallySmall.{wD} E := locallySmall_of_faithful e.inverse
  let _ : ∀ F : D ⥤ M, e.functor.HasLeftKanExtension F :=
    fun F => dD.hasLeftKanExtension e.functor F
  let _ : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wD} (J := D) dD
  let _ : ModelCategory (E ⥤ M) := FunctorProjective.modelCategory.{wE} (J := E) dE
  intro hY hRY
  let _ : IsFibrant Y := hY
  let _ : IsCofibrant (((Functor.whiskeringLeft D E M).obj e.functor).obj Y) := by
    change IsCofibrant (e.functor ⋙ Y)
    exact hRY
  let _ : (e.functor.lanAdjunction M).IsQuillenEquivalence :=
    FunctorProjective.IndexQuillenEquivalence.isQuillenEquivalence dD dE e
  exact (weakEquivalence_iff _).1
    (Adjunction.IsQuillenEquivalence.weakEquivalence_counit (adj := e.functor.lanAdjunction M) Y)

end FixedData

section ShapeClients

variable {κD : Cardinal.{wD}} [Fact κD.IsRegular] [OrderBot κD.ord.ToType]
  {κE : Cardinal.{wE}} [Fact κE.IsRegular] [OrderBot κE.ord.ToType]
  (dD : CofibrantGenerationData M κD) (dE : CofibrantGenerationData M κE)

example :
    let e : Discrete PEmpty.{1} ≌ Discrete PEmpty.{1} := CategoryTheory.Equivalence.refl
    letI : LocallySmall.{wD} (Discrete PEmpty.{1}) := locallySmall_of_faithful e.inverse
    letI : ∀ F : Discrete PEmpty.{1} ⥤ M, e.functor.HasLeftKanExtension F :=
      fun F => dD.hasLeftKanExtension e.functor F
    letI : ModelCategory (Discrete PEmpty.{1} ⥤ M) :=
      FunctorProjective.modelCategory.{wD} dD
    letI : ModelCategory (Discrete PEmpty.{1} ⥤ M) :=
      FunctorProjective.modelCategory.{wE} dE
    @Adjunction.IsQuillenEquivalence _ _ _ _
      (FunctorProjective.modelCategory.{wD} dD)
      (FunctorProjective.modelCategory.{wE} dE) _ _ (e.functor.lanAdjunction M) :=
  FunctorProjective.IndexQuillenEquivalence.isQuillenEquivalence dD dE
    (CategoryTheory.Equivalence.refl (C := Discrete PEmpty.{1}))

example :
    let e : Discrete ℕ ≌ Discrete ℕ := CategoryTheory.Equivalence.refl
    letI : LocallySmall.{wD} (Discrete ℕ) := locallySmall_of_faithful e.inverse
    letI : ∀ F : Discrete ℕ ⥤ M, e.functor.HasLeftKanExtension F :=
      fun F => dD.hasLeftKanExtension e.functor F
    letI : ModelCategory (Discrete ℕ ⥤ M) := FunctorProjective.modelCategory.{wD} dD
    letI : ModelCategory (Discrete ℕ ⥤ M) := FunctorProjective.modelCategory.{wE} dE
    @Adjunction.IsQuillenEquivalence _ _ _ _
      (FunctorProjective.modelCategory.{wD} dD)
      (FunctorProjective.modelCategory.{wE} dE) _ _ (e.functor.lanAdjunction M) :=
  FunctorProjective.IndexQuillenEquivalence.isQuillenEquivalence dD dE
    (CategoryTheory.Equivalence.refl (C := Discrete ℕ))

example :
    let e : SingleObj (Multiplicative ℕ) ≌ SingleObj (Multiplicative ℕ) :=
      CategoryTheory.Equivalence.refl
    letI : LocallySmall.{wD} (SingleObj (Multiplicative ℕ)) :=
      locallySmall_of_faithful e.inverse
    letI : ∀ F : SingleObj (Multiplicative ℕ) ⥤ M, e.functor.HasLeftKanExtension F :=
      fun F => dD.hasLeftKanExtension e.functor F
    letI : ModelCategory (SingleObj (Multiplicative ℕ) ⥤ M) :=
      FunctorProjective.modelCategory.{wD} dD
    letI : ModelCategory (SingleObj (Multiplicative ℕ) ⥤ M) :=
      FunctorProjective.modelCategory.{wE} dE
    @Adjunction.IsQuillenEquivalence _ _ _ _
      (FunctorProjective.modelCategory.{wD} dD)
      (FunctorProjective.modelCategory.{wE} dE) _ _ (e.functor.lanAdjunction M) :=
  FunctorProjective.IndexQuillenEquivalence.isQuillenEquivalence dD dE
    (CategoryTheory.Equivalence.refl (C := SingleObj (Multiplicative ℕ)))

example :
    let e : Discrete Bool ≌ Discrete Bool := Discrete.equivalence (Equiv.swap false true)
    letI : LocallySmall.{wD} (Discrete Bool) := locallySmall_of_faithful e.inverse
    letI : ∀ F : Discrete Bool ⥤ M, e.functor.HasLeftKanExtension F :=
      fun F => dD.hasLeftKanExtension e.functor F
    letI : ModelCategory (Discrete Bool ⥤ M) := FunctorProjective.modelCategory.{wD} dD
    letI : ModelCategory (Discrete Bool ⥤ M) := FunctorProjective.modelCategory.{wE} dE
    @Adjunction.IsQuillenEquivalence _ _ _ _
      (FunctorProjective.modelCategory.{wD} dD)
      (FunctorProjective.modelCategory.{wE} dE) _ _ (e.functor.lanAdjunction M) :=
  FunctorProjective.IndexQuillenEquivalence.isQuillenEquivalence dD dE
    (Discrete.equivalence (Equiv.swap false true))

local instance originalRaisedCategory : Category.{vD} (ULift.{uD + 1} D) := uliftCategory D
local instance originalRaisedHomCategory :
    Category.{max (vD + 1) vD} (ULiftHom.{vD + 1} (ULift.{uD + 1} D)) :=
  @ULiftHom.category (ULift.{uD + 1} D) (inferInstance : Category.{vD} (ULift.{uD + 1} D))

example [Small.{wD} (ULiftHom.{vD + 1} (ULift.{uD + 1} D))]
    [LocallySmall.{wD} (ULiftHom.{vD + 1} (ULift.{uD + 1} D))]
    [Small.{wE} D] [LocallySmall.{wE} D] :
    let e := (ULiftHomULiftCategory.equiv.{vD + 1, uD + 1} D).symm
    letI : LocallySmall.{wD} D := locallySmall_of_faithful e.inverse
    letI : ∀ F : ULiftHom.{vD + 1} (ULift.{uD + 1} D) ⥤ M,
        e.functor.HasLeftKanExtension F :=
      fun F => dD.hasLeftKanExtension e.functor F
    letI : ModelCategory (ULiftHom.{vD + 1} (ULift.{uD + 1} D) ⥤ M) :=
      FunctorProjective.modelCategory.{wD} dD
    letI : ModelCategory (D ⥤ M) := FunctorProjective.modelCategory.{wE} dE
    (e.functor.lanAdjunction M).IsQuillenEquivalence :=
  FunctorProjective.IndexQuillenEquivalence.isQuillenEquivalence dD dE
    (ULiftHomULiftCategory.equiv D).symm

end ShapeClients

end MathlibExtTest.FunctorProjectiveIndexQuillenEquivalence
