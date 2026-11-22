/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.JoyalCartesianModel
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.GenuineTrivialFibrations
import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Joyal.QuasicategoryFibrations
import MathlibExt.AlgebraicTopology.Quasicategory.Core
import Mathlib.AlgebraicTopology.Quasicategory.Nerve
import Mathlib.CategoryTheory.Category.ULift

/-!
# Public clients of the native Joyal model

These clients check the named model's three classes, its genuine right
lifting class, quasicategory fibrancy and both trivial pushout-product
orientations. A directed-category nerve gives a concrete fibrant object
whose underlying simplicial set is not Kan. The fibration-criterion client
retains the required quasicategory codomain.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open MonoidalCategory HomotopicalAlgebra Opposite
open scoped Simplicial MonoidalCategory JoyalSSet.ModelCategory

namespace MathlibExtTest.AtlasJoyalModelAPI

local instance : IsClosedSymmetricMonoidalModelCategory JoyalSSet.{u} :=
  JoyalSSet.isClosedSymmetricMonoidalModelCategory

example {X Y : JoyalSSet.{u}} (f : X ⟶ Y) : Cofibration f ↔ Mono f := by
  rw [cofibration_iff]
  change JoyalSSet.modelCategory.categoryWithCofibrations.cofibrations f ↔ Mono f
  rw [JoyalSSet.modelCategory_cofibrations]

example {X Y : JoyalSSet.{u}} (f : X ⟶ Y) :
    WeakEquivalence f ↔ SSet.categoricalEquivalences (JoyalSSet.forget.map f) := by
  rw [weakEquivalence_iff]
  change JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences f ↔ _
  rw [JoyalSSet.modelCategory_weakEquivalences]
  rfl

example {X Y : JoyalSSet.{u}} (f : X ⟶ Y) :
    Fibration f ↔ SSet.categoricalFibrations (JoyalSSet.forget.map f) := by
  rw [fibration_iff]
  change JoyalSSet.modelCategory.categoryWithFibrations.fibrations f ↔ _
  rw [JoyalSSet.modelCategory_fibrations]
  rfl

example {X Y : JoyalSSet.{u}} (f : X ⟶ Y) :
    trivialFibrations JoyalSSet.{u} f ↔
      SSet.modelCategoryQuillen.I.rlp (JoyalSSet.forget.map f) := by
  change (fibrations JoyalSSet.{u} f ∧ weakEquivalences JoyalSSet.{u} f) ↔ _
  change (JoyalSSet.modelCategory.categoryWithFibrations.fibrations f ∧
    JoyalSSet.modelCategory.categoryWithWeakEquivalences.weakEquivalences f) ↔ _
  rw [JoyalSSet.modelCategory_fibrations, JoyalSSet.modelCategory_weakEquivalences]
  exact SSet.categoricalFibrations_and_categoricalEquivalences_iff _

example (X : JoyalSSet.{u}) : IsFibrant X ↔ SSet.Quasicategory X.toSSet :=
  JoyalSSet.isFibrant_iff_quasicategory X

example {A B K L : JoyalSSet.{u}} (i : A ⟶ B) (j : K ⟶ L)
    [Cofibration i] [Cofibration j] : Cofibration (Arrow.mk i □ Arrow.mk j).hom :=
  (cofibration_iff _).mpr
    (IsClosedSymmetricMonoidalModelCategory.cofibration_pushoutProduct i j
      ((cofibration_iff _).mp inferInstance) ((cofibration_iff _).mp inferInstance))

example {A B K L : JoyalSSet.{u}} (i : A ⟶ B) (j : K ⟶ L)
    [Cofibration i] [WeakEquivalence i] [Cofibration j] :
    trivialCofibrations JoyalSSet.{u} (Arrow.mk i □ Arrow.mk j).hom :=
  IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_left i j
    ((mem_trivialCofibrations_iff _).mpr ⟨inferInstance, inferInstance⟩)
    ((cofibration_iff _).mp inferInstance)

example {A B K L : JoyalSSet.{u}} (i : A ⟶ B) (j : K ⟶ L)
    [Cofibration i] [Cofibration j] [WeakEquivalence j] :
    trivialCofibrations JoyalSSet.{u} (Arrow.mk i □ Arrow.mk j).hom :=
  IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_right i j
    ((cofibration_iff _).mp inferInstance)
    ((mem_trivialCofibrations_iff _).mpr ⟨inferInstance, inferInstance⟩)

example : IsCofibrant (𝟙_ JoyalSSet.{u}) := JoyalSSet.tensorUnit_isCofibrant

example {A B X Y : JoyalSSet.{u}} (i : A ⟶ B) (p : X ⟶ Y)
    (hi : trivialCofibrations JoyalSSet.{u} i) (hp : fibrations JoyalSSet.{u} p) :
    trivialFibrations JoyalSSet.{u} ((Opposite.op (Arrow.mk i) ⋔ Arrow.mk p).hom) :=
  IsClosedSymmetricMonoidalModelCategory.cartesianPullbackHomAxiom.2.1 i p hi hp

example {A B X Y : SSet.{u}} (i : A ⟶ B) [Mono i]
    (hi : SSet.categoricalEquivalences i) (p : X ⟶ Y)
    (hp : SSet.categoricalFibrations p) (a : A ⟶ X) (b : B ⟶ Y)
    (sq : CommSq a i p b) : ∃ l : B ⟶ X, i ≫ l = a ∧ l ≫ p = b := by
  let _ : HasLiftingProperty i p :=
    (SSet.categoricalFibrations.mem_iff p).mp hp i inferInstance hi
  exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩

example {X Y : SSet.{u}} [SSet.Quasicategory Y] (p : X ⟶ Y) :
    SSet.categoricalFibrations p ↔
      SSet.InnerFibration p ∧ (SSet.hoFunctor.map p).toFunctor.IsIsofibration :=
  SSet.categoricalFibrations_iff_innerFibration_and_hoIsofibration p

example {X Y : SSet.{u}} [SSet.Quasicategory Y] (p : X ⟶ Y)
    (hp : SSet.categoricalFibrations p) : SSet.Quasicategory X := by
  let _ : SSet.InnerFibration p :=
    ((SSet.categoricalFibrations_iff_innerFibration_and_hasStrictEquivalenceLifting p).mp hp).1
  exact SSet.quasicategory_of_innerFibration p

-- The specialized criterion cannot silently remove its target hypothesis.
example {X Y : SSet.{u}} (p : X ⟶ Y) : True := by
  fail_if_success
    have h : SSet.categoricalFibrations p ↔
        SSet.InnerFibration p ∧ SSet.HasStrictEquivalenceLifting p :=
      SSet.categoricalFibrations_iff_innerFibration_and_hasStrictEquivalenceLifting p
  trivial

private abbrev Directed := AsSmall.{u} (Fin 2)
private abbrev directedNerve : SSet.{u} := nerve Directed.{u}

private def forwardArrow :
    (AsSmall.up.obj (0 : Fin 2) : Directed.{u}) ⟶ AsSmall.up.obj (1 : Fin 2) :=
  AsSmall.up.map (homOfLE (show (0 : Fin 2) ≤ 1 from by decide))

private theorem forwardArrowNotIso : ¬ IsIso forwardArrow.{u} := by
  intro h
  let _ : IsIso forwardArrow.{u} := h
  have impossible : (1 : Fin 2) ≤ 0 := leOfHom (AsSmall.down.map (inv forwardArrow))
  exact (by decide : ¬ ((1 : Fin 2) ≤ 0)) impossible

example : SSet.Quasicategory directedNerve.{u} := inferInstance

example : IsFibrant (JoyalSSet.ofSSet.obj directedNerve.{u}) :=
  (JoyalSSet.isFibrant_iff_quasicategory _).mpr inferInstance

example : ¬ SSet.KanComplex directedNerve.{u} := by
  intro h
  let _ : SSet.KanComplex directedNerve.{u} := h
  have inCore : ComposableArrows.mk₁ forwardArrow.{u} ∈
      (SSet.core directedNerve).obj (op ⦋1⦌) := by
    rw [SSet.core_eq_top_of_kanComplex]
    trivial
  exact forwardArrowNotIso ((SSet.mem_core_nerve_mk₁_iff forwardArrow).mp inCore)

end MathlibExtTest.AtlasJoyalModelAPI
