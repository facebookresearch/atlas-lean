/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.ModelCategory.PointedSmash

/-! Owner tests for the generic Under smash-model transfer. -/

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory CategoryTheory.Functor
open CategoryTheory.MorphismProperty HomotopicalAlgebra
open scoped MonoidalCategory

namespace MathlibExtTest.AlgebraicTopology.ModelCategory.PointedSmash

section PublicSurface

#check HomotopicalAlgebra.isCofibrant_under_smashUnit
#check HomotopicalAlgebra.underSmashIsClosedSymmetricMonoidalModelCategory
#check @HomotopicalAlgebra.isCofibrant_under_smashUnit.{0, 0}
#check @HomotopicalAlgebra.isCofibrant_under_smashUnit.{1, 1}
#check @HomotopicalAlgebra.isCofibrant_under_smashUnit.{0, 1}
#check @HomotopicalAlgebra.isCofibrant_under_smashUnit.{1, 0}
#check @HomotopicalAlgebra.underSmashIsClosedSymmetricMonoidalModelCategory.{0, 0}
#check @HomotopicalAlgebra.underSmashIsClosedSymmetricMonoidalModelCategory.{1, 1}
#check @HomotopicalAlgebra.underSmashIsClosedSymmetricMonoidalModelCategory.{0, 1}
#check @HomotopicalAlgebra.underSmashIsClosedSymmetricMonoidalModelCategory.{1, 0}

end PublicSurface

variable {C : Type u} [Category.{v} C] [ModelCategory C]

section RightOrthogonals

/-- Independent owner reconstruction of the free-cofibration right class. -/
example (P : C) :
    ((cofibrations C).strictMap (Under.costar P)).rlp =
      trivialFibrations (Under P) := by
  rw [strictMap_rlp_eq_inverseImage_rlp _ (Under.costar P)
    (Under.forget P) (Under.costarAdjForget P), cofibrations_rlp]
  rw [← MorphismProperty.under_eq_inverseImage,
    ← trivialFibrations_under_eq]

/-- Independent owner reconstruction of the free-trivial-cofibration
right class. -/
example (P : C) :
    ((trivialCofibrations C).strictMap (Under.costar P)).rlp =
      fibrations (Under P) := by
  rw [strictMap_rlp_eq_inverseImage_rlp _ (Under.costar P)
    (Under.forget P) (Under.costarAdjForget P),
    trivialCofibrations_rlp]
  rw [← MorphismProperty.under_eq_inverseImage, ← fibrations_under_def]

end RightOrthogonals

section MonoidalTransfer

variable [CartesianMonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C] [IsClosedSymmetricMonoidalModelCategory C]
variable (P : C) (hP : IsTerminal P)

/-- The terminal point remains arbitrary; it is not definitionally forced
to be the cartesian tensor unit. -/
example : True := by
  fail_if_success
    have _ : P = 𝟙_ C := rfl
  trivial

/-- Owner reconstruction of the strict cofibration/cofibration leaf. -/
private theorem ownerFreeCofibrationCofibration
    {A B K L : Under P} (i : A ⟶ B)
    (hi : ((cofibrations C).strictMap (Under.costar P)) i)
    (j : K ⟶ L)
    (hj : ((cofibrations C).strictMap (Under.costar P)) j) :
    letI := CategoryTheory.Pointed.smashMonoidalCategory P hP
    ((cofibrations C).strictMap (Under.costar P)).rlp.llp
      ((Arrow.mk i □ Arrow.mk j).hom) := by
  let _ : MonoidalCategory (Under P) :=
    CategoryTheory.Pointed.smashMonoidalCategory P hP
  let _ : (Under.costar P).IsLeftAdjoint :=
    (Under.costarAdjForget P).isLeftAdjoint
  let _ : (Under.costar P).Monoidal :=
    (CategoryTheory.Pointed.costarCoreMonoidal P hP).toMonoidal
  cases hi with
  | @map X Y f hi =>
    cases hj with
    | @map W Z g hj =>
      let e := Functor.mapArrowPushoutProductIso (Under.costar P) f g
      have homSquare := e.hom.w
      have invSquare := e.inv.w
      have hSource : cofibrations C
          ((Arrow.mk f □ Arrow.mk g).hom) :=
        IsClosedSymmetricMonoidalModelCategory.cofibration_pushoutProduct
          f g hi hj
      have hMapped : ((cofibrations C).strictMap (Under.costar P))
          ((Under.costar P).map ((Arrow.mk f □ Arrow.mk g).hom)) :=
        (cofibrations C).map_mem_strictMap (Under.costar P) _ hSource
      have hOrth :=
        ((cofibrations C).strictMap (Under.costar P)).le_llp_rlp
          _ hMapped
      clear homSquare invSquare
      exact
        (((cofibrations C).strictMap (Under.costar P)).rlp.llp.arrow_iso_iff
          e).mp hOrth

/-- Owner reconstruction of the strict left-trivial leaf. -/
private theorem ownerFreeTrivialCofibrationLeft
    {A B K L : Under P} (i : A ⟶ B)
    (hi : ((trivialCofibrations C).strictMap (Under.costar P)) i)
    (j : K ⟶ L)
    (hj : ((cofibrations C).strictMap (Under.costar P)) j) :
    letI := CategoryTheory.Pointed.smashMonoidalCategory P hP
    ((trivialCofibrations C).strictMap (Under.costar P)).rlp.llp
      ((Arrow.mk i □ Arrow.mk j).hom) := by
  let _ : MonoidalCategory (Under P) :=
    CategoryTheory.Pointed.smashMonoidalCategory P hP
  let _ : (Under.costar P).IsLeftAdjoint :=
    (Under.costarAdjForget P).isLeftAdjoint
  let _ : (Under.costar P).Monoidal :=
    (CategoryTheory.Pointed.costarCoreMonoidal P hP).toMonoidal
  cases hi with
  | @map X Y f hi =>
    cases hj with
    | @map W Z g hj =>
      have hSource : trivialCofibrations C
          ((Arrow.mk f □ Arrow.mk g).hom) :=
        IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_left
          f g hi hj
      have hMapped :
          ((trivialCofibrations C).strictMap (Under.costar P))
            ((Under.costar P).map ((Arrow.mk f □ Arrow.mk g).hom)) :=
        (trivialCofibrations C).map_mem_strictMap
          (Under.costar P) _ hSource
      have hOrth :=
        ((trivialCofibrations C).strictMap
          (Under.costar P)).le_llp_rlp _ hMapped
      exact
        (((trivialCofibrations C).strictMap
          (Under.costar P)).rlp.llp.arrow_iso_iff
            (Functor.mapArrowPushoutProductIso (Under.costar P) f g)).mp
              hOrth

/-- Owner reconstruction of the distinct strict right-trivial leaf. -/
private theorem ownerFreeTrivialCofibrationRight
    {A B K L : Under P} (i : A ⟶ B)
    (hi : ((cofibrations C).strictMap (Under.costar P)) i)
    (j : K ⟶ L)
    (hj : ((trivialCofibrations C).strictMap (Under.costar P)) j) :
    letI := CategoryTheory.Pointed.smashMonoidalCategory P hP
    ((trivialCofibrations C).strictMap (Under.costar P)).rlp.llp
      ((Arrow.mk i □ Arrow.mk j).hom) := by
  let _ : MonoidalCategory (Under P) :=
    CategoryTheory.Pointed.smashMonoidalCategory P hP
  let _ : (Under.costar P).IsLeftAdjoint :=
    (Under.costarAdjForget P).isLeftAdjoint
  let _ : (Under.costar P).Monoidal :=
    (CategoryTheory.Pointed.costarCoreMonoidal P hP).toMonoidal
  cases hi with
  | @map X Y f hi =>
    cases hj with
    | @map W Z g hj =>
      have hSource : trivialCofibrations C
          ((Arrow.mk f □ Arrow.mk g).hom) :=
        IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_right
          f g hi hj
      have hMapped :
          ((trivialCofibrations C).strictMap (Under.costar P))
            ((Under.costar P).map ((Arrow.mk f □ Arrow.mk g).hom)) :=
        (trivialCofibrations C).map_mem_strictMap
          (Under.costar P) _ hSource
      have hOrth :=
        ((trivialCofibrations C).strictMap
          (Under.costar P)).le_llp_rlp _ hMapped
      exact
        (((trivialCofibrations C).strictMap
          (Under.costar P)).rlp.llp.arrow_iso_iff
            (Functor.mapArrowPushoutProductIso (Under.costar P) f g)).mp
              hOrth

/-- The reviewed mapped-box comparison has one load-bearing orientation. -/
example {A B K L : C} (_i : A ⟶ B) (_j : K ⟶ L) : True := by
  let _ : MonoidalCategory (Under P) :=
    CategoryTheory.Pointed.smashMonoidalCategory P hP
  let _ : (Under.costar P).IsLeftAdjoint :=
    (Under.costarAdjForget P).isLeftAdjoint
  let _ : (Under.costar P).Monoidal :=
    (CategoryTheory.Pointed.costarCoreMonoidal P hP).toMonoidal
  fail_if_success
    have _ :
        Arrow.mk ((Under.costar P).map _i) □
            Arrow.mk ((Under.costar P).map _j) ≅
          (Under.costar P).mapArrow.obj (Arrow.mk _i □ Arrow.mk _j) :=
      Functor.mapArrowPushoutProductIso (Under.costar P) _i _j
  trivial

/-- The three strict owner leaves elaborate together and retain their
ordered class triples. -/
example :
    (∀ {A B K L : Under P} (i : A ⟶ B),
      ((cofibrations C).strictMap (Under.costar P)) i →
      ∀ (j : K ⟶ L),
      ((cofibrations C).strictMap (Under.costar P)) j →
      letI := CategoryTheory.Pointed.smashMonoidalCategory P hP
      ((cofibrations C).strictMap (Under.costar P)).rlp.llp
        ((Arrow.mk i □ Arrow.mk j).hom)) ∧
    (∀ {A B K L : Under P} (i : A ⟶ B),
      ((trivialCofibrations C).strictMap (Under.costar P)) i →
      ∀ (j : K ⟶ L),
      ((cofibrations C).strictMap (Under.costar P)) j →
      letI := CategoryTheory.Pointed.smashMonoidalCategory P hP
      ((trivialCofibrations C).strictMap (Under.costar P)).rlp.llp
        ((Arrow.mk i □ Arrow.mk j).hom)) ∧
    (∀ {A B K L : Under P} (i : A ⟶ B),
      ((cofibrations C).strictMap (Under.costar P)) i →
      ∀ (j : K ⟶ L),
      ((trivialCofibrations C).strictMap (Under.costar P)) j →
      letI := CategoryTheory.Pointed.smashMonoidalCategory P hP
      ((trivialCofibrations C).strictMap (Under.costar P)).rlp.llp
        ((Arrow.mk i □ Arrow.mk j).hom)) :=
  ⟨ownerFreeCofibrationCofibration P hP,
    ownerFreeTrivialCofibrationLeft P hP,
    ownerFreeTrivialCofibrationRight P hP⟩

section CofibrantPoint

variable [IsCofibrant P]

/-- Unit cofibrancy is independently reconstructed from the named Quillen
adjunction, not from terminality. -/
example :
    letI := CategoryTheory.Pointed.smashMonoidalCategory P hP
    IsCofibrant (𝟙_ (Under P)) := by
  let _ : MonoidalCategory (Under P) :=
    CategoryTheory.Pointed.smashMonoidalCategory P hP
  let _ : CategoryTheory.Adjunction.IsQuillenAdjunction
      (Under.costarAdjForget P) :=
    Under.costarAdjForget_isQuillenAdjunction P
  change IsCofibrant ((Under.costar P).obj P)
  exact
    (CategoryTheory.Adjunction.IsQuillenAdjunction.preservesCofibrantObjects
      (adj := Under.costarAdjForget P)).isCofibrant
        (inferInstance : IsCofibrant P)

example :
    letI := CategoryTheory.Pointed.smashMonoidalCategory P hP
    IsCofibrant (𝟙_ (Under P)) :=
  HomotopicalAlgebra.isCofibrant_under_smashUnit P hP

example :
    letI := CategoryTheory.Pointed.smashMonoidalCategory P hP
    letI := CategoryTheory.Pointed.smashSymmetricCategory P hP
    letI := CategoryTheory.Pointed.smashMonoidalClosed P hP
    IsClosedSymmetricMonoidalModelCategory (Under P) :=
  HomotopicalAlgebra.underSmashIsClosedSymmetricMonoidalModelCategory P hP

/-- Both ordered trivial clauses are independently required by the final
four-field constructor. -/
example : True := by
  let _ : MonoidalCategory (Under P) :=
    CategoryTheory.Pointed.smashMonoidalCategory P hP
  let _ : SymmetricCategory (Under P) :=
    CategoryTheory.Pointed.smashSymmetricCategory P hP
  let _ : MonoidalClosed (Under P) :=
    CategoryTheory.Pointed.smashMonoidalClosed P hP
  let h : IsClosedSymmetricMonoidalModelCategory (Under P) :=
    HomotopicalAlgebra.underSmashIsClosedSymmetricMonoidalModelCategory P hP
  fail_if_success
    exact (show IsClosedSymmetricMonoidalModelCategory (Under P) from
      { cofibration_pushoutProduct := h.cofibration_pushoutProduct
        trivial_pushoutProduct_left := h.trivial_pushoutProduct_left
        unit_axiom := h.unit_axiom })
  fail_if_success
    exact (show IsClosedSymmetricMonoidalModelCategory (Under P) from
      { cofibration_pushoutProduct := h.cofibration_pushoutProduct
        trivial_pushoutProduct_right := h.trivial_pushoutProduct_right
        unit_axiom := h.unit_axiom })
  trivial

section OrderedPublicClauses

example {A B K L : Under P} (i : A ⟶ B) (j : K ⟶ L)
    (hi : cofibrations (Under P) i) (hj : cofibrations (Under P) j) :
    letI := CategoryTheory.Pointed.smashMonoidalCategory P hP
    cofibrations (Under P) ((Arrow.mk i □ Arrow.mk j).hom) := by
  let _ : MonoidalCategory (Under P) :=
    CategoryTheory.Pointed.smashMonoidalCategory P hP
  let _ : SymmetricCategory (Under P) :=
    CategoryTheory.Pointed.smashSymmetricCategory P hP
  let _ : MonoidalClosed (Under P) :=
    CategoryTheory.Pointed.smashMonoidalClosed P hP
  let _ : IsClosedSymmetricMonoidalModelCategory (Under P) :=
    HomotopicalAlgebra.underSmashIsClosedSymmetricMonoidalModelCategory P hP
  exact IsClosedSymmetricMonoidalModelCategory.cofibration_pushoutProduct
    i j hi hj

example {A B K L : Under P} (i : A ⟶ B) (j : K ⟶ L)
    (hi : trivialCofibrations (Under P) i)
    (hj : cofibrations (Under P) j) :
    letI := CategoryTheory.Pointed.smashMonoidalCategory P hP
    trivialCofibrations (Under P) ((Arrow.mk i □ Arrow.mk j).hom) := by
  let _ : MonoidalCategory (Under P) :=
    CategoryTheory.Pointed.smashMonoidalCategory P hP
  let _ : SymmetricCategory (Under P) :=
    CategoryTheory.Pointed.smashSymmetricCategory P hP
  let _ : MonoidalClosed (Under P) :=
    CategoryTheory.Pointed.smashMonoidalClosed P hP
  let _ : IsClosedSymmetricMonoidalModelCategory (Under P) :=
    HomotopicalAlgebra.underSmashIsClosedSymmetricMonoidalModelCategory P hP
  exact IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_left
    i j hi hj

example {A B K L : Under P} (i : A ⟶ B) (j : K ⟶ L)
    (hi : cofibrations (Under P) i)
    (hj : trivialCofibrations (Under P) j) :
    letI := CategoryTheory.Pointed.smashMonoidalCategory P hP
    trivialCofibrations (Under P) ((Arrow.mk i □ Arrow.mk j).hom) := by
  let _ : MonoidalCategory (Under P) :=
    CategoryTheory.Pointed.smashMonoidalCategory P hP
  let _ : SymmetricCategory (Under P) :=
    CategoryTheory.Pointed.smashSymmetricCategory P hP
  let _ : MonoidalClosed (Under P) :=
    CategoryTheory.Pointed.smashMonoidalClosed P hP
  let _ : IsClosedSymmetricMonoidalModelCategory (Under P) :=
    HomotopicalAlgebra.underSmashIsClosedSymmetricMonoidalModelCategory P hP
  exact IsClosedSymmetricMonoidalModelCategory.trivial_pushoutProduct_right
    i j hi hj

example :
    letI := CategoryTheory.Pointed.smashMonoidalCategory P hP
    letI := CategoryTheory.Pointed.smashSymmetricCategory P hP
    letI := CategoryTheory.Pointed.smashMonoidalClosed P hP
    Nonempty (MonoidalUnitAxiomWitness (Under P)) := by
  let _ : MonoidalCategory (Under P) :=
    CategoryTheory.Pointed.smashMonoidalCategory P hP
  let _ : SymmetricCategory (Under P) :=
    CategoryTheory.Pointed.smashSymmetricCategory P hP
  let _ : MonoidalClosed (Under P) :=
    CategoryTheory.Pointed.smashMonoidalClosed P hP
  let _ : IsClosedSymmetricMonoidalModelCategory (Under P) :=
    HomotopicalAlgebra.underSmashIsClosedSymmetricMonoidalModelCategory P hP
  exact IsClosedSymmetricMonoidalModelCategory.unit_axiom

end OrderedPublicClauses

end CofibrantPoint

/-- Importing the provider installs none of its factory values globally. -/
example : True := by
  fail_if_success
    let _ : MonoidalCategory (Under P) := inferInstance
  fail_if_success
    let _ : IsCofibrant P := inferInstance
  fail_if_success
    have _ :
        letI := CategoryTheory.Pointed.smashMonoidalCategory P hP
        IsCofibrant (𝟙_ (Under P)) :=
      HomotopicalAlgebra.isCofibrant_under_smashUnit P hP
  trivial

end MonoidalTransfer

#print axioms HomotopicalAlgebra.isCofibrant_under_smashUnit
#print axioms HomotopicalAlgebra.underSmashIsClosedSymmetricMonoidalModelCategory

end MathlibExtTest.AlgebraicTopology.ModelCategory.PointedSmash
