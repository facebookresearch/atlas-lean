/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.ModelCategory.Monoidal
public import MathlibExt.AlgebraicTopology.ModelCategory.UnderOverProperQuillen
public import MathlibExt.CategoryTheory.Monoidal.Pointed.Closed
public import MathlibExt.CategoryTheory.Monoidal.Pointed.Free
public import MathlibExt.CategoryTheory.Monoidal.PushoutProductFunctor
public import MathlibExt.CategoryTheory.MorphismProperty.PushoutProduct

/-!
# The smash-product model structure on an Under category

For a cofibrant terminal object `P` in a cartesian closed symmetric
monoidal model category, this file transfers the three ordered
pushout-product clauses to `Under P` with its generic smash product.

The proof first treats literal images under `Under.costar P`.  The lifting
adjunction identifies their right orthogonals with the created Under
fibration classes, and double orthogonality extends the strict-image
results to arbitrary cofibrations.  The actual smash unit is cofibrant
because the free-under-object functor is left Quillen.

The two exported declarations are factory values.  No generic monoidal,
symmetric, closed, or monoidal-model instance is installed here.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe v u

open CategoryTheory Limits MonoidalCategory CategoryTheory.Functor
open CategoryTheory.MorphismProperty
open scoped MonoidalCategory

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C]

/-!
## Right orthogonals of strict free images
-/

/-- The right orthogonal of literal free images of base cofibrations is
the class of trivial fibrations in the created Under model. -/
private theorem underFreeCofibration_rlp_eq (P : C) :
    ((cofibrations C).strictMap (Under.costar P)).rlp =
      trivialFibrations (Under P) := by
  rw [strictMap_rlp_eq_inverseImage_rlp _ (Under.costar P)
    (Under.forget P) (Under.costarAdjForget P), cofibrations_rlp]
  rw [← MorphismProperty.under_eq_inverseImage,
    ← trivialFibrations_under_eq]

/-- The right orthogonal of literal free images of base trivial
cofibrations is the class of fibrations in the created Under model. -/
private theorem underFreeTrivialCofibration_rlp_eq (P : C) :
    ((trivialCofibrations C).strictMap (Under.costar P)).rlp =
      fibrations (Under P) := by
  rw [strictMap_rlp_eq_inverseImage_rlp _ (Under.costar P)
    (Under.forget P) (Under.costarAdjForget P),
    trivialCofibrations_rlp]
  rw [← MorphismProperty.under_eq_inverseImage, ← fibrations_under_def]

section

variable [CartesianMonoidalCategory C] [SymmetricCategory C]
  [MonoidalClosed C]

/-!
## Three ordered strict-image leaves

Each result maps the corresponding base pushout-product through the
strong monoidal left adjoint and crosses the reviewed Arrow isomorphism in
the mapped-box-to-box-of-maps direction.
-/

/-- The smash box of two literal free cofibrations belongs to the double
left orthogonal of the free cofibration class. -/
private theorem underFreeCofibrationCofibration
    [IsClosedSymmetricMonoidalModelCategory C]
    (P : C) (hP : IsTerminal P)
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
      exact
        (((cofibrations C).strictMap (Under.costar P)).rlp.llp.arrow_iso_iff
          (Functor.mapArrowPushoutProductIso (Under.costar P) f g)).mp
            hOrth

/-- The smash box of a literal free trivial cofibration on the left and a
literal free cofibration on the right belongs to the corresponding
trivial double orthogonal. -/
private theorem underFreeTrivialCofibrationLeft
    [IsClosedSymmetricMonoidalModelCategory C]
    (P : C) (hP : IsTerminal P)
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

/-- The smash box of a literal free cofibration on the left and a literal
free trivial cofibration on the right belongs to the corresponding
trivial double orthogonal. -/
private theorem underFreeTrivialCofibrationRight
    [IsClosedSymmetricMonoidalModelCategory C]
    (P : C) (hP : IsTerminal P)
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

/-!
## Double-orthogonality extension
-/

/-- The smash pushout-product of two arbitrary Under cofibrations is an
Under cofibration. -/
private theorem underCofibrationPushoutProduct
    [IsClosedSymmetricMonoidalModelCategory C]
    (P : C) (hP : IsTerminal P)
    {A B K L : Under P} (i : A ⟶ B) (j : K ⟶ L)
    (hi : cofibrations (Under P) i)
    (hj : cofibrations (Under P) j) :
    letI := CategoryTheory.Pointed.smashMonoidalCategory P hP
    cofibrations (Under P) ((Arrow.mk i □ Arrow.mk j).hom) := by
  let _ : MonoidalCategory (Under P) :=
    CategoryTheory.Pointed.smashMonoidalCategory P hP
  let _ : SymmetricCategory (Under P) :=
    CategoryTheory.Pointed.smashSymmetricCategory P hP
  let _ : MonoidalClosed (Under P) :=
    CategoryTheory.Pointed.smashMonoidalClosed P hP
  have hi' :
      ((cofibrations C).strictMap (Under.costar P)).rlp.llp i := by
    rw [underFreeCofibration_rlp_eq, trivialFibrations_llp]
    exact hi
  have hj' :
      ((cofibrations C).strictMap (Under.costar P)).rlp.llp j := by
    rw [underFreeCofibration_rlp_eq, trivialFibrations_llp]
    exact hj
  have h := pushoutProduct_mem_rlp_llp
    ((cofibrations C).strictMap (Under.costar P))
    ((cofibrations C).strictMap (Under.costar P))
    ((cofibrations C).strictMap (Under.costar P))
    (fun ⦃X Y W Z⦄ a ha b hb =>
      underFreeCofibrationCofibration P hP a ha b hb) hi' hj'
  rwa [underFreeCofibration_rlp_eq, trivialFibrations_llp] at h

/-- The smash pushout-product is an Under trivial cofibration when its left
factor is trivial and its right factor is a cofibration. -/
private theorem underTrivialPushoutProductLeft
    [IsClosedSymmetricMonoidalModelCategory C]
    (P : C) (hP : IsTerminal P)
    {A B K L : Under P} (i : A ⟶ B) (j : K ⟶ L)
    (hi : trivialCofibrations (Under P) i)
    (hj : cofibrations (Under P) j) :
    letI := CategoryTheory.Pointed.smashMonoidalCategory P hP
    trivialCofibrations (Under P)
      ((Arrow.mk i □ Arrow.mk j).hom) := by
  let _ : MonoidalCategory (Under P) :=
    CategoryTheory.Pointed.smashMonoidalCategory P hP
  let _ : SymmetricCategory (Under P) :=
    CategoryTheory.Pointed.smashSymmetricCategory P hP
  let _ : MonoidalClosed (Under P) :=
    CategoryTheory.Pointed.smashMonoidalClosed P hP
  have hi' :
      ((trivialCofibrations C).strictMap
        (Under.costar P)).rlp.llp i := by
    rw [underFreeTrivialCofibration_rlp_eq, fibrations_llp]
    exact hi
  have hj' :
      ((cofibrations C).strictMap (Under.costar P)).rlp.llp j := by
    rw [underFreeCofibration_rlp_eq, trivialFibrations_llp]
    exact hj
  have h := pushoutProduct_mem_rlp_llp
    ((trivialCofibrations C).strictMap (Under.costar P))
    ((cofibrations C).strictMap (Under.costar P))
    ((trivialCofibrations C).strictMap (Under.costar P))
    (fun ⦃X Y W Z⦄ a ha b hb =>
      underFreeTrivialCofibrationLeft P hP a ha b hb) hi' hj'
  rwa [underFreeTrivialCofibration_rlp_eq, fibrations_llp] at h

/-- The smash pushout-product is an Under trivial cofibration when its left
factor is a cofibration and its right factor is trivial. -/
private theorem underTrivialPushoutProductRight
    [IsClosedSymmetricMonoidalModelCategory C]
    (P : C) (hP : IsTerminal P)
    {A B K L : Under P} (i : A ⟶ B) (j : K ⟶ L)
    (hi : cofibrations (Under P) i)
    (hj : trivialCofibrations (Under P) j) :
    letI := CategoryTheory.Pointed.smashMonoidalCategory P hP
    trivialCofibrations (Under P)
      ((Arrow.mk i □ Arrow.mk j).hom) := by
  let _ : MonoidalCategory (Under P) :=
    CategoryTheory.Pointed.smashMonoidalCategory P hP
  let _ : SymmetricCategory (Under P) :=
    CategoryTheory.Pointed.smashSymmetricCategory P hP
  let _ : MonoidalClosed (Under P) :=
    CategoryTheory.Pointed.smashMonoidalClosed P hP
  have hi' :
      ((cofibrations C).strictMap (Under.costar P)).rlp.llp i := by
    rw [underFreeCofibration_rlp_eq, trivialFibrations_llp]
    exact hi
  have hj' :
      ((trivialCofibrations C).strictMap
        (Under.costar P)).rlp.llp j := by
    rw [underFreeTrivialCofibration_rlp_eq, fibrations_llp]
    exact hj
  have h := pushoutProduct_mem_rlp_llp
    ((cofibrations C).strictMap (Under.costar P))
    ((trivialCofibrations C).strictMap (Under.costar P))
    ((trivialCofibrations C).strictMap (Under.costar P))
    (fun ⦃X Y W Z⦄ a ha b hb =>
      underFreeTrivialCofibrationRight P hP a ha b hb) hi' hj'
  rwa [underFreeTrivialCofibration_rlp_eq, fibrations_llp] at h

/-!
## The actual unit and the three-clause factory
-/

/-- If the chosen terminal object is cofibrant, then the actual unit of
the generic smash product on `Under P` is cofibrant. -/
theorem isCofibrant_under_smashUnit (P : C) (hP : IsTerminal P)
    [IsCofibrant P] :
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

/-- The generic smash product on pointed objects under a cofibrant terminal
object satisfies the closed symmetric monoidal model axioms.

This is a factory value: it installs no monoidal-model instance. -/
theorem underSmashIsClosedSymmetricMonoidalModelCategory
    [IsClosedSymmetricMonoidalModelCategory C]
    (P : C) (hP : IsTerminal P) [IsCofibrant P] :
    letI := CategoryTheory.Pointed.smashMonoidalCategory P hP
    letI := CategoryTheory.Pointed.smashSymmetricCategory P hP
    letI := CategoryTheory.Pointed.smashMonoidalClosed P hP
    IsClosedSymmetricMonoidalModelCategory (Under P) := by
  let _ : MonoidalCategory (Under P) :=
    CategoryTheory.Pointed.smashMonoidalCategory P hP
  let _ : SymmetricCategory (Under P) :=
    CategoryTheory.Pointed.smashSymmetricCategory P hP
  let _ : MonoidalClosed (Under P) :=
    CategoryTheory.Pointed.smashMonoidalClosed P hP
  let _ : IsCofibrant (𝟙_ (Under P)) :=
    isCofibrant_under_smashUnit P hP
  exact isClosedSymmetricMonoidalModelCategory_of_isCofibrant_tensorUnit
    (Under P)
    (underCofibrationPushoutProduct P hP)
    (underTrivialPushoutProductLeft P hP)
    (underTrivialPushoutProductRight P hP)

end

end HomotopicalAlgebra
