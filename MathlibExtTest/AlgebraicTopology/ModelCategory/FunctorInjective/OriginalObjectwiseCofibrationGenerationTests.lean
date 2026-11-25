/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.ModelCategory.FunctorInjective.OriginalObjectwiseCofibrationGeneration

set_option autoImplicit false
noncomputable section

universe w uD vD uC vC

open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty
open CategoryTheory.SmallObject.CompactRootBaseChange
open HomotopicalAlgebra HomotopicalAlgebra.FunctorInjective

attribute [local instance] constructionIndexWellFounded constructionIndexSuccOrder

variable {D : Type uD} [Category.{vD} D] {C : Type uC} [Category.{vC} C]
  [ModelCategory C] {kappa : Cardinal.{w}} [Fact kappa.IsRegular]
  [OrderBot kappa.ord.ToType] (d : CofibrantGenerationData C kappa)
  (kappaLP : Cardinal.{w}) [Fact kappaLP.IsRegular]
  [IsCardinalLocallyPresentable C kappaLP] (s : Functor.EssentialIndexData.{w} D C)
  (b : BoundedConstruction d kappaLP s.equivalence)

-- Consume all three equalities for the same original small family and all original maps.
example : b.family.generators.rlp.llp = (cofibrations C).functorCategory D :=
  originalGenerators_rlp_llp_eq_objectwiseCofibrations d kappaLP s b

example : b.family.generators.rlp = ((cofibrations C).functorCategory D).rlp :=
  originalGenerators_rlp_eq_objectwiseRlp d kappaLP s b

example :
    (transfiniteCompositions.{w} (coproducts.{w} b.family.generators).pushouts).retracts =
      (cofibrations C).functorCategory D :=
  originalGenerators_weakSaturation_eq_objectwiseCofibrations d kappaLP s b

-- The original source data internally constructs b; no generation equality is a premise.
example :
    let b := boundedConstruction d kappaLP s.equivalence
    b.family.generators.rlp.llp = (cofibrations C).functorCategory D := by
  exact originalGenerators_rlp_llp_eq_objectwiseCofibrations d kappaLP s
    (boundedConstruction d kappaLP s.equivalence)

example {F G : D ⥤ C} (f : F ⟶ G) :
    b.family.generators.rlp.llp f ↔ ∀ a : D, cofibrations C (f.app a) :=
  originalGenerators_generated_iff_objectwise d kappaLP s b f

-- A right-class member provides every complete original objectwise-cofibration lifting square.
example {X Y A B : D ⥤ C} (p : X ⟶ Y) (hp : b.family.generators.rlp p)
    (i : A ⟶ B) (hi : ∀ a : D, cofibrations C (i.app a)) : HasLiftingProperty i p := by
  rw [originalGenerators_rlp_eq_objectwiseRlp d kappaLP s b] at hp
  exact hp i hi

-- The full original pointwise cofibration has an actual generated native transfinite witness.
example {F G : D ⥤ C} (f : F ⟶ G) (hf : ∀ a : D, cofibrations C (f.app a)) :
    b.family.generators.rlp.llp.TransfiniteCompositionOfShape
      (ConstructionIndex (originalSliceHistoryIndex d kappaLP s b f hf)) f :=
  originalGeneratedFiltration d kappaLP s b f hf
