/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.CategoryTheory.MorphismProperty.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Composition
public import Mathlib.CategoryTheory.NatIso

/-!
# Functor-category closure for morphism properties

For `W : MorphismProperty C` and a category `J`, the pointwise property
`W.functorCategory J` inherits `IsMultiplicative`,
`HasTwoOutOfThreeProperty`, and `RespectsIso` from `W`. Proofs are pointwise
in `j : J`, using functor-category identity/composition laws with
`NatTrans.isIso_iff_isIso_app` and `RespectsIso.precomp/postcomp`.
-/

@[expose] public section

universe v u v' u'

namespace CategoryTheory.MorphismProperty

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C)

/-- Pointwise multiplicative closure: if `W` is multiplicative, so is
`W.functorCategory J`. -/
theorem IsMultiplicative.functorCategory [IsMultiplicative W]
    (J : Type u') [Category.{v'} J] :
    IsMultiplicative (W.functorCategory J) where
  id_mem X j := W.id_mem (X.obj j)
  comp_mem f g hf hg j := W.comp_mem (f.app j) (g.app j) (hf j) (hg j)

/-- Global multiplicative closure for pointwise functor-category properties. -/
instance [IsMultiplicative W] (J : Type u') [Category.{v'} J] :
    IsMultiplicative (W.functorCategory J) :=
  IsMultiplicative.functorCategory W J

/-- Pointwise two-out-of-three closure: if `W` has two-out-of-three, so does
`W.functorCategory J`. -/
theorem HasTwoOutOfThreeProperty.functorCategory
    [W.HasTwoOutOfThreeProperty] (J : Type u') [Category.{v'} J] :
    (W.functorCategory J).HasTwoOutOfThreeProperty where
  comp_mem f g hf hg j := W.comp_mem (f.app j) (g.app j) (hf j) (hg j)
  of_postcomp f g hg hfg j :=
    W.of_postcomp (f.app j) (g.app j) (hg j) (hfg j)
  of_precomp f g hf hfg j :=
    W.of_precomp (f.app j) (g.app j) (hf j) (hfg j)

/-- Global two-out-of-three closure for pointwise functor-category
properties. -/
instance [W.HasTwoOutOfThreeProperty] (J : Type u') [Category.{v'} J] :
    (W.functorCategory J).HasTwoOutOfThreeProperty :=
  HasTwoOutOfThreeProperty.functorCategory W J

/-- Pointwise iso closure: if `W` respects isos, so does `W.functorCategory J`. -/
theorem RespectsIso.functorCategory [W.RespectsIso]
    (J : Type u') [Category.{v'} J] :
    (W.functorCategory J).RespectsIso where
  precomp e he f hf j := by
    have := (NatTrans.isIso_iff_isIso_app _).mp he j
    exact RespectsIso.precomp W _ _ (hf j)
  postcomp e he f hf j := by
    have := (NatTrans.isIso_iff_isIso_app _).mp he j
    exact RespectsIso.postcomp W _ _ (hf j)

/-- Global iso closure for pointwise functor-category properties. -/
instance [W.RespectsIso] (J : Type u') [Category.{v'} J] :
    (W.functorCategory J).RespectsIso :=
  RespectsIso.functorCategory W J

end CategoryTheory.MorphismProperty
