/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.Algebra.Category.ModuleCat.TensorBifunctor

/-!
# Coefficient tensor functors for Koszul complexes

The coefficient module is the first factor of the module tensor bifunctor,
and the variable term is the second factor. Their carrier universes are
independent. When the universes coincide, the functor and the natural maps
agree with Mathlib's tensoring-left construction.
-/

@[expose] public section

noncomputable section
set_option autoImplicit false

open CategoryTheory CategoryTheory.MonoidalCategory

universe u v

namespace KoszulComplex

variable (R : Type u) [CommRing R]

/-- Tensor an original module with a coefficient module in an independent
universe, using the original tensor objects and linear maps. -/
def coefficientTensorFunctor (M : ModuleCat.{v} R) :
    ModuleCat.{u} R ⥤ ModuleCat.{max u v} R :=
  (ModuleCat.tensorBifunctorAt.{u, v, u} R).obj M

instance coefficientTensorFunctor_additive (M : ModuleCat.{v} R) :
    (coefficientTensorFunctor R M).Additive :=
  inferInstanceAs (((ModuleCat.tensorBifunctorAt.{u, v, u} R).obj M).Additive)

/-- Original coefficient maps act naturally on the same mixed-universe
tensor functors. -/
def coefficientTensoringLeft :
    ModuleCat.{v} R ⥤ (ModuleCat.{u} R ⥤ ModuleCat.{max u v} R) :=
  ModuleCat.tensorBifunctorAt.{u, v, u} R

instance coefficientTensoringLeft_obj_additive (M : ModuleCat.{v} R) :
    ((coefficientTensoringLeft R).obj M).Additive :=
  inferInstanceAs ((coefficientTensorFunctor R M).Additive)

/-- At the original universe, the mixed-universe fixed tensor functor is
literally Mathlib's original tensoring-left object. -/
theorem coefficientTensorFunctor_sameUniverse (M : ModuleCat.{u} R) :
    coefficientTensorFunctor R M = (tensoringLeft (ModuleCat.{u} R)).obj M := by
  fapply CategoryTheory.Functor.hext
  · intro N
    rfl
  · intro N N' g
    apply heq_of_eq
    apply ModuleCat.hom_ext
    change TensorProduct.map LinearMap.id g.hom = g.hom.lTensor M
    rfl

/-- At the original universe, every original coefficient map uses exactly
the original tensoring-left natural transformation. -/
theorem coefficientTensoringLeft_sameUniverse :
    coefficientTensoringLeft.{u, u} R = tensoringLeft (ModuleCat.{u} R) := by
  fapply CategoryTheory.Functor.hext
  · intro M
    exact coefficientTensorFunctor_sameUniverse R M
  · intro M N f
    apply heq_of_eq
    apply NatTrans.ext
    funext K
    apply ModuleCat.hom_ext
    change TensorProduct.map f.hom LinearMap.id = f.hom.rTensor K
    rfl

end KoszulComplex
