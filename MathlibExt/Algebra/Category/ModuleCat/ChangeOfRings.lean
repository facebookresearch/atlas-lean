/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# Additivity of extension of scalars

Extension of scalars along a commutative-ring homomorphism `f : R →+* S`
is additive.
-/

@[expose] public section

open CategoryTheory

namespace ModuleCat

universe v uR uS

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] (f : R →+* S)

/-- Extension of scalars along a commutative-ring homomorphism is additive. -/
instance extendScalars_additive :
    (ModuleCat.extendScalars f :
      ModuleCat.{v} R ⥤ ModuleCat.{max uS v} S).Additive where
  map_add := by
    intro M N g h
    apply ModuleCat.hom_ext
    simp only [ModuleCat.hom_add]
    let alg : Algebra R S := ((algebraMap S _).comp f).toAlgebra
    change @LinearMap.baseChange R S M N _ _ alg _ _ _ _ (g.hom + h.hom) =
      @LinearMap.baseChange R S M N _ _ alg _ _ _ _ g.hom +
      @LinearMap.baseChange R S M N _ _ alg _ _ _ _ h.hom
    exact @LinearMap.baseChange_add R S M N _ _ alg _ _ _ _ g.hom h.hom

end ModuleCat
