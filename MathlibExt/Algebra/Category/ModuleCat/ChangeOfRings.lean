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
# Extension of scalars is additive across independent ring worlds

Let R,S be commutative rings in independent worlds u_R,u_S and
f:R→S a ring homomorphism. Extension of scalars sends an R-module
X in carrier world v to S⊗[R,f]X in world max(u_S,v).
On maps it sends g to id_S⊗g, so it preserves addition of morphisms.
-/

@[expose] public section

open CategoryTheory

namespace ModuleCat

universe v uR uS

variable {R : Type uR} {S : Type uS} [CommRing R] [CommRing S] (f : R →+* S)

/-- For a homomorphism f:R→S of commutative rings,
the extension-of-scalars functor
ModuleCat^v(R)→ModuleCat^max(u_S,v)(S) is additive.
It sends g+h to id_S⊗g+id_S⊗h, with independent ring
and module-carrier worlds. -/
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
