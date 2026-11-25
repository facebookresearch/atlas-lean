/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.LinearAlgebra.ExteriorAlgebra.PrimitiveEquation
public import Mathlib.RingTheory.Coalgebra.Hom

/-!
# Actual exterior coalgebra maps and primitive transport

Every actual linear map induces a native coalgebra homomorphism for the
constructed exterior coproduct. Its counit and coproduct laws are earned
from the existing naturality proofs. The multiplicative exterior-map unit
law supplies the primitive endpoints. No coalgebra-map or primitive-map
certificate is a caller parameter. Ring and module universes are independent.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w x

namespace ExteriorAlgebra

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- The actual exterior functor map, bundled as a native coalgebra homomorphism. -/
def coalgMap (f : M →ₗ[R] N) : ExteriorAlgebra R M →ₗc[R] ExteriorAlgebra R N where
  toLinearMap := (map f).toLinearMap
  counit_comp := by
    apply LinearMap.ext
    intro a
    exact augmentation_map R M f a
  map_comp_comul := by
    apply LinearMap.ext
    intro a
    exact coproduct_naturality R M f a

@[simp]
theorem coalgMap_apply (f : M →ₗ[R] N) (a : ExteriorAlgebra R M) :
    coalgMap R M f a = map f a := rfl

theorem coalgMap_one (f : M →ₗ[R] N) : coalgMap R M f (1 : ExteriorAlgebra R M) = 1 :=
  map_one (map f)

@[simp]
theorem coalgMap_id :
    coalgMap R M (LinearMap.id : M →ₗ[R] M) = CoalgHom.id R (ExteriorAlgebra R M) := by
  apply CoalgHom.ext
  intro a
  change map (LinearMap.id : M →ₗ[R] M) a = a
  simp only [map_id, AlgHom.id_apply]

/-- The actual native exterior coalgebra maps compose by the actual linear maps. -/
theorem coalgMap_comp {P : Type x} [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    (coalgMap R N g).comp (coalgMap R M f) = coalgMap R M (g.comp f) := by
  apply CoalgHom.ext
  intro a
  change map g (map f a) = map (g.comp f) a
  exact AlgHom.congr_fun (map_comp_map f g) a

/-- The actual reduced primitive equation is natural under arbitrary actual linear maps. -/
theorem primitiveEquation_map (f : M →ₗ[R] N) (a : ExteriorAlgebra R M) :
    primitiveEquation R N (map f a) =
      TensorProduct.map (map f).toLinearMap (map f).toLinearMap (primitiveEquation R M a) := by
  simp only [primitiveEquation_apply, map_sub, map_add, TensorProduct.map_tmul,
    AlgHom.toLinearMap_apply, map_one]
  rw [coproduct_naturality R M f a]

/-- Actual exterior coalgebra transport preserves native primitives, with its unit endpoints earned. -/
theorem map_isPrimitive (f : M →ₗ[R] N) (a : ExteriorAlgebra R M)
    (ha : Coalgebra.IsSkewPrimitiveElem R (1 : ExteriorAlgebra R M) 1 a) :
    Coalgebra.IsSkewPrimitiveElem R (1 : ExteriorAlgebra R N) 1 (map f a) := by
  have h := Coalgebra.IsSkewPrimitiveElem.map (coalgMap R M f) ha
  simpa only [coalgMap_apply, map_one] using h

end ExteriorAlgebra
