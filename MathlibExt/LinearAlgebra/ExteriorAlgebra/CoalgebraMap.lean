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
# Exterior coalgebra maps and primitive equations

Let R be a commutative ring and f : M →ₗ[R] N a map of R-modules with independent carrier
universes. The exterior algebra map Λ(f) preserves the exterior coproduct and counit, so it is
a coalgebra homomorphism. These coalgebra maps compose with the underlying linear maps.

For ∆̄(a)=∆(a)−a⊗1−1⊗a, one has ∆̄(Λ(f)(a))=(Λ(f)⊗Λ(f))(∆̄(a)). Since Λ(f) preserves the unit,
it takes primitive elements to primitive elements.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

universe u v w x

namespace ExteriorAlgebra

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]
variable {N : Type w} [AddCommGroup N] [Module R N]

/-- Let R be a commutative ring, M,N R-modules, and f : M →ₗ[R] N. The exterior algebra map Λ(f)
defines a coalgebra homomorphism ExteriorAlgebra R M →ₗc[R] ExteriorAlgebra R N. Its
underlying R-linear map is the exterior algebra map, and it satisfies ε_N∘Λ(f)=ε_M and
∆_N∘Λ(f)=(Λ(f)⊗Λ(f))∘∆_M. The scalar and module carriers may occupy independent universes. -/
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

/-- For R-modules M,N,P over a commutative ring R and R-linear maps f : M → N, g : N → P, the
exterior coalgebra maps satisfy coalgMap(g) ∘ coalgMap(f) = coalgMap(g∘f). This is equality of
coalgebra homomorphisms ExteriorAlgebra R M → ExteriorAlgebra R P, with no requirement that
the three module carriers have the same universe. -/
theorem coalgMap_comp {P : Type x} [AddCommGroup P] [Module R P]
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    (coalgMap R N g).comp (coalgMap R M f) = coalgMap R M (g.comp f) := by
  apply CoalgHom.ext
  intro a
  change map g (map f a) = map (g.comp f) a
  exact AlgHom.congr_fun (map_comp_map f g) a

/-- Let R be a commutative ring, f : M →ₗ[R] N an R-linear map, and a ∈ ExteriorAlgebra R M. With
∆̄(a)=∆(a)−a⊗1−1⊗a, one has ∆̄_N(Λ(f)(a))=(Λ(f)⊗Λ(f))(∆̄_M(a)). Both tensor factors use the
R-linear map of the exterior algebra homomorphism Λ(f). -/
theorem primitiveEquation_map (f : M →ₗ[R] N) (a : ExteriorAlgebra R M) :
    primitiveEquation R N (map f a) =
      TensorProduct.map (map f).toLinearMap (map f).toLinearMap (primitiveEquation R M a) := by
  simp only [primitiveEquation_apply, map_sub, map_add, TensorProduct.map_tmul,
    AlgHom.toLinearMap_apply, map_one]
  rw [coproduct_naturality R M f a]

/-- Let R be a commutative ring, f : M →ₗ[R] N an R-linear map, and a a primitive element of
ExteriorAlgebra R M. Then Λ(f)(a) is primitive in ExteriorAlgebra R N. Here primitive means
(1,1)-skew primitive: ∆(a)=a⊗1+1⊗a with the corresponding zero-counit condition. The exterior
map preserves the coproduct, counit, and unit. -/
theorem map_isPrimitive (f : M →ₗ[R] N) (a : ExteriorAlgebra R M)
    (ha : Coalgebra.IsSkewPrimitiveElem R (1 : ExteriorAlgebra R M) 1 a) :
    Coalgebra.IsSkewPrimitiveElem R (1 : ExteriorAlgebra R N) 1 (map f a) := by
  have h := Coalgebra.IsSkewPrimitiveElem.map (coalgMap R M f) ha
  simpa only [coalgMap_apply, map_one] using h

end ExteriorAlgebra
