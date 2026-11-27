/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.LinearAlgebra.ExteriorPower.ProductOne
public import MathlibExt.Algebra.Homology.KoszulComplexAnnihilation

/-!
# The Koszul differential after adjoining one coefficient

Adjoining a free rank-one summand gives a splitting of each exterior power.
In these coordinates the Koszul differential is
`(a, b) ↦ (d a + f b, -d b)`. The degree-one endpoint has the corresponding
scalar formula. The component maps are the inclusions, projections,
contraction and exterior multiplication for this splitting.
-/

@[expose] public section

noncomputable section

set_option autoImplicit false

namespace KoszulComplex

universe u v

variable (R : Type u) [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- The original functional on the product module after one coefficient
is added. -/
def productOneFunctional (y : M →ₗ[R] R) (f : R) : (M × R) →ₗ[R] R :=
  y.comp (LinearMap.fst R M R) + f • LinearMap.snd R M R

@[simp]
theorem productOneFunctional_apply (y : M →ₗ[R] R) (f : R) (m : M) (r : R) :
    productOneFunctional R M y f (m, r) = y m + f * r := rfl

theorem productOneFunctional_comp_inl (y : M →ₗ[R] R) (f : R) :
    (productOneFunctional R M y f).comp (LinearMap.inl R M R) = y := by
  apply LinearMap.ext
  intro m
  simp

/-- Naturality for the original summand in each differential. -/
theorem productOneDifferential_map_inl
    (y : M →ₗ[R] R) (f : R) (n : ℕ) (a : ⋀[R]^(n + 1) M) :
    differential R (M × R) (productOneFunctional R M y f) n
        (exteriorPower.map (n + 1) (LinearMap.inl R M R) a) =
      exteriorPower.map n (LinearMap.inl R M R) (differential R M y n a) :=
  congrArg (fun q => q a)
    (differential_naturality R M y (productOneFunctional R M y f)
      (LinearMap.inl R M R) (productOneFunctional_comp_inl R M y f) n)

/-- The actual product-one differential in all positive target degrees,
including the literal negative sign of the lower component. -/
theorem productOneDifferential_assemble
    (y : M →ₗ[R] R) (f : R) (n : ℕ)
    (a : ⋀[R]^(n + 2) M) (b : ⋀[R]^(n + 1) M) :
    differential R (M × R) (productOneFunctional R M y f) (n + 1)
        (exteriorPower.productOneAssemble R M (n + 1) (a, b)) =
      exteriorPower.productOneAssemble R M n
        (differential R M y (n + 1) a + f • b, -differential R M y n b) := by
  have h := congrArg (fun q => q (exteriorPower.map (n + 1) (LinearMap.inl R M R) b))
    (differential_comp_wedgeLeft_add_wedgeLeft_comp_differential R (M × R)
      (productOneFunctional R M y f) (0, 1) n)
  simp only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.id_apply, productOneFunctional_apply, map_zero, zero_add, mul_one,
    productOneDifferential_map_inl] at h
  rw [exteriorPower.productOneAssemble_apply, map_add,
    productOneDifferential_map_inl]
  rw [eq_sub_of_add_eq h, exteriorPower.productOneAssemble_apply]
  simp only [map_add, map_smul, map_neg]
  abel

/-- The canonical degree-zero exterior map retains the original scalar. -/
theorem productOneZeroEquiv_map_inl (a : ⋀[R]^0 M) :
    exteriorPower.zeroEquiv R (M × R)
        (exteriorPower.map 0 (LinearMap.inl R M R) a) =
      exteriorPower.zeroEquiv R M a :=
  congrArg (fun q => q a) (exteriorPower.zeroEquiv_naturality (LinearMap.inl R M R))

/-- The actual degree-one endpoint is the original old differential plus
the new coefficient times the original lower scalar. -/
theorem productOneDifferential_assemble_zero
    (y : M →ₗ[R] R) (f : R) (a : ⋀[R]^1 M) (b : ⋀[R]^0 M) :
    exteriorPower.zeroEquiv R (M × R)
        (differential R (M × R) (productOneFunctional R M y f) 0
          (exteriorPower.productOneAssemble R M 0 (a, b))) =
      exteriorPower.zeroEquiv R M (differential R M y 0 a) +
        f * exteriorPower.zeroEquiv R M b := by
  have h := congrArg (fun q => q (exteriorPower.map 0 (LinearMap.inl R M R) b))
    (differential_comp_wedgeLeft_zero R (M × R) (productOneFunctional R M y f) (0, 1))
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    productOneFunctional_apply, map_zero, zero_add, mul_one] at h
  rw [exteriorPower.productOneAssemble_apply, map_add,
    productOneDifferential_map_inl, h, map_add, map_smul,
    productOneZeroEquiv_map_inl, productOneZeroEquiv_map_inl]
  rfl

end KoszulComplex
