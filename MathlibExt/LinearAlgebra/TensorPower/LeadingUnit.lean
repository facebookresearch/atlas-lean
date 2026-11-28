/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua, Avocado
-/
module

public import Mathlib.LinearAlgebra.TensorPower.Basic

/-!
# Native tensor powers and categorical leading-unit coherence

The first native tensor power is identified with a leading-unit tensor by the canonical
single-factor and tensor-unit equivalences. This coefficient-natural first-power comparison
is used by the actual categorical representation tensor-power carrier transport; it does not
introduce a recursive carrier.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
open scoped TensorProduct

universe u v w

namespace TensorPower

variable {R : Type u} [CommSemiring R]

/-- The native first tensor power carries the same information as a leading-unit tensor. -/
def leadingUnitEquiv (M : Type v) [AddCommMonoid M] [Module R M] :
    TensorPower R 1 M ≃ₗ[R] R ⊗[R] M :=
  (PiTensorProduct.subsingletonEquiv (R := R) (s := fun _ : Fin 1 => M) 0) ≪≫ₗ
    (TensorProduct.lid R M).symm

@[simp]
theorem leadingUnitEquiv_tprod (M : Type v) [AddCommMonoid M] [Module R M]
    (x : Fin 1 → M) :
    leadingUnitEquiv (R := R) M (PiTensorProduct.tprod R x) =
      (1 : R) ⊗ₜ[R] x 0 := by
  simp [leadingUnitEquiv]

/-- The native first-power/leading-unit comparison is natural in the coefficient map. -/
theorem leadingUnitEquiv_naturality
    {M : Type v} {N : Type w} [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (f : M →ₗ[R] N) :
    (leadingUnitEquiv (R := R) N).toLinearMap.comp
        (PiTensorProduct.map (fun _ : Fin 1 => f)) =
      (TensorProduct.map (LinearMap.id : R →ₗ[R] R) f).comp
        (leadingUnitEquiv (R := R) M).toLinearMap := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    PiTensorProduct.map_tprod, leadingUnitEquiv_tprod, TensorProduct.map_tmul,
    LinearMap.id_apply]

end TensorPower
