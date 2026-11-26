/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Quotient base change detects a kernel condition

Let R be a commutative ring, I an ideal and f:P→M a surjective linear map of arbitrary
R-modules. The induced map (R/I)⊗_RP→(R/I)⊗_RM is injective exactly when ker(f)⊆IP.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

open Function
open scoped TensorProduct

universe u v w

namespace LinearMap

/-- **Kernel containment is injectivity after quotient base change.**

Let R be a commutative ring, I an ideal and f:P→M surjective R-linear. Then ker(f)≤I•P if and
only if f.baseChange(R/I) is injective. The modules and ideal are arbitrary.
-/
theorem ker_le_ideal_smul_top_iff_baseChange_quotient_injective
    {R : Type u} [CommRing R] (I : Ideal R)
    {P : Type v} [AddCommGroup P] [Module R P]
    {M : Type w} [AddCommGroup M] [Module R M]
    (f : P →ₗ[R] M) (hf : Surjective f) :
    LinearMap.ker f ≤ I • (⊤ : Submodule R P) ↔
      Injective (f.baseChange (R ⧸ I)) := by
  constructor
  · intro hker
    have hzeroMap :
        (LinearMap.ker f).subtype.lTensor (R ⧸ I) = 0 := by
      apply LinearMap.ext
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul q y =>
          have hyI : (y : P) ∈ I • (⊤ : Submodule R P) :=
            hker y.property
          simp only [LinearMap.lTensor_tmul, LinearMap.zero_apply]
          obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective q
          have hrone :
              r • (1 : R ⧸ I) = Ideal.Quotient.mk I r := by
            simpa using
              (Submodule.Quotient.mk_smul I r (1 : R)).symm
          rw [← hrone, TensorProduct.smul_tmul]
          change (TensorProduct.mk R (R ⧸ I) P 1)
            (r • (y : P)) = 0
          apply LinearMap.mem_ker.mp
          rw [LinearMap.ker_tensorProductMk]
          exact (I • (⊤ : Submodule R P)).smul_mem r hyI
      | add y z hy hz => simp [hy, hz]
    rw [injective_iff_map_eq_zero]
    intro x hx
    rw [LinearMap.baseChange_eq_lTensor] at hx
    obtain ⟨y, hy⟩ :=
      ((lTensor_exact (R ⧸ I)
        f.exact_subtype_ker_map hf) x).mp hx
    rw [← hy, hzeroMap, LinearMap.zero_apply]
  · intro hinj x hx
    rw [← LinearMap.ker_tensorProductMk, LinearMap.mem_ker]
    apply hinj
    simp [LinearMap.baseChange_tmul, LinearMap.mem_ker.mp hx]

end LinearMap
