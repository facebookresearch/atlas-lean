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

public import Mathlib.RingTheory.Length
import Mathlib.RingTheory.HopkinsLevitzki

/-!
# Natural-length additivity with finite ends

For an Artinian ring, finite modules have finite composition length. An exact
sequence with finite first and last terms therefore has natural-length additivity.
The statement uses `(Module.length A M).toNat` directly and allows independent
module universes. Casting a finite length back to `ENat` uses the native
`ENat.natCast_toNat_eq_self`; a named grading-free length interface is unnecessary.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
namespace Module
universe u v w z

/-- Let `A` be an Artinian ring, and let `M₁ → M₂ → M₃` be
`A`-linear maps whose first map is injective, second map is surjective, and
image equals kernel at `M₂`. If `M₁` and `M₃` are finitely generated,
`lengthNat_A(M₂) = lengthNat_A(M₁) + lengthNat_A(M₃)`. The three module
universes are independent. -/
theorem length_toNat_eq_add_of_exact_of_finite
    (A : Type u) [Ring A] [IsArtinianRing A]
    {M₁ : Type v} [AddCommGroup M₁] [Module A M₁] [Module.Finite A M₁]
    {M₂ : Type w} [AddCommGroup M₂] [Module A M₂]
    {M₃ : Type z} [AddCommGroup M₃] [Module A M₃] [Module.Finite A M₃]
    (f : M₁ →ₗ[A] M₂) (g : M₂ →ₗ[A] M₃)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hfg : Function.Exact f g) :
    (Module.length A M₂).toNat =
      (Module.length A M₁).toNat + (Module.length A M₃).toNat := by
  have h₁ : Module.length A M₁ ≠ ⊤ := by
    rw [Module.length_ne_top_iff]
    have hfin : Module.Finite A M₁ := inferInstance
    exact ((IsArtinianRing.tfae A M₁).out 1 4).mp hfin
  have h₃ : Module.length A M₃ ≠ ⊤ := by
    rw [Module.length_ne_top_iff]
    have hfin : Module.Finite A M₃ := inferInstance
    exact ((IsArtinianRing.tfae A M₃).out 1 4).mp hfin
  rw [Module.length_eq_add_of_exact f g hf hg hfg,
    ENat.toNat_add h₁ h₃]

end Module
