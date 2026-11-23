/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Group structure on self-diffeomorphisms

This module provides the group structure on `M ≃ₘ^n⟮I, I⟯ M`, following `Equiv.Perm`:
multiplication is composition, `1` is the identity diffeomorphism, and `⁻¹` is the inverse.
-/

@[expose] public section

open scoped Manifold ContDiff

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners 𝕜 E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
variable {n : ℕ∞ω}

namespace Diffeomorph

/-- Group of self-diffeomorphisms, with multiplication as composition. -/
instance instGroup : Group (M ≃ₘ^n⟮I, I⟯ M) where
  mul φ ψ := ψ.trans φ
  mul_assoc φ ψ χ := Diffeomorph.ext fun _ => rfl
  one := Diffeomorph.refl I M n
  one_mul φ := Diffeomorph.ext fun _ => rfl
  mul_one φ := Diffeomorph.ext fun _ => rfl
  inv φ := φ.symm
  inv_mul_cancel φ := Diffeomorph.ext fun x => Diffeomorph.symm_apply_apply φ x

/-- Coercion of a product is composition of the coercions. -/
@[simp]
theorem coe_mul (φ ψ : M ≃ₘ^n⟮I, I⟯ M) : ⇑(φ * ψ) = φ ∘ ψ :=
  rfl

/-- Coercion of `1` is the identity. -/
@[simp]
theorem coe_one : ⇑(1 : M ≃ₘ^n⟮I, I⟯ M) = id :=
  rfl

/-- Application of a product is composition of applications. -/
@[simp]
theorem mul_apply (φ ψ : M ≃ₘ^n⟮I, I⟯ M) (x : M) : (φ * ψ) x = φ (ψ x) :=
  rfl

/-- Application of `1` is the identity. -/
@[simp]
theorem one_apply (x : M) : (1 : M ≃ₘ^n⟮I, I⟯ M) x = x :=
  rfl

/-- Application of `⁻¹` is application of the symmetric diffeomorphism. -/
@[simp]
theorem inv_apply (φ : M ≃ₘ^n⟮I, I⟯ M) (x : M) : φ⁻¹ x = φ.symm x :=
  rfl

/-- Multiplication is reversed composition via `Diffeomorph.trans`. -/
theorem mul_def (φ ψ : M ≃ₘ^n⟮I, I⟯ M) : φ * ψ = ψ.trans φ :=
  rfl

/-- `1` is the identity diffeomorphism. -/
theorem one_def : (1 : M ≃ₘ^n⟮I, I⟯ M) = Diffeomorph.refl I M n :=
  rfl

/-- `⁻¹` is the symmetric diffeomorphism. -/
theorem inv_def (φ : M ≃ₘ^n⟮I, I⟯ M) : φ⁻¹ = φ.symm :=
  rfl

end Diffeomorph

end
