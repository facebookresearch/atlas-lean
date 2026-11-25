/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Authors: @toskua, Codex
-/

module

public import Mathlib.Algebra.Lie.BaseChange

/-!
# Scalar extension of Lie morphisms

For a commutative ring algebra `R → S`, the native Lie bracket on
`S ⊗[R] L` extends the original bracket on `L`. The unit sends `x` to
`1 ⊗ x`. An `R`-Lie morphism extends to an `S`-Lie morphism through the
native tensor linear map, preserving identity and composition.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace LieHom

universe u v w w' w''

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]

/-- The original Lie algebra maps into its scalar extension by `x ↦ 1 ⊗ x`. -/
def baseChangeUnit (L : Type w) [LieRing L] [LieAlgebra R L] :
    L →ₗ⁅R⁆ S ⊗[R] L where
  toLinearMap := TensorProduct.mk R S L 1
  map_lie' := by
    intro x y
    change (1 : S) ⊗ₜ[R] ⁅x, y⁆ = ⁅(1 : S) ⊗ₜ[R] x, (1 : S) ⊗ₜ[R] y⁆
    rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul]

/-- The scalar-extension unit has the native pure-tensor value. -/
@[simp]
theorem baseChangeUnit_apply (L : Type w) [LieRing L] [LieAlgebra R L] (x : L) :
    baseChangeUnit R S L x = (1 : S) ⊗ₜ[R] x := rfl

variable {L : Type w} [LieRing L] [LieAlgebra R L]
  {L' : Type w'} [LieRing L'] [LieAlgebra R L']
  {L'' : Type w''} [LieRing L''] [LieAlgebra R L'']

/-- Extend an `R`-Lie morphism to an `S`-linear Lie morphism on the native scalar extensions. -/
def baseChange (f : L →ₗ⁅R⁆ L') : S ⊗[R] L →ₗ⁅S⁆ S ⊗[R] L' where
  toLinearMap := TensorProduct.AlgebraTensorModule.lTensor S S f.toLinearMap
  map_lie' := by
    intro x y
    change (LieAlgebra.ExtendScalars.map (AlgHom.id R S) f) ⁅x, y⁆ =
      ⁅(LieAlgebra.ExtendScalars.map (AlgHom.id R S) f) x,
        (LieAlgebra.ExtendScalars.map (AlgHom.id R S) f) y⁆
    exact (LieAlgebra.ExtendScalars.map (AlgHom.id R S) f).map_lie x y

/-- Scalar extension leaves the scalar coefficient and applies the original Lie morphism. -/
@[simp]
theorem baseChange_tmul (f : L →ₗ⁅R⁆ L') (s : S) (x : L) :
    baseChange R S f (s ⊗ₜ[R] x) = s ⊗ₜ[R] f x := rfl

/-- Scalar extension carries the identity Lie morphism to the identity. -/
@[simp]
theorem baseChange_id :
    baseChange R S (LieHom.id : L →ₗ⁅R⁆ L) = LieHom.id := by
  apply LieHom.ext
  intro x
  exact LinearMap.congr_fun
    (TensorProduct.AlgebraTensorModule.lTensor_id (R := R) (A := S) (M := S) (N := L)) x

/-- Scalar extension preserves composition across independent Lie-carrier universes. -/
@[simp]
theorem baseChange_comp (f : L →ₗ⁅R⁆ L') (g : L' →ₗ⁅R⁆ L'') :
    baseChange R S (g.comp f) = (baseChange R S g).comp (baseChange R S f) := by
  apply LieHom.ext
  intro x
  exact LinearMap.congr_fun
    (TensorProduct.AlgebraTensorModule.lTensor_comp
      (R := R) (A := S) (M := S) g.toLinearMap f.toLinearMap) x

end LieHom
