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
# Scalar extension of Lie algebra morphisms

Let R,S be commutative rings with an R-algebra structure on S and L an R-Lie algebra. On S
⊗[R] L the extended bracket satisfies [s ⊗ x,t ⊗ y] = st ⊗ [x,y]. The map x ↦ 1 ⊗ x is an
R-Lie morphism from L to this scalar extension.

For an R-Lie morphism f : L → L', its scalar extension is the S-Lie morphism s ⊗ x ↦ s ⊗ f(x).
These maps preserve identities and composition. The two scalar and all Lie-carrier universes
are independent.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace LieHom

universe u v w w' w''

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]

/-- Lie morphism into scalar extension by the unit tensor.

For a commutative R-algebra S and an R-Lie algebra L, define the R-Lie map L → S ⊗[R] L by x ↦
1 ⊗ x. The extended bracket [s ⊗ x,t ⊗ y] = st ⊗ [x,y] makes this map bracket preserving. -/
def baseChangeUnit (L : Type w) [LieRing L] [LieAlgebra R L] :
    L →ₗ⁅R⁆ S ⊗[R] L where
  toLinearMap := TensorProduct.mk R S L 1
  map_lie' := by
    intro x y
    change (1 : S) ⊗ₜ[R] ⁅x, y⁆ = ⁅(1 : S) ⊗ₜ[R] x, (1 : S) ⊗ₜ[R] y⁆
    rw [LieAlgebra.ExtendScalars.bracket_tmul, one_mul]

/-- Value of the Lie scalar-extension unit.

For x ∈ L, the map baseChangeUnit R S L takes x to 1 ⊗[R] x in the Lie algebra S ⊗[R] L. -/
@[simp]
theorem baseChangeUnit_apply (L : Type w) [LieRing L] [LieAlgebra R L] (x : L) :
    baseChangeUnit R S L x = (1 : S) ⊗ₜ[R] x := rfl

variable {L : Type w} [LieRing L] [LieAlgebra R L]
  {L' : Type w'} [LieRing L'] [LieAlgebra R L']
  {L'' : Type w''} [LieRing L''] [LieAlgebra R L'']

/-- Scalar extension of a Lie morphism.

For f : L →ₗ⁅R⁆ L' and a commutative R-algebra S, extend its linear map to S ⊗[R] L → S ⊗[R]
L'. The resulting S-Lie morphism sends s ⊗ x to s ⊗ f(x). -/
def baseChange (f : L →ₗ⁅R⁆ L') : S ⊗[R] L →ₗ⁅S⁆ S ⊗[R] L' where
  toLinearMap := TensorProduct.AlgebraTensorModule.lTensor S S f.toLinearMap
  map_lie' := by
    intro x y
    change (LieAlgebra.ExtendScalars.map (AlgHom.id R S) f) ⁅x, y⁆ =
      ⁅(LieAlgebra.ExtendScalars.map (AlgHom.id R S) f) x,
        (LieAlgebra.ExtendScalars.map (AlgHom.id R S) f) y⁆
    exact (LieAlgebra.ExtendScalars.map (AlgHom.id R S) f).map_lie x y

/-- Pure-tensor formula for a scalar-extended Lie morphism.

For an R-Lie map f : L → L', scalar s ∈ S and x ∈ L, baseChange R S f takes s ⊗[R] x to s ⊗[R]
f(x). The coefficient remains in the left tensor factor. -/
@[simp]
theorem baseChange_tmul (f : L →ₗ⁅R⁆ L') (s : S) (x : L) :
    baseChange R S f (s ⊗ₜ[R] x) = s ⊗ₜ[R] f x := rfl

/-- Identity law for Lie scalar extension.

Scalar extension of the identity R-Lie map on L is the identity S-Lie map on S ⊗[R] L. -/
@[simp]
theorem baseChange_id :
    baseChange R S (LieHom.id : L →ₗ⁅R⁆ L) = LieHom.id := by
  apply LieHom.ext
  intro x
  exact LinearMap.congr_fun
    (TensorProduct.AlgebraTensorModule.lTensor_id (R := R) (A := S) (M := S) (N := L)) x

/-- Composition law for Lie scalar extension.

For R-Lie maps f : L → L' and g : L' → L'', baseChange(g ∘ f) = baseChange(g) ∘ baseChange(f)
as S-Lie maps. The three Lie-carrier universes may be independent. -/
@[simp]
theorem baseChange_comp (f : L →ₗ⁅R⁆ L') (g : L' →ₗ⁅R⁆ L'') :
    baseChange R S (g.comp f) = (baseChange R S g).comp (baseChange R S f) := by
  apply LieHom.ext
  intro x
  exact LinearMap.congr_fun
    (TensorProduct.AlgebraTensorModule.lTensor_comp
      (R := R) (A := S) (M := S) g.toLinearMap f.toLinearMap) x

end LieHom
