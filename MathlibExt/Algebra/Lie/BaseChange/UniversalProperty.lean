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

public import MathlibExt.Algebra.Lie.BaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Lift

/-!
# Universal property of Lie scalar extension

For a commutative ring algebra `R → S`, let `L` be an `R`-Lie algebra
and let `N` carry compatible `R`- and `S`-Lie algebra actions. Lie maps
`L → N` over `R` correspond to Lie maps `S ⊗[R] L → N` over `S`.
The extension sends `s ⊗ x` to `s • f x`; restriction composes with
`x ↦ 1 ⊗ x`.

The correspondence uses the native linear scalar-extension equivalence.
It is a plain equivalence, since general Lie morphism spaces need not
be additive. All carrier universes are independent, and no flatness or
projectivity hypothesis is required.
-/

@[expose] public section

noncomputable section

open scoped TensorProduct

namespace LieHom

universe u v w w' z z'

variable (R : Type u) [CommRing R] (S : Type v) [CommRing S] [Algebra R S]

section Restriction

variable {M : Type w} [LieRing M] [LieAlgebra R M] [LieAlgebra S M]
  [IsScalarTower R S M]
  {N : Type z} [LieRing N] [LieAlgebra R N] [LieAlgebra S N]
  [IsScalarTower R S N]

/-- Restrict an `S`-Lie morphism along the actual compatible scalar tower. -/
def restrictScalars (f : M →ₗ⁅S⁆ N) : M →ₗ⁅R⁆ N where
  toLinearMap := f.toLinearMap.restrictScalars R
  map_lie' := by
    intro x y
    exact f.map_lie x y

/-- Restriction leaves the underlying map unchanged. -/
@[simp]
theorem restrictScalars_apply (f : M →ₗ⁅S⁆ N) (x : M) :
    restrictScalars R S f x = f x := rfl

end Restriction

variable {L : Type w} [LieRing L] [LieAlgebra R L]
  {N : Type z} [LieRing N] [LieAlgebra R N] [LieAlgebra S N]
  [IsScalarTower R S N]

private theorem liftBaseChange_map_lie (f : L →ₗ⁅R⁆ N) (x y : S ⊗[R] L) :
    LinearMap.liftBaseChangeEquiv S f.toLinearMap ⁅x, y⁆ =
      ⁅LinearMap.liftBaseChangeEquiv S f.toLinearMap x,
        LinearMap.liftBaseChangeEquiv S f.toLinearMap y⁆ := by
  refine x.inductionOn ?_ ?_
  · intro s x
    refine y.inductionOn ?_ ?_
    · intro t y
      simp only [LieAlgebra.ExtendScalars.bracket_tmul, LinearMap.liftBaseChange_tmul,
        smul_lie, lie_smul, smul_smul]
      rw [f.map_lie x y, mul_comm s t]
    · intro y y' hy hy'
      simpa only [lie_add, map_add] using congrArg₂ (· + ·) hy hy'
  · intro x x' hx hx'
    simpa only [add_lie, map_add] using congrArg₂ (· + ·) hx hx'

/-- Extend an `R`-Lie morphism using the native `S`-linear scalar-extension map. -/
def liftBaseChange (f : L →ₗ⁅R⁆ N) : S ⊗[R] L →ₗ⁅S⁆ N where
  toLinearMap := LinearMap.liftBaseChangeEquiv S f.toLinearMap
  map_lie' := by
    intro x y
    exact liftBaseChange_map_lie R S f x y

/-- The Lie extension has the actual native coefficient value on a pure tensor. -/
@[simp]
theorem liftBaseChange_tmul (f : L →ₗ⁅R⁆ N) (s : S) (x : L) :
    liftBaseChange R S f (s ⊗ₜ[R] x) = s • f x := rfl

/-- Lie scalar extension and restriction form a plain Hom equivalence. -/
def liftBaseChangeEquiv (L : Type w) [LieRing L] [LieAlgebra R L]
    (N : Type z) [LieRing N] [LieAlgebra R N] [LieAlgebra S N]
    [IsScalarTower R S N] :
    (L →ₗ⁅R⁆ N) ≃ (S ⊗[R] L →ₗ⁅S⁆ N) where
  toFun := liftBaseChange R S
  invFun f := (restrictScalars R S f).comp (baseChangeUnit R S L)
  left_inv f := by
    apply LieHom.ext
    intro x
    change liftBaseChange R S f ((1 : S) ⊗ₜ[R] x) = f x
    rw [liftBaseChange_tmul, one_smul]
  right_inv f := by
    have h : ((restrictScalars R S f).comp (baseChangeUnit R S L)).toLinearMap =
        (LinearMap.liftBaseChangeEquiv S).symm f.toLinearMap := by
      ext x
      rfl
    apply LieHom.ext
    intro x
    change LinearMap.liftBaseChangeEquiv S
      ((restrictScalars R S f).comp (baseChangeUnit R S L)).toLinearMap x = f x
    rw [h]
    exact LinearMap.congr_fun
      ((LinearMap.liftBaseChangeEquiv S).apply_symm_apply f.toLinearMap) x

/-- The Hom equivalence extends each morphism by the coefficient tensor formula. -/
@[simp]
theorem liftBaseChangeEquiv_tmul (f : L →ₗ⁅R⁆ N) (s : S) (x : L) :
    liftBaseChangeEquiv R S L N f (s ⊗ₜ[R] x) = s • f x := rfl

/-- The inverse Hom equivalence evaluates the extended morphism on the unit tensor. -/
@[simp]
theorem liftBaseChangeEquiv_symm_apply (f : S ⊗[R] L →ₗ⁅S⁆ N) (x : L) :
    (liftBaseChangeEquiv R S L N).symm f x = f ((1 : S) ⊗ₜ[R] x) := rfl

/-- Extension is contravariantly natural in the original Lie source. -/
theorem liftBaseChange_comp {L' : Type w'} [LieRing L'] [LieAlgebra R L']
    (f : L →ₗ⁅R⁆ N) (g : L' →ₗ⁅R⁆ L) :
    liftBaseChange R S (f.comp g) =
      (liftBaseChange R S f).comp (baseChange R S g) := by
  apply LieHom.ext
  intro x
  exact LinearMap.congr_fun
    (LinearMap.liftBaseChange_comp (R := R) (A := S) f.toLinearMap g.toLinearMap) x

/-- Extension is covariantly natural in compatible `S`-Lie target morphisms. -/
theorem comp_liftBaseChange {N' : Type z'} [LieRing N']
    [LieAlgebra R N'] [LieAlgebra S N'] [IsScalarTower R S N']
    (f : L →ₗ⁅R⁆ N) (g : N →ₗ⁅S⁆ N') :
    g.comp (liftBaseChange R S f) = liftBaseChange R S ((restrictScalars R S g).comp f) := by
  apply LieHom.ext
  intro x
  exact LinearMap.congr_fun
    (LinearMap.comp_liftBaseChange (R := R) (A := S) f.toLinearMap g.toLinearMap) x

end LieHom
