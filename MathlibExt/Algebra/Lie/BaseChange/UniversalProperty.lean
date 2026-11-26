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
# Lie morphisms out of scalar extension

Let S be a commutative R-algebra, L an R-Lie algebra and N an S-Lie algebra with a compatible
R-Lie algebra action and scalar tower. An R-Lie map f : L → N extends uniquely to an S-Lie map
S ⊗[R] L → N by s ⊗ x ↦ s • f(x).

Restriction of an S-Lie map along R → S leaves its underlying function unchanged. Composing
such a map on S ⊗[R] L with x ↦ 1 ⊗ x is inverse to extension, giving a set equivalence of the
two Lie-morphism spaces. It is natural contravariantly in L and covariantly in compatible
S-Lie target maps. All scalar and Lie-carrier universes are independent.
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

/-- Restriction of a Lie morphism along a scalar tower.

For Lie algebras M,N with compatible R- and S-actions and scalar towers R → S → M,N, an S-Lie
morphism M → N is also an R-Lie morphism. Restriction keeps its underlying function and
bracket equation. -/
def restrictScalars (f : M →ₗ⁅S⁆ N) : M →ₗ⁅R⁆ N where
  toLinearMap := f.toLinearMap.restrictScalars R
  map_lie' := by
    intro x y
    exact f.map_lie x y

/-- Underlying value of a scalar-restricted Lie morphism.

For an S-Lie map f between Lie algebras with compatible R-actions, restrictScalars R S f takes
each x to the same value f(x). -/
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

/-- Extension of a Lie morphism from the original scalar algebra.

Let L be an R-Lie algebra and N an S-Lie algebra with compatible R-action, for a commutative
R-algebra S. An R-Lie map f : L → N extends to the S-Lie map S ⊗[R] L → N whose value on s ⊗ x
is s • f(x). -/
def liftBaseChange (f : L →ₗ⁅R⁆ N) : S ⊗[R] L →ₗ⁅S⁆ N where
  toLinearMap := LinearMap.liftBaseChangeEquiv S f.toLinearMap
  map_lie' := by
    intro x y
    exact liftBaseChange_map_lie R S f x y

/-- Coefficient formula for a Lie scalar-extension lift.

For f : L →ₗ⁅R⁆ N with N carrying compatible S-Lie scalars, liftBaseChange R S f sends s ⊗[R]
x to s • f(x). -/
@[simp]
theorem liftBaseChange_tmul (f : L →ₗ⁅R⁆ N) (s : S) (x : L) :
    liftBaseChange R S f (s ⊗ₜ[R] x) = s • f x := rfl

/-- Hom equivalence for Lie scalar extension.

For an R-Lie algebra L and an S-Lie algebra N with compatible R-action, extension gives (L
→ₗ⁅R⁆ N) ≃ (S ⊗[R] L →ₗ⁅S⁆ N). Its inverse restricts scalars and precomposes with x ↦ 1 ⊗ x.
This is an equivalence of Lie-morphism sets. -/
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

/-- Pure-tensor value of the Lie Hom equivalence.

The extension corresponding to f : L →ₗ⁅R⁆ N under liftBaseChangeEquiv sends s ⊗[R] x to s •
f(x), using the S-action on N. -/
@[simp]
theorem liftBaseChangeEquiv_tmul (f : L →ₗ⁅R⁆ N) (s : S) (x : L) :
    liftBaseChangeEquiv R S L N f (s ⊗ₜ[R] x) = s • f x := rfl

/-- Unit-tensor value of the inverse Lie Hom equivalence.

For an S-Lie map f : S ⊗[R] L → N, the inverse of liftBaseChangeEquiv evaluates it on unit
tensors: the corresponding R-Lie map takes x to f(1 ⊗[R] x). -/
@[simp]
theorem liftBaseChangeEquiv_symm_apply (f : S ⊗[R] L →ₗ⁅S⁆ N) (x : L) :
    (liftBaseChangeEquiv R S L N).symm f x = f ((1 : S) ⊗ₜ[R] x) := rfl

/-- Contravariant naturality of a Lie scalar-extension lift.

For R-Lie maps g : L' → L and f : L → N, with N carrying compatible S-scalars,
liftBaseChange(f ∘ g) = liftBaseChange(f) ∘ baseChange(g). -/
theorem liftBaseChange_comp {L' : Type w'} [LieRing L'] [LieAlgebra R L']
    (f : L →ₗ⁅R⁆ N) (g : L' →ₗ⁅R⁆ L) :
    liftBaseChange R S (f.comp g) =
      (liftBaseChange R S f).comp (baseChange R S g) := by
  apply LieHom.ext
  intro x
  exact LinearMap.congr_fun
    (LinearMap.liftBaseChange_comp (R := R) (A := S) f.toLinearMap g.toLinearMap) x

/-- Covariant naturality of a Lie scalar-extension lift.

For f : L →ₗ⁅R⁆ N and an S-Lie map g : N → N' between compatible scalar towers, g ∘
liftBaseChange(f) equals liftBaseChange((restrictScalars g) ∘ f). -/
theorem comp_liftBaseChange {N' : Type z'} [LieRing N']
    [LieAlgebra R N'] [LieAlgebra S N'] [IsScalarTower R S N']
    (f : L →ₗ⁅R⁆ N) (g : N →ₗ⁅S⁆ N') :
    g.comp (liftBaseChange R S f) = liftBaseChange R S ((restrictScalars R S g).comp f) := by
  apply LieHom.ext
  intro x
  exact LinearMap.congr_fun
    (LinearMap.comp_liftBaseChange (R := R) (A := S) f.toLinearMap g.toLinearMap) x

end LieHom
