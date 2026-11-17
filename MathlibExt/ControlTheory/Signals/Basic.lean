/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Module.Equiv.Basic
public import Mathlib.Algebra.Module.LinearMap.Basic

/-!
# Signals, shifts, causality, and time invariance

Raw pointwise signals `T → E`; a linear system is a Mathlib linear map
`(T → E) →ₗ[𝕜] (T → F)` (no duplicate linearity predicate). `shiftₗ 𝕜 E a`
delays by `a`, `shiftₗ 𝕜 E a x t = x (t - a)`, with group law
`shiftₗ a ∘ shiftₗ b = shiftₗ (a + b)` over an additive commutative group
(for `ℤ` or `ℝ` time). `IsCausal` is the prefix condition: the output at
`t` depends only on inputs at `s ≤ t`. `IsTimeInvariant` is commutation
with every shift. Both predicates are closed under composition (series) and
pointwise sum (parallel). No `Lp`-class predicates and no `ℕ`-time
translations are treated here.

Roadmap leaf `SSC-U01.T01`, clauses `SSC-U01.c01`, `SSC-U01.c02`.
-/

@[expose] public section

namespace ControlTheory

/-- Time shift of a raw pointwise signal, as a linear map: `shiftₗ 𝕜 E a`
sends `x` to the signal `t ↦ x (t - a)` (delay by `a` when `a` is positive).
It is `LinearMap.funLeft` along `t ↦ t - a`. -/
def shiftₗ (𝕜 : Type*) (E : Type*) {T : Type*} [Semiring 𝕜] [AddCommMonoid E]
    [Module 𝕜 E] [Sub T] (a : T) : (T → E) →ₗ[𝕜] (T → E) :=
  LinearMap.funLeft 𝕜 E (fun t => t - a)

/-- A linear system `S` on raw pointwise signals is causal when its output at
each time `t` depends only on input values at times `s ≤ t`. -/
def IsCausal {𝕜 T E F : Type*} [Semiring 𝕜] [AddCommMonoid E] [AddCommMonoid F]
    [Module 𝕜 E] [Module 𝕜 F] [Preorder T] (S : (T → E) →ₗ[𝕜] (T → F)) : Prop :=
  ∀ t x y, (∀ s ≤ t, x s = y s) → S x t = S y t

/-- A linear system `S` on raw pointwise signals is time invariant when it
commutes with every time shift: `S ∘ shiftₗ 𝕜 E a = shiftₗ 𝕜 F a ∘ S`. -/
def IsTimeInvariant {𝕜 T E F : Type*} [Semiring 𝕜] [AddCommMonoid E]
    [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F] [Sub T]
    (S : (T → E) →ₗ[𝕜] (T → F)) : Prop :=
  ∀ a : T, S.comp (shiftₗ 𝕜 E a) = (shiftₗ 𝕜 F a).comp S

@[simp]
theorem shiftₗ_apply {𝕜 T E : Type*} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    [Sub T] (a : T) (x : T → E) (t : T) : shiftₗ 𝕜 E a x t = x (t - a) := by
  rfl

theorem shiftₗ_zero {𝕜 T E : Type*} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    [AddCommGroup T] :
    (shiftₗ 𝕜 E (0 : T) : (T → E) →ₗ[𝕜] (T → E)) = LinearMap.id := by
  ext x t
  simp

theorem shiftₗ_comp {𝕜 T E : Type*} [Semiring 𝕜] [AddCommMonoid E] [Module 𝕜 E]
    [AddCommGroup T] (a b : T) :
    ((shiftₗ 𝕜 E a : (T → E) →ₗ[𝕜] (T → E)).comp (shiftₗ 𝕜 E b)) =
      shiftₗ 𝕜 E (a + b) := by
  ext x t
  simp only [LinearMap.comp_apply, shiftₗ_apply, sub_sub]

theorem IsCausal.comp {𝕜 T E F G : Type*} [Semiring 𝕜] [AddCommMonoid E]
    [AddCommMonoid F] [AddCommMonoid G] [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 G]
    [Preorder T] {S₁ : (T → E) →ₗ[𝕜] (T → F)} {S₂ : (T → F) →ₗ[𝕜] (T → G)}
    (h₁ : IsCausal S₁) (h₂ : IsCausal S₂) : IsCausal (S₂.comp S₁) := by
  intro t x y h
  simp only [LinearMap.comp_apply]
  exact h₂ t _ _ (fun s hs => h₁ s _ _ (fun s' hs' => h s' (le_trans hs' hs)))

theorem IsCausal.add {𝕜 T E F : Type*} [Semiring 𝕜] [AddCommMonoid E]
    [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F] [Preorder T]
    {S₁ S₂ : (T → E) →ₗ[𝕜] (T → F)} (h₁ : IsCausal S₁) (h₂ : IsCausal S₂) :
    IsCausal (S₁ + S₂) := by
  intro t x y h
  simp only [LinearMap.add_apply, Pi.add_apply, h₁ t x y h, h₂ t x y h]

theorem IsTimeInvariant.comp {𝕜 T E F G : Type*} [Semiring 𝕜] [AddCommMonoid E]
    [AddCommMonoid F] [AddCommMonoid G] [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 G]
    [Sub T] {S₁ : (T → E) →ₗ[𝕜] (T → F)} {S₂ : (T → F) →ₗ[𝕜] (T → G)}
    (h₁ : IsTimeInvariant S₁) (h₂ : IsTimeInvariant S₂) :
    IsTimeInvariant (S₂.comp S₁) := by
  intro a
  calc (S₂.comp S₁).comp (shiftₗ 𝕜 E a)
      = S₂.comp (S₁.comp (shiftₗ 𝕜 E a)) := by rw [LinearMap.comp_assoc]
    _ = S₂.comp ((shiftₗ 𝕜 F a).comp S₁) := by rw [h₁ a]
    _ = (S₂.comp (shiftₗ 𝕜 F a)).comp S₁ := by rw [← LinearMap.comp_assoc]
    _ = ((shiftₗ 𝕜 G a).comp S₂).comp S₁ := by rw [h₂ a]
    _ = (shiftₗ 𝕜 G a).comp (S₂.comp S₁) := by rw [LinearMap.comp_assoc]

theorem IsTimeInvariant.add {𝕜 T E F : Type*} [Semiring 𝕜] [AddCommMonoid E]
    [AddCommMonoid F] [Module 𝕜 E] [Module 𝕜 F] [Sub T]
    {S₁ S₂ : (T → E) →ₗ[𝕜] (T → F)} (h₁ : IsTimeInvariant S₁)
    (h₂ : IsTimeInvariant S₂) : IsTimeInvariant (S₁ + S₂) := by
  intro a
  rw [LinearMap.add_comp, LinearMap.comp_add, h₁ a, h₂ a]

end ControlTheory
