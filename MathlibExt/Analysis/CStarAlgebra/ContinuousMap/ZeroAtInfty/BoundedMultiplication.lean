/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Analysis.CStarAlgebra.Multiplier
public import Mathlib.Analysis.Normed.Ring.Lemmas

/-!
# Bounded scalar multiplication on C0

A bounded continuous scalar function acts pointwise on the existing C0
function algebra. The actual supremum-norm estimate bundles a continuous
linear map and its balanced double centralizer. No BCF-module instance,
norm model, nonzero hypothesis or multiplier-equivalence oracle is supplied.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter
open scoped ZeroAtInfty MultiplierAlgebra Topology

namespace BoundedContinuousFunction

universe u

/-- Let `X` be an arbitrary topological space. Bounded continuous complex functions and complex
continuous functions vanishing at infinity carry their supremum norms.

Multiply the C0 function by a bounded continuous scalar function. -/
def mulZeroAtInfty
    {X : Type u} [TopologicalSpace X]
    (g : X →ᵇ ℂ) (f : C₀(X, ℂ)) : C₀(X, ℂ) where
  toFun x := g x * f x
  continuous_toFun := g.continuous.mul f.continuous_toFun
  zero_at_infty' := by
    have hg : (cocompact X).IsBoundedUnder (· ≤ ·) (norm ∘ (g : X → ℂ)) :=
      Filter.isBoundedUnder_of ⟨‖g‖, fun x => g.norm_coe_le_norm x⟩
    exact Filter.isBoundedUnder_le_mul_tendsto_zero hg (zero_at_infty f)

/-- Let `X` be an arbitrary topological space. Bounded continuous complex functions and complex
continuous functions vanishing at infinity carry their supremum norms.

The product retains its pointwise scalar value. -/
@[simp]
theorem mulZeroAtInfty_apply
    {X : Type u} [TopologicalSpace X]
    (g : X →ᵇ ℂ) (f : C₀(X, ℂ)) (x : X) :
    mulZeroAtInfty g f x = g x * f x := rfl

/-- Let `X` be an arbitrary topological space. Bounded continuous complex functions and complex
continuous functions vanishing at infinity carry their supremum norms.

The existing bounded inclusion sends this product to BCF multiplication. -/
@[simp]
theorem mulZeroAtInfty_toBCF
    {X : Type u} [TopologicalSpace X]
    (g : X →ᵇ ℂ) (f : C₀(X, ℂ)) :
    (mulZeroAtInfty g f).toBCF = g * f.toBCF := by
  apply BoundedContinuousFunction.ext
  intro x
  rfl

/-- Let `X` be an arbitrary topological space. Bounded continuous complex functions and complex
continuous functions vanishing at infinity carry their supremum norms.

Bounded multiplication obeys the same existing supremum-norm estimate. -/
theorem norm_mulZeroAtInfty_le
    {X : Type u} [TopologicalSpace X]
    (g : X →ᵇ ℂ) (f : C₀(X, ℂ)) :
    ‖mulZeroAtInfty g f‖ ≤ ‖g‖ * ‖f‖ := by
  calc
    ‖mulZeroAtInfty g f‖ = ‖(mulZeroAtInfty g f).toBCF‖ :=
      (ZeroAtInftyContinuousMap.norm_toBCF_eq_norm (f := mulZeroAtInfty g f)).symm
    _ = ‖g * f.toBCF‖ := congrArg norm (mulZeroAtInfty_toBCF g f)
    _ ≤ ‖g‖ * ‖f.toBCF‖ := norm_mul_le g f.toBCF
    _ = ‖g‖ * ‖f‖ := congrArg (fun r : ℝ => ‖g‖ * r)
      (ZeroAtInftyContinuousMap.norm_toBCF_eq_norm (f := f))

/-- Let `X` be an arbitrary topological space. Bounded continuous complex functions and complex
continuous functions vanishing at infinity carry their supremum norms.

The bounded multiplication operator, without a new scalar action instance. -/
noncomputable def mulZeroAtInftyCLM
    {X : Type u} [TopologicalSpace X] (g : X →ᵇ ℂ) :
    C₀(X, ℂ) →L[ℂ] C₀(X, ℂ) :=
  let L : C₀(X, ℂ) →ₗ[ℂ] C₀(X, ℂ) :=
    { toFun := mulZeroAtInfty g
      map_add' f h := by
        apply ZeroAtInftyContinuousMap.ext
        intro x
        change g x * (f x + h x) = g x * f x + g x * h x
        exact mul_add _ _ _
      map_smul' z f := by
        apply ZeroAtInftyContinuousMap.ext
        intro x
        change g x * (z * f x) = z * (g x * f x)
        calc
          g x * (z * f x) = (g x * z) * f x := (mul_assoc _ _ _).symm
          _ = (z * g x) * f x := congrArg (fun a : ℂ => a * f x) (mul_comm _ _)
          _ = z * (g x * f x) := mul_assoc _ _ _ }
  L.mkContinuous ‖g‖ (norm_mulZeroAtInfty_le g)

/-- Let `X` be an arbitrary topological space. Bounded continuous complex functions and complex
continuous functions vanishing at infinity carry their supremum norms.

The CLM's entry is exactly the scalar product. -/
@[simp]
theorem mulZeroAtInftyCLM_apply
    {X : Type u} [TopologicalSpace X]
    (g : X →ᵇ ℂ) (f : C₀(X, ℂ)) (x : X) :
    mulZeroAtInftyCLM g f x = g x * f x := rfl

/-- Let `X` be an arbitrary topological space. Bounded continuous complex functions and complex
continuous functions vanishing at infinity carry their supremum norms.

The multiplication CLM has operator norm bounded by the supplied function norm. -/
theorem norm_mulZeroAtInftyCLM_le
    {X : Type u} [TopologicalSpace X] (g : X →ᵇ ℂ) :
    ‖mulZeroAtInftyCLM g‖ ≤ ‖g‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg g)
  intro f
  exact norm_mulZeroAtInfty_le g f

/-- Let `X` be an arbitrary topological space. Bounded continuous complex functions and complex
continuous functions vanishing at infinity carry their supremum norms.

The two multiplication components form a balanced double centralizer. -/
noncomputable def toZeroAtInftyMultiplier
    {X : Type u} [TopologicalSpace X] (g : X →ᵇ ℂ) :
    𝓜(ℂ, C₀(X, ℂ)) where
  toProd := (mulZeroAtInftyCLM g, mulZeroAtInftyCLM g)
  central f h := by
    apply ZeroAtInftyContinuousMap.ext
    intro x
    change (g x * f x) * h x = f x * (g x * h x)
    calc
      (g x * f x) * h x = (f x * g x) * h x :=
        congrArg (fun a : ℂ => a * h x) (mul_comm _ _)
      _ = f x * (g x * h x) := mul_assoc _ _ _

/-- Let `X` be an arbitrary topological space. Bounded continuous complex functions and complex
continuous functions vanishing at infinity carry their supremum norms.

The left multiplier action is the bounded scalar multiplication. -/
@[simp]
theorem toZeroAtInftyMultiplier_fst_apply
    {X : Type u} [TopologicalSpace X]
    (g : X →ᵇ ℂ) (f : C₀(X, ℂ)) (x : X) :
    (toZeroAtInftyMultiplier g).fst f x = g x * f x := rfl

/-- Let `X` be an arbitrary topological space. Bounded continuous complex functions and complex
continuous functions vanishing at infinity carry their supremum norms.

The right multiplier action is the same scalar operation. -/
@[simp]
theorem toZeroAtInftyMultiplier_snd_apply
    {X : Type u} [TopologicalSpace X]
    (g : X →ᵇ ℂ) (f : C₀(X, ℂ)) (x : X) :
    (toZeroAtInftyMultiplier g).snd f x = g x * f x := rfl


end BoundedContinuousFunction
