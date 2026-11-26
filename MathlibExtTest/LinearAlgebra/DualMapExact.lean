/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.DualMapExact
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.LinearMap.Defs

@[expose] public section

/-- Consumer with the original binders. -/
private theorem exactSource {K V₁ V₂ V₃ : Type*} [Field K]
    [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
    [AddCommGroup V₃] [Module K V₃]
    (f : V₁ →ₗ[K] V₂) (g : V₂ →ₗ[K] V₃) (h : Function.Exact f g) :
    Function.Exact g.dualMap f.dualMap :=
  LinearMap.exact_dualMap_of_exact f g h

/-- A concrete exact pair over the rationals, and its dual exactness. -/
example : Function.Exact
    (LinearMap.dualMap (LinearMap.id : ℚ →ₗ[ℚ] ℚ))
    (LinearMap.dualMap (0 : ℚ →ₗ[ℚ] ℚ)) := by
  apply exactSource (0 : ℚ →ₗ[ℚ] ℚ) (LinearMap.id : ℚ →ₗ[ℚ] ℚ)
  rw [LinearMap.exact_iff]
  simp
