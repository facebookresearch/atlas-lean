/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


-- Author: @toskua
module

public import MathlibExt.CategoryTheory.Abelian.AcyclicResolutionCupSign
public import Mathlib.Algebra.Module.LinearMap.Basic
public import Mathlib.Tactic.Ring

/-!
# Cross-degree sign of an integer-bilinear cup pairing

The triangular normalization scalar is `σ_n = (-1)^(n(n+1)/2)`.
For an integer-bilinear pairing, comparing the normalizations in
degrees `p`, `q`, and `p+q` gives the cross-degree sign `(-1)^(pq)`.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe a b c
open CategoryTheory.ProjectiveResolution

namespace CategoryTheory

/- Proof implementation note.
A bilinear pairing transports the two triangular normalization signs with precisely the original
cross-degree sign.
-/

/-- Let `A,B,C` be abelian groups with their integer module actions
and `cup : A →ₗ[ℤ] B →ₗ[ℤ] C`. For `p,q ∈ ℕ`, if
`σ_(p+q) • z = cup(σ_p • x, σ_q • y)`, where
`σ_n = (-1)^(n(n+1)/2)`, then `z = (-1)^(pq) • cup(x,y)`. -/
theorem bilinearCup_normalization_sign
    {A : Type a} {B : Type b} {C : Type c}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module ℤ A] [Module ℤ B] [Module ℤ C]
    (cup : A →ₗ[ℤ] B →ₗ[ℤ] C) (p q : ℕ) (x : A) (y : B) (z : C)
    (h : acyclicResolutionNormalizationSign (p + q) • z =
      cup (acyclicResolutionNormalizationSign p • x)
        (acyclicResolutionNormalizationSign q • y)) :
    z = (-1 : ℤ) ^ (p * q) • cup x y := by
  have hs : acyclicResolutionNormalizationSign (p + q) *
      (acyclicResolutionNormalizationSign p * acyclicResolutionNormalizationSign q) =
        (-1 : ℤ) ^ (p * q) := by
    rw [acyclicResolutionNormalizationSign_add]
    calc
      _ = (-1 : ℤ) ^ (p * q) *
          (acyclicResolutionNormalizationSign p * acyclicResolutionNormalizationSign p) *
          (acyclicResolutionNormalizationSign q * acyclicResolutionNormalizationSign q) := by ring
      _ = _ := by rw [acyclicResolutionNormalizationSign_mul_self,
        acyclicResolutionNormalizationSign_mul_self, mul_one, mul_one]
  have hb : cup (acyclicResolutionNormalizationSign p • x)
      (acyclicResolutionNormalizationSign q • y) =
        (acyclicResolutionNormalizationSign p * acyclicResolutionNormalizationSign q) • cup x y := by
    have hl := congrArg (fun f : B →ₗ[ℤ] C => f (acyclicResolutionNormalizationSign q • y))
      (map_zsmul cup (acyclicResolutionNormalizationSign p) x)
    change cup (acyclicResolutionNormalizationSign p • x)
      (acyclicResolutionNormalizationSign q • y) =
        acyclicResolutionNormalizationSign p • cup x (acyclicResolutionNormalizationSign q • y) at hl
    rw [map_zsmul (cup x) (acyclicResolutionNormalizationSign q) y, smul_smul] at hl
    exact hl
  have he := congrArg (fun v => acyclicResolutionNormalizationSign (p + q) • v) h
  rw [hb] at he
  simpa only [smul_smul, mul_assoc,
    acyclicResolutionNormalizationSign_mul_self, one_smul, hs] using he

end CategoryTheory
