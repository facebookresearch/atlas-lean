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
# The forced degree sign in the bilinear cup comparison
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
universe a b c
open CategoryTheory.ProjectiveResolution

namespace CategoryTheory

/--
A bilinear pairing transports the two triangular normalization signs with precisely the original
cross-degree sign.
-/
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
