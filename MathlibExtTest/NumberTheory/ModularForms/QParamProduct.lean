/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.QParamProduct

@[expose] public section

-- exactSource consumer: the original binders apply verbatim.
example (h : ℝ) (hh : 0 < h) (A B : PowerSeries ℂ) (F G : UpperHalfPlane → ℂ)
    (hA : ∀ τ : UpperHalfPlane, HasSum
      (fun m : ℕ => PowerSeries.coeff m A * Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ))
    (hB : ∀ τ : UpperHalfPlane, HasSum
      (fun m : ℕ => PowerSeries.coeff m B * Function.Periodic.qParam h (τ : ℂ) ^ m) (G τ))
    (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ => PowerSeries.coeff m (A * B) *
      Function.Periodic.qParam h (τ : ℂ) ^ m) (F τ * G τ) :=
  ModularCurve.hasSum_qParam_mul h hh A B F G hA hB τ

-- Boundary: zero series sum to zero, and their product does too.
example (h : ℝ) (hh : 0 < h) (τ : UpperHalfPlane) :
    HasSum (fun m : ℕ => PowerSeries.coeff m ((0 : PowerSeries ℂ) * 0) *
      Function.Periodic.qParam h (τ : ℂ) ^ m) (0 * 0) :=
  ModularCurve.hasSum_qParam_mul h hh 0 0 (fun _ => 0) (fun _ => 0)
    (fun _ => by simpa using hasSum_zero) (fun _ => by simpa using hasSum_zero) τ
