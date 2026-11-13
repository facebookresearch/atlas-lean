/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Beta-plane Rossby mode dispersion

A linear beta-plane Rossby mode `psi(t, x, y) = A cos(kx + ly - omega t)`
has Laplacian `-(k^2 + l^2) psi`, and its beta-plane vorticity residual
`d/dt (nabla^2 psi) + beta * psi_x` factorises as
`-A sin(kx + ly - omega t) * ((k^2 + l^2) omega + beta k)`. The
dispersion relation `omega = -beta k / (k^2 + l^2)` makes the factor
vanish, so the mode satisfies its dispersion relation.

## i. Overview

The derivative helpers differentiate the cosine phase in each variable.
The Laplacian is `-(k^2 + l^2)` times the mode; differentiating it in
time brings out `omega`. The residual factorises, and the dispersion
relation is exactly the vanishing of that factor.

## ii. Key results

- `EarthScience.rossby_mode_beta_plane_residual`: the residual
  factorisation.
- `EarthScience.rossby_mode_satisfies_dispersion`: the mode satisfies
  its dispersion relation.

## iii. Table of contents

- A. Rossby mode residual and dispersion

## iv. References

- `HasDerivAt.cos`, `HasDerivAt.sin` in Mathlib.

## A. Rossby mode residual and dispersion
-/

@[expose] public section

namespace EarthScience

private theorem phase_hasDerivAt_x (k l ω y τ u : ℝ) :
    HasDerivAt (fun u' => k * u' + l * y - ω * τ) k u := by
  simpa using (((hasDerivAt_id' u).const_mul k).add_const (l * y)).sub_const (ω * τ)

private theorem phase_hasDerivAt_y (k l ω x τ v : ℝ) :
    HasDerivAt (fun v' => k * x + l * v' - ω * τ) l v := by
  simpa using ((((hasDerivAt_id' v).const_mul l).const_add (k * x))).sub_const (ω * τ)

private theorem phase_hasDerivAt_t (k l ω x y τ : ℝ) :
    HasDerivAt (fun σ => k * x + l * y - ω * σ) (-ω) τ := by
  have h1 : HasDerivAt (fun _ : ℝ => k * x + l * y) (0 : ℝ) τ := hasDerivAt_const τ (k * x + l * y)
  have h2 : HasDerivAt (fun σ => ω * σ) (ω * 1) τ := (hasDerivAt_id' τ).const_mul ω
  have h := h1.sub h2
  have hfun : ((fun _ : ℝ => k * x + l * y) - (fun σ : ℝ => ω * σ)) =
      (fun σ => k * x + l * y - ω * σ) := by
    ext σ
    simp [Pi.sub_apply]
  rw [hfun] at h
  simpa using h

private theorem deriv_cos_x1 (A k l ω y τ u : ℝ) :
    deriv (fun u' => A * Real.cos (k * u' + l * y - ω * τ)) u =
      (-A * k) * Real.sin (k * u + l * y - ω * τ) := by
  have hφ := phase_hasDerivAt_x k l ω y τ u
  have h := hφ.cos.const_mul A
  have hd := h.deriv
  simpa using hd.trans (by ring : A * (-Real.sin (k * u + l * y - ω * τ) * k) =
    (-A * k) * Real.sin (k * u + l * y - ω * τ))

private theorem deriv_cos_y1 (A k l ω x τ v : ℝ) :
    deriv (fun v' => A * Real.cos (k * x + l * v' - ω * τ)) v =
      (-A * l) * Real.sin (k * x + l * v - ω * τ) := by
  have hφ := phase_hasDerivAt_y k l ω x τ v
  have h := hφ.cos.const_mul A
  have hd := h.deriv
  simpa using hd.trans (by ring : A * (-Real.sin (k * x + l * v - ω * τ) * l) =
    (-A * l) * Real.sin (k * x + l * v - ω * τ))

private theorem deriv_cos_x2 (A k l ω y τ x : ℝ) :
    deriv (fun u => deriv (fun u' => A * Real.cos (k * u' + l * y - ω * τ)) u) x =
      (-A * k ^ 2) * Real.cos (k * x + l * y - ω * τ) := by
  have h1 : ∀ u, deriv (fun u' => A * Real.cos (k * u' + l * y - ω * τ)) u =
      (-A * k) * Real.sin (k * u + l * y - ω * τ) :=
    fun u => deriv_cos_x1 A k l ω y τ u
  have hfun : (fun u => deriv (fun u' => A * Real.cos (k * u' + l * y - ω * τ)) u) =
      (fun u => (-A * k) * Real.sin (k * u + l * y - ω * τ)) := funext h1
  rw [hfun]
  have hφ := phase_hasDerivAt_x k l ω y τ x
  have h := hφ.sin.const_mul (-A * k)
  have hd := h.deriv
  simpa using hd.trans (by ring : (-A * k) * (Real.cos (k * x + l * y - ω * τ) * k) =
    (-A * k ^ 2) * Real.cos (k * x + l * y - ω * τ))

private theorem deriv_cos_y2 (A k l ω x τ y : ℝ) :
    deriv (fun v => deriv (fun v' => A * Real.cos (k * x + l * v' - ω * τ)) v) y =
      (-A * l ^ 2) * Real.cos (k * x + l * y - ω * τ) := by
  have h1 : ∀ v, deriv (fun v' => A * Real.cos (k * x + l * v' - ω * τ)) v =
      (-A * l) * Real.sin (k * x + l * v - ω * τ) :=
    fun v => deriv_cos_y1 A k l ω x τ v
  have hfun : (fun v => deriv (fun v' => A * Real.cos (k * x + l * v' - ω * τ)) v) =
      (fun v => (-A * l) * Real.sin (k * x + l * v - ω * τ)) := funext h1
  rw [hfun]
  have hφ := phase_hasDerivAt_y k l ω x τ y
  have h := hφ.sin.const_mul (-A * l)
  have hd := h.deriv
  simpa using hd.trans (by ring : (-A * l) * (Real.cos (k * x + l * y - ω * τ) * l) =
    (-A * l ^ 2) * Real.cos (k * x + l * y - ω * τ))

private theorem deriv_laplacian_t (A k l ω t x y : ℝ) :
    deriv (fun τ => deriv (fun u => deriv (fun u' => A * Real.cos (k * u' + l * y - ω * τ)) u) x +
        deriv (fun v => deriv (fun v' => A * Real.cos (k * x + l * v' - ω * τ)) v) y) t =
      (-A * (k ^ 2 + l ^ 2) * ω) * Real.sin (k * x + l * y - ω * t) := by
  have hLap : ∀ τ, (deriv (fun u => deriv (fun u' => A * Real.cos (k * u' + l * y - ω * τ)) u) x +
        deriv (fun v => deriv (fun v' => A * Real.cos (k * x + l * v' - ω * τ)) v) y) =
      (-A * (k ^ 2 + l ^ 2)) * Real.cos (k * x + l * y - ω * τ) := by
    intro τ
    rw [deriv_cos_x2, deriv_cos_y2]
    ring
  have hfun : (fun τ => deriv (fun u =>
        deriv (fun u' => A * Real.cos (k * u' + l * y - ω * τ)) u) x +
        deriv (fun v => deriv (fun v' => A * Real.cos (k * x + l * v' - ω * τ)) v) y) =
      (fun τ => (-A * (k ^ 2 + l ^ 2)) * Real.cos (k * x + l * y - ω * τ)) := funext hLap
  rw [hfun]
  have hφ := phase_hasDerivAt_t k l ω x y t
  have h := hφ.cos.const_mul (-A * (k ^ 2 + l ^ 2))
  have hd := h.deriv
  simpa using hd.trans (by ring : (-A * (k ^ 2 + l ^ 2)) *
      (-Real.sin (k * x + l * y - ω * t) * -ω) =
    (-A * (k ^ 2 + l ^ 2) * ω) * Real.sin (k * x + l * y - ω * t))

/-- A linear β-plane Rossby mode `ψ(t, x, y) = A cos(kx + ly - ωt)`:
the β-plane vorticity residual `∂ₜ∇²ψ + β ∂ₓψ` factorises as
`-A sin(kx + ly - ωt) * ((k² + l²) ω + β k)`. -/
theorem rossby_mode_beta_plane_residual {A β k l ω t x y : ℝ} :
    deriv (fun τ => deriv (fun u => deriv (fun u' => A * Real.cos (k * u' + l * y - ω * τ)) u) x +
        deriv (fun v => deriv (fun v' => A * Real.cos (k * x + l * v' - ω * τ)) v) y) t +
      β * deriv (fun u => A * Real.cos (k * u + l * y - ω * t)) x =
      -A * Real.sin (k * x + l * y - ω * t) * ((k ^ 2 + l ^ 2) * ω + β * k) := by
  rw [deriv_laplacian_t, deriv_cos_x1]
  ring

/-- Dispersion relation: with `ω = -β k / (k² + l²)` the residual above
vanishes, i.e. the specified linear β-plane mode satisfies its dispersion
relation. -/
theorem rossby_mode_satisfies_dispersion {A β k l t x y : ℝ}
    (hkl : k ^ 2 + l ^ 2 ≠ 0) :
    deriv (fun τ => deriv (fun u =>
        deriv (fun u' => A * Real.cos (k * u' + l * y - (-β * k / (k ^ 2 + l ^ 2)) * τ)) u) x +
        deriv (fun v =>
          deriv (fun v' => A * Real.cos (k * x + l * v' - (-β * k / (k ^ 2 + l ^ 2)) * τ)) v) y) t +
      β * deriv (fun u => A * Real.cos (k * u + l * y - (-β * k / (k ^ 2 + l ^ 2)) * t)) x = 0 := by
  have h := rossby_mode_beta_plane_residual (A := A) (β := β) (k := k) (l := l)
    (ω := -β * k / (k ^ 2 + l ^ 2)) (t := t) (x := x) (y := y)
  have hfactor : (k ^ 2 + l ^ 2) * (-β * k / (k ^ 2 + l ^ 2)) + β * k = 0 := by
    field_simp
    ring
  rw [hfactor, mul_zero] at h
  exact h

end EarthScience
