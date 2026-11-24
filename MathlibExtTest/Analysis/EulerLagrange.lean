/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.EulerLagrange
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-! # Tests for `MathlibExt.Analysis.EulerLagrange` -/

namespace MathlibExtTest.Analysis.EulerLagrange

open Set MathlibExt.Analysis.EulerLagrangeWanted.Analysis

-- Test section: the partial derivatives on concrete Lagrangians. For the free-particle Lagrangian
-- `v ^ 2 / 2`, the partial derivative in velocity is the velocity and the one in position is `0`.
example (x : ℝ → ℝ) (t : ℝ) :
    lagrangianPartialV (fun _ _ v => v ^ 2 / 2) x t = deriv x t := by
  simp [lagrangianPartialV]

example (x : ℝ → ℝ) (t : ℝ) : lagrangianPartialX (fun _ _ v => v ^ 2 / 2) x t = 0 := by
  simp [lagrangianPartialX]

-- For the harmonic-oscillator Lagrangian `v ^ 2 / 2 - y ^ 2 / 2`, the partial derivative in
-- position is `-x t`.
example (x : ℝ → ℝ) (t : ℝ) :
    lagrangianPartialX (fun _ y v => v ^ 2 / 2 - y ^ 2 / 2) x t = -x t := by
  simp [lagrangianPartialX]

-- Both sides of the equation on concrete paths: they vanish along the affine path `s ↦ 3 s + 1`
-- for the free particle, and are both `-sin t` along `sin` for the harmonic oscillator.
example (t : ℝ) :
    lagrangianPartialX (fun _ _ v => v ^ 2 / 2) (fun s => 3 * s + 1) t =
      deriv (lagrangianPartialV (fun _ _ v => v ^ 2 / 2) (fun s => 3 * s + 1)) t := by
  have hV : lagrangianPartialV (fun _ _ v => v ^ 2 / 2) (fun s => 3 * s + 1) = fun _ => 3 := by
    funext s
    simp [lagrangianPartialV]
  simp [lagrangianPartialX, hV]

example (t : ℝ) :
    lagrangianPartialX (fun _ y v => v ^ 2 / 2 - y ^ 2 / 2) Real.sin t =
      deriv (lagrangianPartialV (fun _ y v => v ^ 2 / 2 - y ^ 2 / 2) Real.sin) t := by
  have hV : lagrangianPartialV (fun _ y v => v ^ 2 / 2 - y ^ 2 / 2) Real.sin = Real.cos := by
    funext s
    simp [lagrangianPartialV]
  simp [lagrangianPartialX, hV]

-- Test section: variational extrema. Every `C¹` path is an extremum of the zero Lagrangian, on
-- every interval, empty ones included.
example (a b : ℝ) (x : ℝ → ℝ) (hx : ContDiff ℝ 1 x) :
    IsVariationalExtremum a b (fun _ _ _ => 0) x :=
  ⟨hx, fun _ _ _ _ => by simp⟩

-- Test section: the Euler–Lagrange equation. A `C²` extremum of the free-particle action has
-- zero acceleration on `(a, b)`.
example {a b : ℝ} (x : ℝ → ℝ) (hab : a < b) (hx : ContDiff ℝ 2 x)
    (hxe : IsVariationalExtremum a b (fun _ _ v => v ^ 2 / 2) x) :
    ∀ t ∈ Ioo a b, deriv (deriv x) t = 0 := by
  intro t ht
  have hV : lagrangianPartialV (fun _ _ v => v ^ 2 / 2) x = deriv x := by
    funext s
    simp [lagrangianPartialV]
  have h := euler_lagrange_equation _ x hab (by fun_prop) hx hxe t ht
  simpa [lagrangianPartialX, hV] using h.symm

-- A `C²` extremum of the harmonic-oscillator action satisfies `x'' = -x` on `(a, b)`.
example {a b : ℝ} (x : ℝ → ℝ) (hab : a < b) (hx : ContDiff ℝ 2 x)
    (hxe : IsVariationalExtremum a b (fun _ y v => v ^ 2 / 2 - y ^ 2 / 2) x) :
    ∀ t ∈ Ioo a b, deriv (deriv x) t = -x t := by
  intro t ht
  have hV : lagrangianPartialV (fun _ y v => v ^ 2 / 2 - y ^ 2 / 2) x = deriv x := by
    funext s
    simp [lagrangianPartialV]
  have h := euler_lagrange_equation _ x hab (by fun_prop) hx hxe t ht
  simpa [lagrangianPartialX, hV] using h.symm

end MathlibExtTest.Analysis.EulerLagrange
