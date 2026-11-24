/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.EulerBernoulliBeam
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Uniqueness of the uniform-load quartic

## i. Overview

In the prescribed quartic class `a * x^4 + b * x^3 + c * x^2 +
d * x + e`, the simply supported uniform-load conditions in
coefficient form (constant fourth derivative through
`24 * a * EI = w`, zero values at the supports, zero formal
second-derivative values at the supports, nonzero span) determine
the quartic uniquely: it is the uniform-load deflection profile,
identified with the canonical `uniformLoadDeflection`.

## ii. Key results

- `Mechanics.EulerBernoulli.quartic_unique`: uniqueness in the
  quartic class.
- `Mechanics.EulerBernoulli.quartic_unique_uniformLoadDeflection`:
  the same conclusion against the canonical deflection.

## iii. Table of contents

- A. Quartic uniqueness

## iv. References

- S. Timoshenko, *Strength of Materials, Part I*, 3rd edition,
  1955 (uniformly loaded simply supported beam).
-/

@[expose] public section

namespace Mechanics.EulerBernoulli

/-! ## A. Quartic uniqueness -/

/-- A quartic profile in coefficient form
`a*x^4 + b*x^3 + c*x^2 + d*x + e`. -/
noncomputable def quarticFun (a b c d e x : ℝ) : ℝ :=
  a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x + e

/-- Uniqueness in the prescribed quartic class: if a quartic has
constant fourth derivative encoded by `24 * a * EI = w`, value
zero at both supports, and formal second-derivative values
`2*c` at `0` and `12*a*L^2 + 6*b*L + 2*c` at `L` equal to zero,
for nonzero span `L`, then it is exactly the uniform-load
simply supported deflection profile. -/
theorem quartic_unique {a b c d e w EI L : ℝ} (hEI : EI ≠ 0)
    (hL : L ≠ 0) (hload : 24 * a * EI = w)
    (hp0 : quarticFun a b c d e 0 = 0)
    (hm0 : 2 * c = 0)
    (hpL : quarticFun a b c d e L = 0)
    (hmL : 12 * a * L ^ 2 + 6 * b * L + 2 * c = 0) :
    ∀ x : ℝ, quarticFun a b c d e x
      = w * x * (L ^ 3 - 2 * L * x ^ 2 + x ^ 3) / (24 * EI) := by
  have he : e = 0 := by simpa [quarticFun] using hp0
  have hc : c = 0 := by
    have h2 : (2 : ℝ) ≠ 0 := by norm_num
    rcases (mul_eq_zero.mp hm0) with h | h
    · exact absurd h h2
    · exact h
  have h6L : (6 : ℝ) * L ≠ 0 := mul_ne_zero (by norm_num) hL
  have hb : b = -2 * a * L := by
    have h0 : (2 * a * L + b) * (6 * L) = 0 := by
      rw [hc] at hmL
      grind
    rcases (mul_eq_zero.mp h0) with h | h
    · grind
    · exact absurd h h6L
  have hd : d = a * L ^ 3 := by
    have hpL' := hpL
    simp only [quarticFun] at hpL'
    rw [he, hc, hb] at hpL'
    have hsub : d * L = a * L ^ 4 := by grind
    have h0 : (d - a * L ^ 3) * L = 0 := by grind
    rcases (mul_eq_zero.mp h0) with h | h
    · grind
    · exact absurd h hL
  intro x
  have h24 : (24 : ℝ) * EI ≠ 0 := mul_ne_zero (by norm_num) hEI
  simp only [quarticFun]
  rw [he, hc, hb, hd, ← hload, eq_div_iff h24]
  grind

/-- Uniqueness against the canonical deflection: under the same
coefficient hypotheses the quartic is the uniform-load
deflection `uniformLoadDeflection`. -/
theorem quartic_unique_uniformLoadDeflection {a b c d e w EI L : ℝ}
    (hEI : EI ≠ 0) (hL : L ≠ 0) (hload : 24 * a * EI = w)
    (hp0 : quarticFun a b c d e 0 = 0)
    (hm0 : 2 * c = 0)
    (hpL : quarticFun a b c d e L = 0)
    (hmL : 12 * a * L ^ 2 + 6 * b * L + 2 * c = 0) :
    ∀ x : ℝ, quarticFun a b c d e x
      = uniformLoadDeflection w EI L x := by
  intro x
  rw [quartic_unique hEI hL hload hp0 hm0 hpL hmL x]
  unfold uniformLoadDeflection
  ring

end Mechanics.EulerBernoulli
