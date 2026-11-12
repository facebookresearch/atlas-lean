/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.Ring

/-!
# Vorticity and large-scale atmospheric waves

For the linear barotropic beta-plane vorticity equation, a plane mode
has dispersion relation `omega = U * k - beta * k / (k^2 + l^2)` for
`k^2 + l^2 > 0`, equivalently
`(omega - U * k) * (k^2 + l^2) = -beta * k`. For `k ≠ 0` the phase
speed is `omega / k = U - beta / (k^2 + l^2)`; in particular `beta = 0`
gives pure advection `omega = U * k`. This is a model dispersion
identity, not nonlinear existence or stability.

## i. Overview

The dispersion relation and its solved form are related by clearing
the denominator `k^2 + l^2`; dividing by `k` gives the phase speed.

## ii. Key results

- `EarthScience.rossby_dispersion`: plane mode satisfies the dispersion product form.
- `EarthScience.rossby_dispersion_iff`: the dispersion relation determines `omega` uniquely.
- `EarthScience.rossby_phase_speed`: phase speed formula.

## iii. Table of contents

- A. Rossby dispersion

## iv. References

- `field_simp` / `linear_combination` in Mathlib.
-/

@[expose] public section

namespace EarthScience


/-- Rossby dispersion: a plane mode with `omega = U * k - beta * k / (k^2 + l^2)`
satisfies `(omega - U * k) * (k^2 + l^2) = -beta * k`. -/
theorem rossby_dispersion {U beta k l omega : ℝ} (h : k ^ 2 + l ^ 2 ≠ 0)
    (homega : omega = U * k - beta * k / (k ^ 2 + l ^ 2)) :
    (omega - U * k) * (k ^ 2 + l ^ 2) = -beta * k := by
  rw [homega]
  field_simp
  ring

/-- The dispersion relation determines `omega` uniquely: for
`k^2 + l^2 ≠ 0`, `omega = U * k - beta * k / (k^2 + l^2)` iff
`(omega - U * k) * (k^2 + l^2) = -beta * k`. -/
theorem rossby_dispersion_iff {U beta k l omega : ℝ} (h : k ^ 2 + l ^ 2 ≠ 0) :
    omega = U * k - beta * k / (k ^ 2 + l ^ 2) ↔
      (omega - U * k) * (k ^ 2 + l ^ 2) = -beta * k := by
  constructor
  · intro homega
    exact rossby_dispersion h homega
  · intro hmul
    have heq : omega - U * k = -beta * k / (k ^ 2 + l ^ 2) := by
      rw [eq_div_iff h]
      linarith
    linear_combination heq

/-- Phase speed: for `k ≠ 0`, `omega / k = U - beta / (k^2 + l^2)`;
in particular `beta = 0` gives `omega = U * k` (pure advection). -/
theorem rossby_phase_speed {U beta k l omega : ℝ} (hk : k ≠ 0)
    (h : k ^ 2 + l ^ 2 ≠ 0)
    (homega : omega = U * k - beta * k / (k ^ 2 + l ^ 2)) :
    omega / k = U - beta / (k ^ 2 + l ^ 2) := by
  rw [homega]
  field_simp


end EarthScience
