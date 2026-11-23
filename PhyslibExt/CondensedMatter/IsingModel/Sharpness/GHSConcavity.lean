/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.MagnetizationFieldDeriv

/-!
# Concavity of the magnetization and slope bounds

Slope and derivative bounds for a magnetization that is concave in the external field on `[0, ∞)`.

## i. Overview

For a concave function `φ` on `[0, ∞)`, the derivative at `b` is at most the secant slope over `[a,
b]`, and a function with nonpositive second derivative on the interior is concave. Applied to the
Ising magnetization `h ↦ ⟨σ_o⟩_{β,h}`, which vanishes at `h = 0`, the slope bound with `a = 0` gives
`χ(h) ≤ m(h)/h`.

The general statements are thin specializations of Mathlib's `ConcaveOn.deriv_le_slope` and
`concaveOn_of_deriv2_nonpos` to the half-line `[0, ∞)`.

## ii. Key results

- `shg_concaveOn_deriv_le_slope` : derivative versus secant slope for a concave function on `[0, ∞)`
- `shg_concaveOn_of_deriv2_nonpos` : second-derivative test for concavity on `[0, ∞)`
- `shg_magnetization_susceptibility_bound` : `χ(h) ≤ m(h)/h` for a concave magnetization

## iii. Table of contents

- A. Concave functions on the half-line
- B. Application to the magnetization

## iv. References

- R. B. Griffiths, C. A. Hurst, S. Sherman, "Concavity of magnetization of an Ising ferromagnet in a
  positive external field", J. Math. Phys. 11 (1970) 790–795

-/

@[expose] public section

open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Sharpness

open StatMech.Ising

/-! ## A. Concave functions on the half-line -/

/-- The derivative of a concave function on `[0, ∞)` at `b` is at most the secant slope over `[a,
b]`. This is Mathlib's `ConcaveOn.deriv_le_slope` with the slope unfolded. -/
lemma shg_concaveOn_deriv_le_slope (φ : ℝ → ℝ) (hconc : ConcaveOn ℝ (Ici 0) φ)
    {a b : ℝ} (ha : a ∈ Ici (0 : ℝ)) (hb : b ∈ Ici (0 : ℝ)) (hab : a < b)
    (hd : DifferentiableAt ℝ φ b) :
    deriv φ b ≤ (φ b - φ a) / (b - a) := by
  have h := hconc.deriv_le_slope ha hb hab hd
  rwa [slope_def_field] at h

/-- A continuous function on `[0, ∞)`, twice differentiable on the interior with nonpositive second
derivative, is concave. This is Mathlib's `concaveOn_of_deriv2_nonpos` specialized to `Ici 0`. -/
lemma shg_concaveOn_of_deriv2_nonpos (φ : ℝ → ℝ)
    (hcont : ContinuousOn φ (Ici 0))
    (hf' : DifferentiableOn ℝ φ (interior (Ici 0)))
    (hf'' : DifferentiableOn ℝ (deriv φ) (interior (Ici 0)))
    (hu3 : ∀ h ∈ interior (Ici (0 : ℝ)), deriv^[2] φ h ≤ 0) :
    ConcaveOn ℝ (Ici 0) φ :=
  concaveOn_of_deriv2_nonpos (convex_Ici 0) hcont hf' hf'' hu3

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-! ## B. Application to the magnetization -/

lemma shg_magnetization_differentiable (β : ℝ) (o : V) :
    ∀ h ∈ Ici (0 : ℝ),
      DifferentiableAt ℝ (fun h => isingExpectation G β h (fun s => spin s o)) h :=
  fun h _ => (hasDerivAt_magnetization G β h o).differentiableAt

lemma shg_magnetization_antitoneOn_deriv (β : ℝ) (o : V)
    (hconc : ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o))) :
    AntitoneOn (deriv (fun h => isingExpectation G β h (fun s => spin s o))) (Ici 0) :=
  hconc.antitoneOn_deriv (shg_magnetization_differentiable G β o)

lemma shg_magnetization_deriv_le_slope (β : ℝ) (o : V)
    (hconc : ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o)))
    {a b : ℝ} (ha : a ∈ Ici (0 : ℝ)) (hb : b ∈ Ici (0 : ℝ)) (hab : a < b) :
    deriv (fun h => isingExpectation G β h (fun s => spin s o)) b
      ≤ (isingExpectation G β b (fun s => spin s o)
          - isingExpectation G β a (fun s => spin s o)) / (b - a) :=
  shg_concaveOn_deriv_le_slope _ hconc ha hb hab
    ((hasDerivAt_magnetization G β b o).differentiableAt)

lemma shg_magnetization_slope_anti (β : ℝ) (o : V)
    (hconc : ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o)))
    {x : ℝ} (hx : x ∈ Ici (0 : ℝ)) :
    AntitoneOn (slope (fun h => isingExpectation G β h (fun s => spin s o)) x)
      ((Ici 0) \ {x}) :=
  hconc.slope_anti hx

/-- If the magnetization is concave in the field on `[0, ∞)`, then for `h > 0` the susceptibility
satisfies `χ(h) ≤ m(h)/h`, using `m(0) = 0`. -/
lemma shg_magnetization_susceptibility_bound (β h : ℝ) (hh : 0 < h) (o : V)
    (hconc : ConcaveOn ℝ (Ici 0) (fun h => isingExpectation G β h (fun s => spin s o))) :
    deriv (fun h => isingExpectation G β h (fun s => spin s o)) h
      ≤ isingExpectation G β h (fun s => spin s o) / h := by
  have hslope := shg_magnetization_deriv_le_slope G β o hconc
    (mem_Ici.mpr le_rfl) (mem_Ici.mpr hh.le) hh
  rwa [magnetization_zero_field G β o, sub_zero, sub_zero] at hslope

end Sharpness

end StatMech
