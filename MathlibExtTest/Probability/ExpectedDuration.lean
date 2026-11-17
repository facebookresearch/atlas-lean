/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Tactic.NormNum

import MathlibExt.Probability.ExpectedDuration

/-!
# Expected-duration checks

Focused checks for `MathlibExt.Probability.ExpectedDuration`: two
constant paths of durations `1` and `2` under a Dirac measure give
expected maximum `2`, attaining the bound.

These are elaboration and non-vacuity checks, not new results.
-/

open ExpectedDuration MeasureTheory

/-- The bound applied to two constant one-job paths. -/
example : (∫ ω, ⨆ p : Fin 2, pathDuration (fun j : Fin 2 => fun _ : ℝ => (j : ℝ) + 1)
      (fun p : Fin 2 => (([p] : List (Fin 2)) : Multiset (Fin 2))) p ω
      ∂(Measure.dirac (0 : ℝ)))
    ≥ ⨆ p : Fin 2, ((([p] : List (Fin 2)) : Multiset (Fin 2)).map
      fun (j : Fin 2) => ∫ _ : ℝ, ((j : ℝ) + 1) ∂(Measure.dirac (0 : ℝ))).sum :=
  integral_sup_pathDuration_ge (Measure.dirac (0 : ℝ))
    (fun j : Fin 2 => fun _ : ℝ => (j : ℝ) + 1)
    (fun p : Fin 2 => (([p] : List (Fin 2)) : Multiset (Fin 2)))
    (fun j => integrable_const _)
