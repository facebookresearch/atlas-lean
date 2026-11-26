/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Copyright (c) 2026 Anthropic, PBC (adapted counting conventions and statement types).
Released under the Apache License, Version 2.0, as described in the LICENSE file.
-/

module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Data.Set.Card
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Algebra.BigOperators.Finprod

/-! # Complex zero counts in height windows -/

@[expose] public noncomputable section

open scoped BigOperators

namespace ComplexZeroCounts

/-- **Zeros in a window.** Zeros of a complex function $f$ in the region $S$
whose imaginary parts belong to the half-open interval $(a,b]$. -/
def windowZeros (f : ℂ → ℂ) (S : Set ℂ) (a b : ℝ) : Set ℂ :=
  {z | z ∈ S ∧ f z = 0 ∧ a < z.im ∧ z.im ≤ b}

/-- **The open critical strip.** The set of complex numbers with real part strictly
between zero and one. -/
def openCriticalStrip : Set ℂ := {z | 0 < z.re ∧ z.re < 1}

/-- **Zero count with multiplicity.** Sum the natural orders of vanishing of $f$ over $S$.
This is a count when $S$ is a finite set of zeros and those orders are finite. The order
is expressed as `analyticOrderAt`; its infinite value is sent to zero, and the finite
sum is zero when its support is infinite. -/
def countWithMultiplicity (f : ℂ → ℂ) (S : Set ℂ) : ℕ :=
  ∑ᶠ z ∈ S, (analyticOrderAt f z).toNat

/-- **Simple zeros on the critical line.** The number of points in $S$ on
$\operatorname{Re}(z)=1/2$ where the analytic order of $f$ is one. Each point is
counted once, with `Set.ncard` returning zero for an infinite set. -/
def countSimpleOnLine (f : ℂ → ℂ) (S : Set ℂ) : ℕ :=
  (S ∩ {z | z.re = 1 / 2} ∩ {z | (analyticOrderAt f z).toNat = 1}).ncard

end ComplexZeroCounts
