/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`zeta23/ChallengeDeps.lean` (§§1–2) and the same definitions in
`zeta23/Challenge.lean` (anthropics/formal-math,
https://github.com/anthropics/formal-math/tree/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23):
Copyright (c) 2026 Anthropic, PBC (adapted counting conventions and statement types).
Released under the Apache License, Version 2.0; see the upstream LICENSE:
https://github.com/anthropics/formal-math/blob/11b6c7e3c927df2658f513b6b68ea7f8929c62c5/zeta23/LICENSE
Authors: Claude (as credited in `zeta23/formalization.yaml`; no per-file author list).
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
This counts zeros with multiplicity when $S$ is a finite set of zeros at which $f$ is analytic
and has finite order. `analyticOrderAt` returns zero at nonanalytic points, and conversion to
`ℕ` sends infinite order to zero. The finite sum is zero when its support is infinite. -/
def countWithMultiplicity (f : ℂ → ℂ) (S : Set ℂ) : ℕ :=
  ∑ᶠ z ∈ S, (analyticOrderAt f z).toNat

/-- **Simple zeros on the critical line.** The number of points in $S$ on
$\operatorname{Re}(z)=1/2$ where the analytic order of $f$ is one. Each point is
counted once, with `Set.ncard` returning zero for an infinite set. -/
def countSimpleOnLine (f : ℂ → ℂ) (S : Set ℂ) : ℕ :=
  (S ∩ {z | z.re = 1 / 2} ∩ {z | (analyticOrderAt f z).toNat = 1}).ncard

end ComplexZeroCounts
