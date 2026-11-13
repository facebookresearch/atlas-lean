/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Entire zeros ones lines
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.Basic.Finite.Defs

@[expose] public section

namespace MathlibExt.Analysis.EntireZerosOnesLinesWanted

/-! Source record `AMR-022-2024` (Research Problems in Function Theory,
Problem 2.24). -/

/-- Straight line in the complex plane, [AMR-022-2024] Problem 2.24. -/
def IsComplexLine (s : Set ℂ) : Prop :=
  ∃ a v : ℂ, v ≠ 0 ∧ s = { z | ∃ t : ℝ, z = a + t • v }

/-- All zeros of `f` lie on `l`, [AMR-022-2024] Problem 2.24. -/
def ZerosOnLine (f : ℂ → ℂ) (l : Set ℂ) : Prop :=
  ∀ z : ℂ, f z = 0 → z ∈ l

/-- All ones of `f` lie on `m`, [AMR-022-2024] Problem 2.24. -/
def OnesOnLine (f : ℂ → ℂ) (m : Set ℂ) : Prop :=
  ∀ z : ℂ, f z = 1 → z ∈ m

/-- Open existence question of [AMR-022-2024] Problem 2.24: whether an
entire function can have all its zeros on one straight line and all its
ones on a distinct straight line, with infinitely many of each. Stated as
a proposition whose truth is not asserted here. -/
def conjecture : Prop :=
  ∃ f : ℂ → ℂ, ∃ l m : Set ℂ,
    Differentiable ℂ f ∧ IsComplexLine l ∧ IsComplexLine m ∧ l ≠ m ∧
      ZerosOnLine f l ∧ OnesOnLine f m ∧
      Set.Infinite { z : ℂ | f z = 0 } ∧ Set.Infinite { z : ℂ | f z = 1 }

/--
Resolved true: Baker (Math. Z. 86 (1964)) and Kobayashi (Kodai Math. J. 2 (1979)) showed that
for parallel lines the only transcendental examples are f = P(e^{az}); e.g. e^z - 1 has zeros
2*pi*i*k on the imaginary axis and ones log 2 + 2*pi*i*k, infinitely many each (restated in
arXiv:1509.03283). Source: Walter Bergweiler, Alexandre Eremenko and Aimo Hinkkanen, Entire
functions with two radially distributed values, Math. Proc. Cambridge Philos. Soc. 165 (2018)
93-108, arXiv:1509.03283, https://arxiv.org/abs/1509.03283. Moved from
`OpenConjectures/Analysis/EntireZerosOnesLines`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.Analysis.EntireZerosOnesLinesWanted
