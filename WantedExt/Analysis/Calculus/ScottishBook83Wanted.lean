/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Analysis.Calculus.ScottishBook83Wanted

/-- Auerbach's Problem 83 from the Scottish Book: if a continuous
function `f` satisfies, at every point `x`, that the difference
quotients `|f (x + h) - f x| / |h| ^ a` stay below a constant `M` for
all sufficiently small nonzero `h` — that is, if the limsup of the
quotients as `h → 0` is `< M`, with `0 < a < 1` — does `f` then satisfy
a Hölder condition of exponent `a`? -/
def ScottishBookProblem83Claim : Prop :=
  ∀ (a M : ℝ), 0 < a → a < 1 → 0 < M → ∀ f : ℝ → ℝ,
    Continuous f →
    (∀ x : ℝ, ∃ M' : ℝ, M' < M ∧ ∃ δ : ℝ, 0 < δ ∧ ∀ h : ℝ,
      0 < |h| → |h| < δ →
      |f (x + h) - f x| / Real.rpow |h| a ≤ M') →
    ∃ C : ℝ, ∀ x y : ℝ, |f x - f y| ≤ C * Real.rpow |x - y| a

/--
Auerbach's Problem 83 is false: the pointwise limsup condition does
not imply a Hölder condition. Source: H. Auerbach, Problem 83 of the
Scottish Book; typescript Ad 83 records the negative answer, with
Marcinkiewicz's counterexample: a triangular function on intervals
`1 / n - xₙ`, `1 / n + xₙ` with height `1 / n` and suitably small
half-widths `xₙ`, whose difference quotients are small near every
point but which is not globally Hölder.
-/
theorem_wanted auerbach83_refuted : ¬ ScottishBookProblem83Claim

end MathlibExt.Analysis.Calculus.ScottishBook83Wanted
