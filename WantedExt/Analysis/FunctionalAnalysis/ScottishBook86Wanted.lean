/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Restrict
public import Mathlib.Order.Interval.Set.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.Analysis.FunctionalAnalysis.ScottishBook86Wanted

open MeasureTheory

/-- Lebesgue measure restricted to the unit interval, the ambient
measure for Problem 86. -/
noncomputable def scottishBook86Measure : MeasureTheory.Measure ℝ :=
  MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)

/-- Banach's Problem 86 from the Scottish Book: can every sequence
`φ` of functions on `[0, 1]` that is orthogonal, normed (in `L²`),
measurable, and uniformly bounded by `M` be completed, using functions
with the same bound `M`, to a sequence `ψ` that is orthogonal, normed,
and complete? Completeness is the vanishing of the orthogonal
complement in `L²`: every square-integrable `g` orthogonal to all of
`ψ` is zero almost everywhere. The case of interest is when infinitely
many functions are necessary for the completion. -/
def ScottishBookProblem86Claim : Prop :=
  ∀ (M : ℝ) (φ : ℕ → ℝ → ℝ), 0 < M →
    (∀ n, AEStronglyMeasurable (φ n) scottishBook86Measure) →
    (∀ n m, ∫ t, φ n t * φ m t ∂scottishBook86Measure =
      if n = m then 1 else 0) →
    (∀ n t, t ∈ Set.Icc (0 : ℝ) 1 → |φ n t| ≤ M) →
    ∃ ψ : ℕ → ℝ → ℝ,
      (∀ n, AEStronglyMeasurable (ψ n) scottishBook86Measure) ∧
      (∀ n m, ∫ t, ψ n t * ψ m t ∂scottishBook86Measure =
        if n = m then 1 else 0) ∧
      (∀ n t, t ∈ Set.Icc (0 : ℝ) 1 → |ψ n t| ≤ M) ∧
      (∀ n, ∃ m, ψ m = φ n) ∧
      ∀ g : ℝ → ℝ, MemLp g 2 scottishBook86Measure →
        (∀ n, ∫ t, ψ n t * g t ∂scottishBook86Measure = 0) →
        g =ᵐ[scottishBook86Measure] 0

/--
Banach's Problem 86 is false: an orthogonal, normed, measurable,
uniformly bounded sequence need not admit a completion to a complete
orthonormal sequence using functions with the same bound. Source:
S. Banach, Problem 86 of the Scottish Book; negative answer via
A. Plichko and A. Razenkov, "On three problems from the Scottish Book
connected with orthogonal systems", Colloq. Math. 70 (1996), 227–234,
Proposition 3, which constructs a bounded orthogonal sequence in a
Banach space densely and non-compactly embedded in a Hilbert space
that admits no extension to a fundamental orthogonal sequence using
elements of the Banach space. Earlier work on the problem includes
S. Kaczmarz (1936) and K. S. Kazarian ("On a problem of S. Banach
from the Scottish Book", Proc. Amer. Math. Soc. 110 (1990), 881–887).
-/
theorem_wanted banach86_refuted : ¬ ScottishBookProblem86Claim

end MathlibExt.Analysis.FunctionalAnalysis.ScottishBook86Wanted
