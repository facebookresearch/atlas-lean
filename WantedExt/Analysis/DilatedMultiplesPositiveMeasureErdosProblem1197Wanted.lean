/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Multiples of almost every point meeting dilates of a set (Erdős Problem 1197)

Erdős Problem 1197: let `E ⊆ (0, ∞)` have positive measure. Is it true that for almost all `x > 0`,
for all sufficiently large integers `n` there is an integer `r ≥ 1` with `n x ∈ r · E`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.Analysis.DilatedMultiplesPositiveMeasureErdosProblem1197Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1197, https://www.erdosproblems.com/1197 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30007238 (`EP-1197`), dataset ulamai/UnsolvedMath v1.8.0.

`E` is Lebesgue measurable (Borel measurable in Lean), its measure may be infinite, and
`r · E = {r e : e ∈ E}`. No set `E` containing an interval `(a, b)` with `0 < a < b` can be a
counterexample, so no nonempty open set can: for every `x > 0`, once `n x (1/a - 1/b) > 1` the
interval `(n x / b, n x / a)` contains an integer `r ≥ 1`, and then `n x / r ∈ (a, b) ⊆ E`. Compared
with the formal-conjectures statement `ErdosProblems/1197.lean` (equivalent; no code imported).
-/

open MeasureTheory Filter
open scoped Pointwise

/-- Erdős Problem 1197: for every measurable `E ⊆ (0, ∞)` of positive Lebesgue measure, for almost
every `x > 0` and all sufficiently large integers `n`, there is an integer `r ≥ 1` with
`n x ∈ r • E = {r e : e ∈ E}`. -/
def dilatedMultiplesEventuallyHit : Prop :=
  ∀ E : Set ℝ, MeasurableSet E → E ⊆ Set.Ioi 0 → 0 < volume E →
    ∀ᵐ x ∂(volume.restrict (Set.Ioi (0 : ℝ))), ∀ᶠ n : ℕ in atTop,
      ∃ r : ℕ, 1 ≤ r ∧ (n : ℝ) * x ∈ (r : ℝ) • E

/--
Resolved false: erdosproblems.com/1197 records a counterexample by ebarschkis, built from a variant
of the Buczolich-Mauldin construction: a measurable `E ⊆ (0, ∞)` of positive measure and a set of
`x > 0` of positive measure such that each such `x` has infinitely many `n` with `n x ∉ r • E` for
every integer `r ≥ 1`. Avoiding `E` itself, `x ∉ E / n` for all large `n`, is only the case `r = 1`
and does not suffice, and no set containing an interval can be a counterexample (see the module
note); the site lists the problem as disproved with a Lean proof (plby/lean-proofs,
`Erdos1197.lean`). Source: T. F. Bloom, Erdős Problems, Problem #1197,
https://www.erdosproblems.com/1197 (status DISPROVED (LEAN)); resolution: ebarschkis, negative
solution in the erdosproblems.com/1197 discussion (a variant of the construction of Z. Buczolich and
R. D. Mauldin, Mathematika (1999), 337-341); formal proof plby/lean-proofs,
src/latest/ErdosProblems/Erdos1197.lean, erdosproblems.com/1197: solved in the negative by
ebarschkis with a counterexample built from a variant of the Buczolich-Mauldin construction; status
DISPROVED (LEAN), https://github.com/ebarschkis/ErdosProblem/blob/main/Problem1197/Solution.pdf.
-/
public theorem_wanted dilatedMultiplesEventuallyHit_refuted : ¬ dilatedMultiplesEventuallyHit

end MathlibExt.Analysis.DilatedMultiplesPositiveMeasureErdosProblem1197Wanted
