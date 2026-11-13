/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Khinchin's conjecture on strong uniform distribution (Erdős Problem 994)

Erdős Problem 994: let `E ⊆ (0, 1)` be a measurable subset with Lebesgue measure `λ(E)`. Is it true
that, for almost all `α`, `lim_{n → ∞} (1/n) ∑_{1 ≤ k ≤ n} 1_{{kα} ∈ E} = λ(E)` for all `E`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Measure.Haar.OfBasis

@[expose] public section

namespace MathlibExt.Analysis.KhinchinStrongUniformDistributionErdosProblem994Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #994, https://www.erdosproblems.com/994 (status
DISPROVED (LEAN)). UnsolvedMath record UM-30007115 (`EP-994`), dataset ulamai/UnsolvedMath v1.8.0.

Khinchin's conjecture fixes `E` first: with 'for almost every `α`, for all `E`' the statement fails
trivially, by removing the countable orbit `{{kα} : k ≥ 1}` from `(0, 1)`. Measurable means Lebesgue
measurable (`NullMeasurableSet E volume`) and `{kα}` is `Int.fract (k α)`. Compared with the
formal-conjectures statement `ErdosProblems/994.lean` (`erdos_994`, same quantifier order over Borel
sets; its refutation implies this one; no code imported).
-/

open MeasureTheory

/-- Erdős Problem 994 (Khinchin's conjecture): for every Lebesgue measurable `E ⊆ (0, 1)`, for
almost every `α`, `(1/n) #{k ≤ n : {kα} ∈ E} → λ(E)`. -/
def khinchinStrongUniformDistribution : Prop :=
  ∀ E : Set ℝ, NullMeasurableSet E volume → E ⊆ Set.Ioo 0 1 →
    ∀ᵐ (α : ℝ) ∂volume, Filter.Tendsto
      (fun n : ℕ => ({k : ℕ | 1 ≤ k ∧ k ≤ n ∧ Int.fract ((k : ℝ) * α) ∈ E}.ncard : ℝ) / n)
      Filter.atTop (nhds (volume E).toReal)

/--
Resolved false: Marstrand disproved Khinchin's conjecture, giving a Borel set `E ⊆ (0, 1)` for which
the averages `(1/n) #{k ≤ n : {kα} ∈ E}` fail to converge to `λ(E)` for almost every `α`;
erdosproblems.com/994 lists the problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem
#994, https://www.erdosproblems.com/994 (status DISPROVED (LEAN)); resolution: J. M. Marstrand, On
Khinchin's conjecture about strong uniform distribution, Proc. London Math. Soc. (3) (1970),
540-556, erdosproblems.com/994: 'In fact this is false, and was disproved by Marstrand'; the
erdosproblems database (teorth/erdosproblems) records Marstrand's answer in the fixed-set quantifier
order: one Borel set fails for almost every α, https://www.erdosproblems.com/994.
-/
public theorem_wanted khinchinStrongUniformDistribution_refuted :
    ¬ khinchinStrongUniformDistribution

end MathlibExt.Analysis.KhinchinStrongUniformDistributionErdosProblem994Wanted
