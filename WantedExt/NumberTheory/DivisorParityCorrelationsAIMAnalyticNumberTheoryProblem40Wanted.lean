/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Liouville-like functions with vanishing correlations (AimPL, Sarnak's conjecture, Problem 7.2)

AimPL, Sarnak's conjecture, Problem 7.2: let `A = {a₁, a₂, …}` be integers with `(aᵢ, aⱼ) = 1` for
`i ≠ j` and `π(n) = (-1)^{#{aⱼ : aⱼ ∣ n}}`. Is `∑_{n ≤ X} π(n) = o(X)`? Can we find `A` such that
`∑_{n ≤ X} π(n + h₁) ⋯ π(n + h_k) = o(X)` for all distinct `h₁, …, h_k`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Topology.MetricSpace.Pseudo.Defs

@[expose] public section

namespace MathlibExt.NumberTheory.DivisorParityCorrelationsAIMAnalyticNumberTheoryProblem40Wanted

/-!
Source: AimPL: Sarnak's conjecture, Problem 7.2, http://aimpl.org/sarnakconjecture/7/ (remark:
settled by the preprint arXiv:2304.05344 for suitable sets of primes). UnsolvedMath record
UM-20000676 (`AIM-ANALYTIC_NUMBER_THEORY-0040`), dataset ulamai/UnsolvedMath v1.8.0.

Only the second question is stated. The first ('is `∑ π(n) = o(X)`' for every pairwise coprime `A`)
is omitted: as printed it fails for `A = {p² : p prime}`, and the version with `∑ 1/a = ∞` rests on
a result this module does not cite. Elements of `A` are at least `2`, so `#{a ∈ A : a ∣ n}` is
finite for `n ≥ 1`. Shifts are distinct naturals `h₁, …, h_k` with `k ≥ 1`: translating all shifts
by a constant changes the sum by `O(1)` terms, so this is the problem's 'all distinct `hᵢ`'.
-/

/-- `π_A(n) = (-1)^{#{a ∈ A : a ∣ n}}` (the count is finite for `n ≥ 1` when `A ⊆ {2, 3, …}`). -/
noncomputable def divisorParity (A : Set ℕ) (n : ℕ) : ℤ :=
  (-1) ^ Set.ncard {a | a ∈ A ∧ a ∣ n}

/-- The second question of AimPL Problem 7.2 (Sarnak's conjecture): there is a set `A` of pairwise
coprime integers `a ≥ 2` such that for every `k ≥ 1` and all distinct shifts `h₁, …, h_k ≥ 0`,
`∑_{n ≤ X} π_A(n + h₁) ⋯ π_A(n + h_k) = o(X)`. -/
def existsCoprimeSetWithVanishingCorrelations : Prop :=
  ∃ A : Set ℕ, (∀ a ∈ A, 2 ≤ a) ∧ A.Pairwise Nat.Coprime ∧
    ∀ (k : ℕ) (h : Fin k → ℕ), 1 ≤ k → Function.Injective h →
      Filter.Tendsto
        (fun X : ℕ => ((∑ n ∈ Finset.Icc 1 X, ∏ i, divisorParity A (n + h i) : ℤ) : ℝ) / X)
        Filter.atTop (nhds 0)

/--
Resolved true: Klurman, Mangerel and Teräväinen proved that for a set `P` of primes of relative
density `0` with `∑_{p ∈ P} 1/p = ∞`, `f = (-1)^{ω_P}` (which is `π_P`) has `(1/x) ∑_{n ≤ x} f(n +
h₁) ⋯ f(n + h_k) → 0` for all distinct shifts, settling the second question; AimPL cites their
preprint. Source: AimPL: Sarnak's conjecture, Problem 7.2, http://aimpl.org/sarnakconjecture/7/
(remark: settled by the preprint arXiv:2304.05344 for suitable sets of primes); resolution: O.
Klurman, A. P. Mangerel and J. Teräväinen, On Elliott's conjecture and applications, Proc. London
Math. Soc. 133 (2026), arXiv:2304.05344, Theorem 2.1: for f(n) = (-1)^{ω_P(n)}, P a set of primes of
relative density 0 in the primes with Σ_{p∈P} 1/p = ∞, and a_i h_j ≠ a_j h_i for i ≠ j, (1/x)
Σ_{n≤x} f(a_1 n + h_1) ⋯ f(a_k n + h_k) → 0; Section 2.1 presents it as settling de la Rue's AIM
Problem 7.2, and the AimPL remark cites the preprint, https://doi.org/10.1112/plms.70205.
-/
public theorem_wanted existsCoprimeSetWithVanishingCorrelations_holds :
    existsCoprimeSetWithVanishingCorrelations

end MathlibExt.NumberTheory.DivisorParityCorrelationsAIMAnalyticNumberTheoryProblem40Wanted
