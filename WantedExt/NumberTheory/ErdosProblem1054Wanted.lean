/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Divisors
public import Mathlib.Data.Set.Card
public import Mathlib.Topology.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import MathlibExt.Data.Set.Density
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem1054Wanted

open scoped BigOperators

/-!
Clause list for [EP-1054] (Erdős Problem #1054):
(a) `n : ℕ` is the target sum;
(b) `m : ℕ` with `1 ≤ m`, minimal with the property;
(c) `k : ℕ` with `1 ≤ k`;
(d) `k ≤ (Nat.divisors m).card`;
(e) `n` equals the sum of the `k` smallest divisors of `m`;
(f) `n = 2` admits no `m`;
(g) `n = 5` admits no `m`;
(h) well-definedness on the domain `6 ≤ n`: a least witness `m` exists (asserted as a conjunct);
(i) universal little-o `f(n) = o(n)`;
(j) almost-all little-o on a density-one set;
(k) `limsup f(n) / n = ∞`.
Every clause appears in the binders below.
-/

/-- Sum of the `k` smallest divisors of `m`, via the sorted divisor list
(helper for [EP-1054]; cf. [Gu04] B2, [468], OEIS A167485). -/
def smallestDivisorPartialSum (m k : ℕ) : ℕ :=
  List.sum (List.take k ((Nat.divisors m).sort (· ≤ ·)))

/-- `IsDivisorInitialSum m n k` holds when `1 ≤ k`, `k` does not exceed the
divisor count of `m`, and `n` is the sum of the `k` smallest divisors of `m`
([EP-1054] defining property). -/
def IsDivisorInitialSum (m n k : ℕ) : Prop :=
  1 ≤ k ∧ k ≤ (Nat.divisors m).card ∧ smallestDivisorPartialSum m k = n

/-- `IsAdmissibleTarget m n` holds when `n` is a sum of an initial segment of
the divisors of `m` ([EP-1054] achievability). -/
def IsAdmissibleTarget (m n : ℕ) : Prop :=
  ∃ k : ℕ, IsDivisorInitialSum m n k

/-- `IsErdosValue n m` holds when `m` is the least integer achieving `n`
([EP-1054] minimality defining `f`). -/
def IsErdosValue (n m : ℕ) : Prop :=
  IsAdmissibleTarget m n ∧ ∀ m' : ℕ, IsAdmissibleTarget m' n → m ≤ m'

/-- The historical question of [EP-1054] (cf. [Gu04] B2, [468], OEIS A167485):
exceptional values `2` and `5`, well-definedness for every `6 ≤ n`, universal little-o versus
almost-all little-o together with `limsup f(n) / n = ∞`. The universal little-o branch is now
known to be false: Tao proved that the upper density of `{n | f(n) ≤ δ • n}` is `O(δ ^ 2)`,
which also rules out the density-one branch (a density-one set on which `f(n) / n → 0` would
force that upper density to be `1` for every `δ > 0`). The historical disjunction below is
therefore false as a whole; it is retained as the source record's statement. -/
def conjecture : Prop :=
  (¬ ∃ m : ℕ, IsAdmissibleTarget m 2) ∧
    (¬ ∃ m : ℕ, IsAdmissibleTarget m 5) ∧
    (∀ n : ℕ, 6 ≤ n → ∃ m : ℕ, IsErdosValue n m) ∧
    ((∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, 6 ≤ n → N ≤ n →
        ∀ m : ℕ, IsErdosValue n m → (m : ℝ) ≤ δ * (n : ℝ)) ∨
      ((∃ S : Set ℕ, S.HasDensity (1 : ℝ) ∧ ∀ δ : ℝ, 0 < δ → ∃ N : ℕ,
          ∀ n : ℕ, n ∈ S → 6 ≤ n → N ≤ n →
            ∀ m : ℕ, IsErdosValue n m → (m : ℝ) ≤ δ * (n : ℝ)) ∧
        ∀ C : ℝ, ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 6 ≤ n ∧
          ∃ m : ℕ, IsErdosValue n m ∧ C * (n : ℝ) ≤ (m : ℝ)))

/--
Resolved false: Both little-o alternatives in the historical EP-1054 question were disproved by
Tao (reported in the maintained EP-1054 record, via the comments to EP-468): the upper density
of {n : f(n) <= delta n} is O(delta^2). This rules out global f(n) = o(n) and also density-one
f(n) = o(n), since a density-one set on which f(n)/n tends to 0 would force that upper density
to be 1 for every delta > 0. The formal target (the historical disjunction, with
well-definedness asserted for n >= 6) is therefore false. Well-definedness of f(n) for all n >=
6 is a separate point: the maintained record (last edited 2025-12-06) calls it likely, following
from a strong form of Goldbach's conjecture. Source: T. F. Bloom, Erdos Problem #1054,
https://www.erdosproblems.com/1054. Moved from `OpenConjectures/NumberTheory/ErdosProblem1054`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.NumberTheory.ErdosProblem1054Wanted
