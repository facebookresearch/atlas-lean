/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 1063
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Topology.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

open Filter
open scoped Nat Topology

namespace MathlibExt.NumberTheory.ErdosProblem1063Wanted

/-! Source record `FC-ErdosProblem1063`, ported from FormalConjectures
`ErdosProblems/1063.lean` (`noncomputable def n`, `theorem
erdos_1063.variants.exists_exception`, `small_values`,
`monier_upper_bound`, `cambie_upper_bound`, `exp_upper_bound`) and checked
against erdosproblems.com/1063. The vacuous `better_upper` claim (an
`answer` placeholder function as a term) is skipped. Hypotheses are
universally closed. The TIP conjunction is split into five established
targets; the open "Estimate `n_k`" question states no conjectured value
and cannot be a target. Status: resolved true as formalized (the five
listed clauses are settled; the estimation question is open). -/

/-- `n k` is the least `n ≥ 2k` such that all but one of `n - i`
(`0 ≤ i < k`) divide `C(n, k)`. -/
noncomputable def n (k : ℕ) : ℕ :=
  sInf {m | 2 * k ≤ m ∧ ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧
    ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k}

/-- The divisibility exception: some `n - i` fails to divide `C(n, k)`
(established). -/
def existsException : Prop :=
  ∀ {n k : ℕ}, 2 ≤ k → 2 * k ≤ n →
    ∃ i < k, ¬ (n - i) ∣ n.choose k

/-- The small values `n_2 = 4`, `n_3 = 6`, `n_4 = 9`, `n_5 = 12`
(established). -/
def smallValues : Prop :=
  n 2 = 4 ∧ n 3 = 6 ∧ n 4 = 9 ∧ n 5 = 12

/-- Monier's `k!` upper bound (established). -/
def monierBound : Prop :=
  ∀ {k : ℕ}, 3 ≤ k → n k ≤ k !

/-- Cambie's lcm upper bound (established). -/
def cambieBound : Prop :=
  ∀ {k : ℕ}, 3 ≤ k → n k ≤ k * (Finset.Icc 1 (k - 1)).lcm id

/-- The `e^((1 + o(1))k)` upper bound (established). -/
def expBound : Prop :=
  ∃ f : ℕ → ℝ, Tendsto f atTop (𝓝 0) ∧
    ∀ k, (n k : ℝ) ≤ Real.exp ((1 + f k) * k)

/--
Resolved true: Every formalized clause is established, per erdosproblems.com/1063 (checked
2026-10-22): for n ≥ 2k some n - i fails to divide C(n, k) (Erdős and Selfridge; proof in Monier
[Mo85]); n_2 = 4, n_3 = 6, n_4 = 9, n_5 = 12; n_k ≤ k! for k ≥ 3 (Monier [Mo85]); and n_k ≤
k·lcm(1, ..., k-1) ≤ e^((1+o(1))k) (Cambie, recorded on the page). The source's request to
estimate n_k states no conjectured value and has no formal target (see gaps). This target holds:
Page: Erdős and Selfridge noted, with a proof in Monier [Mo85], that for n >= 2k at least one n
- i with 0 <= i < k fails to divide C(n, k). Source: Monier [Mo85] (divisibility exception and
k! bound), per erdosproblems.com/1063, https://www.erdosproblems.com/1063; Cambie (lcm
upper-bound improvement, comments), per erdosproblems.com/1063,
https://www.erdosproblems.com/1063. Moved from `OpenConjectures/NumberTheory/ErdosProblem1063`.
-/
public theorem_wanted existsException_holds : existsException

/--
Resolved true: Every formalized clause is established, per erdosproblems.com/1063 (checked
2026-10-22): for n ≥ 2k some n - i fails to divide C(n, k) (Erdős and Selfridge; proof in Monier
[Mo85]); n_2 = 4, n_3 = 6, n_4 = 9, n_5 = 12; n_k ≤ k! for k ≥ 3 (Monier [Mo85]); and n_k ≤
k·lcm(1, ..., k-1) ≤ e^((1+o(1))k) (Cambie, recorded on the page). The source's request to
estimate n_k states no conjectured value and has no formal target (see gaps). This target holds:
Page: n_2 = 4, n_3 = 6, n_4 = 9 and n_5 = 12. Source: Monier [Mo85] (divisibility exception and
k! bound), per erdosproblems.com/1063, https://www.erdosproblems.com/1063; Cambie (lcm
upper-bound improvement, comments), per erdosproblems.com/1063,
https://www.erdosproblems.com/1063. Moved from `OpenConjectures/NumberTheory/ErdosProblem1063`.
-/
public theorem_wanted smallValues_holds : smallValues

/--
Resolved true: Every formalized clause is established, per erdosproblems.com/1063 (checked
2026-10-22): for n ≥ 2k some n - i fails to divide C(n, k) (Erdős and Selfridge; proof in Monier
[Mo85]); n_2 = 4, n_3 = 6, n_4 = 9, n_5 = 12; n_k ≤ k! for k ≥ 3 (Monier [Mo85]); and n_k ≤
k·lcm(1, ..., k-1) ≤ e^((1+o(1))k) (Cambie, recorded on the page). The source's request to
estimate n_k states no conjectured value and has no formal target (see gaps). This target holds:
Page: Monier [Mo85] observed n_k <= k! for k >= 3, since C(k!, k) is divisible by k! - i for 1
<= i < k. Source: Monier [Mo85] (divisibility exception and k! bound), per
erdosproblems.com/1063, https://www.erdosproblems.com/1063; Cambie (lcm upper-bound improvement,
comments), per erdosproblems.com/1063, https://www.erdosproblems.com/1063. Moved from
`OpenConjectures/NumberTheory/ErdosProblem1063`.
-/
public theorem_wanted monierBound_holds : monierBound

/--
Resolved true: Every formalized clause is established, per erdosproblems.com/1063 (checked
2026-10-22): for n ≥ 2k some n - i fails to divide C(n, k) (Erdős and Selfridge; proof in Monier
[Mo85]); n_2 = 4, n_3 = 6, n_4 = 9, n_5 = 12; n_k ≤ k! for k ≥ 3 (Monier [Mo85]); and n_k ≤
k·lcm(1, ..., k-1) ≤ e^((1+o(1))k) (Cambie, recorded on the page). The source's request to
estimate n_k states no conjectured value and has no formal target (see gaps). This target holds:
Page: Cambie improved this to n_k <= k [2, 3, ..., k-1], the lcm form of cambieBound for k >= 3.
Source: Monier [Mo85] (divisibility exception and k! bound), per erdosproblems.com/1063,
https://www.erdosproblems.com/1063; Cambie (lcm upper-bound improvement, comments), per
erdosproblems.com/1063, https://www.erdosproblems.com/1063. Moved from
`OpenConjectures/NumberTheory/ErdosProblem1063`.
-/
public theorem_wanted cambieBound_holds : cambieBound

/--
Resolved true: Every formalized clause is established, per erdosproblems.com/1063 (checked
2026-10-22): for n ≥ 2k some n - i fails to divide C(n, k) (Erdős and Selfridge; proof in Monier
[Mo85]); n_2 = 4, n_3 = 6, n_4 = 9, n_5 = 12; n_k ≤ k! for k ≥ 3 (Monier [Mo85]); and n_k ≤
k·lcm(1, ..., k-1) ≤ e^((1+o(1))k) (Cambie, recorded on the page). The source's request to
estimate n_k states no conjectured value and has no formal target (see gaps). This target holds:
Page: k [2, 3, ..., k-1] <= e^((1+o(1))k), giving expBound. Source: Monier [Mo85] (divisibility
exception and k! bound), per erdosproblems.com/1063, https://www.erdosproblems.com/1063; Cambie
(lcm upper-bound improvement, comments), per erdosproblems.com/1063,
https://www.erdosproblems.com/1063. Moved from `OpenConjectures/NumberTheory/ErdosProblem1063`.
-/
public theorem_wanted expBound_holds : expBound

end MathlibExt.NumberTheory.ErdosProblem1063Wanted
