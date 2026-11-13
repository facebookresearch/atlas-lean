/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 415
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem415Wanted

/-! Source record `EP-415` (Erdős Problems), statement frozen from
https://www.erdosproblems.com/415. The first question (a positive leading
constant) was answered negatively: the cited page records the
Pollack–Pomerance–Treviño [PPT13] asymptotic with an extra iterated-log
denominator, so no `c > 0` works.

Clause map: "ordering pattern" is a permutation `σ` of `Fin k`, appearing in
a value sequence when `σ`-earlier positions hold strictly smaller values;
"`F(n)`, the largest `k` with all `k!` patterns appearing" is `patNum`
(`sSup` over `k ≤ n`, nonempty since `0` qualifies); "`F(n) =
(c+o(1)) log log log n` with `c > 0`" is convergence of the ratio to a
positive `c`. The "first failing pattern" and "most likely pattern"
questions have no precise conjectured form and are not formalized. -/

/-- A permutation pattern `σ` appears in the value sequence `x` when
`σ`-earlier positions are strictly increasing. -/
def patternAppears (k : ℕ) (σ : Equiv.Perm (Fin k)) (x : Fin k → ℕ) : Prop :=
  ∀ i j : Fin k, σ i < σ j → x i < x j

/-- All `k!` patterns appear somewhere in `φ` below `n`. -/
def allPatternsBelow (k n : ℕ) : Prop :=
  ∀ σ : Equiv.Perm (Fin k),
    ∃ m : ℕ, m + k ≤ n ∧
      patternAppears k σ (fun i : Fin k => Nat.totient (m + 1 + (i : ℕ)))

/-- `F(n)`: the largest `k ≤ n` with all patterns appearing below `n`. -/
noncomputable def patNum (n : ℕ) : ℕ :=
  sSup { k : ℕ | k ≤ n ∧ allPatternsBelow k n }

/-- Erdős Problem 415: `F(n) / log log log n → c` for some positive constant `c`. -/
def conjecture : Prop :=
  ∃ c : ℝ, 0 < c ∧
    Filter.Tendsto
      (fun n : ℕ => (patNum n : ℝ) /
        Real.log (Real.log (Real.log (n : ℝ))))
      Filter.atTop (nhds c)

/--
Resolved false: The formalized first question (F(n) = (c + o(1)) log log log n with c > 0) has a
negative answer: Pollack, Pomerance, and Treviño (Ramanujan J. 2013) proved that the longest
strictly decreasing run G(n) of φ(m+1), …, φ(m+k) with m + k ≤ n satisfies G(n) ~ log log log n
/ log log log log log log n, and F(n) ≤ G(n) (erdosproblems.com/415, checked 2026-10-22). The
questions about the first failing and the most likely patterns are not formalized. Source: Erdős
Problems, Problem 415 (records the Pollack–Pomerance–Treviño [PPT13] negative answer),
https://www.erdosproblems.com/415; Paul Pollack, Carl Pomerance, and Enrique Treviño, Sets of
monotonicity for Euler's totient function, The Ramanujan Journal 30 (2013), 379-398,
https://doi.org/10.1007/s11139-012-9386-6. Moved from
`OpenConjectures/NumberTheory/ErdosProblem415`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.NumberTheory.ErdosProblem415Wanted
