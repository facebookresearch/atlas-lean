/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 650
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Floor.Defs
public import Mathlib.Data.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Order.Interval.Set.Defs
public import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace MathlibExt.NumberTheory.ErdosProblem650Wanted

/-! Source record `FC-ErdosProblem650`, ported from FormalConjectures
`ErdosProblems/650.lean` (`noncomputable def f`, `theorem erdos_650` and
its `variants`) and checked against erdosproblems.com/650. The upstream
`answer(False)` is elaborated to a negation. Status: resolved
([ErSu59], Erdős–Selfridge, [VLT26]; formalized in Lean by van Doorn). -/

/-- **Erdős's matching function for multiples in intervals.** For a natural number $m$, $f(m)$ is
the largest natural number $r$ such that for every natural number $N$, every set
$A \subseteq \{1, \dots, N\}$ with exactly $m$ elements and every real $x \ge 1$, there are
distinct $a_1, \dots, a_r \in A$ and distinct natural numbers $b_1, \dots, b_r$ in the open
interval $(x, x + 2N)$ with $a_i \mid b_i$ for every $i$. -/
noncomputable def f (m : ℕ) : ℕ :=
  sSup {r : ℕ | ∀ N : ℕ, ∀ A ⊆ Finset.Icc 1 N, A.card = m → ∀ x : ℝ, 1 ≤ x →
    ∃ a b : Fin r → ℕ, Function.Injective a ∧ Function.Injective b ∧
      (∀ i, a i ∈ A) ∧ (∀ i, (b i : ℝ) ∈ Set.Ioo x (x + 2 * (N : ℝ))) ∧
      (∀ i, a i ∣ b i)}

/-- **Statement of Erdős Problem 650.** Let $f$ be Erdős's matching function for multiples in
intervals. The statement is the conjunction of four claims: for every natural number $m$,
$f(m) = \min(m, \lceil 2\sqrt{m}\,\rceil)$; it is not the case that $f(m) \le \sqrt{m}$ for every
natural number $m$; $\sqrt{m} \le f(m)$ for every natural number $m$; and $f(m^2) \le 2m$ for
every natural number $m$. -/
def conjecture : Prop :=
  (∀ m : ℕ, f m = min m ⌈2 * Real.sqrt m⌉₊) ∧
  (¬ ∀ m : ℕ, (f m : ℝ) ≤ Real.sqrt m) ∧
  (∀ m : ℕ, Real.sqrt m ≤ (f m : ℝ)) ∧
  (∀ m : ℕ, f (m ^ 2) ≤ 2 * m)

/--
**Erdős Problem 650: matching integers to distinct multiples.** For a natural number $m$, let
$f(m)$ be the largest natural number $r$ such that for every natural number $N$, every set
$A \subseteq \{1, \dots, N\}$ with exactly $m$ elements and every real $x \ge 1$, there are
distinct $a_1, \dots, a_r \in A$ and distinct natural numbers $b_1, \dots, b_r$ in the open
interval $(x, x + 2N)$ with $a_i \mid b_i$ for every $i$. Then $f(m) = \min(m,
\lceil 2\sqrt{m}\,\rceil)$ for every natural number $m$; it is not the case that
$f(m) \le \sqrt{m}$ for every natural number $m$; $\sqrt{m} \le f(m)$ for every natural number
$m$; and $f(m^2) \le 2m$ for every natural number $m$.

Solved by Erdős–Surányi [ErSu59], Erdős–Selfridge [Er78], [Er86c] and van Doorn–Li–Tang [VLT26].

Source: [VLT26] W. van Doorn, Y. Li and Q. Tang, Optimal bounds
for an Erdős problem on matching integers to distinct multiples, arXiv:2603.28636 (2026),
https://arxiv.org/abs/2603.28636; W. van Doorn, Lean formalization of Erdős Problem 650
(Aristotle-assisted),
https://github.com/Woett/Lean-files/blob/c100ed4a4429e987a9555ee428a1aa524a46e16d/ErdosProblem650.lean.
Moved from `OpenConjectures/NumberTheory/ErdosProblem650`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.ErdosProblem650Wanted
