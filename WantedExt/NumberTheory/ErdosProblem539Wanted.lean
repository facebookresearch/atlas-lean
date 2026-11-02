/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős Problem 539
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Order.Lattice.Nat

@[expose] public section

open Filter

open scoped Asymptotics

namespace MathlibExt.NumberTheory.ErdosProblem539Wanted

/-! Source record `FC-ErdosProblem539`, ported from FormalConjectures
`ErdosProblems/539.lean` (`def IsCofactorLowerBound`,
`noncomputable def cofactorThreshold`, and the `sq_isBigO` variant) and
checked against erdosproblems.com/539. The open `=Θ` problems are not ported.
Status: resolved true (Erdős–Szemerédi `n^{1/2} ≪ h(n)`). -/

/-- **Cofactor lower bound.** For natural numbers $n$ and $m$, $m$ is a cofactor lower bound for
$n$ when, for every set $A$ of exactly $n$ positive integers, the set
$\{a/\gcd(a,b) : a, b \in A\}$ has at least $m$ elements.

Members of $A$ are required to be positive since the quotient $a/\gcd(a,b)$ is undefined at
$a = b = 0$. -/
def IsCofactorLowerBound (n m : ℕ) : Prop := ∀ A : Finset ℕ, A.card = n →
  (∀ a ∈ A, 0 < a) →
  m ≤ ((A ×ˢ A).image fun (a, b) ↦ a / a.gcd b).card

/-- **Erdős cofactor threshold.** For a natural number $n$, the cofactor threshold $h(n)$ is the
largest natural number $m$ such that for every set $A$ of exactly $n$ positive integers, the set
$\{a/\gcd(a,b) : a, b \in A\}$ has at least $m$ elements. -/
noncomputable def cofactorThreshold (n : ℕ) : ℕ :=
  sSup {m | IsCofactorLowerBound n m}

/-- **Statement of Erdős Problem 539.** Let $h(n)$ denote the cofactor threshold of $n$. The
statement is that $\sqrt{n} = O(h(n))$ as $n \to \infty$, that is, there are a real constant $C$
and an $n_0$ such that $\sqrt{n} \le C\,h(n)$ for all natural numbers $n \ge n_0$. -/
def conjecture : Prop :=
  (fun n : ℕ ↦ Real.sqrt (n : ℝ)) =O[atTop]
    fun n ↦ (cofactorThreshold n : ℝ)

/--
**Erdős Problem 539: square-root lower bound for the cofactor threshold.** For a natural number
$n$, let $h(n)$ be the largest natural number $m$ such that for every set $A$ of exactly $n$
positive integers, the set $\{a/\gcd(a,b) : a, b \in A\}$ has at least $m$ elements. Then
$\sqrt{n} = O(h(n))$ as $n \to \infty$: there are a real constant $C$ and an $n_0$ such that
$\sqrt{n} \le C\,h(n)$ for all natural numbers $n \ge n_0$.

This lower bound was proved by Erdős and Szemerédi. The open problem of determining the exact
order of growth of $h(n)$ is not part of this statement.

Source: J.
Schmitt, T. Gehrunger, J. Dekoninck, G. Bérczi, U. Kreitner, L. Price, D. Holmes, ProofCouncil:
An LLM Agent for Solving Open Mathematical Problems, arXiv:2607.09474 (2026),
https://arxiv.org/abs/2607.09474. Moved from `OpenConjectures/NumberTheory/ErdosProblem539`.
-/
public theorem_wanted conjecture_holds : conjecture

end MathlibExt.NumberTheory.ErdosProblem539Wanted
