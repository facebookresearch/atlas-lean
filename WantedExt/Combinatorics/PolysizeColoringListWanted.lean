/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Polynomial-size list of discrepancy colorings
-/
module

public import Mathlib.Data.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.SetNotation
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.PolysizeColoringListWanted

/-! Source record `AIM-COMBINATORICS-0047__20000922`. -/

open scoped BigOperators

/-- **Discrepancy of a matrix on a set of columns.** For a real $n \times m$ matrix $A$ and a set
$S$ of columns of $A$, the discrepancy of $A$ on $S$ is the minimum, over all sign vectors
$\varepsilon \in \{-1, 1\}^m$, of $\max_i \left|\sum_{j \in S} A_{ij} \varepsilon_j\right|$, the
largest absolute value of a row sum of $A$ restricted to $S$ and weighted by $\varepsilon$
(taken to be $0$ when $A$ has no rows). -/
noncomputable def discrepancyOn {n m : ℕ} (A : Fin n → Fin m → ℝ)
    (S : Finset (Fin m)) : ℝ :=
  sInf ((fun ε : Fin m → Bool =>
    ⨆ i : Fin n, |∑ j ∈ S, A i j * (if ε j then (1 : ℝ) else -1)|) ''
    Set.univ)

/-- **Hereditary discrepancy of a real matrix.** The hereditary discrepancy
$\operatorname{herdisc}(A)$ of a real $n \times m$ matrix $A$ is the maximum, over all sets $S$
of columns of $A$, of the discrepancy of $A$ on $S$. -/
noncomputable def hereditaryDisc {n m : ℕ} (A : Fin n → Fin m → ℝ) : ℝ :=
  ⨆ S : Finset (Fin m), discrepancyOn A S

/-- **Polynomial-size colouring list conjecture.** The statement that there exist a real number
$C > 0$ and a natural number $k$ such that for all positive integers $n$ and $m$ and every real
$n \times m$ matrix $A$ there is a set $L$ of at most $m^k$ sign vectors in $\{-1, 1\}^m$ with
the following property: for every set $S$ of columns of $A$ some $\varepsilon \in L$ satisfies
$\left|\sum_{j \in S} A_{ij} \varepsilon_j\right| \le C \operatorname{herdisc}(A)$ for every row
$i$, where $\operatorname{herdisc}(A)$ is the hereditary discrepancy of $A$.

Source: AIM-COMBINATORICS-0047__20000922; AIM Hereditary discrepancy, item 1.85. -/
def conjecture : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ k : ℕ,
    ∀ (n m : ℕ), 0 < n → 0 < m →
    ∀ A : Fin n → Fin m → ℝ,
      ∃ L : Finset (Fin m → ℝ),
        (L.card : ℝ) ≤ (m : ℝ) ^ k ∧
        (∀ ε ∈ L, ∀ j, ε j = 1 ∨ ε j = -1) ∧
        ∀ S : Finset (Fin m),
          ∃ ε ∈ L, ∀ i, |∑ j ∈ S, A i j * ε j| ≤
            C * hereditaryDisc A

/--
**The polynomial-size colouring list conjecture is false.** There do not exist a real number
$C > 0$ and a natural number $k$ such that for all positive integers $n$ and $m$ and every real
$n \times m$ matrix $A$ there is a set $L$ of at most $m^k$ sign vectors in $\{-1, 1\}^m$ with
the following property: for every set $S$ of columns of $A$ some $\varepsilon \in L$ satisfies
$\left|\sum_{j \in S} A_{ij} \varepsilon_j\right| \le C \operatorname{herdisc}(A)$ for every row
$i$, where $\operatorname{herdisc}(A)$ is the hereditary discrepancy of $A$.

The AIM problem list records this negative answer: for the $0/1$ matrix with $m$ columns whose
$\sqrt{m}$ rows are the indicators of disjoint sets of $\sqrt{m}$ columns, the hereditary
discrepancy is $1$, yet for fixed $C$ and lists of polynomial size some set of columns has
discrepancy above $C$ under every listed colouring.

Source: AIM Problem Lists,
Hereditary discrepancy and factorization norms, Problem 1.85 (Polysize list of colorings),
https://aimpl.org/hereddiscrep/1/. Moved from
`OpenConjectures/Combinatorics/PolysizeColoringList`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Combinatorics.PolysizeColoringListWanted
