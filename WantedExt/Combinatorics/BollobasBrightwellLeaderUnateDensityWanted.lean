/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.DivInvMonoid
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Basic
public import Mathlib.Basic.SetLike.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import Mathlib.Order.Filter.Defs
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Topology.MetricSpace.Pseudo.Defs
public import Mathlib.Topology.UniformSpace.Defs
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.Combinatorics.BollobasBrightwellLeaderUnateDensityWanted


/-!
# Enumeration and typical structure of k-SAT functions

Clause list from the supplied source:
* `k` is fixed (independent of `n`).
* numeric threshold `2 ≤ k` (source: fixed `k ≥ 2`).
* quantifier domain `n` Boolean variables; assignments `Fin n → Bool`.
* object: `k`-SAT functions on `n` variables (conjunctions of clauses
  of size at most `k` on distinct variables).
* property: unate (each variable monotone in one fixed polarity).
* claim: a `1 - o(1)` fraction of all such functions is unate as `n → ∞`.
* status: proved for every fixed `k` by Balogh, Dong, Lidický, Mani and Zhao
  (arXiv:2209.04894, Theorem 1.1); stated here as a proposition.

Stable source identifiers: [OWR-10252930-018];
Combinatorics, Probability and Computing (2023), Oberwolfach Reports,
DOI 10.4171/owr/2022/22, pp. 1165--1237;
Dong–Mani–Zhao, Enumerating k-SAT functions, arXiv:2107.09233.
-/

/-- **Satisfied clause.** Let $n \in \mathbb{N}$. A clause on $n$ variables is a finite set $C$ of
literals $(i, b)$, where $i \in \{0, \dots, n - 1\}$ is a variable and $b \in \{\mathrm{true},
\mathrm{false}\}$. An assignment $x : \{0, \dots, n - 1\} \to \{\mathrm{true}, \mathrm{false}\}$
satisfies $C$ if $x_i = b$ for some literal $(i, b) \in C$.

Source: [OWR-10252930-018], `k`-SAT clause semantics. -/
def ClauseSatisfied {n : ℕ} (x : Fin n → Bool)
    (C : Finset (Fin n × Bool)) : Prop :=
  ∃ l ∈ C, x l.1 = l.2

/-- **$k$-SAT function.** Let $k, n \in \mathbb{N}$. A Boolean function
$f : \{\mathrm{true}, \mathrm{false}\}^n \to \{\mathrm{true}, \mathrm{false}\}$ is a $k$-SAT
function on $n$ variables if there is a finite set $S$ of clauses on $n$ variables such that each
clause in $S$ has at most $k$ literals, no two of them on the same variable, and for every
assignment $x$, $f(x) = \mathrm{true}$ if and only if $x$ satisfies every clause in $S$.

Source: [OWR-10252930-018], `k`-SAT functions. -/
def IsKSATFunction (k n : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ S : Finset (Finset (Fin n × Bool)),
    (∀ C ∈ S, C.card ≤ k ∧ ∀ l₁ ∈ C, ∀ l₂ ∈ C, l₁.1 = l₂.1 → l₁ = l₂) ∧
    ∀ x : Fin n → Bool, (f x = true ↔ ∀ C ∈ S, ClauseSatisfied x C)

/-- **Positively unate variable.** Let $f : \{\mathrm{true}, \mathrm{false}\}^n \to
\{\mathrm{true}, \mathrm{false}\}$ be a Boolean function and $i$ one of its $n$ variables. Then
$f$ is positively unate in $i$ if for all assignments $x$ and $y$ that agree at every variable
other than $i$ and have $x_i = \mathrm{false}$ and $y_i = \mathrm{true}$, $f(x) = \mathrm{true}$
implies $f(y) = \mathrm{true}$. Equivalently, switching $i$ from false to true never switches
the value of $f$ from true to false.

Source: [OWR-10252930-018], unate. -/
def IsPositiveUnateIn {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) : Prop :=
  ∀ x y : Fin n → Bool, x i = false → y i = true →
    (∀ j : Fin n, j ≠ i → x j = y j) → f x = true → f y = true

/-- **Negatively unate variable.** Let $f : \{\mathrm{true}, \mathrm{false}\}^n \to
\{\mathrm{true}, \mathrm{false}\}$ be a Boolean function and $i$ one of its $n$ variables. Then
$f$ is negatively unate in $i$ if for all assignments $x$ and $y$ that agree at every variable
other than $i$ and have $x_i = \mathrm{false}$ and $y_i = \mathrm{true}$, $f(y) = \mathrm{true}$
implies $f(x) = \mathrm{true}$. Equivalently, switching $i$ from false to true never switches
the value of $f$ from false to true.

Source: [OWR-10252930-018], unate. -/
def IsNegativeUnateIn {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) : Prop :=
  ∀ x y : Fin n → Bool, x i = false → y i = true →
    (∀ j : Fin n, j ≠ i → x j = y j) → f y = true → f x = true

/-- **Unate Boolean function.** A Boolean function $f : \{\mathrm{true}, \mathrm{false}\}^n \to
\{\mathrm{true}, \mathrm{false}\}$ is unate if, for every variable $i$, $f$ is positively unate
in $i$ or negatively unate in $i$.

Source: [OWR-10252930-018], unate. -/
def IsUnate {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ i : Fin n, IsPositiveUnateIn f i ∨ IsNegativeUnateIn f i

/-- **Number of $k$-SAT functions.** For natural numbers $k$ and $n$, the number of Boolean
functions $f : \{\mathrm{true}, \mathrm{false}\}^n \to \{\mathrm{true}, \mathrm{false}\}$ that are
$k$-SAT functions on $n$ variables.

Source: [OWR-10252930-018], enumeration of `k`-SAT functions. -/
noncomputable def countKSATFunctions (k n : ℕ) : ℕ :=
  Nat.card { f : (Fin n → Bool) → Bool // IsKSATFunction k n f }

/-- **Number of unate $k$-SAT functions.** For natural numbers $k$ and $n$, the number of Boolean
functions $f : \{\mathrm{true}, \mathrm{false}\}^n \to \{\mathrm{true}, \mathrm{false}\}$ that are
$k$-SAT functions on $n$ variables and are unate.

Source: [OWR-10252930-018], typical structure (unate). -/
noncomputable def countUnateKSATFunctions (k n : ℕ) : ℕ :=
  Nat.card { f : (Fin n → Bool) → Bool // IsKSATFunction k n f ∧ IsUnate f }

/-- **Bollobás–Brightwell–Leader conjecture for $k$.** For a natural number $k$, the proposition
that if $k \ge 2$, then the number of unate $k$-SAT functions on $n$ Boolean variables divided by
the number of $k$-SAT functions on $n$ Boolean variables tends to $1$ as $n \to \infty$; that is,
a $1 - o(1)$ fraction of the $k$-SAT functions on $n$ variables is unate.

Source: [OWR-10252930-018], DOI 10.4171/owr/2022/22, arXiv:2107.09233. -/
noncomputable def conjecture (k : ℕ) : Prop :=
  2 ≤ k →
    Filter.Tendsto
      (fun n : ℕ =>
        (countUnateKSATFunctions k n : ℝ) / (countKSATFunctions k n : ℝ))
      Filter.atTop (nhds 1)

/-- **Bollobás–Brightwell–Leader conjecture for all $k$.** The proposition that for every natural
number $k \ge 2$, the number of unate $k$-SAT functions on $n$ Boolean variables divided by the
number of $k$-SAT functions on $n$ Boolean variables tends to $1$ as $n \to \infty$. -/
def conjectureAllK : Prop :=
  ∀ k : ℕ, conjecture k

/--
**Nearly all $k$-SAT functions are unate.** For every natural number $k \ge 2$, the number of
unate $k$-SAT functions on $n$ Boolean variables divided by the number of $k$-SAT functions on
$n$ Boolean variables tends to $1$ as $n \to \infty$; that is, the Bollobás–Brightwell–Leader
conjecture holds for every $k$.

Balogh, Dong, Lidický, Mani and Zhao prove this as Theorem 1.1 of arXiv:2209.04894. They use a
DNF convention with exactly $k$ distinct variables per clause, which gives the same counts as the
CNF, at-most-$k$ convention here for $n \ge k$ (negation preserves unateness).

Source: J. Balogh, D. Dong, B.
Lidický, N. Mani, Y. Zhao, Nearly all k-SAT functions are unate, STOC 2023; J. Eur. Math. Soc.
(2026), arXiv:2209.04894, https://arxiv.org/abs/2209.04894. Moved from
`OpenConjectures/Combinatorics/BollobasBrightwellLeaderUnateDensity`.
-/
public theorem_wanted conjectureAllK_holds : conjectureAllK

end MathlibExt.Combinatorics.BollobasBrightwellLeaderUnateDensityWanted
