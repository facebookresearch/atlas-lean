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

/-- Clause satisfaction for a Boolean assignment: some literal `(i, b)`
in the clause agrees with the assignment.
Cites [OWR-10252930-018] `k`-SAT clause semantics. -/
def ClauseSatisfied {n : ℕ} (x : Fin n → Bool)
    (C : Finset (Fin n × Bool)) : Prop :=
  ∃ l ∈ C, x l.1 = l.2

/-- A Boolean function is a `k`-SAT function on `n` variables if it is the
conjunction of a finite set of clauses, each of size at most `k` on pairwise
distinct variables. Cites [OWR-10252930-018] `k`-SAT functions. -/
def IsKSATFunction (k n : ℕ) (f : (Fin n → Bool) → Bool) : Prop :=
  ∃ S : Finset (Finset (Fin n × Bool)),
    (∀ C ∈ S, C.card ≤ k ∧ ∀ l₁ ∈ C, ∀ l₂ ∈ C, l₁.1 = l₂.1 → l₁ = l₂) ∧
    ∀ x : Fin n → Bool, (f x = true ↔ ∀ C ∈ S, ClauseSatisfied x C)

/-- Positive unateness in variable `i`: flipping `i` from `false` to `true`
while fixing all other variables never flips the function from `true`
to `false`. Cites [OWR-10252930-018] unate. -/
def IsPositiveUnateIn {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) : Prop :=
  ∀ x y : Fin n → Bool, x i = false → y i = true →
    (∀ j : Fin n, j ≠ i → x j = y j) → f x = true → f y = true

/-- Negative unateness in variable `i`: flipping `i` from `false` to `true`
while fixing all other variables never flips the function from `false`
to `true`. Cites [OWR-10252930-018] unate. -/
def IsNegativeUnateIn {n : ℕ} (f : (Fin n → Bool) → Bool) (i : Fin n) : Prop :=
  ∀ x y : Fin n → Bool, x i = false → y i = true →
    (∀ j : Fin n, j ≠ i → x j = y j) → f y = true → f x = true

/-- A Boolean function is unate if every variable is either positively or
negatively unate. Cites [OWR-10252930-018] unate. -/
def IsUnate {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ i : Fin n, IsPositiveUnateIn f i ∨ IsNegativeUnateIn f i

/-- Number of `k`-SAT functions on `n` Boolean variables.
Cites [OWR-10252930-018] enumeration of `k`-SAT functions. -/
noncomputable def countKSATFunctions (k n : ℕ) : ℕ :=
  Nat.card { f : (Fin n → Bool) → Bool // IsKSATFunction k n f }

/-- Number of unate `k`-SAT functions on `n` Boolean variables.
Cites [OWR-10252930-018] typical structure (unate). -/
noncomputable def countUnateKSATFunctions (k n : ℕ) : ℕ :=
  Nat.card { f : (Fin n → Bool) → Bool // IsKSATFunction k n f ∧ IsUnate f }

/-- For fixed `k ≥ 2`, is a `1 - o(1)` fraction of all `k`-SAT functions on
`n` variables unate as `n → ∞`? This is the Bollobás–Brightwell–Leader
typical-structure question for this `k`. Cites [OWR-10252930-018],
DOI 10.4171/owr/2022/22, arXiv:2107.09233. -/
noncomputable def conjecture (k : ℕ) : Prop :=
  2 ≤ k →
    Filter.Tendsto
      (fun n : ℕ =>
        (countUnateKSATFunctions k n : ℝ) / (countKSATFunctions k n : ℝ))
      Filter.atTop (nhds 1)

/-- The Bollobás–Brightwell–Leader conjecture for every fixed `k`: `conjecture k` for all `k`,
i.e. for each `k ≥ 2` a `1 - o(1)` fraction of the `k`-SAT functions on `n` variables is unate
as `n → ∞`. -/
def conjectureAllK : Prop :=
  ∀ k : ℕ, conjecture k

/--
Resolved true: Resolved affirmatively by Balogh, Dong, Lidický, Mani and Zhao (Nearly all k-SAT
functions are unate, STOC 2023 and J. Eur. Math. Soc. (2026), arXiv:2209.04894, Theorem 1.1):
for every fixed k, a 1 - o(1) fraction of k-SAT functions on n variables are unate. Their DNF
convention with exactly k distinct variables per clause gives the same function classes as the
CNF, at-most-k convention here (negation preserves unateness). Source: J. Balogh, D. Dong, B.
Lidický, N. Mani, Y. Zhao, Nearly all k-SAT functions are unate, STOC 2023; J. Eur. Math. Soc.
(2026), arXiv:2209.04894, https://arxiv.org/abs/2209.04894. Moved from
`OpenConjectures/Combinatorics/BollobasBrightwellLeaderUnateDensity`.
-/
public theorem_wanted conjectureAllK_holds : conjectureAllK

end MathlibExt.Combinatorics.BollobasBrightwellLeaderUnateDensityWanted
