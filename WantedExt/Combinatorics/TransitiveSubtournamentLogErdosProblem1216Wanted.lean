/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Largest transitive subtournaments (Erdős Problem 1216)

Erdős Problem 1216: let `f(n)` be such that every tournament on `n` vertices contains a transitive
tournament on `f(n)` vertices. Is `f(n) = ⌊log₂ n⌋ + 1`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Nat.Log
public import Mathlib.Order.Lattice.Nat

@[expose] public section

namespace MathlibExt.Combinatorics.TransitiveSubtournamentLogErdosProblem1216Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1216, https://www.erdosproblems.com/1216 (status
DISPROVED). UnsolvedMath record UM-30007257 (`EP-1216`), dataset ulamai/UnsolvedMath v1.8.0.

`f(n)` is the largest such number (the source's "let f(n) be such that" with the asked equality
means the optimal value), as `sSup`; the set is bounded by `n`. The equality is read for every `n ≥
1`. formal-conjectures has no statement.
-/

/-- **Tournaments.** Let $n \in \mathbb{N}$. A relation $T$ on $\{0, \dots, n-1\}$ is a
tournament when $T(x, x)$ holds for no $x$ and, for all distinct $x$ and $y$, exactly one of
$T(x, y)$ and $T(y, x)$ holds. -/
def IsTournament {n : ℕ} (T : Fin n → Fin n → Prop) : Prop :=
  (∀ x, ¬ T x x) ∧ ∀ x y, x ≠ y → (T x y ↔ ¬ T y x)

/-- **Transitivity on a vertex set.** Let $n \in \mathbb{N}$, let $T$ be a relation on
$\{0, \dots, n-1\}$ and let $S$ be a set of its elements. Then $T$ is transitive on $S$ when, for
all $x, y, z \in S$, $T(x, y)$ and $T(y, z)$ imply $T(x, z)$. For a tournament $T$ this says that
the subtournament of $T$ on $S$ is transitive. -/
def IsTransitiveOn {n : ℕ} (T : Fin n → Fin n → Prop) (S : Finset (Fin n)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, T x y → T y z → T x z

/-- **Transitive subtournament number.** For $n \in \mathbb{N}$, $f(n)$ is the largest $m$ such
that every tournament $T$ on $\{0, \dots, n-1\}$ is transitive on some set of exactly $m$
vertices, that is, contains a transitive subtournament on $m$ vertices.

Such $m$ exist (for instance $m = 0$) and are at most $n$, so the largest one exists. -/
noncomputable def transitiveSubtournamentNumber (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ T : Fin n → Fin n → Prop, IsTournament T →
    ∃ S : Finset (Fin n), S.card = m ∧ IsTransitiveOn T S}

/-- **Erdős Problem 1216 (the Erdős–Moser formula).** For every $n \ge 1$,
$f(n) = \lfloor \log_2 n \rfloor + 1$, where $f(n)$ is the largest $m$ such that every tournament
on $n$ vertices contains a transitive subtournament on $m$ vertices. -/
def transitiveSubtournamentNumberEqLogTwo : Prop :=
  ∀ n : ℕ, 1 ≤ n → transitiveSubtournamentNumber n = Nat.log 2 n + 1

/--
**Erdős Problem 1216 is false.** It is not the case that $f(n) = \lfloor \log_2 n \rfloor + 1$ for
every $n \ge 1$, where $f(n)$ is the largest $m$ such that every tournament on $n$ vertices
contains a transitive subtournament on $m$ vertices.

Reid and Parker proved $f(n) \ge \lfloor \log_2 n + 4 - \log_2 7 \rfloor$ for all $n \ge 14$; at
$n = 14$ this gives $f(14) \ge 5 > 4 = \lfloor \log_2 14 \rfloor + 1$, while Stearns' bound
$f(n) \ge \lfloor \log_2 n \rfloor + 1$ holds for every $n \ge 1$.

Source: T. F. Bloom, Erdős Problems, Problem
#1216, https://www.erdosproblems.com/1216 (status DISPROVED); resolution: K. B. Reid and E. T.
Parker, Disproof of a conjecture of Erdős and Moser on tournaments, J. Combinatorial Theory 9
(1970), 225-238, erdosproblems.com/1216: f(n) ≥ ⌊log₂ n + 4 - log₂ 7⌋ for all n ≥ 14, so f(14) ≥ 5 >
⌊log₂ 14⌋ + 1.
-/
public theorem_wanted transitiveSubtournamentNumberEqLogTwo_refuted :
    ¬ transitiveSubtournamentNumberEqLogTwo

end MathlibExt.Combinatorics.TransitiveSubtournamentLogErdosProblem1216Wanted
