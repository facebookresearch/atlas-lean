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

/-- A tournament on `Fin n`: an irreflexive relation with exactly one of `T x y`, `T y x` for
distinct `x, y`. -/
def IsTournament {n : ℕ} (T : Fin n → Fin n → Prop) : Prop :=
  (∀ x, ¬ T x x) ∧ ∀ x y, x ≠ y → (T x y ↔ ¬ T y x)

/-- The subtournament of `T` on `S` is transitive. -/
def IsTransitiveOn {n : ℕ} (T : Fin n → Fin n → Prop) (S : Finset (Fin n)) : Prop :=
  ∀ x ∈ S, ∀ y ∈ S, ∀ z ∈ S, T x y → T y z → T x z

/-- `f(n)`: the largest `m` such that every tournament on `n` vertices contains a transitive
subtournament on `m` vertices. -/
noncomputable def transitiveSubtournamentNumber (n : ℕ) : ℕ :=
  sSup {m : ℕ | ∀ T : Fin n → Fin n → Prop, IsTournament T →
    ∃ S : Finset (Fin n), S.card = m ∧ IsTransitiveOn T S}

/-- Erdős Problem 1216: `f(n) = ⌊log₂ n⌋ + 1` for every `n ≥ 1`. -/
def transitiveSubtournamentNumberEqLogTwo : Prop :=
  ∀ n : ℕ, 1 ≤ n → transitiveSubtournamentNumber n = Nat.log 2 n + 1

/--
Resolved false: Reid and Parker proved `f(n) ≥ ⌊log₂ n + 4 - log₂ 7⌋` for all `n ≥ 14`; at `n = 14`
this is `5 > 4 = ⌊log₂ 14⌋ + 1` (Stearns' bound `f(n) ≥ ⌊log₂ n⌋ + 1` always holds).
erdosproblems.com/1216 lists the problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem
#1216, https://www.erdosproblems.com/1216 (status DISPROVED); resolution: K. B. Reid and E. T.
Parker, Disproof of a conjecture of Erdős and Moser on tournaments, J. Combinatorial Theory 9
(1970), 225-238, erdosproblems.com/1216: f(n) ≥ ⌊log₂ n + 4 - log₂ 7⌋ for all n ≥ 14, so f(14) ≥ 5 >
⌊log₂ 14⌋ + 1.
-/
public theorem_wanted transitiveSubtournamentNumberEqLogTwo_refuted :
    ¬ transitiveSubtournamentNumberEqLogTwo

end MathlibExt.Combinatorics.TransitiveSubtournamentLogErdosProblem1216Wanted
