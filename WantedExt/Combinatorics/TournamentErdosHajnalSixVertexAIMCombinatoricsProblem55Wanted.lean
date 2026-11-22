/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Erdős–Hajnal for the last six-vertex tournament (AIM Graph Ramsey theory, Problem 1.12)

AimPL: Graph Ramsey Theory, Section 1, item 6 "Erdős–Hajnal for tournaments", Problem 1.12 [Maria
Chudnovsky]: let `T*` be the tournament on `{1, …, 6}` with `6 → 1`, `6 → 3`, `5 → 2`, `4 → 1` and
`i → j` for all remaining pairs `i < j`. Does there exist `ε > 0` such that every `n`-vertex
tournament not containing `T*` as a subtournament contains a transitive tournament with at least
`n^ε` vertices?
-/

module

public import Batteries.Util.ProofWanted
public import WantedExt.Combinatorics.TransitiveSubtournamentLogErdosProblem1216Wanted
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

namespace MathlibExt.Combinatorics.TournamentErdosHajnalSixVertexAIMCombinatoricsProblem55Wanted

open MathlibExt.Combinatorics.TransitiveSubtournamentLogErdosProblem1216Wanted
  (IsTournament IsTransitiveOn)

/-!
Source: AimPL: Graph Ramsey Theory, Problem 1.12 [Maria Chudnovsky], http://aimpl.org/graphramsey/1/
(the UnsolvedMath extraction of the workshop's Overleaf list,
https://www.overleaf.com/read/mnvcscjjysvg, has the same question and the remark that, by
Berger–Choromanski–Chudnovsky, `T*` is the smallest tournament for which the conclusion is not
known). UnsolvedMath record UM-20000930 (`AIM-COMBINATORICS-0055`), dataset ulamai/UnsolvedMath
v1.8.0.

Vertices `1, …, 6` of `T*` are relabelled `0, …, 5`. Tournaments on `Fin n` and transitive vertex
sets are `IsTournament` and `IsTransitiveOn` of the Erdős Problem 1216 module. "Containing `T*` as a
subtournament" is an injective map `Fin 6 → Fin n` preserving and reflecting arcs. The size bound
`n^ε` is the real power, so `n = 0` asks for nothing.
-/

/-- The reversed pairs of `T*` (`6 → 1`, `6 → 3`, `5 → 2`, `4 → 1`, relabelled to `Fin 6`). -/
def tStarBackArcs : List (Fin 6 × Fin 6) :=
  [(5, 0), (5, 2), (4, 1), (3, 0)]

/-- The tournament `T*`: `i → j` iff `(i, j)` is a reversed pair, or `i < j` and `(j, i)` is not. -/
def tStar (i j : Fin 6) : Prop :=
  (i, j) ∈ tStarBackArcs ∨ (i < j ∧ (j, i) ∉ tStarBackArcs)

/-- The tournament `T` on `Fin n` contains `T*` as a subtournament. -/
def ContainsTStar {n : ℕ} (T : Fin n → Fin n → Prop) : Prop :=
  ∃ f : Fin 6 → Fin n, Function.Injective f ∧ ∀ i j, tStar i j ↔ T (f i) (f j)

/-- Problem 1.12: there is `ε > 0` such that every tournament on `n` vertices without `T*` has a
transitive subtournament on at least `n^ε` vertices. -/
def tStarErdosHajnal : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ (n : ℕ) (T : Fin n → Fin n → Prop), IsTournament T → ¬ ContainsTStar T →
    ∃ S : Finset (Fin n), IsTransitiveOn T S ∧ (n : ℝ) ^ ε ≤ S.card

/--
Resolved true: Nguyen, Scott and Seymour prove that every two-colourable tournament has the
Erdős–Hajnal property, "which completes the verification of the conjecture for six-vertex
tournaments"; Berger, Choromanski and Chudnovsky had proved it for every tournament on at most six
vertices except `T*` (the remark recorded with the problem), and `T*` is two-colourable (`{1, 2, 3}`
and `{4, 5, 6}` are transitive). Source: AimPL: Graph Ramsey Theory, Problem 1.12 [Maria
Chudnovsky], http://aimpl.org/graphramsey/1/; resolution: T. Nguyen, A. Scott and P. Seymour,
Induced subgraph density. VI. Bounded VC-dimension, Adv. Math. 482 (2025), 110601, arXiv:2312.15572,
abstract and introduction, https://arxiv.org/abs/2312.15572.
-/
public theorem_wanted tStarErdosHajnal_holds : tStarErdosHajnal

end MathlibExt.Combinatorics.TournamentErdosHajnalSixVertexAIMCombinatoricsProblem55Wanted
