/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Geography is PSPACE-complete

Source:
T. J. Schaefer, "On the complexity of some two-person perfect-information games", Journal of
Computer and System Sciences 16 (1978), 185-225.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes


@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.GeographyPSPACEComplete

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# Geography is PSPACE-complete

Geography, the two-player game of moving a token along directed edges without revisiting
vertices, is `PSPACE`-complete: the first player has a winning strategy exactly for the
`PSPACE`-complete language. `GeoWins` alternates players: a position is winning when there is a
move to a position from which the opponent cannot win. The start vertex is marked visited at
the outset, so a path never repeats a vertex; edge endpoints and the start are required below
`n`. The instance decodes to `(n, edges, start)`.
-/


/-- **Winning positions in Geography.** Let $E$ be a list of pairs of natural numbers, read as
directed edges, let $v$ be a natural number (the current vertex) and let $V$ be a list of natural
numbers (the visited vertices). For a natural number $k$ (the fuel), the predicate
$\mathrm{GeoWins}(k, E, v, V)$ is defined by recursion on $k$: $\mathrm{GeoWins}(0, E, v, V)$ is
false, and $\mathrm{GeoWins}(k + 1, E, v, V)$ holds exactly when there is a natural number $w$
with $(v, w) \in E$ and $w \notin V$ such that $\mathrm{GeoWins}(k, E, w, V')$ is false, where
$V'$ is the list $V$ with $w$ added at the front.

Read as a game, the player to move wins when they can move the token along an edge of $E$ to a
vertex not in $V$ from which the opponent does not win; a player with no such move, or with no
fuel left, loses. -/
def GeoWins : ℕ → List (ℕ × ℕ) → ℕ → List ℕ → Prop
  | 0, _, _, _ => False
  | fuel + 1, edges, pos, visited =>
    ∃ nxt, (pos, nxt) ∈ edges ∧ nxt ∉ visited ∧ ¬ GeoWins fuel edges nxt (nxt :: visited)

open Classical in
/-- **Geography as a decision problem.** The Geography decision problem accepts a bitstring $x$
exactly when $x$ decodes, under the canonical bitstring encoding of triples $(n, E, s)$ of a
natural number, a list of pairs of natural numbers and a natural number, to a triple with
$s < n$, with both entries of every pair in $E$ less than $n$, and with
$\mathrm{GeoWins}(n + 1, E, s, [s])$, where $[s]$ is the list whose only entry is $s$.
Bitstrings that do not decode are rejected.

A play never revisits one of the $n$ vertices, so the fuel $n + 1$ never runs out: the condition
says that the player who moves first wins Geography on the directed graph with vertices
$0, \ldots, n - 1$ and edge list $E$, with the token starting on $s$ and $s$ marked visited. -/
noncomputable def geographyDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ℕ × List (ℕ × ℕ) × ℕ) x with
  | some i => decide (i.2.2 < i.1 ∧
      (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1) ∧
      GeoWins (i.1 + 1) i.2.1 i.2.2 [i.2.2])
  | none => false

/-- **Geography is PSPACE-complete.** The Geography decision problem belongs to PSPACE, and every
decision problem in PSPACE has a polynomial-time many-one reduction to it.

Source: T. J. Schaefer, "On the complexity of some two-
person perfect-information games", Journal of Computer and System Sciences 16 (1978),
185-225. -/
public theorem_wanted geography_pspace_complete :
    geographyDec ∈ PSPACE ∧ ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
      L ∈ PSPACE → Cslib.CookLevin.PolyManyOneRed L geographyDec

end MetaMathlibExt.Complexity.KeyTheorems.GeographyPSPACEComplete
