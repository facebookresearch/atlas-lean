/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# KURODOKO (KUROMASU) is NP-complete

Source:
J. Kölker, "Kurodoko is NP-complete", Journal of Information Processing 20(3) (2012),
694-706, doi:10.2197/ipsjjip.20.694 (Section 1, Theorems 2 and 3).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Kurodoko

/-!
# KURODOKO (KUROMASU) is NP-complete

Kölker's Kurodoko Decision Problem. INSTANCE: a `w × h` grid of squares, a set `C` of clue
squares, and clue values `N : C → {1, …, w + h - 1}`, with `w` and `h` in binary, `C` a list
of points and `N` a list of integers. QUESTION: is there a set `B` of black squares (the rest,
`W`, being white) such that
1. the clue squares are all white, `B ∩ C = ∅`;
2. no two squares of `B` are adjacent;
3. all white squares are connected via paths of only white squares, i.e. the induced subgraph
   on `W` is connected;
4. the number at each clue square equals the number of white squares reachable from that
   square going in each of the four compass directions, never off the board nor through a
   black square (the square itself counted once: `N(v) = hz + vt - 1`, with `hz` and `vt` the
   lengths of the horizontal and vertical runs of white squares through `v`)?

Squares are pairs `(r, c)` of a row `r < h` and a column `c < w`; adjacency is the grid graph
`pathGraph h □ pathGraph w` (`|r - r'| + |c - c'| = 1`). The board has at least one row and
one column: the source's membership algorithm accepts a board with no white square only when
`w = h = 1`, and rejects the empty board. Rule 3 uses `Preconnected`, which accepts `W = ∅`;
with rule 2 that happens only on the `1 × 1` board, as in that algorithm.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance `(w, h, clues)`: the width `w`, the height `h` (both in binary), and the
clues, each a square `(r, c)` with its value `N(r, c)`. -/
abbrev KurodokoInstance := ℕ × ℕ × List ((ℕ × ℕ) × ℕ)

/-- The grid graph: squares `(r, c)` with `r < h`, `c < w`, adjacent when horizontally or
vertically adjacent. -/
def Grid (i : KurodokoInstance) : SimpleGraph (Fin i.2.1 × Fin i.1) :=
  SimpleGraph.pathGraph i.2.1 □ SimpleGraph.pathGraph i.1

/-- Square `u` is visible from square `v` given the black squares `B`: they share a row or a
column, and every square on the segment from `v` to `u` (both ends included) is white. -/
def Visible {h w : ℕ} (B : Finset (Fin h × Fin w)) (v u : Fin h × Fin w) : Prop :=
  (u.1 = v.1 ∧ ∀ c : Fin w, min v.2 u.2 ≤ c → c ≤ max v.2 u.2 → (v.1, c) ∉ B) ∨
    (u.2 = v.2 ∧ ∀ r : Fin h, min v.1 u.1 ≤ r → r ≤ max v.1 u.1 → (r, v.2) ∉ B)

instance {h w : ℕ} (B : Finset (Fin h × Fin w)) (v : Fin h × Fin w) :
    DecidablePred (Visible B v) := fun _ => by
  unfold Visible; infer_instance

/-- Well-formedness of an instance `(w, h, clues)`: `w, h ≥ 1`, the clue squares are distinct
squares of the grid, and each clue value lies in `{1, …, w + h - 1}`. -/
def WellFormed (i : KurodokoInstance) : Prop :=
  0 < i.1 ∧ 0 < i.2.1 ∧ (i.2.2.map Prod.fst).Nodup ∧
    ∀ q ∈ i.2.2, q.1.1 < i.2.1 ∧ q.1.2 < i.1 ∧ 1 ≤ q.2 ∧ q.2 ≤ i.1 + i.2.1 - 1

/-- Some set `B` of black squares satisfies rules 1-4. -/
def KurodokoFeasible (i : KurodokoInstance) : Prop :=
  ∃ B : Finset (Fin i.2.1 × Fin i.1),
    (∀ q ∈ i.2.2, ∀ v : Fin i.2.1 × Fin i.1, ((v.1 : ℕ), (v.2 : ℕ)) = q.1 → v ∉ B) ∧
    (∀ a ∈ B, ∀ b ∈ B, ¬ (Grid i).Adj a b) ∧
    ((Grid i).induce {v | v ∉ B}).Preconnected ∧
    ∀ q ∈ i.2.2, ∀ v : Fin i.2.1 × Fin i.1, ((v.1 : ℕ), (v.2 : ℕ)) = q.1 →
      (Finset.univ.filter (Visible B v)).card = q.2

open Classical in
/-- KURODOKO as a decision problem over bitstrings. -/
noncomputable def kurodokoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := KurodokoInstance) x with
  | some i => decide (WellFormed i ∧ KurodokoFeasible i)
  | none => false

/-- **KURODOKO (KUROMASU) is NP-complete.** Source: Kölker (2012), Theorem 2 (membership,
with `w` and `h` in binary) and Theorem 3 (hardness: a reduction from one-in-three SAT). -/
public theorem_wanted kurodoko_npComplete :
    kurodokoDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L kurodokoDec

end MetaMathlibExt.Complexity.NPComplete.Kurodoko
