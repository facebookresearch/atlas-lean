/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STACKER-CRANE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND26] STACKER-CRANE;
G. N. Frederickson, M. S. Hecht, and C. E. Kim, "Approximation algorithms for
some routing problems", SIAM Journal on Computing 7 (1978), 178-193,
doi:10.1137/0207017.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StackerCrane

/-!
# STACKER-CRANE is NP-complete

INSTANCE: a mixed graph `G = (V, A, E)` (`A` directed edges, `E` undirected edges), a length
`l(e) ∈ ℤ₀⁺` for each `e ∈ A ∪ E`, and a bound `B ∈ ℤ⁺`.
QUESTION: is there a cycle in `G` that includes each directed edge in `A` at least once,
traversing such edges only in the specified direction, and that has total length no more than
`B`?

The cycle is a closed walk (edges may be repeated, as "at least once" requires): a list of
moves, each traversing a directed edge from its tail to its head or an undirected edge in either
direction, where each move starts at the vertex where the previous one ended and the last move
ends where the first one starts. Its length is the sum of the lengths of its moves, counted
with repetition. Numbers use the binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `0, ..., n - 1`), the directed edges `A` as
`(tail, head, length)`, the undirected edges `E` as `(u, v, length)`, and the bound `B`. -/
abbrev StackerCraneInstance := ℕ × List (ℕ × ℕ × ℕ) × List (ℕ × ℕ × ℕ) × ℕ

/-- The traversals allowed in a cycle, as `(from, to, length)`: each directed edge from its
tail to its head, and each undirected edge in both directions. The first `|A|` entries are the
directed edges, in order. -/
def moves (i : StackerCraneInstance) : List (ℕ × ℕ × ℕ) :=
  i.2.1 ++ i.2.2.1 ++ i.2.2.1.map fun e => (e.2.1, e.1, e.2.2)

/-- Well-formedness of an instance: every edge joins two distinct vertices in range, no two
directed edges have the same tail and head, no two undirected edges join the same pair of
vertices (in either orientation), and `B` is positive. -/
def WellFormed (i : StackerCraneInstance) : Prop :=
  (∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1) ∧
    (i.2.1.map fun e => (e.1, e.2.1)).Nodup ∧
    (∀ e ∈ i.2.2.1, e.1 < i.1 ∧ e.2.1 < i.1 ∧ e.1 ≠ e.2.1) ∧
    (i.2.2.1.map fun e => (e.1, e.2.1)).Nodup ∧
    (∀ e ∈ i.2.2.1, (e.2.1, e.1) ∉ i.2.2.1.map fun e => (e.1, e.2.1)) ∧
    0 < i.2.2.2

/-- A closed walk, given as a list `c` of indices into `moves i`, in which consecutive moves
(cyclically) share an endpoint, every directed edge (index `< |A|`) occurs, and the total
length is at most `B`. -/
def StackerCraneFeasible (i : StackerCraneInstance) : Prop :=
  ∃ c : List (Fin (moves i).length),
    (∀ j (h : j < c.length),
      ((moves i)[c[j]]).2.1 = ((moves i)[c[(j + 1) % c.length]'(Nat.mod_lt _ (by omega))]).1) ∧
    (∀ a : Fin (moves i).length, (a : ℕ) < i.2.1.length → a ∈ c) ∧
    (c.map fun m => ((moves i)[m]).2.2).sum ≤ i.2.2.2

open Classical in
/-- STACKER-CRANE as a decision problem over bitstrings. -/
noncomputable def stackerCraneDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := StackerCraneInstance) x with
  | some i => decide (WellFormed i ∧ StackerCraneFeasible i)
  | none => false

/-- **STACKER-CRANE is NP-complete.** Source: Garey and Johnson (1979), [ND26];
Frederickson, Hecht, and Kim (1978). -/
public theorem_wanted stackerCrane_npComplete :
    stackerCraneDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L stackerCraneDec

end MetaMathlibExt.Complexity.NPComplete.StackerCrane
