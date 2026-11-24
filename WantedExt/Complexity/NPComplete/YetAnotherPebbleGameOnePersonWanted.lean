/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# YET ANOTHER PEBBLE GAME (one-person version) is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 4 (1983), 397-411,
doi:10.1016/0196-6774(83)90019-6, problem [4] YET ANOTHER PEBBLE GAME, comment;
T. Kasai, A. Adachi and S. Iwata, "Classes of pebble games and complete problems", SIAM Journal
on Computing 8 (1979), 574-586, doi:10.1137/0208046.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Insert
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.YetAnotherPebbleGameOnePerson

/-!
# YET ANOTHER PEBBLE GAME (one-person version) is NP-complete

Johnson's column states YET ANOTHER PEBBLE GAME on an acyclic directed graph `G = (V, A)` with a
distinguished goal vertex `v₀`, a set `S ⊆ V` of start vertices, and a collection `R` of rules,
each rule being a triple `(x, y, z)` of distinct vertices where `(x, z)` and `(y, z)` are both
arcs in `A`. Initially there is a pebble on each vertex in `S`; given a configuration of pebbles,
a rule `(x, y, z) ∈ R` is applicable if there are pebbles on `x` and `y` but not on `z`, and its
application moves the pebble from `x` to `z`. The two-person game is PSPACE-complete; the
column's comment: "The corresponding one-person game (can a single player pebble `v₀` by
starting from the initial position and repeatedly applying applicable rules?) is NP-complete"
(Kasai, Adachi and Iwata). This is the one-person game:

INSTANCE: an acyclic directed graph `G = (V, A)`, a goal vertex `v₀`, a set `S ⊆ V` of start
vertices, and a collection `R` of rules as above.
QUESTION: can a single player, starting with a pebble on each vertex of `S` and repeatedly
applying applicable rules, place a pebble on `v₀`?

The vertices are `0, …, n - 1`; arcs, the start set and rules are lists. `G` is acyclic when no
vertex reaches itself by a nonempty sequence of arcs (`Relation.TransGen`). A configuration is
the finite set of pebbled vertices, and the positions reachable from the initial one are those
of `Relation.ReflTransGen` of single rule applications.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the number `n` of vertices, the arcs, the goal `v₀`, the start vertices `S`,
and the rules `(x, y, z)`. -/
abbrev YetAnotherPebbleGameOnePersonInstance :=
  ℕ × List (ℕ × ℕ) × ℕ × List ℕ × List (ℕ × ℕ × ℕ)

/-- Well-formedness: arcs, goal and start vertices are vertices, the graph is acyclic, the
start vertices are listed without repetition, and every rule `(x, y, z)` has distinct vertices
with `(x, z)` and `(y, z)` arcs. -/
def WellFormed (i : YetAnotherPebbleGameOnePersonInstance) : Prop :=
  (∀ a ∈ i.2.1, a.1 < i.1 ∧ a.2 < i.1) ∧
    (∀ v, ¬ Relation.TransGen (fun a b => (a, b) ∈ i.2.1) v v) ∧
    i.2.2.1 < i.1 ∧ (∀ s ∈ i.2.2.2.1, s < i.1) ∧ i.2.2.2.1.Nodup ∧
    ∀ r ∈ i.2.2.2.2, r.1 ≠ r.2.1 ∧ r.1 ≠ r.2.2 ∧ r.2.1 ≠ r.2.2 ∧
      (r.1, r.2.2) ∈ i.2.1 ∧ (r.2.1, r.2.2) ∈ i.2.1

/-- One application of a rule `(x, y, z)` applicable in configuration `C` (pebbles on `x` and
`y`, none on `z`): the pebble on `x` moves to `z`. -/
def Move (i : YetAnotherPebbleGameOnePersonInstance) (C C' : Finset ℕ) : Prop :=
  ∃ r ∈ i.2.2.2.2, r.1 ∈ C ∧ r.2.1 ∈ C ∧ r.2.2 ∉ C ∧ C' = insert r.2.2 (C.erase r.1)

/-- Starting from a pebble on each start vertex, some sequence of rule applications puts a
pebble on `v₀`. -/
def YetAnotherPebbleGameOnePersonFeasible (i : YetAnotherPebbleGameOnePersonInstance) : Prop :=
  ∃ C, Relation.ReflTransGen (Move i) i.2.2.2.1.toFinset C ∧ i.2.2.1 ∈ C

open Classical in
/-- YET ANOTHER PEBBLE GAME (one-person version) as a decision problem over bitstrings. -/
noncomputable def yetAnotherPebbleGameOnePersonDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := YetAnotherPebbleGameOnePersonInstance) x with
  | some i => decide (WellFormed i ∧ YetAnotherPebbleGameOnePersonFeasible i)
  | none => false

/-- **YET ANOTHER PEBBLE GAME (one-person version) is NP-complete.** Source: Johnson (1983),
problem [4], comment; Kasai, Adachi and Iwata (1979). -/
public theorem_wanted yetAnotherPebbleGameOnePerson_npComplete :
    yetAnotherPebbleGameOnePersonDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L yetAnotherPebbleGameOnePersonDec

end MetaMathlibExt.Complexity.NPComplete.YetAnotherPebbleGameOnePerson
