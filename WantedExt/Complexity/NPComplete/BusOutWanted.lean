/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BUS OUT is NP-complete

Source:
T. Ishibashi, R. Yoshinaka and A. Shinohara, "BusOut is NP-complete", arXiv:2505.09165 (2025),
Section 2 and Theorem 2.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Data.Finset.Basic
public import Mathlib.Logic.Relation

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BusOut

/-!
# BUS OUT is NP-complete

Ishibashi, Yoshinaka and Shinohara (Section 2) formalize the smartphone game Bus Out. A
configuration `(G, Q, S)` consists of a congestion graph `G`, whose vertices are the buses in
traffic, each labeled with a color and a capacity, with an edge from a bus to each bus that
blocks it (a bus is free when its out-degree is zero); a passenger queue `Q`, a sequence of
colors; and a spot occupancy state `S`, whose entries are the parking spots, each empty (`ε`) or
holding a bus `(x, k)` of color `x` with `k` remaining seats. A configuration can move to
`(G', Q', S')` when
* (dispatch) `Q' = Q`, `G'` is `G` minus a free vertex labeled `(x, k)`, and `S'` is `S` with
  an `ε` replaced by `(x, k)`; or
* (board) `G' = G`, `Q'` is `Q` with its first element `x` removed, and `S'` is `S` with an
  element `(x, k + 1)` replaced by `(x, k)` for some `k ≥ 1`, or `(x, 1)` replaced by `ε`;
and whenever a board move is applicable it takes place before the player dispatches a bus.
A configuration is solvable if some sequence of moves empties it (no buses in traffic, no
passengers, all spots empty). The instances of BUSOUT are the eligible configurations (`G` has
no cycle, and for every color the total capacity of its buses equals its number of passengers)
whose spot state is `εˢ`, `s` empty spots; capacities and `s` are positive integers.

INSTANCE: an eligible configuration `(G, Q, εˢ)`.
QUESTION: is it solvable? (NP-complete already for one spot, two colors and capacity `1`,
Theorem 2.)

The buses are `Fin n`, given by their labels `(color, capacity)`; a pair `(u, v)` in the edge
list means that bus `v` blocks bus `u`. Colors are natural numbers. A state records the set of
buses still in traffic, the remaining queue (first passenger first), and the `s` spots.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the bus labels `(color, capacity)`, the blocking edges `(u, v)` (bus `v` blocks
bus `u`), the passenger queue (colors, first passenger first), and the number `s` of spots. -/
abbrev BusOutInstance := List (ℕ × ℕ) × List (ℕ × ℕ) × List ℕ × ℕ

/-- Bus `v` blocks bus `u`: the congestion graph has the edge `u → v`. -/
def Blocks (i : BusOutInstance) (u v : Fin i.1.length) : Prop :=
  ((u : ℕ), (v : ℕ)) ∈ i.2.1

/-- A state: the buses still in traffic, the remaining passenger queue, and the spots (`none`
for an empty spot, `some (x, k)` for a bus of color `x` with `k` remaining seats). -/
abbrev State (i : BusOutInstance) := Finset (Fin i.1.length) × List ℕ × List (Option (ℕ × ℕ))

/-- A board move is applicable: the first passenger's color matches a bus in a spot. -/
def CanBoard (i : BusOutInstance) (c : State i) : Prop :=
  ∃ (x : ℕ) (q : List ℕ), c.2.1 = x :: q ∧ ∃ (j k : ℕ), c.2.2[j]? = some (some (x, k))

/-- One move: board the first passenger, or, when no boarding is applicable, dispatch a free bus
to an empty spot. -/
def Step (i : BusOutInstance) (c c' : State i) : Prop :=
  (∃ (x : ℕ) (q : List ℕ) (j k : ℕ), c.2.1 = x :: q ∧ c.2.2[j]? = some (some (x, k + 1)) ∧
      c' = (c.1, q, c.2.2.set j (if k = 0 then none else some (x, k)))) ∨
    (¬ CanBoard i c ∧ ∃ u ∈ c.1, (∀ v ∈ c.1, ¬ Blocks i u v) ∧ ∃ j : ℕ, c.2.2[j]? = some none ∧
      c' = (c.1.erase u, c.2.1, c.2.2.set j (some (i.1.get u))))

/-- Well-formedness: the edges join buses, the congestion graph has no cycle, every capacity
and the number of spots are positive, and for every color the capacities of its buses sum to
its number of passengers. -/
def WellFormed (i : BusOutInstance) : Prop :=
  (∀ e ∈ i.2.1, e.1 < i.1.length ∧ e.2 < i.1.length) ∧
    (∀ u, ¬ Relation.TransGen (Blocks i) u u) ∧ (∀ b ∈ i.1, 0 < b.2) ∧ 0 < i.2.2.2 ∧
    ∀ x, ((i.1.filter fun b => b.1 = x).map Prod.snd).sum = i.2.2.1.count x

/-- From `(G, Q, εˢ)` some sequence of moves reaches the empty configuration. -/
def BusOutFeasible (i : BusOutInstance) : Prop :=
  Relation.ReflTransGen (Step i) (Finset.univ, i.2.2.1, List.replicate i.2.2.2 none)
    (∅, [], List.replicate i.2.2.2 none)

open Classical in
/-- BUS OUT as a decision problem over bitstrings. -/
noncomputable def busOutDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode (α := BusOutInstance) x with
  | some i => decide (WellFormed i ∧ BusOutFeasible i)
  | none => false

/-- **BUS OUT is NP-complete.** Source: Ishibashi, Yoshinaka and Shinohara (2025), Theorem 2. -/
public theorem_wanted busOut_npComplete :
    busOutDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L busOutDec

end MetaMathlibExt.Complexity.NPComplete.BusOut
