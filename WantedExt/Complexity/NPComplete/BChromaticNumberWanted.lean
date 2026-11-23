/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# B-CHROMATIC NUMBER is NP-complete

Source:
R. W. Irving and D. F. Manlove, "The b-chromatic number of a graph", Discrete Applied
Mathematics 91 (1999), 127-141, doi:10.1016/S0166-218X(98)00146-2 (Theorem 3.3).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BChromaticNumber

/-!
# B-CHROMATIC NUMBER is NP-complete

A b-colouring of a graph `G` with `k` colours is a proper colouring of `G` with colours
`1, …, k` in which every colour class contains a vertex adjacent to a vertex of every other
colour. The b-chromatic number `φ(G)` is the largest `k` for which `G` has a b-colouring with
`k` colours.

INSTANCE: a graph `G = (V, E)` and an integer `K`. QUESTION: is `φ(G) ≥ K`, i.e., does `G` have
a b-colouring with `k` colours for some `k ≥ K`?

This is Irving and Manlove's decision problem ("determine whether `φ(G) ≥ K`, for a given
integer `K` and graph `G`"). Since b-colourings need not exist for every number of colours
between `χ(G)` and `φ(G)`, the question asks for some `k ≥ K`, not for exactly `K` colours. A
proper colouring with `k` colours is Mathlib's `SimpleGraph.Coloring` into `Fin k`; every
colour class is nonempty because it contains a vertex of the b-condition. `K` ranges over `ℕ`
(a negative `K` is a trivial yes-instance, as is `K = 0`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, bound `K`. -/
abbrev BChromaticNumberInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : BChromaticNumberInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : BChromaticNumberInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- The proper colouring `c` of `G` with colours `Fin k` is a b-colouring: every colour `a` has
a vertex `v` of colour `a` adjacent to a vertex of every other colour `b`. -/
def IsBColoring {n k : ℕ} {G : SimpleGraph (Fin n)} (c : G.Coloring (Fin k)) : Prop :=
  ∀ a : Fin k, ∃ v, c v = a ∧ ∀ b : Fin k, b ≠ a → ∃ w, G.Adj v w ∧ c w = b

/-- `φ(G) ≥ K`: the graph has a b-colouring with `k` colours for some `k ≥ K`. -/
def BChromaticNumberFeasible (i : BChromaticNumberInstance) : Prop :=
  ∃ k, i.2.2 ≤ k ∧ ∃ c : (Graph i).Coloring (Fin k), IsBColoring c

open Classical in
/-- B-CHROMATIC NUMBER as a decision problem over bitstrings. -/
noncomputable def bChromaticNumberDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := BChromaticNumberInstance) x with
  | some i => decide (WellFormed i ∧ BChromaticNumberFeasible i)
  | none => false

/-- **B-CHROMATIC NUMBER is NP-complete.** Source: Irving and Manlove (1999), Theorem 3.3. -/
public theorem_wanted bChromaticNumber_npComplete :
    bChromaticNumberDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bChromaticNumberDec

end MetaMathlibExt.Complexity.NPComplete.BChromaticNumber
