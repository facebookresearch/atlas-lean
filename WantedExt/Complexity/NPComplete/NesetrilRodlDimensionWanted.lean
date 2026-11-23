/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NESETRIL-RODL DIMENSION is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [GT62] NESETRIL-RODL DIMENSION;
J. Nešetřil and A. Pultr, "A Dushnik-Miller type dimension of graphs and its complexity",
Fundamentals of Computation Theory (FCT 1977), Lecture Notes in Computer Science 56 (1977),
482-493, doi:10.1007/3-540-08442-8_119.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.NesetrilRodlDimension

/-!
# NESETRIL-RODL DIMENSION is NP-complete

INSTANCE: a graph `G = (V, E)` and a positive integer `K ≤ |E|`. QUESTION: is there a
one-to-one function `f : V → {(a₁, ..., a_K) : 1 ≤ aᵢ ≤ |V| for 1 ≤ i ≤ K}` such that, for
all `u, v ∈ V`, `{u, v} ∈ E` if and only if `f(u)` and `f(v)` disagree in all `K` components?

This is Garey and Johnson's [GT62] (p. 205), with reference Nešetřil and Pultr (1977),
transformation from GRAPH 3-COLORABILITY; the definition is due to Nešetřil and Rödl. In
Nešetřil and Pultr's terms, the question asks whether `G` is an induced subgraph of a product of
`K` complete graphs on `|V|` vertices; their introduction announces that evaluating this
dimension "is polynomial iff the evaluation of chromatic number is". Membership in NP: `f` is a
certificate of `|V| · K ≤ |V| · |E|` numbers below `|V|`.

The graph is given by its number of vertices `n = |V|`, written in unary as the length of a
list `[true, ..., true]` (as in `BoundedDiameterAugmentation`), and a simple edge list on
`Fin n`, so the list's length is `|E|`. A graph is given with its vertex set; a binary `n` would
make the problem succinct, since isolated vertices would cost no input while `f` must give each
of them a tuple. The values `1, ..., |V|` of each component are `Fin n` (`0, ..., n - 1`), and a
`K`-tuple is a function `Fin K → Fin n`. For `u = v` both sides of the equivalence are false
(`K ≥ 1`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the vertex count `n` in unary (a list of length `n`; vertices
`0, ..., n - 1`), the edge list, and the bound `K`. -/
abbrev NesetrilRodlDimensionInstance := List Bool × List (ℕ × ℕ) × ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`, `n` the length of the unary list. -/
def Graph (i : NesetrilRodlDimensionInstance) : SimpleGraph (Fin i.1.length) :=
  Cslib.Complexity.Karp.edgeGraph i.1.length i.2.1

/-- Well-formedness of an instance: `n` is written in unary as `[true, ..., true]`, the edge
list describes a simple graph on `0, ..., n - 1`, and `1 ≤ K ≤ |E|`. -/
def WellFormed (i : NesetrilRodlDimensionInstance) : Prop :=
  (∀ b ∈ i.1, b = true) ∧
    (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1.length ∧ e.2 < i.1.length ∧ e.1 ≠ e.2 ∧
      (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

/-- Some one-to-one `f : V → (Fin K → Fin n)` has, for all `u, v`, `{u, v} ∈ E` iff `f(u)` and
`f(v)` disagree in every component. -/
def NesetrilRodlDimensionFeasible (i : NesetrilRodlDimensionInstance) : Prop :=
  ∃ f : Fin i.1.length → Fin i.2.2 → Fin i.1.length, Function.Injective f ∧
    ∀ u v, (Graph i).Adj u v ↔ ∀ k, f u k ≠ f v k

open Classical in
/-- NESETRIL-RODL DIMENSION as a decision problem over bitstrings. -/
noncomputable def nesetrilRodlDimensionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NesetrilRodlDimensionInstance) x with
  | some i => decide (WellFormed i ∧ NesetrilRodlDimensionFeasible i)
  | none => false

/-- **NESETRIL-RODL DIMENSION is NP-complete.** Source: Garey and Johnson (1979), [GT62];
Nešetřil and Pultr (1977). -/
public theorem_wanted nesetrilRodlDimension_npComplete :
    nesetrilRodlDimensionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nesetrilRodlDimensionDec

end MetaMathlibExt.Complexity.NPComplete.NesetrilRodlDimension
