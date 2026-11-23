/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ANOTHER 3-COLORING is NP-complete

Source:
D. P. Dailey, "Uniqueness of colorability and colorability of planar 4-regular graphs are
NP-complete", Discrete Mathematics 30(3) (1980), 289-293, doi:10.1016/0012-365X(80)90236-8;
Shalu M. A. and C. Antony, "Hardness transitions and uniqueness of acyclic colouring", Discrete
Applied Mathematics 345 (2024), 77-98, doi:10.1016/j.dam.2023.11.030, Section 1.4.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Karp.Color
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AnotherThreeColoring

/-!
# ANOTHER 3-COLORING is NP-complete

INSTANCE: a graph `G = (V, E)` and a proper 3-coloring `c : V → {0, 1, 2}` of `G`.
QUESTION: does `G` have a proper 3-coloring that is not obtained from `c` by permuting the
colors, i.e. a proper 3-coloring `f` such that `f ≠ σ ∘ c` for every permutation `σ` of the
three colors?

This is the another-solution problem of GRAPH 3-COLORABILITY ([GT4] with `K = 3`). Shalu and
Antony (Section 1.4) state ANOTHER `k`-COLOURING `[R_swap]` with instance "a graph `G`, and a
`k`-colouring `f` of `G`" and question "Is there another `k`-colouring of `G` up to colour
swaps?", two colorings being equivalent when "the same up to colour swaps", and record that
"Dailey proved that for all `k ≥ 3`, ANOTHER `k`-COLOURING `[R_swap]` is NP-hard" (by a
reduction from `k`-COLOURABILITY), hence NP-complete. This module states the case `k = 3`.
A proper 3-coloring is Mathlib's `SimpleGraph.Coloring (Fin 3)`; two colorings are the same up
to color swaps exactly when one is the other composed with a permutation of `Fin 3`.

The graph is simple and given by an edge list on `Fin n`; the coloring is the list of the
colors `c(0), …, c(n - 1)`, each below `3`, and it must be proper. The list has length `n`, so
the vertex count is bounded by the input length.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count `n` (vertices `Fin n`), edge list, and the colors
`c(0), …, c(n - 1)` of the given coloring. -/
abbrev AnotherThreeColoringInstance := ℕ × List (ℕ × ℕ) × List ℕ

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : AnotherThreeColoringInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The given coloring: vertex `v` gets the color `c(v)`, read in `Fin 3` (`Fin.ofNat` reduces
modulo `3`, which is exact because `WellFormed` requires every listed color to be below `3`). -/
def given (i : AnotherThreeColoringInstance) (v : Fin i.1) : Fin 3 :=
  Fin.ofNat 3 (i.2.2.getD v 0)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), the coloring lists
one color below `3` per vertex, and it is proper. -/
def WellFormed (i : AnotherThreeColoringInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    i.2.2.length = i.1 ∧ (∀ x ∈ i.2.2, x < 3) ∧
      ∀ u v, (Graph i).Adj u v → given i u ≠ given i v

/-- The graph has a proper 3-coloring that is not the given one up to a permutation of the
colors. -/
def AnotherThreeColoringFeasible (i : AnotherThreeColoringInstance) : Prop :=
  ∃ f : (Graph i).Coloring (Fin 3), ¬ ∃ σ : Equiv.Perm (Fin 3), ∀ v, f v = σ (given i v)

open Classical in
/-- ANOTHER 3-COLORING as a decision problem over bitstrings. -/
noncomputable def anotherThreeColoringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := AnotherThreeColoringInstance) x with
  | some i => decide (WellFormed i ∧ AnotherThreeColoringFeasible i)
  | none => false

/-- **ANOTHER 3-COLORING is NP-complete.** Source: Dailey (1980), as recorded by Shalu and
Antony (2024). -/
public theorem_wanted anotherThreeColoring_npComplete :
    anotherThreeColoringDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L anotherThreeColoringDec

end MetaMathlibExt.Complexity.NPComplete.AnotherThreeColoring
