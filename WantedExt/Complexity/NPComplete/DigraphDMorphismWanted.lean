/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# DIGRAPH D-MORPHISM is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT53] DIGRAPH D-MORPHISM;
A. S. Fraenkel and Y. Yesha, "Complexity of problems in games, graphs and algebraic
equations", Discrete Applied Mathematics 1 (1979), 15-30,
doi:10.1016/0166-218X(79)90012-X.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Combinatorics.Digraph.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.DigraphDMorphism

/-!
# DIGRAPH D-MORPHISM is NP-complete

Given directed graphs `G = (V₁, A₁)` and `H = (V₂, A₂)`, is there a D-morphism from `G` to
`H`, that is, a function `f : V₁ → V₂` such that for all `(u, v) ∈ A₁` either
`(f u, f v) ∈ A₂` or `(f v, f u) ∈ A₂`, and such that for all `u ∈ V₁` and `v' ∈ V₂`, if
`(f u, v') ∈ A₂` then there is a `v ∈ f⁻¹(v')` with `(u, v) ∈ A₁`?

The vertices of a digraph with `n` vertices are `0, ..., n - 1`, and its arcs are a list of
ordered pairs (a repeated arc does not change the digraph). As in the repository's other
directed-graph problems, digraphs have no loops: every arc `(u, v)` has `u ≠ v`. Each digraph
is a Mathlib `Digraph (Fin n)`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count and arc list of `G`, vertex count and arc list of `H`. -/
abbrev DigraphDMorphismInstance := ℕ × List (ℕ × ℕ) × ℕ × List (ℕ × ℕ)

/-- The digraph `G` as a `Digraph (Fin n₁)`: `u → v` is an arc when `(u, v)` is listed. -/
def DigraphG (i : DigraphDMorphismInstance) : Digraph (Fin i.1) where
  Adj u v := ((u : ℕ), (v : ℕ)) ∈ i.2.1

/-- The digraph `H` as a `Digraph (Fin n₂)`: `u → v` is an arc when `(u, v)` is listed. -/
def DigraphH (i : DigraphDMorphismInstance) : Digraph (Fin i.2.2.1) where
  Adj u v := ((u : ℕ), (v : ℕ)) ∈ i.2.2.2

/-- Well-formedness of an instance: every arc of `G` joins two distinct vertices below `n₁`,
and every arc of `H` joins two distinct vertices below `n₂` (no loops). -/
def WellFormed (i : DigraphDMorphismInstance) : Prop :=
  (∀ a ∈ i.2.1, a.1 < i.1 ∧ a.2 < i.1 ∧ a.1 ≠ a.2) ∧
    ∀ a ∈ i.2.2.2, a.1 < i.2.2.1 ∧ a.2 < i.2.2.1 ∧ a.1 ≠ a.2

/-- There is a D-morphism from `G` to `H`: every arc of `G` is sent to an arc of `H` in one
of the two directions, and every arc of `H` leaving the image `f u` of a vertex `u` ends at
the image of some out-neighbor of `u`. -/
def DigraphDMorphismFeasible (i : DigraphDMorphismInstance) : Prop :=
  ∃ f : Fin i.1 → Fin i.2.2.1,
    (∀ u v, (DigraphG i).Adj u v →
      (DigraphH i).Adj (f u) (f v) ∨ (DigraphH i).Adj (f v) (f u)) ∧
    ∀ u v', (DigraphH i).Adj (f u) v' → ∃ v, f v = v' ∧ (DigraphG i).Adj u v

open Classical in
/-- DIGRAPH D-MORPHISM as a decision problem over bitstrings. -/
noncomputable def digraphDMorphismDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := DigraphDMorphismInstance) x with
  | some i => decide (WellFormed i ∧ DigraphDMorphismFeasible i)
  | none => false

/-- **DIGRAPH D-MORPHISM is NP-complete.** Source: Garey and Johnson (1979), [GT53];
Fraenkel and Yesha (1979). -/
public theorem_wanted digraphDMorphism_npComplete :
    digraphDMorphismDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L digraphDMorphismDec

end MetaMathlibExt.Complexity.NPComplete.DigraphDMorphism
