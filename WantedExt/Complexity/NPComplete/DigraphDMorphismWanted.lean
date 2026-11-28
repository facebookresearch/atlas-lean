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
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.DigraphDMorphismDefs

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

/-- **DIGRAPH D-MORPHISM is NP-complete.** Source: Garey and Johnson (1979), [GT53];
Fraenkel and Yesha (1979). -/
public theorem_wanted digraphDMorphism_npComplete :
    digraphDMorphismDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L digraphDMorphismDec

end MetaMathlibExt.Complexity.NPComplete.DigraphDMorphism
