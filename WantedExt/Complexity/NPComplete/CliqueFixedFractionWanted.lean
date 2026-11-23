/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLIQUE of linear size (fixed fraction r) is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [GT19] CLIQUE, comment.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CliqueFixedFraction

/-!
# CLIQUE of linear size (fixed fraction r) is NP-complete

For a fixed rational `r` with `0 < r < 1`:
INSTANCE: a graph `G = (V, E)`.
QUESTION: does `G` contain a clique of size `r|V|` or more?

The comment to CLIQUE (Garey and Johnson [GT19]) reads: "The variant in which, for a given r,
0 < r < 1, we are asked whether G contains a clique of size r|V| or more is NP-complete for any
fixed value of r." The theorem states this for every fixed `r = p / q` with natural numbers
`0 < p < q`; "size `r|V|` or more" is `p * |V| ≤ q * k` for the size `k` of the clique. A clique
of size `k` is Mathlib's `SimpleGraph.IsNClique k s` (a set `s` of `k` pairwise adjacent
vertices); a clique of size at least `r|V|` exists exactly when one of size exactly some
`k ≥ r|V|` does.

The graph is given by its vertex count `n` (vertices `0, …, n - 1`) and a simple edge list, as a
`SimpleGraph (Fin n)` through `Cslib.Complexity.Karp.edgeGraph`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count, edge list. -/
abbrev CliqueFixedFractionInstance := ℕ × List (ℕ × ℕ)

/-- The graph of the instance as a `SimpleGraph (Fin n)`. -/
def Graph (i : CliqueFixedFractionInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2

/-- Well-formedness of an instance: a simple edge list on the vertices `0, …, n - 1` (no
duplicate edges in either orientation, no self-loops, endpoints in range). -/
def WellFormed (i : CliqueFixedFractionInstance) : Prop :=
  i.2.Nodup ∧ ∀ e ∈ i.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2

/-- The graph has a clique of size at least `(p / q) |V|`: a clique of `k` vertices with
`p * |V| ≤ q * k`. -/
def CliqueFixedFractionFeasible (p q : ℕ) (i : CliqueFixedFractionInstance) : Prop :=
  ∃ k, p * i.1 ≤ q * k ∧ ∃ s, (Graph i).IsNClique k s

open Classical in
/-- CLIQUE of size at least `(p / q) |V|` as a decision problem over bitstrings. -/
noncomputable def cliqueFixedFractionDec (p q : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CliqueFixedFractionInstance) x with
  | some i => decide (WellFormed i ∧ CliqueFixedFractionFeasible p q i)
  | none => false

/-- **CLIQUE of linear size is NP-complete** for every fixed fraction `r = p / q`, `0 < r < 1`.
Source: Garey and Johnson (1979), [GT19], comment. -/
public theorem_wanted cliqueFixedFraction_npComplete (p q : ℕ) (hp : 0 < p) (hpq : p < q) :
    cliqueFixedFractionDec p q ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (cliqueFixedFractionDec p q)

end MetaMathlibExt.Complexity.NPComplete.CliqueFixedFraction
