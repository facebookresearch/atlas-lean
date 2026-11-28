/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LINEAR CLIQUE-WIDTH is NP-complete

Source:
M. R. Fellows, F. A. Rosamond, U. Rotics and S. Szeider, "Proving NP-hardness for clique-width
I: non-approximability of sequential clique-width", Electronic Colloquium on Computational
Complexity, Technical Report TR05-080, Revision 1 (2005),
https://eccc.weizmann.ac.il/report/2005/080/ (Section 3, the `r`-sequential clique-width and
footnote 1; Theorem 1, part 2, with `r = 1`);
F. Gurski and E. Wanke, "On the relationship between NLC-width and linear NLC-width",
Theoretical Computer Science 347(1-2) (2005), 76-89, doi:10.1016/j.tcs.2005.05.018 (linear
clique-width).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.LinearCliqueWidthDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LinearCliqueWidth

open MetaMathlibExt.Complexity.NPComplete.CliqueWidth
  (CliqueWidthInstance Generated Graph WellFormed)

/-!
# LINEAR CLIQUE-WIDTH is NP-complete

INSTANCE: a graph `G = (V, E)` (finite, simple, undirected, with at least one vertex) and a
positive integer `K`. QUESTION: is the linear clique-width of `G` at most `K`, that is, is `G`
defined by a linear `K`-expression, a `K`-expression in which every disjoint union has a single
vertex as one of its operands?

Fellows, Rosamond, Rotics and Szeider (Section 3) consider "clique-width constructions where
disjoint union of two `k`-graphs is only allowed if at least one of them has `r` or fewer
vertices. We call such clique-width constructions and the corresponding `k`-expressions
`r`-sequential (or sequential for `r = 1`)"; footnote 1: "Sequential cliquewidth was also
considered by Gurski and Wanke under the term linear clique-width". Theorem 1, part 2: for every
positive integer `r`, "`cwd_r`-minimization is NP-complete", where `cwd_r`-minimization is
"Instance: A graph `G` and a positive integer `k`. Question: Is the `r`-sequential clique-width
of `G` at most `k`?". This module states the case `r = 1`.

The `k`-expressions, the instance, the graph and its well-formedness are those of CLIQUE-WIDTH
(`WantedExt.Complexity.NPComplete.CliqueWidthWanted`: labels `Fin k`, the operations `i(v)`,
`⊕`, `η_{i,j}` and `ρ_{i→j}` of Courcelle and Olariu, graphs given by an edge list on `Fin n`
with `0 < n`). `CliqueWidth.Generated` records which labelled graphs some `k`-expression
defines, but not the sizes of the operands of its unions, so the linear expressions are a
separate inductive predicate `LinearGenerated` with the same `vertex`, `join` and `relabel`
constructors, and with `union` replaced by `addVertex`: the union `G ⊕ i(v)` with one new
vertex labelled `i`, which Fellows et al. write `α_{i(v)}`. A one-vertex operand of a union is
`i(v)` for some label `i` (joins add no edge to one vertex, and relabelling changes only its
label), and putting it on the right loses nothing, since the graph is asked for only up to
isomorphism (`≃g`), under any final labelling. `LinearGenerated.generated` shows that every
linear `k`-expression is a `k`-expression. With `K = 0` no vertex can be created, so `K = 0`
is a no-instance.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **LINEAR CLIQUE-WIDTH is NP-complete.** Source: Fellows, Rosamond, Rotics and Szeider
(2005), Theorem 1 with `r = 1`. -/
public theorem_wanted linearCliqueWidth_npComplete :
    linearCliqueWidthDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L linearCliqueWidthDec

end MetaMathlibExt.Complexity.NPComplete.LinearCliqueWidth
