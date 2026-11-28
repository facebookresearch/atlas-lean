/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COLLAPSE OF A 3-COMPLEX TO A 1-COMPLEX is NP-complete

Source:
R. Malgouyres and A. R. Francés, "Determining whether a simplicial 3-complex collapses to a
1-complex is NP-complete", Discrete Geometry for Computer Imagery (DGCI 2008), Lecture Notes in
Computer Science 4992, Springer (2008), 177-188, doi:10.1007/978-3-540-79126-3_17;
M. Tancer, "Recognition of collapsible complexes is NP-complete", Discrete & Computational
Geometry 55 (2016), 21-38, doi:10.1007/s00454-015-9747-1 (definitions, Section 2).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.CollapseToOneComplexDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CollapseToOneComplex

open MathlibExt.Combinatorics.RationalSimplicialHomologyShared

/-!
# COLLAPSE OF A 3-COMPLEX TO A 1-COMPLEX is NP-complete

INSTANCE: a finite 3-dimensional simplicial complex `K`. QUESTION: does `K` collapse to some
1-dimensional complex?

Complexes are the repository's finite abstract simplicial complexes on the vertex set `ℕ`
(`MathlibExt.Combinatorics.RationalSimplicialHomologyShared`): finite families of finite sets
closed under taking subsets. A face with `k + 1` vertices has dimension `k`. The instance lists
generating faces, each a list of at most 4 distinct vertices, at least one with exactly 4;
`K` is the family of all subsets of the listed faces (`complex`), so `K` has dimension 3. (The
faces of `K` number at most 16 per listed face, so this input and the list of all faces used
by Tancer are polynomially equivalent.)

Collapses follow Tancer, Section 2. A face `σ` of `K` is free when it is nonempty, not
maximal, and contained in exactly one maximal face `τ` of `K` (`IsFreeFace`). The complex
`K \ {ϑ ∈ K | σ ⊆ ϑ}` arises from `K` by an elementary collapse (`ElementaryCollapse`), and `K`
collapses to `L` when a finite sequence of elementary collapses leads from `K` to `L`
(`Collapses`, the reflexive-transitive closure). A 1-complex is a complex of dimension at most
1: every face has at most 2 vertices (`topCard L ≤ 2`). An elementary collapse lowers the
dimension by at most one, so a 3-complex collapses to a complex of dimension at most 1 exactly
when it collapses to one of dimension exactly 1.

Malgouyres and Francés prove that deciding whether a 3-complex collapses to a 1-complex is
NP-complete (title and main theorem; also recorded by Tancer, Section 1). Membership in NP:
a sequence of elementary collapses is a polynomial certificate (Tancer, Section 1).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **COLLAPSE OF A 3-COMPLEX TO A 1-COMPLEX is NP-complete.** Source: Malgouyres and Francés
(2008); Tancer (2016). -/
public theorem_wanted collapseToOneComplex_npComplete :
    collapseToOneComplexDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L collapseToOneComplexDec

end MetaMathlibExt.Complexity.NPComplete.CollapseToOneComplex
