/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HOMOLOGY LOCALIZATION (one-dimensional, over Z₂) is NP-complete

Source:
C. Chen and D. Freedman, "Hardness results for homology localization", Discrete and
Computational Geometry 45 (2011), 425-448, doi:10.1007/s00454-010-9322-8.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HomologyLocalizationDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HomologyLocalization

open scoped symmDiff
open MathlibExt.Combinatorics.RationalSimplicialHomologyShared (IsSimplicialComplex)

/-!
# HOMOLOGY LOCALIZATION (one-dimensional, over Z₂) is NP-complete

INSTANCE: a finite simplicial complex `K`, a one-dimensional cycle `z` of `K` over `Z₂`, and a
natural number `k`. QUESTION: is there a one-dimensional cycle `z'` of `K` over `Z₂` that is
homologous to `z` and has at most `k` edges?

Over `Z₂` a one-dimensional chain is a set of edges (one-dimensional faces) of `K`, and the sum
of two chains is their symmetric difference. The boundary of an edge `{a, b}` is `{a} + {b}`,
so a chain `c` is a cycle exactly when every vertex lies in an even number of edges of `c`. The
boundary of a set `T` of triangles (two-dimensional faces) is the set of edges that lie in an
odd number of triangles of `T`. Two cycles `z, z'` are homologous when `z + z' = ∂T` for some
set `T` of triangles. The number of edges of `z'` is its volume (1-norm), the measure of
Chen and Freedman's volume localization.

Complexes are the repository's finite abstract simplicial complexes on the vertex set `ℕ`
(`MathlibExt.Combinatorics.RationalSimplicialHomologyShared`): finite families of finite sets
closed under taking subsets (`IsSimplicialComplex`). The instance lists all faces of `K`, each
a list of distinct vertices, every face listed once. The cycle `z` is a list of distinct edges
of `K`.

Chen and Freedman prove that localizing a given homology class over `Z₂` with a cycle of
minimal volume is NP-hard, indeed NP-hard to approximate within any constant factor, already
for one-dimensional classes. Membership in NP: `z'` and the set `T` of triangles are a
certificate of size at most the number of faces of `K`, checked by parity counts. The bound
`k` may be `0`, when the question asks whether `z` is a boundary.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HOMOLOGY LOCALIZATION (one-dimensional, over `Z₂`) is NP-complete.** Source: Chen and
Freedman (2011). -/
public theorem_wanted homologyLocalization_npComplete :
    homologyLocalizationDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L homologyLocalizationDec

end MetaMathlibExt.Complexity.NPComplete.HomologyLocalization
