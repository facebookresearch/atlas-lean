/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HORN CORE is NP-complete

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, problem
MAXIMUM HORN CORE (decision version);
D. Kavvadias, C. H. Papadimitriou and M. Sideri, "On Horn envelopes and hypergraph
transversals", Algorithms and Computation (ISAAC 1993), Lecture Notes in Comput. Sci. 762,
Springer (1993), 399-405, doi:10.1007/3-540-57568-5_271;
G. Gogic, C. H. Papadimitriou and M. Sideri, "Incremental recompilation of knowledge",
J. Artificial Intelligence Res. 8 (1998), 23-37, doi:10.1613/jair.380, Theorem 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.HornCoreDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.HornCore

open Cslib.Logic.LegacyPL Cslib.Algorithms.SAT.Horn

/-!
# HORN CORE is NP-complete

INSTANCE: a set `M` of truth assignments on `n` variables, and a positive integer `K`.
QUESTION: is there a Horn core of `M`, that is, a subset `M' ⊆ M` such that `M'` is equal to
the set of truth assignments satisfying a Horn Boolean formula, with `|M'| ≥ K`?

A truth assignment on `n` variables is a list of `n` Booleans (entry `x` is the value of
variable `x`), and `M` is a duplicate-free list of such lists. A Horn formula is a CNF formula
(`Cslib.Logic.LegacyPL.CNF`) in which every clause has at most one positive literal
(`Cslib.Algorithms.SAT.Horn.IsHorn`); a formula on the `n` variables uses only the variables
`0, …, n - 1`, and its set of satisfying truth assignments on the `n` variables must be exactly
`M'`. The subset `M'` is a sublist of `M`, so it has no duplicates and its length is `|M'|`.

Kavvadias, Papadimitriou and Sideri (1993) call such a formula a Horn core when `M'` is
maximal; a subset of size at least `K` exists iff a maximal one does, so the question is the
same. Gogic, Papadimitriou and Sideri (1998), Theorem 1, record their result that selecting
the Horn core with the maximum number of models is NP-complete.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **HORN CORE is NP-complete.** Source: Crescenzi and Kann, MAXIMUM HORN CORE; Kavvadias,
Papadimitriou and Sideri (1993); Gogic, Papadimitriou and Sideri (1998), Theorem 1. -/
public theorem_wanted hornCore_npComplete :
    hornCoreDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hornCoreDec

end MetaMathlibExt.Complexity.NPComplete.HornCore
