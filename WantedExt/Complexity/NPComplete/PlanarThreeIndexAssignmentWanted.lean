/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PLANAR 3-INDEX ASSIGNMENT is NP-complete

Source:
A. M. Frieze, "Complexity of a 3-dimensional assignment problem", European Journal of
Operational Research 13 (1983), 161-164, doi:10.1016/0377-2217(83)90078-4;
A. Ćustić, B. Klinz and G. J. Woeginger, "Planar 3-dimensional assignment problems with
Monge-like cost arrays", arXiv:1405.5210 (2014), Section 1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.PlanarThreeIndexAssignmentDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PlanarThreeIndexAssignment

/-!
# PLANAR 3-INDEX ASSIGNMENT is NP-complete

INSTANCE: an `n × n × n` array (`n ≥ 1`) of integer costs `c_{ijk}` and an integer bound `B`.
QUESTION: is there a 0-1 array `x_{ijk}` with `∑_k x_{ijk} = 1` for all `i, j`,
`∑_i x_{ijk} = 1` for all `j, k` and `∑_j x_{ijk} = 1` for all `i, k` (a set of `n²` cells
meeting every line of the array exactly once), whose cost `∑ c_{ijk} x_{ijk}` is at most `B`?

The first family of constraints says that `x` is the graph of a function
`L : (i, j) ↦ k`; the other two say that every column `i ↦ L i j` and every row
`j ↦ L i j` of `L` is a bijection, i.e. `L` is a Latin square. Indices run over
`Fin n`. Frieze proves the problem NP-hard, already for 0-1 cost arrays (as recorded by
Ćustić, Klinz and Woeginger); a Latin square is a certificate checkable in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **PLANAR 3-INDEX ASSIGNMENT is NP-complete.** Source: Frieze (1983); Ćustić, Klinz and
Woeginger (2014). -/
public theorem_wanted planarThreeIndexAssignment_npComplete :
    planarThreeIndexAssignmentDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L planarThreeIndexAssignmentDec

end MetaMathlibExt.Complexity.NPComplete.PlanarThreeIndexAssignment
