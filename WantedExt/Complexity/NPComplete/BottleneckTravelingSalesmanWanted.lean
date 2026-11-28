/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# BOTTLENECK TRAVELING SALESMAN is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND24] BOTTLENECK TRAVELING
SALESMAN (transformation from HAMILTONIAN CIRCUIT; NP-complete even with all distances in
`{1, 2}`).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.BottleneckTravelingSalesmanDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.BottleneckTravelingSalesman

/-!
# BOTTLENECK TRAVELING SALESMAN is NP-complete

Given a set `C` of `m` cities, a distance `d(cᵢ, cⱼ) ∈ Z⁺` for each pair of cities, and a
positive integer `B`, is there a tour of `C` whose longest edge is no longer than `B`, i.e.,
a permutation `⟨c_π(1), ..., c_π(m)⟩` of `C` with `d(c_π(i), c_π(i+1)) ≤ B` for `1 ≤ i < m`
and `d(c_π(m), c_π(1)) ≤ B`?

The cities are `0, ..., m - 1` with `m ≥ 1`, and the distances are an `m × m` symmetric
matrix with positive off-diagonal entries and zero diagonal (the diagonal only enters the
return edge of the one-city tour), as in `TspWanted`. A tour is a permutation of the cities,
given as a list.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **BOTTLENECK TRAVELING SALESMAN is NP-complete.** Source: Garey and Johnson
(1979), [ND24]. -/
public theorem_wanted bottleneckTravelingSalesman_npComplete :
    bottleneckTravelingSalesmanDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L bottleneckTravelingSalesmanDec

end MetaMathlibExt.Complexity.NPComplete.BottleneckTravelingSalesman
