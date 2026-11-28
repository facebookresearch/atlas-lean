/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLOSEST VECTOR PROBLEM is NP-complete

Source:
P. van Emde Boas, "Another NP-complete partition problem and the complexity of computing short
vectors in a lattice", Report 81-04, Mathematisch Instituut, University of Amsterdam (1981),
p. 2, problem NEAREST VECTOR and Theorem 2;
D. Micciancio, "The shortest vector in a lattice is hard to approximate to within some
constant", SIAM J. Comput. 30 (2001), 2008-2035, doi:10.1137/S0097539700373039, Sections 1-2
(the closest vector problem "was proved NP-hard to solve exactly by van Emde Boas", who calls it
"Nearest Vector").
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ClosestVectorDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ClosestVector

/-!
# CLOSEST VECTOR PROBLEM is NP-complete

INSTANCE: a basis `(v₁, …, v_k)` for a lattice in `ℤᵏ`, a positive integer `K`, and a vector
`b ∈ ℤᵏ`.
QUESTION: does the lattice contain a vector `v = x₁v₁ + ⋯ + x_kv_k` with integral `xᵢ` such
that the Euclidean length `|v - b| ≤ K`?

This is van Emde Boas's NEAREST VECTOR problem, proved NP-complete in his Theorem 2, in the
Euclidean norm. A basis for a lattice in `ℤᵏ` is a list of `k` linearly independent vectors of
`ℤᵏ`; for `k` vectors of length `k` this is the nonvanishing of the `k × k` determinant. Since
`K ≥ 0` and all quantities are integers, `|v - b| ≤ K` is stated as
`∑ⱼ (vⱼ - bⱼ)² ≤ K²`. Each integer is encoded as a pair of naturals
`(positive part, negative part)` representing their difference, and numbers use the canonical
binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **CLOSEST VECTOR PROBLEM is NP-complete.** Source: van Emde Boas (1981), Theorem 2;
Micciancio (2001). -/
public theorem_wanted closestVector_npComplete :
    closestVectorDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L closestVectorDec

end MetaMathlibExt.Complexity.NPComplete.ClosestVector
