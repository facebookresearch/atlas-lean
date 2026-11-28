/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LINEAR COMPLEMENTARITY is NP-complete

Source:
S. J. Chung, "NP-completeness of the linear complementarity problem", Journal of Optimization
Theory and Applications 60 (1989), 393-399, doi:10.1007/BF00940344.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.LinearComplementarityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.LinearComplementarity

/-!
# LINEAR COMPLEMENTARITY is NP-complete

INSTANCE: an `n × n` integer matrix `M` and an integer vector `q` of length `n`.
QUESTION: are there vectors `w, z` with `w - M z = q`, `w ≥ 0`, `z ≥ 0` and `wᵀ z = 0`?

Chung (1989) proved that deciding whether a linear complementarity problem `LCP(q, M)` has a
solution is NP-complete. Since `w = M z + q` is determined by `z`, the question asks for a
rational `z ≥ 0` with `M z + q ≥ 0` and `zᵀ (M z + q) = 0`. Solutions are sought over `ℚ`; with
integer data this loses nothing: a solution fixes, for each index, which of `zⱼ` and `wⱼ` is zero,
and the remaining linear feasibility system with integer coefficients has a rational solution
whenever it has a real one.

Numbers use the canonical binary encoding; an integer `a` is a pair `(p, n)` of naturals with
`a = p - n`, as in `ZeroOneILPWanted`. The matrix is given as `n` rows of `n` entries each.

Membership in NP: the certificate is the complementary support (which of `zⱼ`, `wⱼ` may be
nonzero for each `j`), and the remaining linear system is solved in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **LINEAR COMPLEMENTARITY is NP-complete.** Source: Chung (1989). -/
public theorem_wanted linearComplementarity_npComplete :
    linearComplementarityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L linearComplementarityDec

end MetaMathlibExt.Complexity.NPComplete.LinearComplementarity
