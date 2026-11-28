/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED SATISFIABILITY is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO6] GENERALIZED
SATISFIABILITY;
T. J. Schaefer, "The complexity of satisfiability problems", Proceedings of the
Tenth Annual ACM Symposium on Theory of Computing (STOC 1978), 216-226,
doi:10.1145/800133.804350.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GeneralizedSatisfiabilityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeneralizedSatisfiability

/-!
# GENERALIZED SATISFIABILITY is NP-complete

INSTANCE: positive integers `k₁, ..., kₘ`, a sequence `S = ⟨R₁, ..., Rₘ⟩` of subsets
`Rᵢ ⊆ {T, F}^{kᵢ}`, a set `U` of variables, and, for `1 ≤ i ≤ m`, a collection `Cᵢ` of
`kᵢ`-tuples of variables from `U`. QUESTION: is there a truth assignment `t : U → {T, F}` such
that for all `i` and all `(u[1], ..., u[kᵢ]) ∈ Cᵢ`, `(t(u[1]), ..., t(u[kᵢ])) ∈ Rᵢ`?

The relations are part of the instance and are given explicitly, each as the list of its
tuples, with `true` for `T` and `false` for `F`. The variables are `0, ..., n - 1`; a tuple of
variables is a list of variable indices (a variable may repeat within a tuple). An assignment is
a function `t : ℕ → Bool`; only its values on `0, ..., n - 1` matter under `WellFormed`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GENERALIZED SATISFIABILITY is NP-complete.** Source: Garey and Johnson (1979), [LO6];
Schaefer (1978). -/
public theorem_wanted generalizedSatisfiability_npComplete :
    generalizedSatisfiabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L generalizedSatisfiabilityDec

end MetaMathlibExt.Complexity.NPComplete.GeneralizedSatisfiability
