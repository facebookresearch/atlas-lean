/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED SATISFIABILITY WITH CONSTANTS is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the Theory of
NP-Completeness*, W. H. Freeman (1979), problem [LO6] GENERALIZED SATISFIABILITY, comment
("formulas with constants");
T. J. Schaefer, "The complexity of satisfiability problems", Proc. 10th Annual ACM Symposium on
Theory of Computing (1978), 216-226, doi:10.1145/800133.804350, Lemma 4.1 (Dichotomy Theorem for
Satisfiability-with-Constants).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.GeneralizedSatisfiabilityConstantsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeneralizedSatisfiabilityConstants

open MetaMathlibExt.Complexity.NPComplete.GeneralizedSatisfiabilityFixed
  (Relation RelationsWellFormed IsEquivalentCNF IsAffine)

/-!
# GENERALIZED SATISFIABILITY WITH CONSTANTS is NP-complete

GENERALIZED SATISFIABILITY ([LO6]) with the sequence `S = ⟨R₁, ..., Rₘ⟩` of relations
`Rᵢ ⊆ {T, F}^{kᵢ}` fixed, where the tuples in each `Cᵢ` are allowed to be in
`(U ∪ {T, F})^{kᵢ}` ("formulas with constants"). INSTANCE: a set `U` of variables and, for
`1 ≤ i ≤ m`, a collection `Cᵢ` of `kᵢ`-tuples of variables from `U` and constants `T`, `F`.
QUESTION: is there a truth assignment `t : U → {T, F}` such that for all `i` and all
`(u[1], ..., u[kᵢ]) ∈ Cᵢ`, `(t(u[1]), ..., t(u[kᵢ])) ∈ Rᵢ`, where a constant stands for its own
truth value?

Garey and Johnson record, after Schaefer's dichotomy for GENERALIZED SATISFIABILITY
(`GeneralizedSatisfiabilityFixedWanted`), that with constants "the problem is NP-complete even if
(1) or (2) holds, but is still polynomially solvable if (3), (4), (5), or (6) holds", where
(3) each `Rᵢ` is logically "equivalent" to some conjunctive normal form expression having at most
one negated literal per clause, (4) each `Rᵢ` is logically "equivalent" to some conjunctive
normal form expression having at most one un-negated literal per clause, (5) each `Rᵢ` is
logically "equivalent" to some conjunctive normal form expression having at most 2 literals per
clause, and (6) each `Rᵢ` is the "solution set" for some system of linear equations over `GF[2]`.
This module states the NP-complete half: for every fixed `S` for which none of (3)-(6) holds, the
problem with constants is NP-complete. This is Schaefer's Lemma 4.1, whose four conditions are
"weakly positive", "weakly negative", "affine" and "bijunctive".

Relations, their well-formedness, CNF equivalence and the affine condition are those of
`GeneralizedSatisfiabilityFixedWanted`: a relation is its arity `k` and the list of its tuples
(`true` for `T`), and (3)-(6) are the last four alternatives of its `SchaeferCondition`. An entry
of a tuple of `Cᵢ` is `(0, x)` for the variable `x`, `(1, 1)` for the constant `T` and `(1, 0)`
for the constant `F`. The instance carries the number `n` of variables (variables
`0, …, n - 1`) and the collections `C₁, ..., Cₘ`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **GENERALIZED SATISFIABILITY WITH CONSTANTS is NP-complete.** For every fixed well-formed
sequence `S` of relations satisfying none of the alternatives (3)-(6), GENERALIZED SATISFIABILITY
with constants over `S` is NP-complete. Source: Garey and Johnson (1979), [LO6]; Schaefer (1978),
Lemma 4.1. -/
public theorem_wanted generalizedSatisfiabilityConstants_npComplete (S : List Relation)
    (_hS : RelationsWellFormed S) (_hTractable : ¬ ConstantsTractable S) :
    generalizedSatisfiabilityConstantsDec S ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L (generalizedSatisfiabilityConstantsDec S)

end MetaMathlibExt.Complexity.NPComplete.GeneralizedSatisfiabilityConstants
