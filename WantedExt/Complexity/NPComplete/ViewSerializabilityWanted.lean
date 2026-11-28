/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# VIEW SERIALIZABILITY is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 4 (1983), 286-300,
doi:10.1016/0196-6774(83)90028-7, Section 3 (view serializability, "having the same complexity
breakdown as the original notion" of serializability, which is NP-complete; credited to
Yannakakis, "Serializability by locking", manuscript (1982));
M. Yannakakis, "Serializability by locking", J. ACM 31 (1984), 227-244, doi:10.1145/62.322425;
C. H. Papadimitriou, "The serializability of concurrent database updates", J. ACM 26 (1979),
631-653, doi:10.1145/322154.322158 (the semantics of schedules).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.ViewSerializabilityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ViewSerializability

open MetaMathlibExt.Complexity.NPComplete.MultiversionSerializability
  (Value Schedule MultiversionSerializabilityInstance WellFormed action standard values
    finalValue serial)

/-!
# VIEW SERIALIZABILITY is NP-complete

INSTANCE: a schedule `S` for a set `{T₁, ..., Tₙ}` of database transactions whose actions are
`read(x)`'s and `write(x)`'s of single variables. QUESTION: is `S` view serializable, i.e., is
there a serial schedule `S'` of the same transactions such that `S` and `S'` agree not only on
all final values, but also on all reads?

Johnson's column defines the notions. A schedule is serial if it runs the transactions one after
another in the order of some permutation, and `S` is serializable if some serial schedule yields
the same final values as `S`, "assuming that the result of each write depends on the values of all
variables that have previously been read by the transaction containing the write, and no matter
how it depends on those values"; for view serializability "two schedules, to be equivalent, must
agree not only on all final values, but also on all read's as well". Values are therefore
symbolic (Herbrand) values: the original value `init x` of a variable `x`, or `app t k args`, the
uninterpreted function of the `k`-th step of transaction `t` applied to the values `args` that `t`
read at its earlier steps, in order. Every read obtains the value of the latest earlier write of
its variable, or the original value when there is none (the standard interpretation). Two
schedules agree on all reads when every read step of every transaction obtains the same value in
both; this compares every read, unlike the equivalence of SERIALIZABILITY OF DATABASE HISTORIES
([SR33]), which compares the reads of live transactions only.

The schedule model, the symbolic values and the serial schedules are those of
`WantedExt.Complexity.NPComplete.MultiversionSerializabilityWanted` (the same column's problem
[5]), reused here: the instance is the number `n` of transactions and the schedule, a list of
actions `(t, x, w)` in which transaction `t < n` reads (`w = false`) or writes (`w = true`)
variable `x`; each transaction's steps are its actions in schedule order; `standard S` is the
standard interpretation, `values` computes the value of every position, `finalValue` the final
value of every variable, and `serial S π` runs the transactions in the order `π`, each with its
steps in their original order. A transaction's `k`-th read in `S` is its `k`-th read in
`serial S π`.

The number `n` is encoded in binary. NP membership is unaffected: a transaction with no action in
`S` contributes nothing to any serial schedule, so a certificate orders only the at most `|S|`
transactions that occur in `S`; symbolic values are compared as shared DAGs, in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **VIEW SERIALIZABILITY is NP-complete.** Source: Johnson (1983), Section 3; Yannakakis
(1984); Papadimitriou (1979). -/
public theorem_wanted viewSerializability_npComplete :
    viewSerializabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L viewSerializabilityDec

end MetaMathlibExt.Complexity.NPComplete.ViewSerializability
