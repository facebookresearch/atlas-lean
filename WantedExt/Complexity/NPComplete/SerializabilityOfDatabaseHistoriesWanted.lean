/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# SERIALIZABILITY OF DATABASE HISTORIES is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [SR33] SERIALIZABILITY OF DATABASE
HISTORIES;
C. H. Papadimitriou, "The serializability of concurrent database updates", Journal of the ACM
26 (1979), 631-653, doi:10.1145/322154.322158.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.SerializabilityOfDatabaseHistoriesDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.SerializabilityOfDatabaseHistories

/-!
# SERIALIZABILITY OF DATABASE HISTORIES is NP-complete

INSTANCE: a set `V` of database variables, a collection `T` of transactions `(R_i, W_i)`,
`1 ≤ i ≤ n`, where `R_i` and `W_i` are subsets of `V` (the read set and the write set), and a
history `H` for `T`: a permutation of all the `R_i` and `W_i` in which each `R_i` occurs before
the corresponding `W_i`. QUESTION: is there a serial history `H'` for `T` (each `R_i` immediately
followed by `W_i`) that is equivalent to `H`, i.e., has the same set of live transactions and,
for each live read, the same writer it reads from?

The definitions are Papadimitriou's (Section 2), which Garey and Johnson follow. The augmented
history adds a transaction `T_{n+1}` before `H` that reads nothing and writes every variable,
and a transaction `T_{n+2}` after `H` that reads every variable and writes nothing. `R_j` reads
`x` from `W_i` if `x ∈ S(R_j)` and `W_i` is the latest write symbol before `R_j` in the augmented
history whose write set contains `x`. `T_{n+2}` is live; if a live `R_j` reads a variable from
`W_i`, then `T_i` is live; no other transaction is live. Two histories are equivalent iff they
have the same live transactions and every live `R_j` reads each `x` from the same `W_i`
(Papadimitriou's Proposition 1, the characterization Garey and Johnson state). A history is
serial if each `R_i` immediately precedes `W_i`.

Transactions are numbered `0, …, n - 1`; `n` and `n + 1` are the added initial and final
transactions. Variables are `0, …, k - 1`. An operation is `(t, false)` for `R_t` and
`(t, true)` for `W_t`, and a history is a list of operations.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **SERIALIZABILITY OF DATABASE HISTORIES is NP-complete.** Source: Garey and Johnson
(1979), [SR33]; Papadimitriou (1979), Theorem 1. -/
public theorem_wanted serializabilityOfDatabaseHistories_npComplete :
    serializabilityOfDatabaseHistoriesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L serializabilityOfDatabaseHistoriesDec

end MetaMathlibExt.Complexity.NPComplete.SerializabilityOfDatabaseHistories
