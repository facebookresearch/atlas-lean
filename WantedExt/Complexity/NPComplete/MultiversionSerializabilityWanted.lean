/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MULTIVERSION SERIALIZABILITY is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 4 (1983), 286-300,
doi:10.1016/0196-6774(83)90028-7, problem [5] MULTIVERSION SERIALIZABILITY (the problem,
credited to Papadimitriou and Kanellakis, transformation from POLYGRAPH ACYCLICITY);
C. H. Papadimitriou and P. C. Kanellakis, "On concurrency control by multiple versions",
Proc. 1st ACM SIGACT-SIGMOD Symp. on Principles of Database Systems (1982), 76-82,
doi:10.1145/588111.588125, and ACM Trans. Database Systems 9 (1984), 89-99,
doi:10.1145/348.318588;
C. H. Papadimitriou, "The serializability of concurrent database updates", J. ACM 26 (1979),
631-653, doi:10.1145/322154.322158 (the semantics of schedules: written values are
uninterpreted functions of the values the transaction read at earlier steps, and two schedules
are equivalent when they leave the same final values under every interpretation).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.MultiversionSerializabilityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MultiversionSerializability

/-!
# MULTIVERSION SERIALIZABILITY is NP-complete

INSTANCE: a schedule `S` for a set `{T₁, ..., Tₙ}` of database transactions whose actions are
atomic `read(x)`'s and `write(x)`'s of single variables.
QUESTION: is `S` multiversion serializable, i.e., is there an interpretation for `S` that yields
the same collection of final variable values as the standard interpretation of some serial
schedule `S'`?

Johnson's column defines an interpretation of a schedule as an assignment to each `read(x)` of
either the output of some earlier `write(x)` or the original value of `x`; the standard
interpretation uses the most recent value. The values follow the multistep model of
Papadimitriou (1979, Section 7.1): the value written by a step is an uninterpreted function of
all values its transaction read at earlier steps, and schedules are compared through the final
values they leave under every interpretation of these functions and every initial values. This
is the same as comparing symbolic (Herbrand) values, `Value` below: the initial value
`init x` of a variable `x`, or `app t k args`, the function of the `k`-th step of transaction `t`
applied to the values `args` that `t` read at its earlier steps, in order.

The transactions are `0, ..., n - 1`; the schedule is a list of actions `(t, x, w)`: transaction
`t` reads (`w = false`) or writes (`w = true`) variable `x`. Each transaction's steps are its
actions in schedule order. Schedule positions are list indices. An interpretation is a function
`V` from the position of each read to `some q`, the position of an earlier write of the same
variable, or `none`, the original value. The final value of `x` is the value of the last write of
`x` (the original value when `x` is never written). A serial schedule runs the transactions one
after another in some order `π` (a permutation of `0, ..., n - 1`), each with its steps in their
original order.

The number `n` is encoded in binary. NP membership is unaffected: a transaction with no action in
`S` contributes nothing to any serial schedule, so a certificate orders only the at most `|S|`
transactions that occur in `S` (any permutation of `0, ..., n - 1` extending that order gives the
same serial schedule), together with one position per read for `V`; symbolic values are compared
as shared DAGs, in polynomial time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **MULTIVERSION SERIALIZABILITY is NP-complete.** Source: Johnson (1983), problem [5];
Papadimitriou and Kanellakis (1982, 1984). -/
public theorem_wanted multiversionSerializability_npComplete :
    multiversionSerializabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiversionSerializabilityDec

end MetaMathlibExt.Complexity.NPComplete.MultiversionSerializability
