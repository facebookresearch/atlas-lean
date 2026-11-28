/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STRICT SERIALIZABILITY is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 4 (1983),
286-300, doi:10.1016/0196-6774(83)90028-7, problem [4] STRICT SERIALIZABILITY (reference:
Sethi; transformation from 3SAT);
R. Sethi, "Useless actions make a difference: strict serializability of database updates",
Journal of the ACM 29 (1982), 394-403, doi:10.1145/322307.322314.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Complexity.NPComplete.StrictSerializabilityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StrictSerializability

open MetaMathlibExt.Complexity.NPComplete.MultiversionSerializability
  (Schedule standard finalValue serial)

/-!
# STRICT SERIALIZABILITY is NP-complete

INSTANCE: a schedule `S` for a set `{T₁, ..., Tₙ}` of database transactions, where the actions
are atomic `read(X)`'s and `write(X)`'s (`X` a set of variables).
QUESTION: is `S` strictly serializable, i.e., is it equivalent to a serial schedule `S'` such
that for any pair of transactions `T` and `T'`, if all actions of `T` precede all actions of
`T'` in `S`, then they also do so in `S'`?

Johnson's column defines the notions. A schedule is serial if it runs the transactions one after
another in the order of some permutation, and two schedules are equivalent if they yield the same
final values for the variables, "assuming that the result of each write depends on the values of
all variables that have previously been read by the transaction containing the write, and no
matter how it depends on those values". Values are therefore the symbolic (Herbrand) values
`MultiversionSerializability.Value` of the same column's problem [5], MULTIVERSION
SERIALIZABILITY (`WantedExt.Complexity.NPComplete.MultiversionSerializabilityWanted`), whose
single-variable schedule machinery is reused: `standard` (every read obtains the value of the
latest earlier write of its variable), `finalValue` and `serial`.

The transactions are `0, ..., n - 1`, and the schedule is a list of atomic steps `(t, X, w)`:
transaction `t` reads (`w = false`) or writes (`w = true`) the variables of the list `X`, which
has no repetitions. Every transaction has at least one step (the schedule is a schedule for these
transactions; a transaction without actions would vacuously both precede and follow every other).
For the values, each step is listed as the single-variable actions on the variables of `X`, in
order (`flatten`): these actions are consecutive, so the reads of a step obtain the values the
atomic step reads, and each variable written by a step receives its own uninterpreted function of
the values its transaction read at earlier steps. Running the steps serially in the order `π`
and then listing them is `serial (flatten S) π`. All steps of `T` precede all steps of `T'` in
that serial schedule exactly when `T` comes before `T'` in `π`.

Sethi proves strict serializability NP-complete for two-step transactions (a read step followed
by a write step, each on a set of variables) when useless actions are allowed, and for multistep
transactions even without useless actions; such schedules are instances here. Membership in NP:
`π` is a certificate (`n ≤ |S|`), and symbolic values are compared as shared DAGs, in polynomial
time.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- **STRICT SERIALIZABILITY is NP-complete.** Source: Johnson, NP-completeness column (1983),
problem [4]; Sethi (1982). -/
public theorem_wanted strictSerializability_npComplete :
    strictSerializabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L strictSerializabilityDec

end MetaMathlibExt.Complexity.NPComplete.StrictSerializability
