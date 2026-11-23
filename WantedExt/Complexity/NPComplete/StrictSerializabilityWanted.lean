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
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.MultiversionSerializabilityWanted

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

/-- A schedule of atomic steps `(t, X, w)`: transaction `t` reads (`w = false`) or writes
(`w = true`) the variables of `X`. -/
abbrev StepSchedule := List (ℕ × List ℕ × Bool)

/-- An instance: the number `n` of transactions and the schedule of steps. -/
abbrev StrictSerializabilityInstance := ℕ × StepSchedule

/-- The single-variable schedule listing each step `(t, X, w)` as the actions `(t, x, w)` for
the variables `x` of `X`, in order. -/
def flatten (S : StepSchedule) : Schedule :=
  S.flatMap fun s => s.2.1.map fun x => (s.1, x, s.2.2)

/-- Well-formedness of an instance: every step belongs to one of the transactions
`0, ..., n - 1` and lists its variables without repetitions, and every transaction has a
step. -/
def WellFormed (i : StrictSerializabilityInstance) : Prop :=
  (∀ s ∈ i.2, s.1 < i.1 ∧ s.2.1.Nodup) ∧ ∀ t < i.1, ∃ s ∈ i.2, s.1 = t

/-- All steps of transaction `t` precede all steps of transaction `t'` in `S`. -/
def AllBefore (S : StepSchedule) (t t' : ℕ) : Prop :=
  ∀ p q : Fin S.length, S[p].1 = t → S[q].1 = t' → p < q

/-- Some serial order `π` of the `n` transactions yields the same final values as `S`, and puts
`T` before `T'` whenever all steps of `T` precede all steps of `T'` in `S`. -/
def StrictSerializabilityFeasible (i : StrictSerializabilityInstance) : Prop :=
  ∃ π : List ℕ, π.Perm (List.range i.1) ∧
    (∀ x : ℕ, finalValue (flatten i.2) (standard (flatten i.2)) x =
      finalValue (serial (flatten i.2) π) (standard (serial (flatten i.2) π)) x) ∧
    ∀ t < i.1, ∀ t' < i.1, AllBefore i.2 t t' → π.idxOf t < π.idxOf t'

open Classical in
/-- STRICT SERIALIZABILITY as a decision problem over bitstrings. -/
noncomputable def strictSerializabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := StrictSerializabilityInstance) x with
  | some i => decide (WellFormed i ∧ StrictSerializabilityFeasible i)
  | none => false

/-- **STRICT SERIALIZABILITY is NP-complete.** Source: Johnson, NP-completeness column (1983),
problem [4]; Sethi (1982). -/
public theorem_wanted strictSerializability_npComplete :
    strictSerializabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L strictSerializabilityDec

end MetaMathlibExt.Complexity.NPComplete.StrictSerializability
