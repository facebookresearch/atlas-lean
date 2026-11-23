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
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

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

/-- A symbolic value: the original value of a variable, or the value written by step `k` of
transaction `t`, an uninterpreted function of the values `args` that `t` read at earlier
steps. -/
inductive Value where
  | init (x : ℕ)
  | app (t k : ℕ) (args : List Value)

/-- A schedule: actions `(t, x, w)`, transaction `t` reading (`w = false`) or writing
(`w = true`) variable `x`. -/
abbrev Schedule := List (ℕ × ℕ × Bool)

/-- An instance: the number `n` of transactions and the schedule. -/
abbrev MultiversionSerializabilityInstance := ℕ × Schedule

/-- Well-formedness of an instance: every action belongs to one of the transactions
`0, ..., n - 1`. -/
def WellFormed (i : MultiversionSerializabilityInstance) : Prop :=
  ∀ a ∈ i.2, a.1 < i.1

/-- The action at position `p` (a dummy read of variable `0` by transaction `0` out of range). -/
def action (S : Schedule) (p : ℕ) : ℕ × ℕ × Bool :=
  S.getD p (0, 0, false)

/-- `V` is an interpretation of `S`: every read is assigned the position of an earlier write of
the same variable, or `none` (the original value). -/
def IsInterpretation (S : Schedule) (V : ℕ → Option ℕ) : Prop :=
  ∀ p < S.length, (action S p).2.2 = false → ∀ q, V p = some q →
    q < p ∧ (action S q).2.2 = true ∧ (action S q).2.1 = (action S p).2.1

/-- The standard interpretation: a read is assigned the latest earlier write of its variable. -/
def standard (S : Schedule) (p : ℕ) : Option ℕ :=
  ((List.range p).filter fun q =>
    (action S q).2.2 && (action S q).2.1 == (action S p).2.1).getLast?

/-- The value of the action `a` at position `vals.length` of `S` under `V`, given the values
`vals` of the earlier positions: a write of transaction `t` is the function of its step index
in `t` applied to the values `t` read earlier; a read takes the value of the write `V` assigns,
or the original value. -/
def stepValue (S : Schedule) (V : ℕ → Option ℕ) (vals : List Value) (a : ℕ × ℕ × Bool) :
    Value :=
  if a.2.2 then
    .app a.1 ((S.take vals.length).filter fun b => b.1 == a.1).length
      (((List.range vals.length).filter fun q =>
        (action S q).1 == a.1 && !(action S q).2.2).map fun q => vals.getD q (.init 0))
  else
    match V vals.length with
    | none => .init a.2.1
    | some q => vals.getD q (.init a.2.1)

/-- The values of all positions of `S` under `V`, computed left to right. -/
def values (S : Schedule) (V : ℕ → Option ℕ) : List Value :=
  S.foldl (fun vals a => vals ++ [stepValue S V vals a]) []

/-- The final value of `x` under `V`: the value of the last write of `x`, or the original value
when `x` is never written. -/
def finalValue (S : Schedule) (V : ℕ → Option ℕ) (x : ℕ) : Value :=
  match ((List.range S.length).filter fun q =>
      (action S q).2.2 && (action S q).2.1 == x).getLast? with
  | none => .init x
  | some q => (values S V).getD q (.init x)

/-- The serial schedule running the transactions in the order `π`, each with its actions in
their order in `S`. -/
def serial (S : Schedule) (π : List ℕ) : Schedule :=
  π.flatMap fun t => S.filter fun a => a.1 == t

/-- Some interpretation of `S` leaves the same final values as the standard interpretation of
some serial schedule of the same transactions. -/
def MultiversionSerializabilityFeasible (i : MultiversionSerializabilityInstance) : Prop :=
  ∃ V : ℕ → Option ℕ, IsInterpretation i.2 V ∧ ∃ π : List ℕ, π.Perm (List.range i.1) ∧
    ∀ x : ℕ, finalValue i.2 V x = finalValue (serial i.2 π) (standard (serial i.2 π)) x

open Classical in
/-- MULTIVERSION SERIALIZABILITY as a decision problem over bitstrings. -/
noncomputable def multiversionSerializabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MultiversionSerializabilityInstance) x with
  | some i => decide (WellFormed i ∧ MultiversionSerializabilityFeasible i)
  | none => false

/-- **MULTIVERSION SERIALIZABILITY is NP-complete.** Source: Johnson (1983), problem [5];
Papadimitriou and Kanellakis (1982, 1984). -/
public theorem_wanted multiversionSerializability_npComplete :
    multiversionSerializabilityDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L multiversionSerializabilityDec

end MetaMathlibExt.Complexity.NPComplete.MultiversionSerializability
