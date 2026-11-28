/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STRICT SERIALIZABILITY: definitions

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", Journal of Algorithms 4 (1983),
286-300, doi:10.1016/0196-6774(83)90028-7, problem [4] STRICT SERIALIZABILITY (reference:
Sethi; transformation from 3SAT);
R. Sethi, "Useless actions make a difference: strict serializability of database updates",
Journal of the ACM 29 (1982), 394-403, doi:10.1145/322307.322314.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MultiversionSerializabilityDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StrictSerializability

open MetaMathlibExt.Complexity.NPComplete.MultiversionSerializability
  (Schedule standard finalValue serial)

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

end MetaMathlibExt.Complexity.NPComplete.StrictSerializability
