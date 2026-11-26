/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Finset.Option

/-!
# k-set agreement

An outcome records an input and at most one decision for each process, and identifies the
correct processes. Over a finite population, `Outcome.IsKSetAgreement` requires validity and
at most `k` distinct values among **all** recorded decisions, and a decision from every correct
process. The last condition concerns completed outcomes, not progress of a protocol.

## References

* S. Chaudhuri, *More choices allow more faults: set consensus problems in totally asynchronous
  systems*, Information and Computation 105(1):132–158, 1993.
* J. Aspnes, *Notes on Theory of Distributed Systems*, 2020, <https://arxiv.org/abs/2001.04235>.
-/

@[expose] public section

namespace Cslib.Distributed.KSetAgreement

/-- An outcome on processes `P` with values in `V`, without an execution or fault model. -/
structure Outcome (P V : Type*) where
  /-- The input of every process, whether correct or not. -/
  input : P → V
  /-- The recorded decision of each process, or `none` if it did not decide. -/
  decision : P → Option V
  /-- The processes required to decide in a completed outcome. -/
  correct : P → Prop

namespace Outcome

variable {P V : Type*} (o : Outcome P V)

/-- Every recorded decision is an input of some process. Neither the deciding process nor the
process supplying the input is required to be correct. -/
def Valid : Prop :=
  ∀ (p : P) (v : V), o.decision p = some v → ∃ q, o.input q = v

/-- In a completed outcome, every correct process has a recorded decision. -/
def Terminates : Prop :=
  ∀ p, o.correct p → ∃ v, o.decision p = some v

variable [Fintype P] [DecidableEq V]

/-- The finite set of distinct recorded decision values. Absent decisions are omitted, and
recorded decisions are included regardless of the deciding process's correctness. -/
def decidedValues : Finset V :=
  (Finset.univ.image o.decision).eraseNone

/-- A value belongs to the set of recorded decision values exactly when some process decided it. -/
@[simp] lemma mem_decidedValues {v : V} : v ∈ o.decidedValues ↔ ∃ p, o.decision p = some v := by
  simp [decidedValues, Finset.mem_image]

/-- At most `k` distinct values are recorded as decisions. In particular, `k = 0` allows only
outcomes with no recorded decisions. -/
def Agrees (k : ℕ) : Prop :=
  o.decidedValues.card ≤ k

/-- A completed `k`-set agreement outcome is valid, records at most `k` distinct decision values,
and records a decision for each correct process. At `k = 0` this requires no recorded decisions
and no correct processes. -/
def IsKSetAgreement (k : ℕ) : Prop :=
  o.Valid ∧ o.Agrees k ∧ o.Terminates

/-- At `k = 1`, the cardinality bound is equivalent to pairwise equality of all recorded
decision values, with the same validity and termination requirements. -/
lemma isKSetAgreement_one_iff :
    o.IsKSetAgreement 1 ↔
      o.Valid ∧
        (∀ (p q : P) (v w : V), o.decision p = some v → o.decision q = some w → v = w) ∧
        o.Terminates := by
  have h : o.Agrees 1 ↔
      ∀ (p q : P) (v w : V), o.decision p = some v → o.decision q = some w → v = w := by
    rw [Agrees, Finset.card_le_one]
    constructor
    · intro hagree p q v w hp hq
      exact hagree v (o.mem_decidedValues.mpr ⟨p, hp⟩) w (o.mem_decidedValues.mpr ⟨q, hq⟩)
    · intro hagree v hv w hw
      obtain ⟨p, hp⟩ := o.mem_decidedValues.mp hv
      obtain ⟨q, hq⟩ := o.mem_decidedValues.mp hw
      exact hagree p q v w hp hq
  rw [IsKSetAgreement, h]

end Outcome

end Cslib.Distributed.KSetAgreement
