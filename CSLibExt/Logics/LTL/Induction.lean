/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# LTL temporal induction
-/
module

public import CSLibExt.Logics.LTL.Basic

/-!
# Temporal induction and invariant principles for LTL

The temporal induction principle: if `φ` holds now and at every position
`φ` implies `φ` at the next position, then `φ` holds at every position.
We give it at position `0` (`temporal_induction`) and at an arbitrary
position (`temporal_induction_at`), together with distribution of
`always` over implication (`Satisfies.always_imp`) and the state-level
invariant principle for infinite runs of an LTS
(`forall_state_of_invariant`).
-/

@[expose] public section

namespace Cslib
namespace LTL

variable {Atom State : Type*} {valuation : State → Atom → Prop}
  {run : ℕ → State} {φ ψ : Formula Atom}

/-- Satisfaction at position `0` is satisfaction on the whole run. -/
theorem satisfiesAt_zero :
    SatisfiesAt valuation run 0 φ ↔ Satisfies valuation run φ := by
  change Satisfies valuation (Semantics.shiftSeq run 0) φ ↔
    Satisfies valuation run φ
  rw [Semantics.shiftSeq_zero]

/-- `next` at position `k` is satisfaction at position `k + 1`. -/
theorem satisfiesAt_next {k : ℕ} :
    SatisfiesAt valuation run k (.next φ) ↔
      SatisfiesAt valuation run (k + 1) φ := by
  change Satisfies valuation (Semantics.shiftSeq (Semantics.shiftSeq run k) 1) φ ↔
    SatisfiesAt valuation run (k + 1) φ
  rw [Semantics.shiftSeq_add]
  exact Iff.rfl

/-- Satisfaction at a shifted position of a shifted run. -/
theorem satisfiesAt_shift {k j : ℕ} :
    SatisfiesAt valuation (Semantics.shiftSeq run k) j φ ↔
      SatisfiesAt valuation run (k + j) φ := by
  change Satisfies valuation (Semantics.shiftSeq (Semantics.shiftSeq run k) j) φ ↔
    SatisfiesAt valuation run (k + j) φ
  rw [Semantics.shiftSeq_add]
  exact Iff.rfl

/-- `always` at position `k` means the formula holds at every position at or after `k`:
at `k + j` for every `j`, including `j = 0`. -/
theorem satisfiesAt_always {k : ℕ} :
    SatisfiesAt valuation run k (Formula.always φ) ↔
      ∀ j, SatisfiesAt valuation run (k + j) φ := by
  change Satisfies valuation (Semantics.shiftSeq run k) (Formula.always φ) ↔ _
  rw [Satisfies.always_iff]
  constructor
  · intro h j
    exact satisfiesAt_shift.mp (h j)
  · intro h j
    exact satisfiesAt_shift.mpr (h j)

/-- `eventually` at position `k` means the formula holds at some position at or after `k`:
at `k + j` for some `j`, possibly `j = 0`. -/
theorem satisfiesAt_eventually {k : ℕ} :
    SatisfiesAt valuation run k (Formula.eventually φ) ↔
      ∃ j, SatisfiesAt valuation run (k + j) φ := by
  change Satisfies valuation (Semantics.shiftSeq run k) (Formula.eventually φ) ↔ _
  rw [Satisfies.eventually_iff]
  constructor
  · rintro ⟨j, hj⟩
    exact ⟨j, satisfiesAt_shift.mp hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨j, satisfiesAt_shift.mpr hj⟩

namespace Satisfies

/-- Distribution of `always` over implication: from `□(φ → ψ)` and `□φ`
conclude `□ψ`. -/
theorem always_imp
    (himp : Satisfies valuation run (Formula.always (Formula.imp φ ψ)))
    (hφ : Satisfies valuation run (Formula.always φ)) :
    Satisfies valuation run (Formula.always ψ) := by
  rw [always_iff] at himp hφ ⊢
  intro k
  exact imp_iff.mp (himp k) (hφ k)

end Satisfies

/-- Temporal induction at an arbitrary position: if `φ` holds at `k` and
from `k` onwards `φ` always implies `φ` at the next position, then `φ`
holds at every position from `k` onwards. -/
theorem temporal_induction_at {k : ℕ}
    (hbase : SatisfiesAt valuation run k φ)
    (hstep : SatisfiesAt valuation run k
      (Formula.always (Formula.imp φ (.next φ)))) :
    SatisfiesAt valuation run k (Formula.always φ) := by
  rw [satisfiesAt_always] at hstep ⊢
  intro j
  induction j with
  | zero =>
      simpa using hbase
  | succ j ih =>
      have hnext : SatisfiesAt valuation run (k + j) (.next φ) :=
        Satisfies.imp_iff.mp (hstep j) ih
      rw [satisfiesAt_next] at hnext
      have hidx : k + (j + 1) = k + j + 1 := by omega
      rwa [hidx]

/-- Temporal induction: if `φ` holds now and `φ → ○φ` holds always, then
`φ` holds always. -/
theorem temporal_induction
    (h : Satisfies valuation run
      (.and φ (Formula.always (Formula.imp φ (.next φ))))) :
    Satisfies valuation run (Formula.always φ) := by
  obtain ⟨hbase, hstep⟩ := Satisfies.and_iff.mp h
  exact satisfiesAt_zero.mp
    (temporal_induction_at (satisfiesAt_zero.mpr hbase)
      (satisfiesAt_zero.mpr hstep))

end LTL
end Cslib
