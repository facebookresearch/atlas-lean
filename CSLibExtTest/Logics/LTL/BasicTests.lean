/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.LTL.Basic

@[expose] public section

set_option autoImplicit false

namespace Cslib.LTL.BasicTests

/-- The natural-number counter: `n` steps to `n + 1` under the unit label. -/
def counter : _root_.Cslib.LTS ℕ Unit := ⟨fun n _ m => m = n + 1⟩

/-- The single atom holds at even states. -/
def evenVal : ℕ → Unit → Prop := fun n _ => ∃ r, n = r + r

example : Cslib.LTS.OmegaRun (lts := counter) (fun i => i) := fun _ => ⟨(), rfl⟩

example : Satisfies evenVal (fun i => i) (.atom ()) := ⟨0, rfl⟩

example : SatisfiesAt evenVal (fun i => i) 1 (.not (.atom ())) := by
  show ¬ ∃ r, (1 : ℕ) = r + r
  rintro ⟨r, hr⟩
  omega

example :
    Satisfies evenVal (fun i => i) (Formula.eventually (.atom ())) :=
  Satisfies.eventually_iff.mpr ⟨0, ⟨0, rfl⟩⟩

example :
    Satisfies evenVal (fun i => i)
      (Formula.eventually (.not (.atom ()))) := by
  refine Satisfies.eventually_iff.mpr ⟨1, ?_⟩
  show ¬ ∃ r, (1 : ℕ) = r + r
  rintro ⟨r, hr⟩
  omega

/-- From any position `k`, shifting by a further `k` reaches `2 * k`,
which is even. -/
example :
    Satisfies evenVal (fun i => i)
      (Formula.always (Formula.eventually (.atom ()))) := by
  rw [Satisfies.always_iff]
  intro k
  show Satisfies evenVal (Semantics.shiftSeq (fun i => i) k)
    (Formula.eventually (.atom ()))
  refine Satisfies.eventually_iff.mpr ⟨k, k, ?_⟩
  show (0 + k) + k = k + k
  omega

/-- At position `1` (odd), `¬ atom` holds until `atom` at position `2`,
proved by two applications of the expansion law. -/
example :
    SatisfiesAt evenVal (fun i => i) 1
      (.until (.not (.atom ())) (.atom ())) := by
  show Satisfies evenVal (Semantics.shiftSeq (fun i => i) 1)
    (.until (.not (.atom ())) (.atom ()))
  rw [Satisfies.until_expansion]
  right
  constructor
  · show ¬ ∃ r, (1 : ℕ) = r + r
    rintro ⟨r, hr⟩
    omega
  · show Satisfies evenVal
      (Semantics.shiftSeq (Semantics.shiftSeq (fun i => i) 1) 1)
      (.until (.not (.atom ())) (.atom ()))
    rw [Satisfies.until_expansion]
    left
    show ∃ r, (2 : ℕ) = r + r
    exact ⟨1, rfl⟩

example :
    ¬ Satisfies evenVal (fun i => i) (Formula.always (.atom ())) := by
  rw [Satisfies.always_iff]
  intro h
  have h1 : (∃ r, (1 : ℕ) = r + r) := h 1
  obtain ⟨r, hr⟩ := h1
  omega

example :
    ExistsRun counter evenVal 1 (Formula.eventually (.atom ())) := by
  refine ⟨fun i => i + 1, rfl, fun _ => ⟨(), rfl⟩, ?_⟩
  refine Satisfies.eventually_iff.mpr ⟨1, ?_⟩
  show ∃ r, (2 : ℕ) = r + r
  exact ⟨1, rfl⟩

/-- An LTS with no transitions at all. -/
def dead : _root_.Cslib.LTS ℕ Unit := ⟨fun _ _ _ => False⟩

/-- `ForallRuns` is vacuous at a deadlocked state: there is no infinite
run, so every formula, even `⊥`, holds on all runs. -/
example (φ : Formula Unit) (s : ℕ) : ForallRuns dead evenVal s φ := by
  intro _ _ hrun
  obtain ⟨_, hstep⟩ := hrun 0
  exact hstep.elim

#print axioms Cslib.LTL.Satisfies.until_expansion
#print axioms Cslib.LTL.Satisfies.always_iff

end Cslib.LTL.BasicTests
