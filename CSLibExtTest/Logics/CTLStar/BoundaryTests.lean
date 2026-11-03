/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Logics.CTLStar.Basic
import CSLibExt.Logics.CTLStar.Boundary

/-!
# Counterexamples to dropping Serial from the CTL embedding

All systems here use the same canonical `Cslib.LTS`. Maximal-path CTL
and infinite-run CTL* disagree at deadlocks, independently of valuation
or labeling choices. These are semantic-boundary tests, not a claim
that CTL cannot express a particular CTL* property.
-/

@[expose] public section

namespace Cslib.CTLStar.Tests

/-- A one-state canonical LTS with no transitions. -/
def deadlockLTS : LTS Unit Unit where
  Tr := fun _ _ _ => False

/-- At deadlock, infinite-run `AF false` is vacuous while maximal-path
CTL's `AF false` fails on the length-zero maximal path. -/
theorem deadlock_af_counterexample :
    StateSat deadlockLTS (fun (_ : Unit) (_ : Unit) => False)
        (embedCTL (.forallUntil .top (.atom ()))) () ∧
      ¬CTL.Satisfies deadlockLTS (fun (_ : Unit) (_ : Unit) => False)
        () (.forallUntil .top (.atom ())) := by
  constructor
  · exact stateSat_forall_of_terminal (fun _ _ h => h)
  · rw [CTL.Satisfies.forallUntil_deadlock (fun _ _ h => h)]
    exact id

/-- CTL's zero-step `EF true` needs no transition, but its CTL*
embedding still requires an infinite path and therefore fails here. -/
theorem deadlock_ef_counterexample :
    CTL.Satisfies deadlockLTS (fun (_ : Unit) (_ : Unit) => True)
        () (.existsUntil .top (.atom ())) ∧
      ¬StateSat deadlockLTS (fun (_ : Unit) (_ : Unit) => True)
        (embedCTL (.existsUntil .top (.atom ()))) () := by
  constructor
  · exact ⟨fun _ => (), 0, rfl, LTS.finiteRun_zero, trivial,
      fun _ _ => trivial⟩
  · exact not_stateSat_exists_of_terminal (fun _ _ h => h)

/-- The countermodel is nonserial; there is no hidden inconsistent
hypothesis behind the disagreement tests. -/
example : ¬CTL.Serial deadlockLTS := by
  rintro h
  obtain ⟨label, t, hstep⟩ := h ()
  exact hstep

/-- Even on the deadlock system, structural LTL agreement is
unconditional on arbitrary sequences and arbitrary positions. -/
example (φ : LTL.Formula Unit) (run : ℕ → Unit) (k : ℕ) :
    PathSat deadlockLTS (fun (_ : Unit) (_ : Unit) => False)
        (embedLTL φ) (Semantics.shiftSeq run k) ↔
      LTL.Word.SatisfiesAt (fun (_ : Unit) (_ : Unit) => False)
        ⟨run⟩ k φ :=
  embedLTL_sat_at φ run k

/-- A canonical system with one transition from `false` to the
terminal state `true`. -/
def oneStepLTS : LTS Bool Unit where
  Tr := fun s _ t => s = false ∧ t = true

/-- A valid one-step CTL witness can end at deadlock and fail to extend
to the infinite run demanded by the CTL* embedding. -/
theorem terminating_ex_counterexample :
    CTL.Satisfies oneStepLTS (fun (_ : Bool) (_ : Unit) => True)
        false (.existsNext .top) ∧
      ¬StateSat oneStepLTS (fun (_ : Bool) (_ : Unit) => True)
        (embedCTL (.existsNext .top)) false := by
  constructor
  · exact ⟨(), true, ⟨rfl, rfl⟩, trivial⟩
  · rintro ⟨run, _, hrun, _⟩
    obtain ⟨_, hfirst⟩ := hrun 0
    obtain ⟨_, hsecond⟩ := hrun 1
    have htf : (true : Bool) = false :=
      hfirst.2.symm.trans hsecond.1
    cases htf

end Cslib.CTLStar.Tests
