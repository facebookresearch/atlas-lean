/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Logics.CTLStar.UpstreamBridge

/-!
# CTL* port consumers

Concrete serial-system checks exercise the reused CTL embedding, nested
path quantification, strong-until boundaries, and the canonical labeled
execution adapter. The EGF toggle example is not an expressiveness
separation.
-/

@[expose] public section

namespace Cslib.CTLStar.Tests

/-- The next toggle state satisfies `p`, transferred from CTL to CTL*. -/
theorem toggle_ex_p :
    StateSat toggleLTS toggleValuation
      (embedCTL (.existsNext (.atom ()))) false := by
  apply (embedCTL_sat toggle_serial _).mpr
  exact ⟨(), true, rfl, rfl⟩

/-- A guarded one-step `EU` witness transfers to infinite-run CTL*. -/
theorem toggle_eu_p :
    StateSat toggleLTS toggleValuation
      (embedCTL (.existsUntil (.not (.atom ())) (.atom ()))) false := by
  apply (embedCTL_sat toggle_serial _).mpr
  refine ⟨toggleRun, 1, rfl, ?_, rfl, ?_⟩
  · intro i _
    exact ⟨(), rfl⟩
  · intro j hj
    have hj0 : j = 0 := by omega
    subst hj0
    exact Bool.noConfusion

/-- The alternating infinite run witnesses `EG true` through the CTL
embedding, and the execution bridge transfers that same state claim. -/
theorem toggle_eg_top :
    UpstreamStateSat toggleLTS toggleValuation
      (embedCTL (.existsGlobally .top)) false := by
  apply (stateSat_iff_upstream _ _).mp
  apply (embedCTL_sat toggle_serial _).mpr
  exact ⟨toggleRun, rfl, fun _ => ⟨(), rfl⟩, fun _ => trivial⟩

/-- Every infinite toggle path reaches `p` at position one; seriality
rules out the finite deadlocked paths in CTL's `AU` semantics. -/
theorem toggle_au_p :
    StateSat toggleLTS toggleValuation
      (embedCTL (.forallUntil .top (.atom ()))) false := by
  apply (embedCTL_sat toggle_serial _).mpr
  constructor
  · intro run h0 hrun
    refine ⟨1, ?_, fun _ _ => trivial⟩
    obtain ⟨_, hstep⟩ := hrun 0
    change run 1 = !run 0 at hstep
    rw [h0] at hstep
    exact hstep
  · intro run k _ _ hdead
    obtain ⟨label, t, hstep⟩ := toggle_serial (run k)
    exact (hdead label t hstep).elim

/-- After every first toggle step, there exists another path whose
next state satisfies `not p`: genuine nesting of `A`, `X`, and `E`. -/
theorem toggle_nested_quantifiers :
    StateSat toggleLTS toggleValuation
      (.forall (.next (.state
        (.exists (.next (.state (.not (.atom ())))))))) false := by
  intro run h0 hrun
  rw [pathSat_next, pathSat_state_shift]
  refine ⟨Semantics.shiftSeq toggleRun 1, ?_,
    LTS.omegaRun_shift (fun _ => ⟨(), rfl⟩) 1, ?_⟩
  · change true = run 1
    obtain ⟨_, hstep⟩ := hrun 0
    change run 1 = !run 0 at hstep
    rw [h0] at hstep
    exact hstep.symm
  · rw [pathSat_next, pathSat_state_shift]
    exact Bool.noConfusion

/-- Strong until permits fulfillment at position zero even when its
left guard is false there. -/
example : PathSat toggleLTS toggleValuation
    (.until (.not (.state .top)) (.state .top)) toggleRun := by
  exact ⟨0, trivial, fun j hj => (Nat.not_lt_zero j hj).elim⟩

/-- An infinite constant sequence with `p` always false never satisfies
strong until, even though the left guard is always true. -/
example : ¬PathSat toggleLTS toggleValuation
    (.until (.state .top) (.state (.atom ()))) (fun _ => false) := by
  rintro ⟨_, htarget, _⟩
  exact Bool.noConfusion htarget

/-- A concrete nonzero-position LTL consumer: after the first toggle
state, the next position satisfies `not p`. -/
example : LTL.Word.SatisfiesAt toggleValuation ⟨toggleRun⟩ 1
    (.next (.not (.atom ()))) := by
  apply (embedLTL_sat_at (lts := toggleLTS) _ toggleRun 1).mp
  exact Bool.noConfusion

/-- Nested path quantifiers retain the same meaning over labeled executions. -/
example : UpstreamStateSat toggleLTS toggleValuation
    (.forall (.next (.state
      (.exists (.next (.state (.not (.atom ())))))))) false :=
  (stateSat_iff_upstream _ _).mp toggle_nested_quantifiers

/-- The toggle satisfies `G F p` but not `F G p`: it never stays at
`p` forever. This compares two formulas on one model, not expressiveness. -/
theorem toggle_not_fg_p :
    ¬PathSat toggleLTS toggleValuation
      (.eventuallyPath (.alwaysPath (.state (.atom ())))) toggleRun := by
  rw [pathSat_eventually]
  rintro ⟨k, hglobal⟩
  rw [pathSat_always] at hglobal
  cases hk : toggleRun k with
  | false =>
      have h := hglobal 0
      rw [pathSat_state, Semantics.shiftSeq_add,
        shiftSeq_apply_zero, Nat.add_zero] at h
      exact Bool.noConfusion (hk.symm.trans h)
  | true =>
      have h := hglobal 1
      rw [pathSat_state, Semantics.shiftSeq_add, shiftSeq_apply_zero] at h
      change !toggleRun k = true at h
      rw [hk] at h
      exact Bool.noConfusion h

end Cslib.CTLStar.Tests
