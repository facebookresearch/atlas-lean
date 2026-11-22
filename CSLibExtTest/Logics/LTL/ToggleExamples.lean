/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.LTL.Basic

/-!
# Linear temporal logic: worked examples

Concrete usage of the LTL semantics in `CSLibExt/Logics/LTL/Basic.lean`.
The running example is the toggle system: states are Booleans, every
transition flips the state, and the atom `p` holds exactly at `true`.

On every infinite run of the toggle system, `p` occurs infinitely often
(`G F p`), but `p` does not hold always (`¬ G p`), and `p` occurs at
least once (`F p`). The proofs use only the unfolding lemmas
`Satisfies.eventually_iff` and `Satisfies.always_iff`.
-/

@[expose] public section

namespace Cslib
namespace LTL
namespace Examples

/-- The toggle system: every transition flips the state. -/
def toggleLTS : _root_.Cslib.LTS Bool Unit where
  Tr := fun s _ t => t = !s

/-- The valuation: `p` holds exactly at `true`. -/
def toggleValuation : Bool → Unit → Prop := fun s _ => s = true

/-- On any infinite run of the toggle system, `p` occurs at least once:
either at position `0`, or at position `1`, which is `!ss 0`. -/
theorem toggle_eventually_atom {ss : ℕ → Bool}
    (hrun : Cslib.LTS.OmegaRun (lts := toggleLTS) ss) :
    Satisfies toggleValuation ss (Formula.eventually (.atom ())) := by
  rw [Satisfies.eventually_iff]
  obtain ⟨_, hstep⟩ := hrun 0
  cases h0 : ss 0 with
  | false =>
      refine ⟨1, ?_⟩
      show toggleValuation (ss 1) ()
      rw [hstep, h0]
      rfl
  | true =>
      refine ⟨0, ?_⟩
      show toggleValuation (ss 0) ()
      rw [h0]
      rfl

/-- On any infinite run of the toggle system, `p` occurs infinitely
often: shift the run and apply `toggle_eventually_atom` at every
position. -/
theorem toggle_always_eventually_atom {ss : ℕ → Bool}
    (hrun : Cslib.LTS.OmegaRun (lts := toggleLTS) ss) :
    Satisfies toggleValuation ss
      (Formula.always (Formula.eventually (.atom ()))) := by
  rw [Satisfies.always_iff]
  intro k
  exact toggle_eventually_atom (Cslib.LTS.omegaRun_shift hrun k)

/-- `p` does not hold always on a run starting at `false`: at position
`2` the state is back to `false`. -/
theorem toggle_not_always_atom {ss : ℕ → Bool} (h0 : ss 0 = false)
    (hrun : Cslib.LTS.OmegaRun (lts := toggleLTS) ss) :
    ¬ Satisfies toggleValuation ss (Formula.always (.atom ())) := by
  rw [Satisfies.always_iff]
  intro hall
  have h1 : ss 1 = true := by
    obtain ⟨_, hstep⟩ := hrun 0
    rw [hstep, h0]
    rfl
  have h2 : ss 2 = false := by
    obtain ⟨_, hstep⟩ := hrun 1
    rw [hstep, h1]
    rfl
  have hat := Satisfies.atomAt_iff.mp (hall 2)
  rw [h2] at hat
  exact Bool.false_ne_true hat

end Examples
end LTL
end Cslib
