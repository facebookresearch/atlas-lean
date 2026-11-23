/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.CTL.Basic

/-!
# Computation tree logic: worked examples

Concrete usage of the CTL semantics in `CSLibExt/Logics/CTL/Basic.lean`,
on the same toggle system as `CSLibExtTest/Logics/LTL/ToggleExamples.lean`: states
are Booleans, every transition flips the state, and `p` holds at `true`.

On this serial system, `EF p` holds at every state (from `false` in one
step), `AF p` holds at `false` (every path reaches `true` within one
step), `AG EF p` holds at `false`, and `EG p` fails at every state
(every infinite run leaves `true`). The `AF` proof is the maximal-path
argument: the infinite-run part uses the one-step reachability, and the
finite-run part is vacuous because the system is serial.
-/

@[expose] public section

namespace Cslib
namespace CTL
namespace Examples

/-- The toggle system: every transition flips the state. -/
def toggleLTS : _root_.Cslib.LTS Bool Unit where
  Tr := fun s _ t => t = !s

/-- The valuation: `p` holds exactly at `true`. -/
def toggleValuation : Bool → Unit → Prop := fun s _ => s = true

/-- The run that witnesses one step of the toggle system from `false`:
`false, true, true, ...`. -/
def runFromFalse : ℕ → Bool := fun n => match n with | 0 => false | _ => true

/-- `runFromFalse` is a finite run of length `1`: the only required step
is `false → true`. -/
theorem runFromFalse_finite : Cslib.LTS.FiniteRun (lts := toggleLTS) runFromFalse 1 := by
  intro i hi
  have hi0 : i = 0 := by omega
  subst hi0
  exact ⟨(), rfl⟩

/-- `EF p` holds at `false`: `true` is reached in one step. -/
theorem toggle_ef_atom_false :
    Satisfies toggleLTS toggleValuation false
      (Formula.existsFinally (.atom ())) := by
  refine ⟨runFromFalse, 1, rfl, runFromFalse_finite, ?_, fun _ _ => True.intro⟩
  rfl

/-- `EF p` holds at `true`: `true` itself satisfies `p`. -/
theorem toggle_ef_atom_true :
    Satisfies toggleLTS toggleValuation true
      (Formula.existsFinally (.atom ())) := by
  refine ⟨fun _ => true, 0, rfl, ?_, ?_, fun _ _ => True.intro⟩
  · intro i hi
    exact (Nat.not_lt_zero i hi).elim
  · rfl

/-- `EF p` holds at every state of the toggle system. -/
theorem toggle_ef_atom (s : Bool) :
    Satisfies toggleLTS toggleValuation s
      (Formula.existsFinally (.atom ())) := by
  cases s with
  | false => exact toggle_ef_atom_false
  | true => exact toggle_ef_atom_true

/-- `AF p` holds at `false`: on every infinite run, position `1` is
`true`; finite runs cannot deadlock because the system is serial. -/
theorem toggle_af_atom_false :
    Satisfies toggleLTS toggleValuation false
      (Formula.forallFinally (.atom ())) := by
  refine ⟨?_, ?_⟩
  · intro ss h0 hrun
    obtain ⟨_, hstep⟩ := hrun 0
    refine ⟨1, ?_, fun j hj => trivial⟩
    show toggleValuation (ss 1) ()
    rw [hstep, h0]
    rfl
  · intro ss k _ _ hdead
    exact absurd rfl (hdead () (!ss k))

/-- `EG p` fails at `false`: the run from `false` is at `false` again
at position `2`. -/
theorem toggle_not_eg_atom_false :
    ¬ Satisfies toggleLTS toggleValuation false
      (Formula.existsGlobally (.atom ())) := by
  rintro ⟨ss, h0, hrun, hall⟩
  have h1 : ss 1 = true := by
    obtain ⟨_, hstep⟩ := hrun 0
    rw [hstep, h0]
    rfl
  have h2 : ss 2 = false := by
    obtain ⟨_, hstep⟩ := hrun 1
    rw [hstep, h1]
    rfl
  have hat := hall 2
  rw [h2] at hat
  exact Bool.false_ne_true hat

/-- `AG EF p` holds at `false`: every reachable state satisfies `EF p`,
since `EF p` holds everywhere. -/
theorem toggle_ag_ef_atom_false :
    Satisfies toggleLTS toggleValuation false
      (Formula.forallGlobally (Formula.existsFinally (.atom ()))) := by
  intro hcontra
  obtain ⟨ss, k, h0, _, hsat, -⟩ := hcontra
  exact hsat (toggle_ef_atom (ss k))

end Examples
end CTL
end Cslib
