/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.TuringMachine.Recursive.Halts

@[expose] public section

/-!
# Tests for halting sets of multi-stack machines

A machine that halts at once and a machine that loops forever, their halting sets, and an
r.e. predicate realized as a halting set.
-/

set_option autoImplicit false

open Computability Turing MetaMathlibExt.TM2Recursive

namespace MathlibExtTest.Computability.TuringMachine.Recursive.Halts

/-- One stack of bits; the program is a single label running `prog`. -/
def oneLabelTM (prog : TM2.Stmt (fun _ : Unit ↦ Bool) Unit Unit) : FinTM2 where
  K := Unit
  k₀ := ()
  k₁ := ()
  Γ := fun _ ↦ Bool
  Λ := Unit
  main := ()
  σ := Unit
  initialState := ()
  m := fun _ ↦ prog

/-- The machine that halts at once halts on every input. -/
example (l : List Bool) : TM2HaltsOn (oneLabelTM .halt) l :=
  dom_eval_iff_exists_iterate.mpr ⟨1, _, rfl, rfl⟩

/-- The machine that jumps back to its only label halts on no input. -/
example (l : List Bool) : ¬TM2HaltsOn (oneLabelTM (.goto fun _ ↦ ())) l := by
  intro h
  obtain ⟨k, b, hk, hb⟩ := dom_eval_iff_exists_iterate.mp h
  have hfix : ∀ j, (flip bind (oneLabelTM (.goto fun _ ↦ ())).step)^[j]
      (some (initList (oneLabelTM (.goto fun _ ↦ ())) l)) =
        some (initList (oneLabelTM (.goto fun _ ↦ ())) l) := fun j ↦ by
    induction j with
    | zero => rfl
    | succ j ih => rw [Function.iterate_succ_apply', ih]; rfl
  rw [hfix k] at hk
  obtain rfl := Option.some.inj hk
  cases hb

/-- Halting sets are r.e. -/
example : REPred fun n ↦ TM2HaltsOn (oneLabelTM .halt) ((encodeNat n).map (Equiv.refl Bool).symm) :=
  rePred_tm2HaltsOn (oneLabelTM .halt) (Equiv.refl Bool)

/-- The even numbers are the halting set of some multi-stack machine (`FinTM2`). -/
example : ∃ (tm : FinTM2) (e : tm.Γ tm.k₀ ≃ Bool),
    ∀ n, Even n ↔ TM2HaltsOn tm ((encodeNat n).map e.symm) := by
  refine exists_tm2HaltsOn_iff_of_rePred (ComputablePred.to_re ?_)
  refine ComputablePred.computable_iff.mpr ⟨fun n ↦ n % 2 == 0, ?_, ?_⟩
  · exact (Primrec.beq.comp (Primrec.nat_mod.comp Primrec.id (Primrec.const 2))
      (Primrec.const 0)).to_comp
  · funext n
    simp [Nat.even_iff]

end MathlibExtTest.Computability.TuringMachine.Recursive.Halts
