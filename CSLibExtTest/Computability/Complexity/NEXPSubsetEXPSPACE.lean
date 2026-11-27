/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Complexity.NEXPSubsetEXPSPACE

/-!
# Tests for the nondeterministic exponential-time simulation

On a leading true bit the test machine can halt with either output. On a blank or false bit it
has no transition. Existential acceptance must include the first case and reject the stuck cases.
-/

namespace MetaMathlibExt.Complexity.KeyTheorems.NEXPSubsetEXPSPACE.Tests

open Turing Cslib.Complexity.Classes

private def haltWith (b : Bool) : Action 0 Bool Unit :=
  ⟨0, Fin.elim0, some b, none⟩

private def branch : MultiTapeNTM 0 Bool Unit where
  q₀ := ()
  Tr _ s _ a := s = some true ∧ ∃ b, a = haltWith b

private def firstBit (w : List Bool) := w.head?.getD false

private theorem firstBit_eq (w : List Bool) :
    firstBit w = true ↔ (branch.initCfg w).inputSymbol = some true := by
  cases w with
  | nil => decide
  | cons b bs =>
    simp [firstBit]

private theorem path_cases {w : List Bool} (p : branch.RunPath w) (hq : p.head.state = some ()) :
    (p.length = 0 ∧ ¬ p.last.Halted) ∨ (p.last.Halted ∧ p.head.inputSymbol = some true) := by
  induction p using RelSeries.inductionOn with
  | singleton c => exact Or.inl ⟨rfl, fun h => by cases h.symm.trans hq⟩
  | cons p x h _ =>
    have hx : x.state = some () := hq
    obtain ⟨a, ha, he⟩ := (show ∃ a, branch.Tr () _ _ a ∧ p.head = a.apply x by
      simpa [MultiTapeNTM.Step, hx] using (show branch.Step x p.head from h))
    obtain ⟨hs, b, rfl⟩ := ha
    have hh : p.head.Halted := he ▸ rfl
    have heq := MultiTapeNTM.RunPath.last_eq_of_head_halted (ntm := branch) p hh
    exact Or.inr ⟨by simpa only [RelSeries.last_cons, heq] using hh, by simpa using hs⟩

private theorem firstBit_mem : firstBit ∈ NEXP := by
  refine ⟨0, 0, 1, 0, Unit, inferInstance, branch, ?_, ?_⟩
  · intro w p ht
    rcases path_cases p.toRunPath (p.head_eq ▸ rfl) with ⟨h, _⟩ | ⟨h, _⟩
    · change 0 * _ + 1 ≤ p.length at ht
      omega
    · exact h
  · intro w
    change firstBit w = true ↔ _
    rw [firstBit_eq]
    constructor
    · intro h
      let c := branch.initCfg w
      have hs : branch.Step c ((haltWith true).apply c) := ⟨haltWith true, ⟨h, true, rfl⟩, rfl⟩
      let path := RelSeries.singleton (branch.stepRel w) c
      let p : branch.ComputationPath w := ⟨path.snoc _ hs, by simp [path, c]⟩
      have he : p.last = (haltWith true).apply c := RelSeries.last_snoc path _ hs
      exact ⟨p, he ▸ rfl, he ▸ rfl⟩
    · rintro ⟨p, hh, _⟩
      rcases path_cases p.toRunPath (p.head_eq ▸ rfl) with ⟨_, h⟩ | ⟨_, h⟩
      · exact (h hh).elim
      · rwa [p.head_eq] at h

-- One deterministic witness must decide both the branching and stuck inputs.
example : ∃ (k : ℕ) (S : Type) (_ : Finite S) (tm : MultiTapeTM k Bool S),
    tm.Computes [true] [true] ∧ tm.Computes [false] [false] ∧ tm.Computes [] [false] := by
  obtain ⟨_, h⟩ := nexp_subset_expspace firstBit_mem
  obtain ⟨_, _, k, S, hS, tm, hd, _, _⟩ := Cslib.Turing.MultiTapeTM.mem_DSPACE_iff.mp h
  refine ⟨k, S, hS, tm, ?_, ?_, ?_⟩
  · simpa [MultiTapeTM.indicator, langOf, firstBit] using hd [true]
  · simpa [MultiTapeTM.indicator, langOf, firstBit] using hd [false]
  · simpa [MultiTapeTM.indicator, langOf, firstBit] using hd []

end MetaMathlibExt.Complexity.KeyTheorems.NEXPSubsetEXPSPACE.Tests
