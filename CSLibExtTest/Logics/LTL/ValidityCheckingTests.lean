/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.LTL.ValidityChecking
public meta import CSLibExt.Logics.LTL.ValidityChecking

namespace Cslib.LTL.ValidityCheckingTests

open Cslib.LTL.ModelChecking

/-- Test atom over `Fin 1`. -/
def p1 : Formula (Fin 1) := .atom 0

#print axioms p1

/-- (i) A contradiction is unsatisfiable. -/
theorem sat_and_not_self_eq_false :
    satisfiableB (.and p1 (.not p1)) = false := by
  have hne : ¬ (satisfiableB (.and p1 (.not p1)) = true) := by
    rw [satisfiableB_iff]
    rintro ⟨W, hW⟩
    have hcon :
        Word.Satisfies (fun s a => a ∈ s) W p1 ∧
          ¬ Word.Satisfies (fun s a => a ∈ s) W p1 := hW
    exact hcon.2 hcon.1
  have hb : ∀ b : Bool, ¬ (b = true) → b = false := by
    intro b h
    cases b <;> simp_all
  exact hb _ hne

#print axioms sat_and_not_self_eq_false

/-- (ii) Always-p is satisfiable. -/
theorem sat_always_eq_true :
    satisfiableB (Formula.always p1) = true := by
  rw [satisfiableB_iff]
  refine ⟨ωSequence.const Set.univ, ?_⟩
  intro hEx
  obtain ⟨k, hnot, _⟩ := hEx
  exact hnot (Set.mem_univ _)

#print axioms sat_always_eq_true

/-- (iii) Excluded middle is valid. -/
theorem valid_or_not_self_eq_true :
    validityB (Formula.or p1 (.not p1)) = true := by
  rw [validityB_iff]
  intro W hCon
  obtain ⟨h1, h2⟩ := hCon
  exact h2 h1

#print axioms valid_or_not_self_eq_true

/-- (iv-a) A bare atom is not valid. -/
theorem valid_atom_eq_false : validityB p1 = false := by
  have hne : ¬ (validityB p1 = true) := by
    rw [validityB_iff]
    intro hAll
    have h0 := hAll (ωSequence.const ∅)
    exact Set.notMem_empty _ h0
  have hb : ∀ b : Bool, ¬ (b = true) → b = false := by
    intro b h
    cases b <;> simp_all
  exact hb _ hne

#print axioms valid_atom_eq_false

/-- (iv-b) A bare atom is satisfiable. -/
theorem sat_atom_eq_true : satisfiableB p1 = true := by
  rw [satisfiableB_iff]
  refine ⟨ωSequence.const Set.univ, ?_⟩
  simp only [p1, Word.Satisfies.atom_iff]
  exact Set.mem_univ _

#print axioms sat_atom_eq_true

#guard validityB (Atom := Empty) .top = true

/-- (v) Truth is valid over the empty alphabet. -/
theorem valid_top_empty_eq_true :
    validityB (Atom := Empty) .top = true := by
  rw [validityB_iff]
  intro W
  trivial

#print axioms valid_top_empty_eq_true

/-- (vi) Falsity is unsatisfiable over the empty alphabet. -/
theorem sat_bot_empty_eq_false :
    satisfiableB (Atom := Empty) Formula.bot = false := by
  have hne :
      ¬ (satisfiableB (Atom := Empty) Formula.bot = true) := by
    rw [satisfiableB_iff]
    rintro ⟨W, hW⟩
    simp only [Formula.bot, Word.Satisfies.not_iff] at hW
    exact hW trivial
  have hb : ∀ b : Bool, ¬ (b = true) → b = false := by
    intro b h
    cases b <;> simp_all
  exact hb _ hne

#print axioms sat_bot_empty_eq_false

/-- (vii) Next-truth is valid over the empty alphabet. -/
theorem valid_next_top_empty_eq_true :
    validityB (Atom := Empty) (.next .top) = true := by
  rw [validityB_iff]
  intro W
  trivial

#print axioms valid_next_top_empty_eq_true

/-- (viii) Until-truth-falsity is unsatisfiable over empty. -/
theorem sat_until_top_bot_empty_eq_false :
    satisfiableB (Atom := Empty)
        (.until .top Formula.bot) = false := by
  have hne :
      ¬ (satisfiableB (Atom := Empty)
        (.until .top Formula.bot) = true) := by
    rw [satisfiableB_iff]
    rintro ⟨W, hW⟩
    obtain ⟨k, hbot, _⟩ := hW
    exact hbot True.intro
  have hb : ∀ b : Bool, ¬ (b = true) → b = false := by
    intro b h
    cases b <;> simp_all
  exact hb _ hne

#print axioms sat_until_top_bot_empty_eq_false

#print axioms Cslib.LTL.ModelChecking.allValuations
#print axioms Cslib.LTL.ModelChecking.allValuationsTrDecidable
#print axioms Cslib.LTL.ModelChecking.allValuationsMemDecidable
#print axioms Cslib.LTL.ModelChecking.allValuationsValDecidable
#print axioms Cslib.LTL.ModelChecking.isRun_allValuations
#print axioms Cslib.LTL.ModelChecking.validityB
#print axioms Cslib.LTL.ModelChecking.satisfiableB
#print axioms Cslib.LTL.ModelChecking.toSet
#print axioms Cslib.LTL.ModelChecking.satisfies_toSet_iff
#print axioms Cslib.LTL.ModelChecking.exists_map_toSet_eq
#print axioms Cslib.LTL.ModelChecking.validityB_iff
#print axioms Cslib.LTL.ModelChecking.satisfiableB_iff

end Cslib.LTL.ValidityCheckingTests
