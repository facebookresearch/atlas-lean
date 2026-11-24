/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Logics.Testing.TestAdequacy
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.OfMap
import Mathlib.Tactic.NormNum
/-! # Tests -/
@[expose] public section
namespace Cslib.Testing

abbrev Sbool : Bool → Bool → Prop := fun x o => o = x
theorem reliable_valid_exhaustive_correct : Correct (id : Bool → Bool) Sbool :=
  reliable_valid_pass_implies_correct exhaustiveCriterion id Sbool Finset.univ
    (reliable_exhaustiveCriterion id Sbool) (valid_exhaustiveCriterion id Sbool)
    rfl (fun _ _ => rfl)
def emptyOnlyCriterion : Criterion Bool Bool := fun _ _ t => t = ∅
theorem reliable_emptyOnlyCriterion : Reliable emptyOnlyCriterion (fun _ => true) Sbool := by
  intro t₁ t₂ h₁ h₂ hp; simp only [emptyOnlyCriterion] at h₁ h₂; subst h₁; subst h₂; exact hp
theorem not_valid_emptyOnlyCriterion : ¬ Valid emptyOnlyCriterion (fun _ => true) Sbool := by
  intro hval; obtain ⟨t, ht, hfail⟩ := hval fun h => absurd (h false) (by decide)
  simp only [emptyOnlyCriterion] at ht; subst ht; exact hfail (passes_empty _ _)
theorem correct_of_empty_domain {O : Type*} (P : Empty → O) (S : Empty → O → Prop) :
    Correct P S := fun x => nomatch x
theorem correct_unit_iff {O : Type*} (P : Unit → O)
    (S : Unit → O → Prop) : Correct P S ↔ S () (P ()) := by
  refine ⟨fun h => h (), fun h x => ?_⟩; cases x; exact h
theorem passes_const_true_singleton_true : Passes (fun _ : Bool => true) Sbool {true} := by
  intro x hx; simp only [Finset.mem_singleton] at hx; subst hx; rfl
theorem not_correct_const_true : ¬ Correct (fun _ : Bool => true) Sbool :=
  fun h => absurd (h false) (by decide)
theorem not_reliable_true_subset :
    ¬ Reliable (fun _ _ t => ({true} : Finset Bool) ⊆ t) (fun _ : Bool => true) Sbool := by
  intro hrel; have h1 : ({true} : Finset Bool) ⊆ {true} := (by decide);
  have h2 : ({true} : Finset Bool) ⊆ {true, false} := (by decide)
  exact absurd (hrel {true} {true, false} h1 h2 passes_const_true_singleton_true
    false (by decide)) (by decide)
def boolMutants (m : Fin 3) : Bool → Bool :=
  match m.val with
  | 0 => fun _ => true
  | 1 => Bool.not
  | _ => id
theorem equiv_mutant_two : EquivalentMutant id boolMutants 2 := fun _ => rfl
theorem subsumes_two_zero : MutantSubsumes id boolMutants 2 0 :=
  mutantSubsumes_of_equivalent id boolMutants equiv_mutant_two
theorem subsumes_zero_one : MutantSubsumes id boolMutants 0 1 := by
  show ∀ x : Bool, (boolMutants 0 x ≠ id x) → (boolMutants 1 x ≠ id x); decide
theorem not_subsumes_one_zero : ¬ MutantSubsumes id boolMutants 1 0 := by
  show ¬ ∀ x : Bool, (boolMutants 1 x ≠ id x) → (boolMutants 0 x ≠ id x); decide
theorem not_killable_zero_true : ¬ KillableWithin id boolMutants {true} 0 := by
  show ¬ ∃ x ∈ ({true} : Finset Bool), (boolMutants 0 x ≠ id x); decide
theorem not_dyn_zero_zero_true : ¬ DynSubsumesWithin id boolMutants {true} 0 0 :=
  fun h => not_killable_zero_true ((dynSubsumesWithin_self_iff _ _ _ _).mp h)
theorem subsumes_zero_zero : MutantSubsumes id boolMutants 0 0 :=
  mutantSubsumes_refl id boolMutants 0
theorem not_equiv_zero : ¬ EquivalentMutant id boolMutants 0 :=
  fun h => absurd (show (true : Bool) = false from h false) (by decide)
theorem not_equiv_one : ¬ EquivalentMutant id boolMutants 1 :=
  fun h => absurd (show (false : Bool) = true from h true) (by decide)
theorem univ_fin_three : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
theorem nonequiv_eq : nonequivMutants id boolMutants = {0, 1} := by
  simp only [nonequivMutants, univ_fin_three, Finset.filter_insert,
    Finset.filter_singleton];
  rw [ite_eq_left not_equiv_zero, ite_eq_left not_equiv_one,
    ite_eq_right (not_not_intro equiv_mutant_two)]; decide
theorem nonequiv_card : (nonequivMutants id boolMutants).card = 2 := by
  rw [nonequiv_eq]; decide
theorem nonequiv_card_ne_zero : (nonequivMutants id boolMutants).card ≠ 0 := by
  rw [nonequiv_card]; decide
theorem killed_true_one : killedBySuite id boolMutants {true} 1 :=
  ⟨true, by decide, show (false : Bool) ≠ true from by decide⟩
theorem not_killed_two (t : Finset Bool) : ¬ killedBySuite id boolMutants t 2 := by
  intro h; obtain ⟨x, _, hk⟩ := h; exact hk (equiv_mutant_two x)
theorem not_killed_true_zero : ¬ killedBySuite id boolMutants {true} 0 := not_killable_zero_true
theorem killed_singleton_true_eq : killedMutants id boolMutants {true} = {1} := by
  simp only [killedMutants, univ_fin_three, Finset.filter_insert,
    Finset.filter_singleton];
  rw [ite_eq_right not_killed_true_zero, ite_eq_left killed_true_one,
    ite_eq_right (not_killed_two {true})]; decide
theorem killed_singleton_true_card :
    (killedMutants id boolMutants {true}).card = 1 := by
  rw [killed_singleton_true_eq]; decide
theorem killed_false_zero : killedBySuite id boolMutants {false} 0 :=
  ⟨false, by decide, show (true : Bool) ≠ false from by decide⟩
theorem killed_false_one : killedBySuite id boolMutants {false} 1 :=
  ⟨false, by decide, show (true : Bool) ≠ false from by decide⟩
theorem killed_singleton_false_eq : killedMutants id boolMutants {false} = {0, 1} := by
  simp only [killedMutants, univ_fin_three, Finset.filter_insert,
    Finset.filter_singleton];
  rw [ite_eq_left killed_false_zero, ite_eq_left killed_false_one,
    ite_eq_right (not_killed_two {false})]; decide
theorem score_empty : mutationScore id boolMutants ∅ = some (0 : ℚ) :=
  mutationScore_empty id boolMutants nonequiv_card_ne_zero
theorem score_singleton_true : mutationScore id boolMutants {true} = some (1/2 : ℚ) := by
  simp only [mutationScore];
  rw [ite_eq_right nonequiv_card_ne_zero, killed_singleton_true_card,
    nonequiv_card]; norm_num
theorem score_singleton_false : mutationScore id boolMutants {false} = some (1 : ℚ) := by
  rw [mutationScore_eq_one];
  exact ⟨nonequiv_card_ne_zero, by rw [killed_singleton_false_eq, nonequiv_eq]⟩
theorem killed_univ_zero : killedBySuite id boolMutants Finset.univ 0 :=
  ⟨false, Finset.mem_univ false, show (true : Bool) ≠ false from by decide⟩
theorem killed_univ_one : killedBySuite id boolMutants Finset.univ 1 :=
  ⟨false, Finset.mem_univ false, show (true : Bool) ≠ false from by decide⟩
theorem killed_univ_eq : killedMutants id boolMutants Finset.univ = {0, 1} := by
  simp only [killedMutants, univ_fin_three, Finset.filter_insert,
    Finset.filter_singleton];
  rw [ite_eq_left killed_univ_zero, ite_eq_left killed_univ_one,
    ite_eq_right (not_killed_two Finset.univ)]; decide
theorem score_univ : mutationScore id boolMutants Finset.univ = some (1 : ℚ) := by
  rw [mutationScore_eq_one]; exact ⟨nonequiv_card_ne_zero, by rw [killed_univ_eq, nonequiv_eq]⟩
theorem score_mono_singleton_true_univ : ∃ q₁ q₂,
    mutationScore id boolMutants {true} = some q₁ ∧
      mutationScore id boolMutants Finset.univ = some q₂ ∧ q₁ ≤ q₂ :=
  ⟨1/2, 1, score_singleton_true, score_univ,
    mutationScore_mono _ _ _ _ (by decide) _ _ score_singleton_true score_univ⟩
theorem nonequiv_of_empty (P : Bool → Bool) (mutant : Empty → Bool → Bool) :
    nonequivMutants P mutant = ∅ := by
  simp only [nonequivMutants, Finset.filter_eq_empty_iff]; intro x _ _; exact nomatch x
theorem score_empty_mutants_empty (P : Bool → Bool)
    (mutant : Empty → Bool → Bool) : mutationScore P mutant ∅ = none := by
  rw [mutationScore_eq_none_iff, nonequiv_of_empty, Finset.card_empty]
theorem score_empty_mutants_univ (P : Bool → Bool)
    (mutant : Empty → Bool → Bool) : mutationScore P mutant Finset.univ = none := by
  rw [mutationScore_eq_none_iff, nonequiv_of_empty, Finset.card_empty]
theorem nonequiv_of_unit_equiv (P : Bool → Bool) (mutant : Unit → Bool → Bool)
    (heq : mutant () = P) : nonequivMutants P mutant = ∅ := by
  simp only [nonequivMutants, Finset.filter_eq_empty_iff];
  intro x _ h; cases x; exact h fun y => congrFun heq y
theorem score_unit_equiv_empty (P : Bool → Bool) (mutant : Unit → Bool → Bool)
    (heq : mutant () = P) : mutationScore P mutant ∅ = none := by
  rw [mutationScore_eq_none_iff, nonequiv_of_unit_equiv P mutant heq, Finset.card_empty]
theorem score_unit_equiv_singleton (P : Bool → Bool)
    (mutant : Unit → Bool → Bool) (heq : mutant () = P) :
    mutationScore P mutant {true} = none := by
  rw [mutationScore_eq_none_iff, nonequiv_of_unit_equiv P mutant heq, Finset.card_empty]
end Cslib.Testing
