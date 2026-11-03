/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.AutomatedReasoning.StringConstraints.WordEquations
public meta import CSLibExt.AutomatedReasoning.StringConstraints.WordEquations

/-!
# Ordinary word-equation boundary tests

Constructive examples exercise empty substitutions, repeated and unused
variables, ground SAT/UNSAT, zero variables, and shared substitutions in a
system. They do not use bounded-search specifications or SAT translation.
-/

@[expose] public section

namespace WordEquationsTests

open Cslib.AutomatedReasoning.StringConstraints

private def withUnused (i : Fin 2) : List Bool :=
  if i = 0 then [true] else [false, false, false]

private def repeated : List (Bool ⊕ Fin 2) := [.inr 0, .inl false, .inr 0]

/-- A different image at unused variable 1 cannot change evaluation. -/
example : evalWord withUnused repeated = evalWord (fun _ => [true]) repeated := by
  apply evalWord_eq_of_agree_on_vars
  intro i hi
  have hi : i = 0 := by simpa [repeated] using hi
  subst i
  rfl

/-- The bound includes equality, without any decidable equality on the alphabet. -/
example {α : Type*} (s : List α) :
    s.length ≤ (evalWord (fun _ : Fin 1 => s) [.inr 0]).length :=
  length_le_evalWord_of_mem (fun _ : Fin 1 => s) (w := [.inr 0]) (i := 0) (by simp)

-- Empty occurring images and strict bounds are allowed.
#guard evalWord (fun _ : Fin 1 => ([] : List Bool)) [.inr 0, .inr 0] = []
#guard (withUnused 0).length < (evalWord withUnused repeated).length
-- Agreement is needed at occurring variables; changing their image changes the result.
#guard evalWord withUnused repeated ≠ evalWord (fun _ => []) repeated
-- Normalization is executable and actually clears the overlong unused image.
#guard normalizeWordSubst withUnused [.inr 0] 0 = [true]
#guard normalizeWordSubst withUnused [.inr 0] 1 = []
#guard normalizeWordSubst withUnused [] 0 = []
#guard normalizeWordSubst withUnused [] 1 = []

/-- The source solution is not globally bounded by the target length, but the
pattern theorem produces a bounded solution including unused variable 1. -/
example : ∃ σ : Fin 2 → List Bool, (∀ i, (σ i).length ≤ 1) ∧
    evalWord σ [.inr 0] = [true] := by
  exact (patternMatch_iff_bounded [.inr 0] [true]).mp ⟨withUnused, rfl⟩

#guard (withUnused 1).length > ([true] : List Bool).length

/-- Repetition does not exclude the empty substitution, and the bound is zero. -/
example : ∃ σ : Fin 2 → List Bool, (∀ i, (σ i).length ≤ 0) ∧
    evalWord σ [.inr 0, .inr 0] = [] := by
  exact (patternMatch_iff_bounded [.inr 0, .inr 0] []).mp ⟨fun _ => [], rfl⟩

/-- The empty alphabet, zero variables, empty pattern and empty target work. -/
example : ∃ σ : Fin 0 → List Empty, (∀ i, (σ i).length ≤ 0) ∧ evalWord σ [] = [] := by
  exact (patternMatch_iff_bounded [] []).mp ⟨fun i => Fin.elim0 i, rfl⟩

/-- Repeated occurrences share one image: `xx` cannot match a one-letter target. -/
example : ¬ ∃ σ : Fin 1 → List Bool, evalWord σ [.inr 0, .inr 0] = [true] := by
  rintro ⟨σ, hσ⟩
  have hlen := congrArg List.length hσ
  simp [evalWord] at hlen
  omega

private def groundYes : WordEq Bool Empty :=
  ⟨[.inl true, .inl false], [.inl true, .inl false]⟩

private def groundNo : WordEq Bool Empty :=
  ⟨[.inl true, .inl false], [.inl false, .inl true]⟩

-- These guards execute the Boolean decider, including false answers.
#guard groundYes.groundSatB
#guard !groundNo.groundSatB
#guard (⟨[], []⟩ : WordEq Empty Empty).groundSatB
#guard !(⟨[], [.inl true]⟩ : WordEq Bool Empty).groundSatB
#guard !(⟨[.inl false], [.inl true]⟩ : WordEq Bool Empty).groundSatB

/-- A successful ground decision yields an actual source-level solution. -/
example : ∃ σ : Empty → List Bool, groundYes.Satisfies σ :=
  groundYes.groundSatB_iff.mp (by decide)

/-- Swapping letters is UNSAT, although both sides have the same length. -/
example : ¬ ∃ σ : Empty → List Bool, groundNo.Satisfies σ := by
  intro h
  have hno : groundNo.groundSatB = true := groundNo.groundSatB_iff.mpr h
  have hfalse : groundNo.groundSatB = false := by decide
  rw [hfalse] at hno
  contradiction

private def oneLetter : WordEq Bool (Fin 2) := ⟨[.inr 0], [.inl true]⟩

/-- The bound theorem includes unused variables, here one with image length 3. -/
example : ∃ B : ℕ, ∃ σ : Fin 2 → List Bool,
    (∀ i, (σ i).length ≤ B) ∧ oneLetter.Satisfies σ :=
  oneLetter.satisfiable_iff_exists_bound.mp ⟨withUnused, rfl⟩

/-- Failure at bound zero is not general UNSAT: `oneLetter` has a solution above. -/
example : ¬ ∃ σ : Fin 2 → List Bool,
    (∀ i, (σ i).length ≤ 0) ∧ oneLetter.Satisfies σ := by
  rintro ⟨σ, hbound, hσ⟩
  have hvalue : σ 0 = [true] := by simpa [oneLetter, WordEq.Satisfies, evalWord] using hσ
  have hzero := hbound 0
  simp [hvalue] at hzero

/-- The unchanged formula embedding consumes the same substitution. -/
example : Sat withUnused oneLetter.toFormula :=
  (WordEq.sat_toFormula withUnused oneLetter).mpr rfl

private def sharedSystem : List (WordEq Bool (Fin 2)) :=
  [oneLetter, ⟨[.inr 0], [.inr 1]⟩]

/-- One substitution and one global bound serve both equations. -/
example : ∃ B : ℕ, ∃ σ : Fin 2 → List Bool,
    (∀ i, (σ i).length ≤ B) ∧ ∀ e ∈ sharedSystem, e.Satisfies σ := by
  apply (wordSystem_satisfiable_iff_exists_bound sharedSystem).mp
  refine ⟨fun _ => [true], ?_⟩
  simp [sharedSystem, oneLetter, WordEq.Satisfies, evalWord]

private def conflictingSystem : List (WordEq Bool (Fin 2)) :=
  [oneLetter, ⟨[.inr 0], [.inl false]⟩]

/-- Separate solutions for each equation do not yield a shared system solution. -/
example : ¬ ∃ B : ℕ, ∃ σ : Fin 2 → List Bool,
    (∀ i, (σ i).length ≤ B) ∧ ∀ e ∈ conflictingSystem, e.Satisfies σ := by
  intro h
  obtain ⟨σ, hσ⟩ := (wordSystem_satisfiable_iff_exists_bound conflictingSystem).mpr h
  have ht : σ 0 = [true] := by
    simpa [oneLetter, WordEq.Satisfies, evalWord] using hσ oneLetter (by simp [conflictingSystem])
  have hf : σ 0 = [false] := by
    simpa [WordEq.Satisfies, evalWord] using
      hσ ⟨[.inr 0], [.inl false]⟩ (by simp [conflictingSystem])
  rw [ht] at hf
  cases hf

/-- Empty systems with no variables need neither letters nor positive bounds. -/
example : ∃ B : ℕ, ∃ σ : Fin 0 → List Empty,
    (∀ i, (σ i).length ≤ B) ∧ ∀ e ∈ ([] : List (WordEq Empty (Fin 0))), e.Satisfies σ := by
  apply (wordSystem_satisfiable_iff_exists_bound []).mp
  exact ⟨fun i => Fin.elim0 i, by simp⟩

end WordEquationsTests
