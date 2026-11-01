/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public meta import CSLibExt.Algorithms.Lean.Search.BinaryBranching

/-! Importing clients for occurrence preservation, traversal, transport and resource bounds. -/

open Cslib.Algorithms.Lean.BinaryBranching

private def duplicateStep : ℕ → Option (ℕ × ℕ)
  | 0 => some (1, 1)
  | _ => none

example : leaves duplicateStep 0 0 = [0] := rfl
example : leaves duplicateStep 1 0 = [1, 1] := rfl
example : leaves (fun s : ℕ => some (s, s)) 2 7 = [7, 7, 7, 7] := rfl
example : (round duplicateStep)^[3] ([0], []) = ([], [1, 1]) := rfl
example : (round duplicateStep)^[3] ([0, 9], [8]) = ([9], [1, 1, 8]) := rfl
example : (roundCount duplicateStep (fun s => s + 2))^[3] ([0], 5) = ([], 11) := rfl
example : (round duplicateStep)^[1] ([1], [8]) = ([], [1, 8]) := rfl
example : (round duplicateStep)^[4] ([], [8]) = ([], [8]) := rfl
example : (roundCount duplicateStep id)^[4] ([], 8) = ([], 8) := rfl

#eval leaves duplicateStep 1 0
#eval leaves (fun s : ℕ => some (s, s)) 2 7
#eval (round duplicateStep)^[3] ([0, 9], [8])
#eval (roundCount duplicateStep (fun s => s + 2))^[3] ([0], 5)

private theorem duplicate_terminal : ∀ x ∈ leaves duplicateStep 1 0, duplicateStep x = none := by
  simp [leaves, duplicateStep]

example : (round duplicateStep)^[3] ([0, 9], [8]) = ([9], [1, 1, 8]) :=
  round_iterate duplicateStep 1 0 duplicate_terminal [9] [8]

example : (round duplicateStep)^[7] ([0], []) = ([], [1, 1]) :=
  round_iterate_of_le duplicateStep 1 0 duplicate_terminal 7 (by decide)

example : (round duplicateStep)^[1] ([1], []) = ([], [1]) :=
  round_iterate duplicateStep 0 1 (by simp [leaves, duplicateStep]) [] []

example : (roundCount duplicateStep (fun s => s + 2))^[7] ([0], 0) = ([], 6) :=
  roundCount_iterate_of_le duplicateStep (fun s => s + 2) 1 0 duplicate_terminal 7 (by decide)

example (i : ℕ) (st out : List ℕ) :
    (roundCount duplicateStep id)^[i] (st, (out.map id).sum) =
      (((round duplicateStep)^[i] (st, out)).1,
        (((round duplicateStep)^[i] (st, out)).2.map id).sum) :=
  roundCount_iterate duplicateStep id i st out

private def weight : ℕ → ℕ
  | 0 => 6
  | n => n + 2

private theorem additive_weight :
    ∀ s l h, duplicateStep s = some (l, h) → weight s = weight l + weight h := by
  intro s l h hs
  cases s with
  | zero =>
    simp only [duplicateStep, Option.some.injEq, Prod.mk.injEq] at hs
    rcases hs with ⟨rfl, rfl⟩
    rfl
  | succ s => simp [duplicateStep] at hs

example : weight 0 = ((leaves duplicateStep 1 0).map weight).sum :=
  sum_leaves duplicateStep weight additive_weight 1 0

private def decoratedStep (s : ℕ × Bool) : Option ((ℕ × Bool) × (ℕ × Bool)) :=
  (duplicateStep s.1).map fun lh => ((lh.1, true), (lh.2, false))

private theorem decoration_commutes (x : ℕ × Bool) :
    duplicateStep x.1 = (decoratedStep x).map fun lh => (lh.1.1, lh.2.1) := by
  cases h : duplicateStep x.1 <;> simp [decoratedStep, h]

example : leaves duplicateStep 1 0 = (leaves decoratedStep 1 (0, true)).map Prod.fst :=
  leaves_map decoration_commutes 1 (0, true)

example (i : ℕ) (p : List (ℕ × Bool) × List (ℕ × Bool)) :
    (round duplicateStep)^[i] (p.1.map Prod.fst, p.2.map Prod.fst) =
      (((round decoratedStep)^[i] p).1.map Prod.fst,
        ((round decoratedStep)^[i] p).2.map Prod.fst) :=
  round_iterate_map decoration_commutes i p

#eval leaves decoratedStep 1 (0, true)
#eval (leaves decoratedStep 1 (0, true)).map Prod.fst

private def Budgets (s p t : ℕ) : Prop :=
  (s = 0 ∧ p = 0 ∧ t = 0) ∨ (s = 1 ∧ p = 1 ∧ t ≤ 1)

private theorem budgets_bound (s p t : ℕ) (hG : Budgets s p t) : p ≤ 1 ∧ t ≤ 1 := by
  rcases hG with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, ht⟩ <;> simp_all

private theorem budgets_step (s p t l h : ℕ) (hG : Budgets s p t)
    (hs : duplicateStep s = some (l, h)) :
    Budgets l (p + 1) t ∧ Budgets h (p + 1) (t + 1) := by
  rcases hG with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, ht⟩
  · simp only [duplicateStep, Option.some.injEq, Prod.mk.injEq] at hs
    rcases hs with ⟨rfl, rfl⟩
    exact ⟨Or.inr ⟨rfl, rfl, by decide⟩, Or.inr ⟨rfl, rfl, by decide⟩⟩
  · simp [duplicateStep] at hs

private theorem root_budget : Budgets 0 0 0 := Or.inl ⟨rfl, rfl, rfl⟩

example : (leaves duplicateStep 1 0).length ≤ ∑ j ∈ Finset.range 2, Nat.choose 1 j :=
  length_leaves_le budgets_bound budgets_step 1 1 1 0 0 0 root_budget
    (by decide) (by decide)

example : ∀ x ∈ leaves duplicateStep 1 0, duplicateStep x = none :=
  step_eq_none_of_mem_leaves budgets_bound budgets_step 1 0 0 0 root_budget (by decide)

example : ∀ x ∈ leaves duplicateStep 1 0, ∃ p t, Budgets x p t :=
  exists_of_mem_leaves budgets_step 1 0 0 0 root_budget

example (i : ℕ) :
    ((round duplicateStep)^[i] ([0], [])).1.length ≤ 2 ∧
      ∀ x ∈ ((round duplicateStep)^[i] ([0], [])).1, ∃ p t, Budgets x p t :=
  stack_bound budgets_bound budgets_step 0 0 0 root_budget i

example (i : ℕ) :
    ((round duplicateStep)^[i] ([0], [])).1.length +
      ((round duplicateStep)^[i] ([0], [])).2.length ≤ 2 :=
  total_le_leaves duplicateStep 1 0 duplicate_terminal i

example : leaves duplicateStep 5 0 = [1, 1] :=
  leaves_eq_of_le duplicateStep 1 5 0 (by decide) duplicate_terminal

example : ¬ (∀ x ∈ leaves duplicateStep 0 0, duplicateStep x = none) := by
  simp [leaves, duplicateStep]

private def orderedStep : ℕ → Option (ℕ × ℕ)
  | 0 => some (2, 3)
  | _ => none

example : leaves orderedStep 1 0 = [2, 3] := rfl
example : (round orderedStep)^[3] ([0, 9], [8]) = ([9], [3, 2, 8]) := rfl
example : (round duplicateStep)^[2] ([0], []) = ([1], [1]) := rfl
example : (round (fun s : ℕ => some (s, s)))^[3] ([7], []) = ([7, 7, 7, 7], []) := rfl

#eval (round orderedStep)^[3] ([0, 9], [8])
#eval (round duplicateStep)^[2] ([0], [])
#eval (round duplicateStep)^[7] ([0], [])
#eval (round (fun s : ℕ => some (s, s)))^[3] ([7], [])

example : (roundCount duplicateStep (fun _ => 1))^[3] ([0], 0) = ([], 2) := rfl
example : ((1, true) : ℕ × Bool) ≠ (1, false) ∧
    Prod.fst (1, true) = Prod.fst (1, false) := by decide

example : round duplicateStep ([0], []) = ([1, 1], []) := rfl
example : round duplicateStep ([1], [8]) = ([], [1, 8]) := rfl
example : roundCount duplicateStep (fun _ => 0) ([1], 5) = ([], 5) := rfl

#print axioms Cslib.Algorithms.Lean.BinaryBranching.round_iterate
#print axioms Cslib.Algorithms.Lean.BinaryBranching.round_iterate_of_le
#print axioms Cslib.Algorithms.Lean.BinaryBranching.sum_leaves
#print axioms Cslib.Algorithms.Lean.BinaryBranching.leaves_map
#print axioms Cslib.Algorithms.Lean.BinaryBranching.round_map
#print axioms Cslib.Algorithms.Lean.BinaryBranching.round_iterate_map
#print axioms Cslib.Algorithms.Lean.BinaryBranching.roundCount_iterate
#print axioms Cslib.Algorithms.Lean.BinaryBranching.roundCount_iterate_of_le
#print axioms Cslib.Algorithms.Lean.BinaryBranching.length_leaves_le
#print axioms Cslib.Algorithms.Lean.BinaryBranching.step_eq_none_of_mem_leaves
#print axioms Cslib.Algorithms.Lean.BinaryBranching.exists_of_mem_leaves
#print axioms Cslib.Algorithms.Lean.BinaryBranching.iff_exists_mem_leaves
#print axioms Cslib.Algorithms.Lean.BinaryBranching.stack_bound
#print axioms Cslib.Algorithms.Lean.BinaryBranching.leaves_sim
#print axioms Cslib.Algorithms.Lean.BinaryBranching.total_le_round
#print axioms Cslib.Algorithms.Lean.BinaryBranching.total_le_leaves
#print axioms Cslib.Algorithms.Lean.BinaryBranching.out_of_stack
#print axioms Cslib.Algorithms.Lean.BinaryBranching.leaves_eq_of_le

example (st : List ℕ × List ℕ) :
    st.1.length + st.2.length ≤
      (round duplicateStep st).1.length + (round duplicateStep st).2.length :=
  total_le_round duplicateStep st

example (P : ℕ → Prop) (s : ℕ)
    (h : ∀ i, ∀ x ∈ ((round duplicateStep)^[i] ([s], [])).1, P x) (i : ℕ) :
    ∀ x ∈ ((round duplicateStep)^[i] ([s], [])).2, P x :=
  out_of_stack duplicateStep P s h i

example {σ σ' : Type*} {s₁ : σ → Option (σ × σ)} {s₂ : σ' → Option (σ' × σ')}
    {f : σ' → σ} {I : σ' → Prop}
    (hsim : ∀ s, I s → (s₂ s).map (Prod.map f f) = s₁ (f s))
    (hinv : ∀ s l h, I s → s₂ s = some (l, h) → I l ∧ I h)
    (k : ℕ) (s : σ') (hs : I s) :
    (leaves s₂ k s).map f = leaves s₁ k (f s) ∧ ∀ x ∈ leaves s₂ k s, I x :=
  leaves_sim hsim hinv k s hs

private theorem small_split (s p t l h : ℕ) (hG : Budgets s p t)
    (hs : duplicateStep s = some (l, h)) : s ≤ 1 ↔ l ≤ 1 ∨ h ≤ 1 := by
  rcases hG with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, ht⟩
  · simp only [duplicateStep, Option.some.injEq, Prod.mk.injEq] at hs
    rcases hs with ⟨rfl, rfl⟩
    decide
  · simp [duplicateStep] at hs

example : 0 ≤ 1 ↔ ∃ x ∈ leaves duplicateStep 1 0, x ≤ 1 :=
  iff_exists_mem_leaves budgets_step (fun s => s ≤ 1) small_split 1 0 0 0 root_budget

example (k : ℕ) (s : ℕ) : 0 < (leaves duplicateStep k s).length :=
  leaves_length_pos duplicateStep k s

example (n : ℕ) : (round duplicateStep)^[n] ([], [8]) = ([], [8]) :=
  round_nil_iterate duplicateStep n [8]
