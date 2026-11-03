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

/-! Higher-universe regression clients. The source Type 0 clients above are retained. -/

-- The same step is accepted by leaves/round and must be accepted by all companion APIs.
private def liftedDuplicateStep (s : ULift.{1} ℕ) :
    Option (ULift.{1} ℕ × ULift.{1} ℕ) :=
  if s.down = 0 then some (⟨1⟩, ⟨1⟩) else none

example : leaves liftedDuplicateStep 1 ⟨0⟩ = [⟨1⟩, ⟨1⟩] := rfl
example : (round liftedDuplicateStep)^[3] ([⟨0⟩], []) = ([], [⟨1⟩, ⟨1⟩]) := rfl

example (f : ULift.{1} ℕ → ℕ)
    (hf : ∀ s l h, liftedDuplicateStep s = some (l, h) → f s = f l + f h)
    (k : ℕ) (s : ULift.{1} ℕ) :
    f s = ((leaves liftedDuplicateStep k s).map f).sum :=
  sum_leaves liftedDuplicateStep f hf k s

example (s₂ : ℕ → Option (ℕ × ℕ))
    (h : ∀ x, s₂ x.down =
      (liftedDuplicateStep x).map fun lh => (lh.1.down, lh.2.down))
    (d : ℕ) (x : ULift.{1} ℕ) :
    leaves s₂ d x.down = (leaves liftedDuplicateStep d x).map ULift.down :=
  leaves_map h d x

example (s₂ : ULift.{2} ℕ → Option (ULift.{2} ℕ × ULift.{2} ℕ))
    (h : ∀ x, s₂ (ULift.up x.down) =
      (liftedDuplicateStep x).map fun lh => (ULift.up lh.1.down, ULift.up lh.2.down))
    (i : ℕ) (p : List (ULift.{1} ℕ) × List (ULift.{1} ℕ)) :
    (round s₂)^[i] (p.1.map (fun x => ULift.up x.down),
        p.2.map (fun x => ULift.up x.down)) =
      (((round liftedDuplicateStep)^[i] p).1.map (fun x => ULift.up x.down),
        ((round liftedDuplicateStep)^[i] p).2.map (fun x => ULift.up x.down)) :=
  round_iterate_map h i p

example : (roundCount liftedDuplicateStep (fun s => s.down + 2))^[3]
    ([⟨0⟩], 5) = ([], 11) := rfl

example (i : ℕ) (st out : List (ULift.{1} ℕ)) :
    (roundCount liftedDuplicateStep ULift.down)^[i] (st, (out.map ULift.down).sum) =
      (((round liftedDuplicateStep)^[i] (st, out)).1,
        (((round liftedDuplicateStep)^[i] (st, out)).2.map ULift.down).sum) :=
  roundCount_iterate liftedDuplicateStep ULift.down i st out

example (d : ℕ) (s : ULift.{1} ℕ)
    (hd : ∀ x ∈ leaves liftedDuplicateStep d s, liftedDuplicateStep x = none)
    (R : ℕ) (hR : 2 * (leaves liftedDuplicateStep d s).length - 1 ≤ R) :
    (roundCount liftedDuplicateStep ULift.down)^[R] ([s], 0) =
      ([], ((leaves liftedDuplicateStep d s).map ULift.down).sum) :=
  roundCount_iterate_of_le liftedDuplicateStep ULift.down d s hd R hR

example (st : List (ULift.{1} ℕ) × List (ULift.{1} ℕ)) :
    st.1.length + st.2.length ≤
      (round liftedDuplicateStep st).1.length + (round liftedDuplicateStep st).2.length :=
  total_le_round liftedDuplicateStep st

example (d : ℕ) (s : ULift.{1} ℕ)
    (hd : ∀ x ∈ leaves liftedDuplicateStep d s, liftedDuplicateStep x = none) (i : ℕ) :
    ((round liftedDuplicateStep)^[i] ([s], [])).1.length +
      ((round liftedDuplicateStep)^[i] ([s], [])).2.length ≤
      (leaves liftedDuplicateStep d s).length :=
  total_le_leaves liftedDuplicateStep d s hd i

example (P : ULift.{1} ℕ → Prop) (s : ULift.{1} ℕ)
    (h : ∀ i, ∀ x ∈ ((round liftedDuplicateStep)^[i] ([s], [])).1, P x) (i : ℕ) :
    ∀ x ∈ ((round liftedDuplicateStep)^[i] ([s], [])).2, P x :=
  out_of_stack liftedDuplicateStep P s h i

private theorem lifted_additive_weight :
    ∀ s l h, liftedDuplicateStep s = some (l, h) →
      weight s.down = weight l.down + weight h.down := by
  intro s l h hs
  by_cases hz : s.down = 0
  · simp only [liftedDuplicateStep, hz, ite_true, Option.some.injEq, Prod.mk.injEq] at hs
    rcases hs with ⟨rfl, rfl⟩
    simp [weight, hz]
  · simp [liftedDuplicateStep, hz] at hs

private theorem lifted_terminal :
    ∀ x ∈ leaves liftedDuplicateStep 1 ⟨0⟩, liftedDuplicateStep x = none := by
  simp [leaves, liftedDuplicateStep]

private theorem lift_down_commutes (x : ULift.{1} ℕ) :
    duplicateStep x.down =
      (liftedDuplicateStep x).map fun lh => (lh.1.down, lh.2.down) := by
  cases h : x.down <;> simp [liftedDuplicateStep, duplicateStep, h]

private theorem lift_up_commutes (x : ℕ) :
    liftedDuplicateStep ⟨x⟩ =
      (duplicateStep x).map fun lh => (ULift.up lh.1, ULift.up lh.2) := by
  cases x <;> simp [liftedDuplicateStep, duplicateStep]

private def higherDuplicateStep (s : ULift.{2} ℕ) :
    Option (ULift.{2} ℕ × ULift.{2} ℕ) :=
  if s.down = 0 then some (⟨1⟩, ⟨1⟩) else none

private theorem lift_higher_commutes (x : ULift.{1} ℕ) :
    higherDuplicateStep (ULift.up x.down) =
      (liftedDuplicateStep x).map fun lh => (ULift.up lh.1.down, ULift.up lh.2.down) := by
  simp only [higherDuplicateStep, liftedDuplicateStep]
  split <;> rfl

example (k : ℕ) :
    6 = ((leaves liftedDuplicateStep k ⟨0⟩).map (fun s => weight s.down)).sum :=
  sum_leaves liftedDuplicateStep (fun s => weight s.down) lifted_additive_weight k ⟨0⟩

example : leaves duplicateStep 1 0 =
    (leaves liftedDuplicateStep 1 ⟨0⟩).map ULift.down :=
  leaves_map lift_down_commutes 1 ⟨0⟩

example : leaves liftedDuplicateStep 1 ⟨0⟩ = (leaves duplicateStep 1 0).map ULift.up :=
  leaves_map lift_up_commutes 1 0

example : leaves higherDuplicateStep 1 ⟨0⟩ =
    (leaves liftedDuplicateStep 1 ⟨0⟩).map (fun x => ULift.up x.down) :=
  leaves_map lift_higher_commutes 1 ⟨0⟩

example (p : List (ULift.{1} ℕ) × List (ULift.{1} ℕ)) :
    round duplicateStep (p.1.map ULift.down, p.2.map ULift.down) =
      ((round liftedDuplicateStep p).1.map ULift.down,
        (round liftedDuplicateStep p).2.map ULift.down) :=
  round_map lift_down_commutes p

example (i : ℕ) (p : List (ULift.{1} ℕ) × List (ULift.{1} ℕ)) :
    (round higherDuplicateStep)^[i] (p.1.map (fun x => ULift.up x.down),
        p.2.map (fun x => ULift.up x.down)) =
      (((round liftedDuplicateStep)^[i] p).1.map (fun x => ULift.up x.down),
        ((round liftedDuplicateStep)^[i] p).2.map (fun x => ULift.up x.down)) :=
  round_iterate_map lift_higher_commutes i p

example : (roundCount liftedDuplicateStep (fun s => s.down + 2))^[7]
    ([⟨0⟩], 0) = ([], 6) :=
  roundCount_iterate_of_le liftedDuplicateStep (fun s => s.down + 2) 1 ⟨0⟩
    lifted_terminal 7 (by decide)

example (i : ℕ) :
    ((round liftedDuplicateStep)^[i] ([⟨0⟩], [])).1.length +
      ((round liftedDuplicateStep)^[i] ([⟨0⟩], [])).2.length ≤ 2 :=
  total_le_leaves liftedDuplicateStep 1 ⟨0⟩ lifted_terminal i

example : (round liftedDuplicateStep)^[3] ([⟨0⟩, ⟨9⟩], [⟨8⟩]) =
    ([⟨9⟩], [⟨1⟩, ⟨1⟩, ⟨8⟩]) :=
  round_iterate liftedDuplicateStep 1 ⟨0⟩ lifted_terminal [⟨9⟩] [⟨8⟩]

example : (roundCount liftedDuplicateStep (fun s => s.down + 2))^[2]
    ([⟨0⟩], 5) = ([⟨1⟩], 8) := rfl
example : (roundCount liftedDuplicateStep (fun _ => 0))^[7] ([⟨0⟩], 5) = ([], 5) := rfl
example : (roundCount higherDuplicateStep (fun s => s.down + 2))^[3]
    ([⟨0⟩], 5) = ([], 11) := rfl

#eval ("UNIVERSE_CONSERVATION", ((leaves liftedDuplicateStep 1 ⟨0⟩).map
  (fun s => weight s.down)).sum)
#eval ("UNIVERSE_MAP_DOWN", (leaves liftedDuplicateStep 1 ⟨0⟩).map ULift.down)
#eval ("UNIVERSE_MAP_HIGHER", (leaves higherDuplicateStep 1 ⟨0⟩).map ULift.down)
#eval let p := (round liftedDuplicateStep)^[3] ([⟨0⟩, ⟨9⟩], [⟨8⟩])
  ("UNIVERSE_ITERATION", p.1.map ULift.down, p.2.map ULift.down)
#eval let p := (roundCount liftedDuplicateStep (fun s => s.down + 2))^[3] ([⟨0⟩], 5)
  ("UNIVERSE_COUNT", p.1.map ULift.down, p.2)
#eval let p := (roundCount liftedDuplicateStep (fun s => s.down + 2))^[2] ([⟨0⟩], 5)
  ("UNIVERSE_COUNT_PARTIAL", p.1.map ULift.down, p.2)
#eval let p := (round liftedDuplicateStep)^[2] ([⟨0⟩], [])
  ("UNIVERSE_TOTAL", p.1.length, p.2.length, p.1.length + p.2.length)
