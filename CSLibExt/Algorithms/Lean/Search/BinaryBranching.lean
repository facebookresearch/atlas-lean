/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Modifications copyright (c) 2026 Meta Platforms, Inc. and affiliates.
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Nat.Choose.Basic

import Mathlib.Algebra.BigOperators.Intervals

/-!
# Binary branching from a partial step

A step either terminates or yields an ordered pair of children. The depth-cut frontier keeps
occurrences, including repeated states; no finiteness or acyclicity is assumed. The explicit
stack walk prepends terminal states to its output, so completed output is in reverse leaf order.
The round bounds count applications of this stack operator, not machine running time.

Ported from `anthropics/formal-math` at `16a5ce41304fcdaea4e0be7c132e1c361dc26da5`:
`StepMachines/Math/SparsifyTree.lean`, `GraphProblems/DomTree.lean`,
`SplitCount/Tree.lean`, `CountKSatRate/Defs.lean`, `CountKSatRate/Walk.lean`,
`StepMachines/Math/SparsifyList.lean`, `SparsificationLemma/Mach/Walk.lean` and
`StepSparsify/CalLeaves.lean`.

Boolean accumulation, preorder and visit lists, early-stop bounds, and application-specific
CNF and machine wrappers are outside this module.
-/

@[expose] public section

namespace Cslib.Algorithms.Lean.BinaryBranching

variable {σ : Type*} (step : σ → Option (σ × σ))

/-- The frontier below `s`, left to right, cut at depth `k`. At depth zero it is `[s]`,
even when `step s` branches. Duplicate occurrences are retained. -/
def leaves : ℕ → σ → List σ
  | 0, s => [s]
  | k + 1, s =>
    match step s with
    | none => [s]
    | some (l, h) => leaves k l ++ leaves k h

/-- One depth-first round on `(stack, output)`. Terminal states are prepended to the output;
a branching state is replaced by its left child followed by its right child. -/
def round : List σ × List σ → List σ × List σ
  | ([], out) => ([], out)
  | (s :: r, out) =>
    match step s with
    | none => (r, s :: out)
    | some (l, h) => (l :: h :: r, out)

/-- Every depth-cut frontier is nonempty. -/
theorem leaves_length_pos (k : ℕ) (s : σ) : 0 < (leaves step k s).length := by
  induction k generalizing s with
  | zero => simp [leaves]
  | succ k ih =>
    rw [leaves]
    split
    · simp
    · rename_i l h _
      have := ih l
      simp only [List.length_append]
      omega

/-- An empty work stack is fixed by any number of rounds. -/
theorem round_nil_iterate (m : ℕ) (out : List σ) : (round step)^[m] ([], out) = ([], out) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply]
    exact ih

/-- If every frontier occurrence is terminal, exactly `2 * length - 1` rounds process
the tree below `s`, preserving the tail `r` and prepending its reversed frontier to `out`.
The terminal-frontier hypothesis is essential: a depth cut may contain branching states. -/
theorem round_iterate (k : ℕ) (s : σ) (hk : ∀ x ∈ leaves step k s, step x = none) (r out : List σ) :
    (round step)^[2 * (leaves step k s).length - 1] (s :: r, out) =
      (r, (leaves step k s).reverse ++ out) := by
  induction k generalizing s r out with
  | zero =>
    have h0 : step s = none := hk s (by simp [leaves])
    simp [leaves, round, h0]
  | succ k ih =>
    cases h0 : step s with
    | none => simp [leaves, round, h0]
    | some lh =>
      obtain ⟨l, h⟩ := lh
      have e0 : leaves step (k + 1) s = leaves step k l ++ leaves step k h := by simp [leaves, h0]
      rw [e0] at hk ⊢
      have hl := leaves_length_pos step k l
      have hh := leaves_length_pos step k h
      have e : 2 * (leaves step k l ++ leaves step k h).length - 1 =
          (2 * (leaves step k h).length - 1) + ((2 * (leaves step k l).length - 1) + 1) := by
        simp only [List.length_append]; omega
      rw [e, Function.iterate_add_apply, Function.iterate_succ_apply]
      have e1 : round step (s :: r, out) = (l :: h :: r, out) := by simp [round, h0]
      rw [e1, ih l (fun x hx => hk x (List.mem_append_left _ hx)),
        ih h (fun x hx => hk x (List.mem_append_right _ hx))]
      simp

/-- After at least `2 * length - 1` rounds from `[s]`, the stack is empty and all
terminal frontier occurrences have been collected in reverse order. -/
theorem round_iterate_of_le (k : ℕ) (s : σ) (hk : ∀ x ∈ leaves step k s, step x = none) (R : ℕ)
    (hR : 2 * (leaves step k s).length - 1 ≤ R) :
    (round step)^[R] ([s], []) = ([], (leaves step k s).reverse) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hR
  rw [Function.iterate_add_apply, round_iterate step k s hk, round_nil_iterate]
  simp

/-- A natural-valued weight additive across each branch equals the sum of the frontier
weights, even when the frontier is cut before termination. -/
theorem sum_leaves {σ : Type} (step : σ → Option (σ × σ)) (f : σ → ℕ)
    (hf : ∀ s l h, step s = some (l, h) → f s = f l + f h)
    (k : ℕ) (s : σ) : f s = ((leaves step k s).map f).sum := by
  induction k generalizing s with
  | zero => simp [leaves]
  | succ k ih =>
    rw [leaves]
    split
    · simp
    · rename_i l h h0
      rw [hf s l h h0, ih l, ih h, List.map_append, List.sum_append]

section Map

variable {σ ρ : Type} {s₁ : σ → Option (σ × σ)} {s₂ : ρ → Option (ρ × ρ)}
  {f : σ → ρ}

/-- A map commuting with both steps transports the ordered frontier, preserving multiplicity. -/
theorem leaves_map (h : ∀ x, s₂ (f x) = (s₁ x).map fun lh => (f lh.1, f lh.2))
    (d : ℕ) (x : σ) : leaves s₂ d (f x) = (leaves s₁ d x).map f := by
  induction d generalizing x with
  | zero => simp [leaves]
  | succ d ih =>
    cases h0 : s₁ x with
    | none =>
      have h1 : s₂ (f x) = none := by rw [h, h0]; rfl
      simp [leaves, h0, h1]
    | some lh =>
      have h1 : s₂ (f x) = some (f lh.1, f lh.2) := by rw [h, h0]; rfl
      simp [leaves, h0, h1, ih]

/-- A commuting node map transports one stack round and its accumulated output. -/
theorem round_map (h : ∀ x, s₂ (f x) = (s₁ x).map fun lh => (f lh.1, f lh.2))
    (p : List σ × List σ) :
    round s₂ (p.1.map f, p.2.map f) = ((round s₁ p).1.map f, (round s₁ p).2.map f) := by
  obtain ⟨st, out⟩ := p
  cases st with
  | nil => simp [round]
  | cons x r =>
    cases h0 : s₁ x with
    | none =>
      have h1 : s₂ (f x) = none := by rw [h, h0]; rfl
      simp [round, h0, h1]
    | some lh =>
      have h1 : s₂ (f x) = some (f lh.1, f lh.2) := by rw [h, h0]; rfl
      simp [round, h0, h1]

/-- A commuting node map transports any number of rounds. No injectivity is required. -/
theorem round_iterate_map
    (h : ∀ x, s₂ (f x) = (s₁ x).map fun lh => (f lh.1, f lh.2))
    (i : ℕ) (p : List σ × List σ) :
    (round s₂)^[i] (p.1.map f, p.2.map f) =
      (((round s₁)^[i] p).1.map f, ((round s₁)^[i] p).2.map f) := by
  let M : List σ × List σ → List ρ × List ρ := fun p => (p.1.map f, p.2.map f)
  have hs : Function.Semiconj M (round s₁) (round s₂) :=
    fun p => (round_map h p).symm
  exact (hs.iterate_right i p).symm

end Map

/-- One stack round accumulating natural weights rather than a list of terminal states.
The previous count is retained, and each terminal occurrence contributes its weight. -/
def roundCount {σ : Type} (step : σ → Option (σ × σ)) (val : σ → ℕ) : List σ × ℕ → List σ × ℕ
  | ([], c) => ([], c)
  | (s :: r, c) =>
    match step s with
    | none => (r, c + val s)
    | some (l, h) => (l :: h :: r, c)

/-- Counting rounds are the projection of list-output rounds to the sum of output weights. -/
theorem roundCount_iterate {σ : Type} (step : σ → Option (σ × σ)) (val : σ → ℕ)
    (i : ℕ) (st out : List σ) :
    (roundCount step val)^[i] (st, (out.map val).sum) =
      (((round step)^[i] (st, out)).1,
        (((round step)^[i] (st, out)).2.map val).sum) := by
  let M : List σ × List σ → List σ × ℕ := fun p => (p.1, (p.2.map val).sum)
  have hs : Function.Semiconj M (round step) (roundCount step val) := by
    rintro ⟨st, out⟩
    cases st with
    | nil => rfl
    | cons s r =>
      cases h0 : step s <;> simp [M, round, roundCount, h0, Nat.add_comm]
  exact (hs.iterate_right i (st, out)).symm

/-- With a terminal frontier and enough rounds, the final count is its total weight. -/
theorem roundCount_iterate_of_le {σ : Type} (step : σ → Option (σ × σ)) (val : σ → ℕ)
    (d : ℕ) (s : σ)
    (hd : ∀ x ∈ leaves step d s, step x = none) (R : ℕ)
    (hR : 2 * (leaves step d s).length - 1 ≤ R) :
    (roundCount step val)^[R] ([s], 0) = ([], ((leaves step d s).map val).sum) := by
  have := roundCount_iterate step val R [s] []
  rw [round_iterate_of_le step d s hd R hR] at this
  simpa [List.sum_reverse] using this

open Finset

section Budget

/-! `G s p t` records depth and heavy-step budget consumed at `s`. -/

variable {step} {G : σ → ℕ → ℕ → Prop} {D T q : ℕ}

private theorem sum_choose_succ (d h : ℕ) :
    ∑ j ∈ range (h + 1 + 1), (d + 1).choose j =
      ∑ j ∈ range (h + 1 + 1), d.choose j + ∑ j ∈ range (h + 1), d.choose j := by
  rw [sum_range_succ' _ (h + 1), sum_range_succ' _ (h + 1)]
  simp only [Nat.choose_succ_succ, sum_add_distrib, Nat.choose_zero_right, Nat.succ_eq_add_one]
  omega

private theorem one_le_sum_choose (d h : ℕ) : 1 ≤ ∑ j ∈ range (h + 1), d.choose j := by
  rw [sum_range_succ']
  simp

/-- With at most `d` further depth steps and `h` further heavy steps, the frontier has
at most `∑ j ∈ range (h + 1), d.choose j` occurrences. The source budget hypotheses
are retained, including the strict heavy-budget inequality. -/
theorem length_leaves_le (hb : ∀ s p t, G s p t → p ≤ D ∧ t ≤ T)
    (hs : ∀ s p t l h, G s p t → step s = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + q))
    (k d h : ℕ) (s : σ) (p t : ℕ) (hG : G s p t) (hd : D ≤ p + d) (hh : T < t + (h + 1) * q) :
    (leaves step k s).length ≤ ∑ j ∈ range (h + 1), d.choose j := by
  induction k generalizing d h s p t with
  | zero => simpa [leaves] using one_le_sum_choose d h
  | succ k ih =>
    rw [leaves]
    split
    · simpa using one_le_sum_choose d h
    · rename_i l r h0
      obtain ⟨hl, hr⟩ := hs s p t l r hG h0
      have hbl := hb _ _ _ hl
      have hbr := hb _ _ _ hr
      obtain _ | d := d
      · omega
      obtain _ | h := h
      · omega
      have h1 := ih d (h + 1) l (p + 1) t hl (by omega) hh
      have h2 := ih d h r (p + 1) (t + q) hr (by omega) (by
        rw [Nat.add_mul (h + 1) 1 q] at hh
        omega)
      rw [List.length_append, sum_choose_succ]
      omega

/-- A depth allowance covering the remaining depth budget produces only terminal states. -/
theorem step_eq_none_of_mem_leaves (hb : ∀ s p t, G s p t → p ≤ D ∧ t ≤ T)
    (hs : ∀ s p t l h, G s p t → step s = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + q))
    (k : ℕ) (s : σ) (p t : ℕ) (hG : G s p t) (hk : D ≤ p + k) :
    ∀ x ∈ leaves step k s, step x = none := by
  induction k generalizing s p t with
  | zero =>
    intro x hx
    obtain rfl : x = s := by simpa [leaves] using hx
    cases h0 : step x with
    | none => rfl
    | some lh =>
      have := (hb _ _ _ (hs x p t lh.1 lh.2 hG h0).1).1
      omega
  | succ k ih =>
    intro x hx
    rw [leaves] at hx
    split at hx
    · rename_i h0
      obtain rfl : x = s := by simpa using hx
      exact h0
    · rename_i l r h0
      obtain ⟨hl, hr⟩ := hs s p t l r hG h0
      rcases List.mem_append.1 hx with hx | hx
      · exact ih l (p + 1) t hl (by omega) x hx
      · exact ih r (p + 1) (t + q) hr (by omega) x hx

/-- Every frontier occurrence satisfies the resource invariant at some budgets. -/
theorem exists_of_mem_leaves
    (hs : ∀ s p t l h, G s p t → step s = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + q))
    (k : ℕ) (s : σ) (p t : ℕ) (hG : G s p t) : ∀ x ∈ leaves step k s, ∃ p' t', G x p' t' := by
  induction k generalizing s p t with
  | zero =>
    intro x hx
    obtain rfl : x = s := by simpa [leaves] using hx
    exact ⟨p, t, hG⟩
  | succ k ih =>
    intro x hx
    rw [leaves] at hx
    split at hx
    · obtain rfl : x = s := by simpa using hx
      exact ⟨p, t, hG⟩
    · rename_i l r h0
      obtain ⟨hl, hr⟩ := hs s p t l r hG h0
      rcases List.mem_append.1 hx with hx | hx
      · exact ih l (p + 1) t hl x hx
      · exact ih r (p + 1) (t + q) hr x hx

/-- A property split by branches holds at the root iff it holds at some frontier occurrence. -/
theorem iff_exists_mem_leaves
    (hs : ∀ s p t l h, G s p t → step s = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + q))
    (S : σ → Prop) (hS : ∀ s p t l h, G s p t → step s = some (l, h) → (S s ↔ S l ∨ S h))
    (k : ℕ) (s : σ) (p t : ℕ) (hG : G s p t) : S s ↔ ∃ x ∈ leaves step k s, S x := by
  induction k generalizing s p t with
  | zero => simp [leaves]
  | succ k ih =>
    rw [leaves]
    split
    · simp
    · rename_i l r h0
      obtain ⟨hl, hr⟩ := hs s p t l r hG h0
      rw [hS s p t l r hG h0, ih l (p + 1) t hl, ih r (p + 1) (t + q) hr]
      simp only [List.mem_append, or_and_right, exists_or]

private def StackOK (G : σ → ℕ → ℕ → Prop) : List σ → Prop
  | [] => True
  | s :: r => (∃ p t, G s p t ∧ r.length ≤ p) ∧ StackOK G r

private theorem StackOK.round
    (hs : ∀ s p t l h, G s p t → step s = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + q))
    (st : List σ × List σ) (h : StackOK G st.1) : StackOK G (round step st).1 := by
  obtain ⟨_ | ⟨s, r⟩, out⟩ := st
  · exact h
  · obtain ⟨⟨p, t, hG, hp⟩, hr⟩ := h
    rw [BinaryBranching.round]
    split
    · exact hr
    · rename_i l h' h0
      obtain ⟨hl, hh⟩ := hs s p t l h' hG h0
      exact ⟨⟨p + 1, t, hl, by simpa using hp⟩, ⟨p + 1, t + q, hh, by omega⟩, hr⟩

private theorem StackOK.mem {st : List σ} (h : StackOK G st) : ∀ x ∈ st, ∃ p t, G x p t := by
  induction st with
  | nil => simp
  | cons s r ih =>
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · obtain ⟨⟨p, t, hG, -⟩, -⟩ := h
      exact ⟨p, t, hG⟩
    · exact ih h.2 x hx

/-- The depth budget bounds the stack by `D + 1` at every round; each pending state
satisfies the resource invariant. This is a list-size bound, not a machine-space model. -/
theorem stack_bound (hb : ∀ s p t, G s p t → p ≤ D ∧ t ≤ T)
    (hs : ∀ s p t l h, G s p t → step s = some (l, h) → G l (p + 1) t ∧ G h (p + 1) (t + q))
    (s : σ) (p t : ℕ) (hG : G s p t) (i : ℕ) :
    ((round step)^[i] ([s], [])).1.length ≤ D + 1 ∧
      ∀ x ∈ ((round step)^[i] ([s], [])).1, ∃ p' t', G x p' t' := by
  have hok : StackOK G ((round step)^[i] ([s], [])).1 := by
    induction i with
    | zero => exact ⟨⟨p, t, hG, Nat.zero_le _⟩, trivial⟩
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact ih.round hs
  refine ⟨?_, hok.mem⟩
  generalize ((round step)^[i] ([s], [])).1 = st at hok
  obtain _ | ⟨x, r⟩ := st
  · simp
  · obtain ⟨⟨p', t', hG', hp'⟩, -⟩ := hok
    have := (hb _ _ _ hG').1
    simp only [List.length_cons]
    omega

end Budget

section Simulation

variable {σ' : Type*} {step' : σ' → Option (σ' × σ')}
  {step : σ → Option (σ × σ)} {f : σ' → σ} {I : σ' → Prop}

/-- Step transport restricted to a preserved invariant transports the frontier and
records that all its occurrences satisfy the invariant. -/
theorem leaves_sim (hsim : ∀ s, I s → (step' s).map (Prod.map f f) = step (f s))
    (hinv : ∀ s l h, I s → step' s = some (l, h) → I l ∧ I h) (k : ℕ) (s : σ') (hs : I s) :
    (leaves step' k s).map f = leaves step k (f s) ∧ ∀ x ∈ leaves step' k s, I x := by
  induction k generalizing s with
  | zero => simp [leaves, hs]
  | succ k ih =>
    have h1 := hsim s hs
    cases h0 : step' s with
    | none =>
      rw [h0] at h1
      simp [leaves, h0, ← h1, hs]
    | some lh =>
      obtain ⟨l, h⟩ := lh
      rw [h0] at h1
      obtain ⟨hl, hh⟩ := hinv s l h hs h0
      have e : leaves step (k + 1) (f s) = leaves step k (f l) ++ leaves step k (f h) := by
        simp [leaves, ← h1]
      have e' : leaves step' (k + 1) s = leaves step' k l ++ leaves step' k h := by
        simp [leaves, h0]
      rw [e, e', List.map_append, (ih l hl).1, (ih h hh).1]
      refine ⟨rfl, fun x hx => ?_⟩
      rcases List.mem_append.1 hx with hx | hx
      exacts [(ih l hl).2 x hx, (ih h hh).2 x hx]

end Simulation

section Totals

variable {σ : Type} (step : σ → Option (σ × σ))

/-- One round does not decrease the combined number of pending and collected occurrences. -/
theorem total_le_round (st : List σ × List σ) :
    st.1.length + st.2.length ≤ (round step st).1.length + (round step st).2.length := by
  obtain ⟨_ | ⟨s, r⟩, out⟩ := st
  · simp [round]
  · simp only [round]
    cases step s <;> (simp only [List.length_cons]; omega)

private theorem total_mono (a : List σ × List σ) :
    Monotone fun i => ((round step)^[i] a).1.length + ((round step)^[i] a).2.length :=
  monotone_nat_of_le_succ fun i => by
    simp only [Function.iterate_succ_apply']
    exact total_le_round step _

/-- With a terminal frontier, pending and collected occurrences together never exceed
its length, including before traversal is complete. -/
theorem total_le_leaves (d : ℕ) (s : σ) (hd : ∀ x ∈ leaves step d s, step x = none) (i : ℕ) :
    ((round step)^[i] ([s], [])).1.length + ((round step)^[i] ([s], [])).2.length ≤
      (leaves step d s).length := by
  have h := total_mono step ([s], []) (le_max_left i (2 * (leaves step d s).length - 1))
  simp only [round_iterate_of_le step d s hd _
    (le_max_right i (2 * (leaves step d s).length - 1))] at h
  simpa using h

/-- A property of every state ever on the stack holds of each collected leaf. -/
theorem out_of_stack (P : σ → Prop) (s : σ)
    (h : ∀ i, ∀ x ∈ ((round step)^[i] ([s], [])).1, P x) (i : ℕ) :
    ∀ x ∈ ((round step)^[i] ([s], [])).2, P x := by
  induction i with
  | zero => simp
  | succ i ih =>
    have h1 := h i
    rw [Function.iterate_succ_apply']
    generalize (round step)^[i] ([s], []) = a at ih h1 ⊢
    obtain ⟨_ | ⟨y, r⟩, out⟩ := a
    · exact ih
    · simp only [round]
      cases step y with
      | none =>
        intro x hx
        rcases List.mem_cons.1 hx with rfl | hx
        · exact h1 x (by simp)
        · exact ih x hx
      | some lh => exact ih

end Totals

/-- Increasing a depth cut beyond a terminal frontier leaves the list unchanged. -/
theorem leaves_eq_of_le {σ : Type*} (step : σ → Option (σ × σ)) (D₀ : ℕ) :
    ∀ (D : ℕ) (r : σ), D₀ ≤ D →
    (∀ x ∈ leaves step D₀ r, step x = none) → leaves step D r = leaves step D₀ r := by
  induction D₀ with
  | zero =>
    intro D r _ h
    have hr : step r = none := h r (by simp [leaves])
    cases D with
    | zero => rfl
    | succ D => simp [leaves, hr]
  | succ D₀ ih =>
    intro D r hD h
    obtain ⟨D, rfl⟩ : ∃ D', D = D' + 1 := ⟨D - 1, by omega⟩
    cases hs : step r with
    | none => simp [leaves, hs]
    | some p =>
      obtain ⟨l, g⟩ := p
      simp only [leaves, hs, List.mem_append] at h ⊢
      rw [ih D l (by omega) fun x hx => h x (Or.inl hx),
        ih D g (by omega) fun x hx => h x (Or.inr hx)]

end Cslib.Algorithms.Lean.BinaryBranching
