/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`thys/Amortized_Complexity/Amortized_Examples.thy` (Archive of Formal Proofs, entry `Amortized Complexity`, https://isa-afp.org/entries/Amortized_Complexity.html):
Copyright (c) 2014 Tobias Nipkow. All rights reserved.
Licensed under the BSD License.
Authors: Tobias Nipkow
-/

module

public import CSLibExt.Algorithms.Lean.DataStructures.Amortized.Framework
public import Mathlib.Data.List.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic

/-!
# Amortized-analysis examples (2)

The remaining framework examples of `Amortized_Examples.thy`, as
`AmortizedData` instances: dynamic tables with insert and delete
(`Dyn_Tab3`, book §19.3.2), the queue with `adjust` (`Queue2`), the
queue with `balance` (`Queue3`), and dynamic tables with a
generalised growth factor (`Dyn_Tab2`, `c > 1`,
`a ≥ c / (c - 1)`, new size `⌈c * l⌉₊`). `dynTab3Phi` is
`noncomputable` because its branch condition is a real comparison;
`dynTab2Ins` / `dynTab2Amortized` are `noncomputable` because
`Int.ceil` is.

Source: the AFP entry `Amortized Complexity` (Tobias Nipkow,
2014; BSD), `thys/Amortized_Complexity/Amortized_Examples.thy`
(https://isa-afp.org/entries/Amortized_Complexity.html)
(`Dyn_Tab3`, `Queue2`, `Queue3`, `Dyn_Tab2`). Book: Ch. 19
section 19.3.2 and the `adjust` / `balance` queues. The instances
and proofs are re-established in Lean; Isabelle-derived names are
kept for traceability.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace Amortized

variable {β : Type u}

/- ### Dynamic tables: insert and delete (`Dyn_Tab3`, book §19.3.2) -/

inductive DynTab3Op where
  | empty : DynTab3Op
  | ins : DynTab3Op
  | del : DynTab3Op

def dynTab3Arity : DynTab3Op → ℕ
  | .empty => 0
  | .ins => 1
  | .del => 1

def dynTab3Exec : DynTab3Op → List (ℕ × ℕ) → ℕ × ℕ
  | .empty, _ => (0, 0)
  | .ins, [(n, l)] => (n + 1, if n < l then l else if l = 0 then 1 else 2 * l)
  | .del, [(n, l)] => (n - 1, if n ≤ 1 then 0 else if 4 * (n - 1) < l then l / 2 else l)
  | _, _ => (0, 0)

def dynTab3Cost : DynTab3Op → List (ℕ × ℕ) → ℕ
  | .empty, _ => 1
  | .ins, [(n, l)] => if n < l then 1 else n + 1
  | .del, [(n, l)] => if n ≤ 1 then 1 else if 4 * (n - 1) < l then n else 1
  | _, _ => 0

/-- The invariant: `l = 0 → n = 0`, else `n ≤ l ∧ l ≤ 4n`. -/
def dynTab3Inv : ℕ × ℕ → Prop
  | (n, l) => if l = 0 then n = 0 else n ≤ l ∧ l ≤ 4 * n

/-- `Φ (n, l) = if 2n < l then l/2 - n else 2n - l` (real division).
Noncomputable because the branch condition is a real comparison
(same reason as `skewU`). -/
noncomputable def dynTab3Phi : ℕ × ℕ → ℝ
  | (n, l) => if 2 * (n : ℝ) < (l : ℝ) then (l : ℝ) / 2 - (n : ℝ) else 2 * (n : ℝ) - (l : ℝ)

def dynTab3U : DynTab3Op → List (ℕ × ℕ) → ℝ
  | .empty, _ => 1
  | .ins, _ => 3
  | .del, _ => 2

theorem dynTab3Exec_empty : dynTab3Exec .empty [] = (0, 0) := by simp [dynTab3Exec]

theorem dynTab3Exec_ins (n l : ℕ) :
    dynTab3Exec .ins [(n, l)] = (n + 1, if n < l then l else if l = 0 then 1 else 2 * l) := by
  simp [dynTab3Exec]

theorem dynTab3Exec_del (n l : ℕ) :
    dynTab3Exec .del [(n, l)] =
      (n - 1, if n ≤ 1 then 0 else if 4 * (n - 1) < l then l / 2 else l) := by
  simp [dynTab3Exec]

theorem dynTab3Cost_empty : dynTab3Cost .empty [] = 1 := by simp [dynTab3Cost]

theorem dynTab3Cost_ins (n l : ℕ) :
    dynTab3Cost .ins [(n, l)] = if n < l then 1 else n + 1 := by simp [dynTab3Cost]

theorem dynTab3Cost_del (n l : ℕ) :
    dynTab3Cost .del [(n, l)] =
      if n ≤ 1 then 1 else if 4 * (n - 1) < l then n else 1 := by simp [dynTab3Cost]

theorem dynTab3U_empty : dynTab3U .empty [] = 1 := by simp [dynTab3U]

theorem dynTab3U_ins (ss : List (ℕ × ℕ)) : dynTab3U .ins ss = 3 := by simp [dynTab3U]

theorem dynTab3U_del (ss : List (ℕ × ℕ)) : dynTab3U .del ss = 2 := by simp [dynTab3U]

/-- The `interpretation Amortized` for dynamic tables, insert and delete.
Noncomputable because `dynTab3Phi` is. -/
noncomputable def dynTab3Amortized : AmortizedData DynTab3Op (ℕ × ℕ) where
  arity := dynTab3Arity
  exec := dynTab3Exec
  inv := dynTab3Inv
  cost := dynTab3Cost
  Phi := dynTab3Phi
  U := dynTab3U
  inv_exec := by
    intro f ss hall hlen
    cases f with
    | empty =>
      cases ss with
      | nil =>
        rw [dynTab3Exec_empty]
        simp [dynTab3Inv]
      | cons s ss => simp [dynTab3Arity] at hlen
    | ins =>
      cases ss with
      | nil => simp [dynTab3Arity] at hlen
      | cons p ss =>
        cases ss with
        | nil =>
          obtain ⟨n, l⟩ := p
          have hinv : dynTab3Inv (n, l) := hall _ (by simp)
          rw [dynTab3Exec_ins]
          by_cases hl : l = 0
          · subst hl
            have hn : n = 0 := by simp [dynTab3Inv] at hinv; exact hinv
            subst hn
            simp [dynTab3Inv]
          · have hn : n ≤ l ∧ l ≤ 4 * n := by
              simp only [dynTab3Inv, ite_eq_right hl] at hinv
              exact hinv
            by_cases hnl : n < l
            · have hexec : (n + 1, if n < l then l else if l = 0 then 1 else 2 * l) = (n + 1, l) := by
                rw [ite_eq_left hnl]
              rw [hexec]
              simp only [dynTab3Inv, ite_eq_right hl]
              exact ⟨by omega, by omega⟩
            · have hnl' : n = l := by omega
              subst hnl'
              have hexec : (n + 1, if n < n then n else if n = 0 then 1 else 2 * n) = (n + 1, 2 * n) := by
                rw [ite_eq_right (Nat.lt_irrefl n), ite_eq_right hl]
              rw [hexec]
              have h2n : 2 * n ≠ 0 := by omega
              simp only [dynTab3Inv, ite_eq_right h2n]
              exact ⟨by omega, by omega⟩
        | cons _ _ => simp [dynTab3Arity] at hlen
    | del =>
      cases ss with
      | nil => simp [dynTab3Arity] at hlen
      | cons p ss =>
        cases ss with
        | nil =>
          obtain ⟨n, l⟩ := p
          have hinv : dynTab3Inv (n, l) := hall _ (by simp)
          rw [dynTab3Exec_del]
          by_cases hn1 : n ≤ 1
          · have hexec : (n - 1, if n ≤ 1 then 0 else if 4 * (n - 1) < l then l / 2 else l) =
                (n - 1, 0) := by simp [hn1]
            rw [hexec]
            have hgoal : dynTab3Inv (n - 1, 0) := by
              show n - 1 = 0
              omega
            exact hgoal
          · have hl : l ≠ 0 := by
              by_contra hlc
              have hn0 : n = 0 := by simp [dynTab3Inv, hlc] at hinv; exact hinv
              omega
            have hn : n ≤ l ∧ l ≤ 4 * n := by
              simp only [dynTab3Inv, ite_eq_right hl] at hinv
              exact hinv
            by_cases h4 : 4 * (n - 1) < l
            · have hexec : (n - 1, if n ≤ 1 then 0 else if 4 * (n - 1) < l then l / 2 else l) =
                  (n - 1, l / 2) := by simp [hn1, h4]
              rw [hexec]
              have hdiv : l / 2 ≠ 0 := by omega
              simp only [dynTab3Inv, ite_eq_right hdiv]
              exact ⟨by omega, by omega⟩
            · have hexec : (n - 1, if n ≤ 1 then 0 else if 4 * (n - 1) < l then l / 2 else l) =
                  (n - 1, l) := by simp [hn1, h4]
              rw [hexec]
              simp only [dynTab3Inv, ite_eq_right hl]
              exact ⟨by omega, by omega⟩
        | cons _ _ => simp [dynTab3Arity] at hlen
  ppos := by
    intro p hp
    obtain ⟨n, l⟩ := p
    simp only [dynTab3Phi]
    by_cases h : 2 * (n : ℝ) < (l : ℝ)
    · rw [ite_eq_left h]
      linarith
    · rw [ite_eq_right h]
      have h' : (l : ℝ) ≤ 2 * (n : ℝ) := le_of_not_gt h
      linarith
  U_bound := by
    intro f ss hall hlen
    cases f with
    | empty =>
      cases ss with
      | nil =>
        rw [dynTab3Exec_empty, dynTab3Cost_empty, dynTab3U_empty]
        simp only [List.map_nil, List.sum_nil]
        simp [dynTab3Phi]
      | cons s ss => simp [dynTab3Arity] at hlen
    | ins =>
      cases ss with
      | nil => simp [dynTab3Arity] at hlen
      | cons p ss =>
        cases ss with
        | nil =>
          obtain ⟨n, l⟩ := p
          have hinv : dynTab3Inv (n, l) := hall _ (by simp)
          rw [dynTab3Exec_ins, dynTab3Cost_ins, dynTab3U_ins]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          by_cases hl : l = 0
          · subst hl
            have hn : n = 0 := by simp [dynTab3Inv] at hinv; exact hinv
            subst hn
            norm_num [dynTab3Phi]
          · have hn : n ≤ l ∧ l ≤ 4 * n := by
              simp only [dynTab3Inv, ite_eq_right hl] at hinv
              exact hinv
            by_cases hnl : n < l
            · have hexec : (n + 1, if n < l then l else if l = 0 then 1 else 2 * l) = (n + 1, l) := by
                rw [ite_eq_left hnl]
              have hcost : (if n < l then (1 : ℕ) else n + 1) = 1 := by rw [ite_eq_left hnl]
              by_cases hA : 2 * (n : ℝ) < (l : ℝ)
              · by_cases hB : 2 * ((n + 1 : ℕ) : ℝ) < (l : ℝ)
                · have hPhiA : dynTab3Phi (n + 1, l) = (l : ℝ) / 2 - ((n + 1 : ℕ) : ℝ) := by
                    simp only [dynTab3Phi, ite_eq_left hB]
                  have hPhiB : dynTab3Phi (n, l) = (l : ℝ) / 2 - (n : ℝ) := by
                    simp only [dynTab3Phi, ite_eq_left hA]
                  rw [hexec, hcost, hPhiA, hPhiB]
                  push_cast
                  linarith
                · have hPhiA : dynTab3Phi (n + 1, l) = 2 * ((n + 1 : ℕ) : ℝ) - (l : ℝ) := by
                    simp only [dynTab3Phi, ite_eq_right hB]
                  have hPhiB : dynTab3Phi (n, l) = (l : ℝ) / 2 - (n : ℝ) := by
                    simp only [dynTab3Phi, ite_eq_left hA]
                  rw [hexec, hcost, hPhiA, hPhiB]
                  push_cast
                  linarith [hA]
              · by_cases hB : 2 * ((n + 1 : ℕ) : ℝ) < (l : ℝ)
                · exfalso
                  have hB' : 2 * ((n : ℝ) + 1) < (l : ℝ) := by
                    push_cast at hB
                    exact hB
                  exact hA (by linarith)
                · have hPhiA : dynTab3Phi (n + 1, l) = 2 * ((n + 1 : ℕ) : ℝ) - (l : ℝ) := by
                    simp only [dynTab3Phi, ite_eq_right hB]
                  have hPhiB : dynTab3Phi (n, l) = 2 * (n : ℝ) - (l : ℝ) := by
                    simp only [dynTab3Phi, ite_eq_right hA]
                  rw [hexec, hcost, hPhiA, hPhiB]
                  push_cast
                  linarith
            · have hnl' : n = l := by omega
              subst hnl'
              have hexec : (n + 1, if n < n then n else if n = 0 then 1 else 2 * n) = (n + 1, 2 * n) := by
                rw [ite_eq_right (Nat.lt_irrefl n), ite_eq_right hl]
              have hcost : (if n < n then (1 : ℕ) else n + 1) = n + 1 := by
                rw [ite_eq_right (Nat.lt_irrefl n)]
              have hPhiA : dynTab3Phi (n + 1, 2 * n) = 2 := by
                simp only [dynTab3Phi]
                push_cast
                split <;> linarith
              have hPhiB : dynTab3Phi (n, n) = (n : ℝ) := by
                simp only [dynTab3Phi]
                have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
                split <;> linarith
              rw [hexec, hcost, hPhiA, hPhiB]
              push_cast
              linarith
        | cons _ _ => simp [dynTab3Arity] at hlen
    | del =>
      cases ss with
      | nil => simp [dynTab3Arity] at hlen
      | cons p ss =>
        cases ss with
        | nil =>
          obtain ⟨n, l⟩ := p
          have hinv : dynTab3Inv (n, l) := hall _ (by simp)
          rw [dynTab3Exec_del, dynTab3Cost_del, dynTab3U_del]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          by_cases hn1 : n ≤ 1
          · have hexec : (n - 1, if n ≤ 1 then 0 else if 4 * (n - 1) < l then l / 2 else l) =
                (n - 1, 0) := by simp [hn1]
            have hcost : (if n ≤ 1 then (1 : ℕ) else if 4 * (n - 1) < l then n else 1) = 1 := by
              simp [hn1]
            have hsub : n - 1 = 0 := by omega
            have hPhiA : dynTab3Phi (n - 1, 0) = 0 := by
              rw [hsub]
              norm_num [dynTab3Phi]
            have hPhiB0 : 0 ≤ dynTab3Phi (n, l) := by
              simp only [dynTab3Phi]
              split <;> linarith
            rw [hexec, hcost, hPhiA]
            push_cast
            linarith
          · have hl : l ≠ 0 := by
              by_contra hlc
              have hn0 : n = 0 := by simp [dynTab3Inv, hlc] at hinv; exact hinv
              omega
            have hn : n ≤ l ∧ l ≤ 4 * n := by
              simp only [dynTab3Inv, ite_eq_right hl] at hinv
              exact hinv
            by_cases h4 : 4 * (n - 1) < l
            · have h4int : 4 * (n : ℝ) ≤ (l : ℝ) + 3 := by
                have h : 4 * n ≤ l + 3 := by omega
                exact_mod_cast h
              have hexec : (n - 1, if n ≤ 1 then 0 else if 4 * (n - 1) < l then l / 2 else l) =
                  (n - 1, l / 2) := by simp [hn1, h4]
              have hcost : (if n ≤ 1 then (1 : ℕ) else if 4 * (n - 1) < l then n else 1) = n := by
                simp [hn1, h4]
              have h2n : 2 * (n : ℝ) < (l : ℝ) := by
                have h4c : (4 * (n - 1 : ℕ) : ℝ) < (l : ℝ) := by exact_mod_cast h4
                have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast (by omega : 2 ≤ n)
                linarith
              have hPhiB : dynTab3Phi (n, l) = (l : ℝ) / 2 - (n : ℝ) := by
                simp only [dynTab3Phi, ite_eq_left h2n]
              have hdivR : 2 * ((l / 2 : ℕ) : ℝ) + ((l % 2 : ℕ) : ℝ) = (l : ℝ) := by
                exact_mod_cast Nat.div_add_mod l 2
              have hmod0 : (0 : ℝ) ≤ ((l % 2 : ℕ) : ℝ) := Nat.cast_nonneg _
              have hmodlt : ((l % 2 : ℕ) : ℝ) < 2 := by
                have h : l % 2 < 2 := Nat.mod_lt l (by norm_num)
                exact_mod_cast h
              have hn1cast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
                rw [Nat.cast_sub (show 1 ≤ n by omega)]
                simp
              have hPhiA_le : dynTab3Phi (n - 1, l / 2) ≤ (l : ℝ) / 2 - 2 * (n : ℝ) + 2 := by
                simp only [dynTab3Phi]
                by_cases hA2 : 2 * ((n - 1 : ℕ) : ℝ) < ((l / 2 : ℕ) : ℝ)
                · rw [ite_eq_left hA2, hn1cast]
                  have hmle : ((l / 2 : ℕ) : ℝ) ≤ (l : ℝ) / 2 := by linarith [hdivR, hmod0]
                  linarith [hmle, h4int]
                · rw [ite_eq_right hA2, hn1cast]
                  have hmge : ((l / 2 : ℕ) : ℝ) ≥ (l : ℝ) / 2 - 1 := by linarith [hdivR, hmodlt]
                  linarith [hmge, h4int]
              rw [hexec, hcost, hPhiB]
              linarith [hPhiA_le]
            · have hexec : (n - 1, if n ≤ 1 then 0 else if 4 * (n - 1) < l then l / 2 else l) =
                  (n - 1, l) := by simp [hn1, h4]
              have hcost : (if n ≤ 1 then (1 : ℕ) else if 4 * (n - 1) < l then n else 1) = 1 := by
                simp [hn1, h4]
              have hn1cast : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
                rw [Nat.cast_sub (show 1 ≤ n by omega)]
                simp
              rw [hexec, hcost]
              push_cast
              by_cases h2a : 2 * (n : ℝ) < (l : ℝ)
              · have hPhiB : dynTab3Phi (n, l) = (l : ℝ) / 2 - (n : ℝ) := by
                  simp only [dynTab3Phi, ite_eq_left h2a]
                rw [hPhiB]
                by_cases h2b : 2 * ((n - 1 : ℕ) : ℝ) < (l : ℝ)
                · have hPhiA : dynTab3Phi (n - 1, l) = (l : ℝ) / 2 - ((n : ℝ) - 1) := by
                    simp only [dynTab3Phi]
                    rw [ite_eq_left h2b, hn1cast]
                  rw [hPhiA]
                  linarith
                · have hPhiA : dynTab3Phi (n - 1, l) = 2 * ((n : ℝ) - 1) - (l : ℝ) := by
                    simp only [dynTab3Phi]
                    rw [ite_eq_right h2b, hn1cast]
                  rw [hPhiA]
                  linarith [h2a]
              · have hPhiB : dynTab3Phi (n, l) = 2 * (n : ℝ) - (l : ℝ) := by
                  simp only [dynTab3Phi, ite_eq_right h2a]
                rw [hPhiB]
                by_cases h2b : 2 * ((n - 1 : ℕ) : ℝ) < (l : ℝ)
                · have hPhiA : dynTab3Phi (n - 1, l) = (l : ℝ) / 2 - ((n : ℝ) - 1) := by
                    simp only [dynTab3Phi]
                    rw [ite_eq_left h2b, hn1cast]
                  rw [hPhiA]
                  have h2a' : (l : ℝ) ≤ 2 * (n : ℝ) := le_of_not_gt h2a
                  linarith
                · have hPhiA : dynTab3Phi (n - 1, l) = 2 * ((n : ℝ) - 1) - (l : ℝ) := by
                    simp only [dynTab3Phi]
                    rw [ite_eq_right h2b, hn1cast]
                  rw [hPhiA]
                  linarith
        | cons _ _ => simp [dynTab3Arity] at hlen

/- ### Queue with `adjust` (`Queue2`) -/

inductive Queue2Op (β : Type u) where
  | empty : Queue2Op β
  | enq : β → Queue2Op β
  | deq : Queue2Op β

def queue2Arity : Queue2Op β → ℕ
  | .empty => 0
  | .enq _ => 1
  | .deq => 1

/-- `adjust`: move `xs` over when `ys` is empty. -/
def queue2Adjust : List β × List β → List β × List β
  | (xs, ys) => if ys = [] then ([], xs.reverse) else (xs, ys)

def queue2Exec : Queue2Op β → List (List β × List β) → List β × List β
  | .empty, _ => ([], [])
  | .enq x, [(xs, ys)] => queue2Adjust (x :: xs, ys)
  | .deq, [(xs, ys)] => queue2Adjust (xs, ys.tail)
  | _, _ => ([], [])

def queue2Cost : Queue2Op β → List (List β × List β) → ℕ
  | .empty, _ => 0
  | .enq _, [(xs, ys)] => 1 + (if ys = [] then xs.length + 1 else 0)
  | .deq, [(xs, ys)] => if ys.tail = [] then xs.length else 0
  | _, _ => 0

/-- `Φ (xs, ys) = length xs` (Isabelle's `size xs`). -/
def queue2Phi : List β × List β → ℝ := fun q => (q.1.length : ℝ)

def queue2U : Queue2Op β → List (List β × List β) → ℝ
  | .empty, _ => 0
  | .enq _, _ => 2
  | .deq, _ => 0

theorem queue2Adjust_eq (xs ys : List β) :
    queue2Adjust (xs, ys) = if ys = [] then ([], xs.reverse) else (xs, ys) := by
  simp [queue2Adjust]

theorem queue2Exec_empty : queue2Exec (Queue2Op.empty : Queue2Op β) [] = ([], []) := by
  simp [queue2Exec]

theorem queue2Exec_enq (x : β) (xs ys : List β) :
    queue2Exec (.enq x) [(xs, ys)] = queue2Adjust (x :: xs, ys) := by simp [queue2Exec]

theorem queue2Exec_deq (xs ys : List β) :
    queue2Exec .deq [(xs, ys)] = queue2Adjust (xs, ys.tail) := by simp [queue2Exec]

theorem queue2Cost_empty : queue2Cost (Queue2Op.empty : Queue2Op β) [] = 0 := by
  simp [queue2Cost]

theorem queue2Cost_enq (x : β) (xs ys : List β) :
    queue2Cost (.enq x) [(xs, ys)] = 1 + (if ys = [] then xs.length + 1 else 0) := by
  simp [queue2Cost]

theorem queue2Cost_deq (xs ys : List β) :
    queue2Cost .deq [(xs, ys)] = if ys.tail = [] then xs.length else 0 := by
  simp [queue2Cost]

theorem queue2U_empty : queue2U (Queue2Op.empty : Queue2Op β) [] = 0 := by simp [queue2U]

theorem queue2U_enq (x : β) (ss : List (List β × List β)) : queue2U (.enq x) ss = 2 := by
  simp [queue2U]

theorem queue2U_deq (ss : List (List β × List β)) : queue2U .deq ss = 0 := by simp [queue2U]

theorem queue2Enq_sum (x : β) (xs ys : List β) :
    (queue2Cost (.enq x) [(xs, ys)] : ℝ) + queue2Phi (queue2Exec (.enq x) [(xs, ys)]) =
      queue2Phi (xs, ys) + 2 := by
  rw [queue2Cost_enq, queue2Exec_enq]
  by_cases h : ys = []
  · rw [ite_eq_left h]
    have hadj : queue2Adjust (x :: xs, ys) = ([], (x :: xs).reverse) := by
      rw [queue2Adjust_eq]
      simp [h]
    have h0 : queue2Phi ([], (x :: xs).reverse) = 0 := by simp [queue2Phi]
    have h1 : queue2Phi (xs, ys) = (xs.length : ℝ) := rfl
    rw [hadj, h0, h1]
    push_cast
    ring
  · rw [ite_eq_right h]
    have hadj : queue2Adjust (x :: xs, ys) = (x :: xs, ys) := by
      rw [queue2Adjust_eq]
      simp [h]
    have h1 : queue2Phi (x :: xs, ys) = queue2Phi (xs, ys) + 1 := by
      simp only [queue2Phi, List.length_cons]
      push_cast
      ring
    rw [hadj, h1]
    push_cast
    ring

theorem queue2Deq_sum (xs ys : List β) :
    (queue2Cost .deq [(xs, ys)] : ℝ) + queue2Phi (queue2Exec .deq [(xs, ys)]) =
      queue2Phi (xs, ys) := by
  rw [queue2Cost_deq, queue2Exec_deq]
  by_cases h : ys.tail = []
  · rw [ite_eq_left h]
    have hadj : queue2Adjust (xs, ys.tail) = ([], xs.reverse) := by
      rw [queue2Adjust_eq]
      simp [h]
    have h0 : queue2Phi ([], xs.reverse) = 0 := by simp [queue2Phi]
    have h1 : queue2Phi (xs, ys) = (xs.length : ℝ) := rfl
    rw [hadj, h0, h1]
    ring
  · rw [ite_eq_right h]
    have hadj : queue2Adjust (xs, ys.tail) = (xs, ys.tail) := by
      rw [queue2Adjust_eq]
      simp [h]
    rw [hadj]
    simp [queue2Phi]

/-- The `interpretation Amortized` for the queue with `adjust`. -/
def queue2Amortized : AmortizedData (Queue2Op β) (List β × List β) where
  arity := queue2Arity
  exec := queue2Exec
  inv := fun _ => True
  cost := queue2Cost
  Phi := queue2Phi
  U := queue2U
  inv_exec := by intro f ss _ _; trivial
  ppos := by
    intro s _
    simp [queue2Phi]
  U_bound := by
    intro f ss _ hlen
    cases f with
    | empty =>
      cases ss with
      | nil =>
        rw [queue2Exec_empty, queue2Cost_empty, queue2U_empty]
        simp only [List.map_nil, List.sum_nil]
        simp [queue2Phi]
      | cons s ss => simp [queue2Arity] at hlen
    | enq x =>
      cases ss with
      | nil => simp [queue2Arity] at hlen
      | cons q ss =>
        cases ss with
        | nil =>
          obtain ⟨xs, ys⟩ := q
          rw [queue2U_enq]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          have h := queue2Enq_sum x xs ys
          linarith
        | cons _ _ => simp [queue2Arity] at hlen
    | deq =>
      cases ss with
      | nil => simp [queue2Arity] at hlen
      | cons q ss =>
        cases ss with
        | nil =>
          obtain ⟨xs, ys⟩ := q
          rw [queue2U_deq]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          have h := queue2Deq_sum xs ys
          linarith
        | cons _ _ => simp [queue2Arity] at hlen

/- ### Queue with `balance` (`Queue3`) -/

inductive Queue3Op (β : Type u) where
  | empty : Queue3Op β
  | enq : β → Queue3Op β
  | deq : Queue3Op β

def queue3Arity : Queue3Op β → ℕ
  | .empty => 0
  | .enq _ => 1
  | .deq => 1

/-- `balance`: if the back list is too long, move it to the front
(`ys @ rev xs`) and empty the back. -/
def queue3Balance : List β × List β → List β × List β
  | (xs, ys) => if xs.length ≤ ys.length then (xs, ys) else ([], ys ++ xs.reverse)

def queue3Exec : Queue3Op β → List (List β × List β) → List β × List β
  | .empty, _ => ([], [])
  | .enq x, [(xs, ys)] => queue3Balance (x :: xs, ys)
  | .deq, [(xs, ys)] => queue3Balance (xs, ys.tail)
  | _, _ => ([], [])

/-- Note the asymmetry in Isabelle's cost: `Deq` charges
`size xs + (size ys - 1)` when it has to balance, i.e. it charges
for the elements it moves. -/
def queue3Cost : Queue3Op β → List (List β × List β) → ℕ
  | .empty, _ => 0
  | .enq _, [(xs, ys)] => 1 + (if xs.length + 1 ≤ ys.length then 0 else xs.length + 1 + ys.length)
  | .deq, [(xs, ys)] => if xs.length ≤ ys.length - 1 then 0 else xs.length + (ys.length - 1)
  | _, _ => 0

/-- The invariant: the back list is never longer than the front. -/
def queue3Inv : List β × List β → Prop
  | (xs, ys) => xs.length ≤ ys.length

/-- `Φ (xs, ys) = 2 * length xs`. -/
def queue3Phi : List β × List β → ℝ := fun q => 2 * (q.1.length : ℝ)

def queue3U : Queue3Op β → List (List β × List β) → ℝ
  | .empty, _ => 0
  | .enq _, _ => 3
  | .deq, _ => 0

theorem queue3Balance_eq (xs ys : List β) :
    queue3Balance (xs, ys) =
      if xs.length ≤ ys.length then (xs, ys) else ([], ys ++ xs.reverse) := by
  simp [queue3Balance]

theorem queue3Exec_empty : queue3Exec (Queue3Op.empty : Queue3Op β) [] = ([], []) := by
  simp [queue3Exec]

theorem queue3Exec_enq (x : β) (xs ys : List β) :
    queue3Exec (.enq x) [(xs, ys)] = queue3Balance (x :: xs, ys) := by simp [queue3Exec]

theorem queue3Exec_deq (xs ys : List β) :
    queue3Exec .deq [(xs, ys)] = queue3Balance (xs, ys.tail) := by simp [queue3Exec]

theorem queue3Cost_empty : queue3Cost (Queue3Op.empty : Queue3Op β) [] = 0 := by
  simp [queue3Cost]

theorem queue3Cost_enq (x : β) (xs ys : List β) :
    queue3Cost (.enq x) [(xs, ys)] =
      1 + (if xs.length + 1 ≤ ys.length then 0 else xs.length + 1 + ys.length) := by
  simp [queue3Cost]

theorem queue3Cost_deq (xs ys : List β) :
    queue3Cost .deq [(xs, ys)] =
      if xs.length ≤ ys.length - 1 then 0 else xs.length + (ys.length - 1) := by
  simp [queue3Cost]

theorem queue3U_empty : queue3U (Queue3Op.empty : Queue3Op β) [] = 0 := by simp [queue3U]

theorem queue3U_enq (x : β) (ss : List (List β × List β)) : queue3U (.enq x) ss = 3 := by
  simp [queue3U]

theorem queue3U_deq (ss : List (List β × List β)) : queue3U .deq ss = 0 := by simp [queue3U]

theorem queue3Enq_bound (x : β) (xs ys : List β) :
    (queue3Cost (.enq x) [(xs, ys)] : ℝ) + queue3Phi (queue3Exec (.enq x) [(xs, ys)]) ≤
      queue3Phi (xs, ys) + 3 := by
  rw [queue3Cost_enq, queue3Exec_enq]
  by_cases h : (x :: xs).length ≤ ys.length
  · have h' : xs.length + 1 ≤ ys.length := by simpa using h
    rw [ite_eq_left h', queue3Balance_eq, ite_eq_left h]
    have hPhi : queue3Phi (x :: xs, ys) = queue3Phi (xs, ys) + 2 := by
      simp only [queue3Phi, List.length_cons]
      push_cast
      ring
    rw [hPhi]
    push_cast
    linarith
  · have h' : ¬ xs.length + 1 ≤ ys.length := by simpa using h
    rw [ite_eq_right h', queue3Balance_eq, ite_eq_right h]
    have hPhi0 : queue3Phi ([], ys ++ (x :: xs).reverse) = 0 := by simp [queue3Phi]
    have hPhi : queue3Phi (xs, ys) = 2 * (xs.length : ℝ) := rfl
    have hle : ys.length ≤ xs.length := by omega
    have hleR : (ys.length : ℝ) ≤ (xs.length : ℝ) := by exact_mod_cast hle
    rw [hPhi0, hPhi]
    push_cast
    linarith

theorem queue3Deq_bound (xs ys : List β) :
    (queue3Cost .deq [(xs, ys)] : ℝ) + queue3Phi (queue3Exec .deq [(xs, ys)]) ≤
      queue3Phi (xs, ys) := by
  rw [queue3Cost_deq, queue3Exec_deq]
  by_cases h : xs.length ≤ ys.length - 1
  · rw [ite_eq_left h]
    have htail : (ys.tail).length = ys.length - 1 := List.length_tail
    have h' : xs.length ≤ (ys.tail).length := by rw [htail]; exact h
    rw [queue3Balance_eq, ite_eq_left h']
    have hPhi : queue3Phi (xs, ys.tail) = queue3Phi (xs, ys) := rfl
    rw [hPhi]
    push_cast
    linarith
  · rw [ite_eq_right h]
    have htail : (ys.tail).length = ys.length - 1 := List.length_tail
    by_cases h2 : xs.length ≤ (ys.tail).length
    · exfalso
      exact h (by rw [htail] at h2; exact h2)
    · rw [queue3Balance_eq, ite_eq_right h2]
      have hPhi0 : queue3Phi ([], ys.tail ++ xs.reverse) = 0 := by simp [queue3Phi]
      have hPhi : queue3Phi (xs, ys) = 2 * (xs.length : ℝ) := rfl
      have hle : ys.length ≤ xs.length + 1 := by omega
      have hleR : (ys.length : ℝ) ≤ (xs.length : ℝ) + 1 := by exact_mod_cast hle
      rw [hPhi0, hPhi]
      by_cases hyse : ys = []
      · subst hyse
        have hcost : xs.length + (List.length ([] : List β) - 1) = xs.length := by simp
        rw [hcost]
        linarith
      · have h1 : 1 ≤ ys.length := by
          cases ys with
          | nil => contradiction
          | cons _ _ => exact Nat.le_add_left 1 _
        have hcast : ((xs.length + (ys.length - 1) : ℕ) : ℝ) =
            (xs.length : ℝ) + (ys.length : ℝ) - 1 := by
          rw [Nat.cast_add, Nat.cast_sub h1]
          push_cast
          ring
        have hle2 : ys.length ≤ xs.length + 1 := by omega
        have hleR2 : (ys.length : ℝ) ≤ (xs.length : ℝ) + 1 := by exact_mod_cast hle2
        rw [hcast]
        linarith [hleR2]

/-- The `interpretation Amortized` for the queue with `balance`. -/
def queue3Amortized : AmortizedData (Queue3Op β) (List β × List β) where
  arity := queue3Arity
  exec := queue3Exec
  inv := queue3Inv
  cost := queue3Cost
  Phi := queue3Phi
  U := queue3U
  inv_exec := by
    intro f ss hall hlen
    cases f with
    | empty =>
      cases ss with
      | nil =>
        rw [queue3Exec_empty]
        simp [queue3Inv]
      | cons s ss => simp [queue3Arity] at hlen
    | enq x =>
      cases ss with
      | nil => simp [queue3Arity] at hlen
      | cons q ss =>
        cases ss with
        | nil =>
          obtain ⟨xs, ys⟩ := q
          rw [queue3Exec_enq, queue3Balance_eq]
          by_cases h : (x :: xs).length ≤ ys.length
          · rw [ite_eq_left h]
            exact h
          · rw [ite_eq_right h]
            exact Nat.zero_le _
        | cons _ _ => simp [queue3Arity] at hlen
    | deq =>
      cases ss with
      | nil => simp [queue3Arity] at hlen
      | cons q ss =>
        cases ss with
        | nil =>
          obtain ⟨xs, ys⟩ := q
          rw [queue3Exec_deq, queue3Balance_eq]
          by_cases h : xs.length ≤ (ys.tail).length
          · rw [ite_eq_left h]
            exact h
          · rw [ite_eq_right h]
            exact Nat.zero_le _
        | cons _ _ => simp [queue3Arity] at hlen
  ppos := by
    intro s _
    simp only [queue3Phi]
    positivity
  U_bound := by
    intro f ss _ hlen
    cases f with
    | empty =>
      cases ss with
      | nil =>
        rw [queue3Exec_empty, queue3Cost_empty, queue3U_empty]
        simp only [List.map_nil, List.sum_nil]
        simp [queue3Phi]
      | cons s ss => simp [queue3Arity] at hlen
    | enq x =>
      cases ss with
      | nil => simp [queue3Arity] at hlen
      | cons q ss =>
        cases ss with
        | nil =>
          obtain ⟨xs, ys⟩ := q
          rw [queue3U_enq]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          have h := queue3Enq_bound x xs ys
          linarith
        | cons _ _ => simp [queue3Arity] at hlen
    | deq =>
      cases ss with
      | nil => simp [queue3Arity] at hlen
      | cons q ss =>
        cases ss with
        | nil =>
          obtain ⟨xs, ys⟩ := q
          rw [queue3U_deq]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          have h := queue3Deq_bound xs ys
          linarith
        | cons _ _ => simp [queue3Arity] at hlen

/- ### Dynamic tables, generalised growth factor (`Dyn_Tab2`) -/

inductive DynTab2Op where
  | empty : DynTab2Op
  | ins : DynTab2Op

def dynTab2Arity : DynTab2Op → ℕ
  | .empty => 0
  | .ins => 1

/-- `ins` with growth factor `c`: on overflow the size becomes
`⌈c * l⌉₊`. Noncomputable because `Int.ceil` is. -/
noncomputable def dynTab2Ins (c : ℝ) : ℕ × ℕ → ℕ × ℕ
  | (n, l) => (n + 1, if n < l then l else if l = 0 then 1 else Int.toNat (Int.ceil (c * (l : ℝ))))

noncomputable def dynTab2Exec (c : ℝ) : DynTab2Op → List (ℕ × ℕ) → ℕ × ℕ
  | .empty, _ => (0, 0)
  | .ins, [(n, l)] => dynTab2Ins c (n, l)
  | _, _ => (0, 0)

def dynTab2Cost : DynTab2Op → List (ℕ × ℕ) → ℕ
  | .empty, _ => 1
  | .ins, [(n, l)] => if n < l then 1 else n + 1
  | _, _ => 0

/-- The invariant, with `b = 1 / (c - 1)` folded in:
`l = 0 → n = 0`, else `n ≤ l ∧ (b / a) * l ≤ n`. -/
def dynTab2Inv (a c : ℝ) : ℕ × ℕ → Prop
  | (n, l) => if l = 0 then n = 0 else n ≤ l ∧ (1 / (c - 1) / a) * (l : ℝ) ≤ (n : ℝ)

/-- `Φ (n, l) = a * n - b * l` with `b = 1 / (c - 1)`. -/
noncomputable def dynTab2Phi (a c : ℝ) : ℕ × ℕ → ℝ
  | (n, l) => a * (n : ℝ) - (1 / (c - 1)) * (l : ℝ)

def dynTab2U (a _c : ℝ) : DynTab2Op → List (ℕ × ℕ) → ℝ
  | .empty, _ => 1
  | .ins, _ => a + 1

theorem dynTab2Exec_empty (c : ℝ) : dynTab2Exec c .empty [] = (0, 0) := by simp [dynTab2Exec]

theorem dynTab2Exec_ins (c : ℝ) (n l : ℕ) :
    dynTab2Exec c .ins [(n, l)] = dynTab2Ins c (n, l) := by simp [dynTab2Exec]

theorem dynTab2Cost_empty : dynTab2Cost .empty [] = 1 := by simp [dynTab2Cost]

theorem dynTab2Cost_ins (n l : ℕ) :
    dynTab2Cost .ins [(n, l)] = if n < l then 1 else n + 1 := by simp [dynTab2Cost]

theorem dynTab2U_empty (a c : ℝ) : dynTab2U a c .empty [] = 1 := by simp [dynTab2U]

theorem dynTab2U_ins (a c : ℝ) (ss : List (ℕ × ℕ)) : dynTab2U a c .ins ss = a + 1 := by
  simp [dynTab2U]

/-- The `interpretation Amortized` for dynamic tables with growth
factor `c`, for `c > 1` and `a ≥ c / (c - 1)` (the locale
`Dyn_Tab2`'s parameters and assumptions). -/
noncomputable def dynTab2Amortized (a c : ℝ) (hc : 1 < c) (ha : c / (c - 1) ≤ a) :
    AmortizedData DynTab2Op (ℕ × ℕ) where
  arity := dynTab2Arity
  exec := dynTab2Exec c
  inv := dynTab2Inv a c
  cost := dynTab2Cost
  Phi := dynTab2Phi a c
  U := dynTab2U a c
  inv_exec := by
    have hc1 : (0 : ℝ) < c - 1 := by linarith
    have hcpos : (0 : ℝ) < c := by linarith
    have ha0 : (0 : ℝ) < a := by
      have h : (0 : ℝ) < c / (c - 1) := div_pos hcpos hc1
      linarith
    have hca : c ≤ a * (c - 1) := (div_le_iff₀ hc1).mp ha
    have hba : (1 / (c - 1) / a) ≤ 1 := by
      rw [div_div, div_le_one (by positivity)]
      linarith [hca, hcpos]
    intro f ss hall hlen
    cases f with
    | empty =>
      cases ss with
      | nil =>
        rw [dynTab2Exec_empty]
        simp [dynTab2Inv]
      | cons s ss => simp [dynTab2Arity] at hlen
    | ins =>
      cases ss with
      | nil => simp [dynTab2Arity] at hlen
      | cons p ss =>
        cases ss with
        | nil =>
          obtain ⟨n, l⟩ := p
          have hinv : dynTab2Inv a c (n, l) := hall _ (by simp)
          rw [dynTab2Exec_ins]
          by_cases hl : l = 0
          · subst hl
            have hn : n = 0 := by simp [dynTab2Inv] at hinv; exact hinv
            subst hn
            have hexec : dynTab2Ins c (0, 0) = (1, 1) := by
              change (0 + 1, if (0 : ℕ) < 0 then (0 : ℕ) else
                  if (0 : ℕ) = 0 then 1 else
                    Int.toNat (Int.ceil (c * ((0 : ℕ) : ℝ)))) = (1, 1)
              rw [ite_eq_right (show ¬(0 : ℕ) < 0 by norm_num), ite_eq_left (rfl : (0 : ℕ) = 0)]
            rw [hexec]
            simp only [dynTab2Inv, ite_eq_right (show (1 : ℕ) ≠ 0 by norm_num)]
            refine ⟨by norm_num, ?_⟩
            rw [Nat.cast_one, mul_one]
            exact hba
          · have hn : n ≤ l ∧ (1 / (c - 1) / a) * (l : ℝ) ≤ (n : ℝ) := by
              simp only [dynTab2Inv, ite_eq_right hl] at hinv
              exact hinv
            by_cases hnl : n < l
            · have hexec : dynTab2Ins c (n, l) = (n + 1, l) := by
                change (n + 1, if n < l then l else if l = 0 then 1 else
                    Int.toNat (Int.ceil (c * (l : ℝ)))) = (n + 1, l)
                rw [ite_eq_left hnl]
              rw [hexec]
              simp only [dynTab2Inv, ite_eq_right hl]
              refine ⟨by omega, by push_cast; linarith [hn.2]⟩
            · have hnl' : n = l := by omega
              subst hnl'
              have hexec : dynTab2Ins c (n, n) =
                  (n + 1, Int.toNat (Int.ceil (c * (n : ℝ)))) := by
                change (n + 1, if n < n then n else if n = 0 then 1 else
                    Int.toNat (Int.ceil (c * (n : ℝ)))) =
                  (n + 1, Int.toNat (Int.ceil (c * (n : ℝ))))
                rw [ite_eq_right hnl, ite_eq_right hl]
              rw [hexec]
              have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
                have : 1 ≤ n := by omega
                exact_mod_cast this
              have hceil : (1 : ℤ) < Int.ceil (c * (n : ℝ)) := by
                rw [Int.lt_ceil]
                push_cast
                have hpos : (0 : ℝ) < (c - 1) * (n : ℝ) := mul_pos hc1 (by linarith)
                have hceil2 : c * (n : ℝ) = (n : ℝ) + (c - 1) * (n : ℝ) := by ring
                rw [hceil2]
                linarith [hpos, hn1]
              have hm0 : Int.toNat (Int.ceil (c * (n : ℝ))) ≠ 0 := by
                by_contra h0
                rw [Int.toNat_eq_zero] at h0
                omega
              have hmR : ((Int.toNat (Int.ceil (c * (n : ℝ))) : ℕ) : ℝ) =
                  (Int.ceil (c * (n : ℝ)) : ℝ) := by
                have h0 : (0 : ℤ) ≤ Int.ceil (c * (n : ℝ)) := by omega
                exact_mod_cast Int.toNat_of_nonneg h0
              have hlt : n < Int.toNat (Int.ceil (c * (n : ℝ))) := by
                have h1 : (n : ℝ) < (Int.ceil (c * (n : ℝ)) : ℝ) := by
                  have hpos : (0 : ℝ) < (c - 1) * (n : ℝ) := mul_pos hc1 (by linarith)
                  have h2 : (n : ℝ) < c * (n : ℝ) := by
                    have hceil2 : c * (n : ℝ) = (n : ℝ) + (c - 1) * (n : ℝ) := by ring
                    rw [hceil2]
                    linarith [hpos, hn1]
                  exact lt_of_lt_of_le h2 (Int.le_ceil _)
                rw [← hmR] at h1
                exact_mod_cast h1
              have hba' : (1 / (c - 1) / a) *
                  ((Int.toNat (Int.ceil (c * (n : ℝ))) : ℕ) : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
                rw [div_div, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
                have hmle : ((Int.toNat (Int.ceil (c * (n : ℝ))) : ℕ) : ℝ) ≤ c * (n : ℝ) + 1 := by
                  rw [hmR]
                  have h := Int.ceil_lt_add_one (c * (n : ℝ))
                  have h' : (Int.ceil (c * (n : ℝ)) : ℝ) ≤ c * (n : ℝ) + 1 := by
                    exact_mod_cast le_of_lt h
                  exact h'
                have hge : (c : ℝ) ≤ (c - 1) * a := by linarith [hca]
                have hge2 : ((n : ℝ) + 1) * c ≤ ((n : ℝ) + 1) * ((c - 1) * a) :=
                  mul_le_mul_of_nonneg_left hge (by linarith)
                have hge3 : ((n : ℝ) + 1) * c = c * (n : ℝ) + c := by ring
                have hcast : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; ring
                rw [hcast]
                linarith [hmle, hge2, hge3, hcpos]
              simp only [dynTab2Inv, ite_eq_right hm0]
              refine ⟨Nat.succ_le_of_lt hlt, ?_⟩
              exact hba'
        | cons _ _ => simp [dynTab2Arity] at hlen
  ppos := by
    have hc1 : (0 : ℝ) < c - 1 := by linarith
    have ha0 : (0 : ℝ) < a := by
      have hca : c ≤ a * (c - 1) := (div_le_iff₀ hc1).mp ha
      have h : (0 : ℝ) < c / (c - 1) := div_pos (by linarith) hc1
      linarith
    have hane : (a : ℝ) ≠ 0 := ne_of_gt ha0
    intro p hp
    obtain ⟨n, l⟩ := p
    by_cases hl : l = 0
    · subst hl
      have hn : n = 0 := by simp [dynTab2Inv] at hp; exact hp
      simp [dynTab2Phi, hn]
    · have hn : n ≤ l ∧ (1 / (c - 1) / a) * (l : ℝ) ≤ (n : ℝ) := by
        simp only [dynTab2Inv, ite_eq_right hl] at hp
        exact hp
      show (0 : ℝ) ≤ a * (n : ℝ) - (1 / (c - 1)) * (l : ℝ)
      have hid : a * (n : ℝ) - (1 / (c - 1)) * (l : ℝ) =
          a * ((n : ℝ) - (1 / (c - 1) / a) * (l : ℝ)) := by
        field_simp
      rw [hid]
      exact mul_nonneg (le_of_lt ha0) (by linarith [hn.2])
  U_bound := by
    have hc1 : (0 : ℝ) < c - 1 := by linarith
    have hcpos : (0 : ℝ) < c := by linarith
    have ha0 : (0 : ℝ) < a := by
      have h : (0 : ℝ) < c / (c - 1) := div_pos hcpos hc1
      linarith
    have hb : (0 : ℝ) < 1 / (c - 1) := div_pos (by norm_num) hc1
    have hc_ne : (c - 1 : ℝ) ≠ 0 := ne_of_gt hc1
    intro f ss hall hlen
    cases f with
    | empty =>
      cases ss with
      | nil =>
        rw [dynTab2Exec_empty, dynTab2Cost_empty, dynTab2U_empty]
        simp only [List.map_nil, List.sum_nil]
        simp [dynTab2Phi]
      | cons s ss => simp [dynTab2Arity] at hlen
    | ins =>
      cases ss with
      | nil => simp [dynTab2Arity] at hlen
      | cons p ss =>
        cases ss with
        | nil =>
          obtain ⟨n, l⟩ := p
          have hinv : dynTab2Inv a c (n, l) := hall _ (by simp)
          rw [dynTab2Exec_ins, dynTab2Cost_ins, dynTab2U_ins]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          by_cases hl : l = 0
          · subst hl
            have hn : n = 0 := by simp [dynTab2Inv] at hinv; exact hinv
            subst hn
            have hexec : dynTab2Ins c (0, 0) = (1, 1) := by
              change (0 + 1, if (0 : ℕ) < 0 then (0 : ℕ) else
                  if (0 : ℕ) = 0 then 1 else
                    Int.toNat (Int.ceil (c * ((0 : ℕ) : ℝ)))) = (1, 1)
              rw [ite_eq_right (show ¬(0 : ℕ) < 0 by norm_num), ite_eq_left (rfl : (0 : ℕ) = 0)]
            have hcost : (if (0 : ℕ) < 0 then (1 : ℕ) else 0 + 1) = 1 := by norm_num
            have hPhi1 : dynTab2Phi a c (1, 1) = a - 1 / (c - 1) := by simp [dynTab2Phi]
            have hPhi0 : dynTab2Phi a c (0, 0) = 0 := by simp [dynTab2Phi]
            rw [hexec, hcost, hPhi1, hPhi0]
            push_cast
            linarith [hb]
          · have hn : n ≤ l ∧ (1 / (c - 1) / a) * (l : ℝ) ≤ (n : ℝ) := by
              simp only [dynTab2Inv, ite_eq_right hl] at hinv
              exact hinv
            by_cases hnl : n < l
            · have hexec : dynTab2Ins c (n, l) = (n + 1, l) := by
                change (n + 1, if n < l then l else if l = 0 then 1 else
                    Int.toNat (Int.ceil (c * (l : ℝ)))) = (n + 1, l)
                rw [ite_eq_left hnl]
              have hcost : (if n < l then (1 : ℕ) else n + 1) = 1 := by rw [ite_eq_left hnl]
              have hPhi : dynTab2Phi a c (n + 1, l) = dynTab2Phi a c (n, l) + a := by
                simp only [dynTab2Phi]
                push_cast
                ring
              rw [hexec, hcost, hPhi]
              push_cast
              linarith
            · have hnl' : n = l := by omega
              subst hnl'
              have hexec : dynTab2Ins c (n, n) =
                  (n + 1, Int.toNat (Int.ceil (c * (n : ℝ)))) := by
                change (n + 1, if n < n then n else if n = 0 then 1 else
                    Int.toNat (Int.ceil (c * (n : ℝ)))) =
                  (n + 1, Int.toNat (Int.ceil (c * (n : ℝ))))
                rw [ite_eq_right hnl, ite_eq_right hl]
              have hcost : (if n < n then (1 : ℕ) else n + 1) = n + 1 := by
                rw [ite_eq_right (Nat.lt_irrefl n)]
              have hmR : ((Int.toNat (Int.ceil (c * (n : ℝ))) : ℕ) : ℝ) =
                  (Int.ceil (c * (n : ℝ)) : ℝ) := by
                have hceil : (1 : ℤ) < Int.ceil (c * (n : ℝ)) := by
                  rw [Int.lt_ceil]
                  push_cast
                  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by
                    exact_mod_cast (show 1 ≤ n by omega)
                  have hpos : (0 : ℝ) < (c - 1) * (n : ℝ) := mul_pos hc1 (by linarith)
                  have hceil2 : c * (n : ℝ) = (n : ℝ) + (c - 1) * (n : ℝ) := by ring
                  rw [hceil2]
                  linarith [hpos, hn1]
                have h0 : (0 : ℤ) ≤ Int.ceil (c * (n : ℝ)) := by omega
                exact_mod_cast Int.toNat_of_nonneg h0
              have hB0 : (0 : ℝ) ≤ 1 / (c - 1) := div_nonneg (by norm_num) (le_of_lt hc1)
              have hstep : (1 / (c - 1)) * ((Int.toNat (Int.ceil (c * (n : ℝ))) : ℕ) : ℝ) ≥
                  (1 / (c - 1)) * (c * (n : ℝ)) := by
                apply mul_le_mul_of_nonneg_left _ hB0
                rw [hmR]
                exact Int.le_ceil _
              have hBc : (1 / (c - 1)) * c = 1 + 1 / (c - 1) := by
                field_simp
                ring
              have hbm : (1 / (c - 1)) * ((Int.toNat (Int.ceil (c * (n : ℝ))) : ℕ) : ℝ) ≥
                  (n : ℝ) + (1 / (c - 1)) * (n : ℝ) := by
                have h1 : (1 / (c - 1)) * (c * (n : ℝ)) =
                    (n : ℝ) + (1 / (c - 1)) * (n : ℝ) := by
                  calc (1 / (c - 1)) * (c * (n : ℝ)) = ((1 / (c - 1)) * c) * (n : ℝ) := by ring
                    _ = (1 + 1 / (c - 1)) * (n : ℝ) := by rw [hBc]
                    _ = (n : ℝ) + (1 / (c - 1)) * (n : ℝ) := by ring
                linarith [hstep, h1]
              rw [hexec, hcost]
              simp only [dynTab2Phi]
              push_cast
              linarith [hbm]
        | cons _ _ => simp [dynTab2Arity] at hlen


end Amortized

end Cslib.Algorithms.Lean
