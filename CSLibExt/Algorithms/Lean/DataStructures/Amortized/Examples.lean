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
import Mathlib.Tactic

/-!
# Amortized-analysis examples (1)

The framework examples of `Amortized_Examples.thy`, as
`AmortizedData` instances: the binary counter (`Bin_Counter`, book
§19.2; `binCounter_a_incr` says the amortized cost of `incr` is
exactly 2), the stack with multipop (`Multipop`), dynamic tables,
insert only (`Dyn_Tab1`, book §19.3.1), and the two-list queue
(`Queue`, after Okasaki). These are the AFP formalisations under
the generic framework; they are not the CLRS-style `TimeM`
developments in `BinaryCounter`, `Stack/Multipop`,
`DynamicTable`, and `Queue/Amortized` elsewhere in this library,
which use different carriers and cost models.

Source: the AFP entry `Amortized Complexity` (Tobias Nipkow,
2014; BSD), `thys/Amortized_Complexity/Amortized_Examples.thy`
(https://isa-afp.org/entries/Amortized_Complexity.html)
(`Bin_Counter`, `Multipop`, `Dyn_Tab1`, `Queue`). Book: Ch. 19
sections 19.2-19.3. The instances and proofs are re-established in
Lean; Isabelle-derived names are kept for traceability.
-/

@[expose] public section

set_option autoImplicit false

universe u

namespace Cslib.Algorithms.Lean
namespace Amortized

variable {β : Type u}

/- ## Amortized examples (`Amortized_Examples.thy`) -/

/-- The examples of the amortized framework in the same AFP entry:
the binary counter (book §19.2), the stack with multipop, the
dynamic tables (book §19.3) and the Okasaki queues. Each locale's
`interpretation Amortized` becomes an `AmortizedData` instance.
Isabelle's `fun` equations cover only arity-matching argument
lists; as for `skewExec`/`skewCost`/`skewU`, Lean totalises them
with fallbacks, never used on a `wf` history. -/

/- ### Binary counter (`Bin_Counter`, book §19.2) -/

inductive BinCounterOp where
  | empty : BinCounterOp
  | incr : BinCounterOp

def binCounterArity : BinCounterOp → ℕ
  | .empty => 0
  | .incr => 1

/-- `incr`: flip the leading `True`s until a `False` (or the end). -/
def binCounterIncr : List Bool → List Bool
  | [] => [true]
  | false :: bs => true :: bs
  | true :: bs => false :: binCounterIncr bs

/-- `t_incr`: the time function of `incr`. -/
def binCounterTIncr : List Bool → ℕ
  | [] => 1
  | false :: _ => 1
  | true :: bs => binCounterTIncr bs + 1

/-- `Φ bs`: the number of `True`s. -/
def binCounterPhi : List Bool → ℝ := fun bs => (bs.count true : ℝ)

def binCounterExec : BinCounterOp → List (List Bool) → List Bool
  | .empty, _ => []
  | .incr, [bs] => binCounterIncr bs
  | _, _ => []

def binCounterCost : BinCounterOp → List (List Bool) → ℕ
  | .empty, _ => 1
  | .incr, [bs] => binCounterTIncr bs
  | _, _ => 0

def binCounterU : BinCounterOp → List (List Bool) → ℝ
  | .empty, _ => 1
  | .incr, _ => 2

theorem binCounterExec_empty : binCounterExec .empty [] = [] := by simp [binCounterExec]

theorem binCounterExec_incr (bs : List Bool) :
    binCounterExec .incr [bs] = binCounterIncr bs := by simp [binCounterExec]

theorem binCounterCost_empty : binCounterCost .empty [] = 1 := by simp [binCounterCost]

theorem binCounterCost_incr (bs : List Bool) :
    binCounterCost .incr [bs] = binCounterTIncr bs := by simp [binCounterCost]

theorem binCounterU_empty : binCounterU .empty [] = 1 := by simp [binCounterU]

theorem binCounterU_incr (ss : List (List Bool)) : binCounterU .incr ss = 2 := by
  simp [binCounterU]

/-- `a_incr`: the amortized cost of `incr` is exactly 2. -/
theorem binCounter_a_incr (bs : List Bool) :
    (binCounterTIncr bs : ℝ) + binCounterPhi (binCounterIncr bs) -
      binCounterPhi bs = 2 := by
  induction bs with
  | nil => norm_num [binCounterIncr, binCounterTIncr, binCounterPhi, List.count_cons_self]
  | cons b bs ih =>
    cases b with
    | false =>
      have e1 : binCounterIncr (false :: bs) = true :: bs := rfl
      have e2 : binCounterTIncr (false :: bs) = 1 := rfl
      have e3 : binCounterPhi (false :: bs) = binCounterPhi bs := by
        simp [binCounterPhi, List.count_cons_of_ne]
      have e4 : binCounterPhi (true :: bs) = binCounterPhi bs + 1 := by
        simp [binCounterPhi, List.count_cons_self]
      rw [e1, e2, e3, e4]
      push_cast
      ring
    | true =>
      have e1 : binCounterIncr (true :: bs) = false :: binCounterIncr bs := rfl
      have e2 : binCounterTIncr (true :: bs) = binCounterTIncr bs + 1 := rfl
      have e3 : binCounterPhi (true :: bs) = binCounterPhi bs + 1 := by
        simp [binCounterPhi, List.count_cons_self]
      have e4 : binCounterPhi (false :: binCounterIncr bs) =
          binCounterPhi (binCounterIncr bs) := by
        simp [binCounterPhi, List.count_cons_of_ne]
      rw [e1, e2, e3, e4]
      push_cast
      linarith

/-- The `interpretation Amortized` for the binary counter. -/
def binCounterAmortized : AmortizedData BinCounterOp (List Bool) where
  arity := binCounterArity
  exec := binCounterExec
  inv := fun _ => True
  cost := binCounterCost
  Phi := binCounterPhi
  U := binCounterU
  inv_exec := by intro f ss _ _; trivial
  ppos := by
    intro s _
    simp [binCounterPhi]
  U_bound := by
    intro f ss _ hlen
    cases f with
    | empty =>
      cases ss with
      | nil =>
        rw [binCounterExec_empty, binCounterCost_empty, binCounterU_empty]
        simp [binCounterPhi]
      | cons s ss => simp [binCounterArity] at hlen
    | incr =>
      cases ss with
      | nil => simp [binCounterArity] at hlen
      | cons bs ss =>
        cases ss with
        | nil =>
          rw [binCounterExec_incr, binCounterCost_incr, binCounterU_incr]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          have h := binCounter_a_incr bs
          linarith
        | cons _ _ => simp [binCounterArity] at hlen

/- ### Stack with multipop (`Multipop`) -/

inductive MultipopOp (β : Type u) where
  | empty : MultipopOp β
  | push : β → MultipopOp β
  | pop : ℕ → MultipopOp β

def multipopArity : MultipopOp β → ℕ
  | .empty => 0
  | .push _ => 1
  | .pop _ => 1

def multipopExec : MultipopOp β → List (List β) → List β
  | .empty, _ => []
  | .push x, [xs] => x :: xs
  | .pop n, [xs] => xs.drop n
  | _, _ => []

def multipopCost : MultipopOp β → List (List β) → ℕ
  | .empty, _ => 1
  | .push _, _ => 1
  | .pop n, [xs] => min n xs.length
  | _, _ => 0

/-- `Φ xs = length xs`: the number of elements that a later `Pop`
can remove. -/
def multipopPhi : List β → ℝ := fun xs => (xs.length : ℝ)

def multipopU : MultipopOp β → List (List β) → ℝ
  | .empty, _ => 1
  | .push _, _ => 2
  | .pop _, _ => 0

theorem multipopExec_empty : multipopExec (MultipopOp.empty : MultipopOp β) [] = [] := by
  simp [multipopExec]

theorem multipopExec_push (x : β) (xs : List β) :
    multipopExec (.push x) [xs] = x :: xs := by simp [multipopExec]

theorem multipopExec_pop (n : ℕ) (xs : List β) :
    multipopExec (.pop n) [xs] = xs.drop n := by simp [multipopExec]

theorem multipopCost_empty : multipopCost (MultipopOp.empty : MultipopOp β) [] = 1 := by
  simp [multipopCost]

theorem multipopCost_push (x : β) (ss : List (List β)) : multipopCost (.push x) ss = 1 := by
  simp [multipopCost]

theorem multipopCost_pop (n : ℕ) (xs : List β) :
    multipopCost (.pop n) [xs] = min n xs.length := by simp [multipopCost]

theorem multipopU_empty : multipopU (MultipopOp.empty : MultipopOp β) [] = 1 := by
  simp [multipopU]

theorem multipopU_push (x : β) (ss : List (List β)) : multipopU (.push x) ss = 2 := by
  simp [multipopU]

theorem multipopU_pop (n : ℕ) (ss : List (List β)) : multipopU (.pop n) ss = 0 := by
  simp [multipopU]

/-- The `interpretation Amortized` for the stack with multipop. -/
def multipopAmortized : AmortizedData (MultipopOp β) (List β) where
  arity := multipopArity
  exec := multipopExec
  inv := fun _ => True
  cost := multipopCost
  Phi := multipopPhi
  U := multipopU
  inv_exec := by intro f ss _ _; trivial
  ppos := by
    intro s _
    simp [multipopPhi]
  U_bound := by
    intro f ss _ hlen
    cases f with
    | empty =>
      cases ss with
      | nil =>
        rw [multipopExec_empty, multipopCost_empty, multipopU_empty]
        simp [multipopPhi]
      | cons s ss => simp [multipopArity] at hlen
    | push x =>
      cases ss with
      | nil => simp [multipopArity] at hlen
      | cons xs ss =>
        cases ss with
        | nil =>
          rw [multipopExec_push, multipopCost_push, multipopU_push]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          have hphi : multipopPhi (x :: xs) = multipopPhi xs + 1 := by
            simp only [multipopPhi, List.length_cons]
            push_cast
            ring
          rw [hphi]
          push_cast
          linarith
        | cons _ _ => simp [multipopArity] at hlen
    | pop n =>
      cases ss with
      | nil => simp [multipopArity] at hlen
      | cons xs ss =>
        cases ss with
        | nil =>
          rw [multipopExec_pop, multipopCost_pop, multipopU_pop]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          have hphi : multipopPhi xs = (xs.length : ℝ) := rfl
          rw [hphi]
          by_cases hle : n ≤ xs.length
          · have hmin : ((min n xs.length : ℕ) : ℝ) = (n : ℝ) := by
              rw [min_eq_left hle]
            have hdrop : multipopPhi (xs.drop n) = (xs.length : ℝ) - (n : ℝ) := by
              have h1 : (xs.drop n).length = xs.length - n := List.length_drop
              rw [show multipopPhi (xs.drop n) = ((xs.drop n).length : ℝ) from rfl, h1,
                Nat.cast_sub hle]
            rw [hmin, hdrop]
            linarith
          · push Not at hle
            have hmin : ((min n xs.length : ℕ) : ℝ) = (xs.length : ℝ) := by
              rw [min_eq_right (le_of_lt hle)]
            have hdrop : xs.drop n = [] := List.drop_eq_nil_of_le (le_of_lt hle)
            have hphi2 : multipopPhi (xs.drop n) = 0 := by rw [hdrop]; simp [multipopPhi]
            rw [hmin, hphi2]
            linarith
        | cons _ _ => simp [multipopArity] at hlen

/- ### Dynamic tables: insert only (`Dyn_Tab1`, book §19.3.1) -/

/-- A table is `(n, l)`: `n` occupied cells out of `l` allocated. -/
inductive DynTab1Op where
  | empty : DynTab1Op
  | ins : DynTab1Op

def dynTab1Arity : DynTab1Op → ℕ
  | .empty => 0
  | .ins => 1

def dynTab1Exec : DynTab1Op → List (ℕ × ℕ) → ℕ × ℕ
  | .empty, _ => (0, 0)
  | .ins, [(n, l)] => (n + 1, if n < l then l else if l = 0 then 1 else 2 * l)
  | _, _ => (0, 0)

def dynTab1Cost : DynTab1Op → List (ℕ × ℕ) → ℕ
  | .empty, _ => 1
  | .ins, [(n, l)] => if n < l then 1 else n + 1
  | _, _ => 0

/-- The invariant: `l = 0 → n = 0`, else `n ≤ l ∧ l < 2n`. -/
def dynTab1Inv : ℕ × ℕ → Prop
  | (n, l) => if l = 0 then n = 0 else n ≤ l ∧ l < 2 * n

/-- `Φ (n, l) = 2n - l`. -/
def dynTab1Phi : ℕ × ℕ → ℝ
  | (n, l) => 2 * (n : ℝ) - (l : ℝ)

def dynTab1U : DynTab1Op → List (ℕ × ℕ) → ℝ
  | .empty, _ => 1
  | .ins, _ => 3

theorem dynTab1Exec_empty : dynTab1Exec .empty [] = (0, 0) := by simp [dynTab1Exec]

theorem dynTab1Exec_ins (n l : ℕ) :
    dynTab1Exec .ins [(n, l)] = (n + 1, if n < l then l else if l = 0 then 1 else 2 * l) := by
  simp [dynTab1Exec]

theorem dynTab1Cost_empty : dynTab1Cost .empty [] = 1 := by simp [dynTab1Cost]

theorem dynTab1Cost_ins (n l : ℕ) :
    dynTab1Cost .ins [(n, l)] = if n < l then 1 else n + 1 := by simp [dynTab1Cost]

theorem dynTab1U_empty : dynTab1U .empty [] = 1 := by simp [dynTab1U]

theorem dynTab1U_ins (ss : List (ℕ × ℕ)) : dynTab1U .ins ss = 3 := by simp [dynTab1U]

/-- The `interpretation Amortized` for dynamic tables, insert only. -/
def dynTab1Amortized : AmortizedData DynTab1Op (ℕ × ℕ) where
  arity := dynTab1Arity
  exec := dynTab1Exec
  inv := dynTab1Inv
  cost := dynTab1Cost
  Phi := dynTab1Phi
  U := dynTab1U
  inv_exec := by
    intro f ss hall hlen
    cases f with
    | empty =>
      cases ss with
      | nil =>
        rw [dynTab1Exec_empty]
        simp [dynTab1Inv]
      | cons s ss => simp [dynTab1Arity] at hlen
    | ins =>
      cases ss with
      | nil => simp [dynTab1Arity] at hlen
      | cons p ss =>
        cases ss with
        | nil =>
          obtain ⟨n, l⟩ := p
          have hinv : dynTab1Inv (n, l) := hall _ (by simp)
          rw [dynTab1Exec_ins]
          by_cases hl : l = 0
          · subst hl
            have hn : n = 0 := by simp [dynTab1Inv] at hinv; exact hinv
            subst hn
            simp [dynTab1Inv]
          · have hn : n ≤ l ∧ l < 2 * n := by
              simp only [dynTab1Inv, ite_eq_right hl] at hinv
              exact hinv
            by_cases hnl : n < l
            · have hexec : (n + 1, if n < l then l else if l = 0 then 1 else 2 * l) = (n + 1, l) := by
                simp [hnl]
              rw [hexec]
              simp only [dynTab1Inv, ite_eq_right hl]
              refine ⟨by omega, by omega⟩
            · have hnl' : n = l := by omega
              subst hnl'
              have hexec : (n + 1, if n < n then n else if n = 0 then 1 else 2 * n) = (n + 1, 2 * n) := by
                simp [hl]
              rw [hexec]
              have h2n : 2 * n ≠ 0 := by omega
              simp only [dynTab1Inv, ite_eq_right h2n]
              refine ⟨by omega, by omega⟩
        | cons _ _ => simp [dynTab1Arity] at hlen
  ppos := by
    intro p hp
    obtain ⟨n, l⟩ := p
    show (0 : ℝ) ≤ 2 * (n : ℝ) - (l : ℝ)
    by_cases hl : l = 0
    · subst hl
      have hn : n = 0 := by simp [dynTab1Inv] at hp; exact hp
      simp [hn]
    · have hn : n ≤ l ∧ l < 2 * n := by
        simp only [dynTab1Inv, ite_eq_right hl] at hp
        exact hp
      have hcast : (l : ℝ) < 2 * (n : ℝ) := by exact_mod_cast hn.2
      linarith
  U_bound := by
    intro f ss hall hlen
    cases f with
    | empty =>
      cases ss with
      | nil =>
        rw [dynTab1Exec_empty, dynTab1Cost_empty, dynTab1U_empty]
        simp only [List.map_nil, List.sum_nil]
        simp [dynTab1Phi]
      | cons s ss => simp [dynTab1Arity] at hlen
    | ins =>
      cases ss with
      | nil => simp [dynTab1Arity] at hlen
      | cons p ss =>
        cases ss with
        | nil =>
          obtain ⟨n, l⟩ := p
          have hinv : dynTab1Inv (n, l) := hall _ (by simp)
          rw [dynTab1Exec_ins, dynTab1Cost_ins, dynTab1U_ins]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          by_cases hl : l = 0
          · subst hl
            have hn : n = 0 := by simp [dynTab1Inv] at hinv; exact hinv
            subst hn
            norm_num [dynTab1Phi]
          · have hn : n ≤ l ∧ l < 2 * n := by
              simp only [dynTab1Inv, ite_eq_right hl] at hinv
              exact hinv
            by_cases hnl : n < l
            · have hexec : (n + 1, if n < l then l else if l = 0 then 1 else 2 * l) = (n + 1, l) := by
                simp [hnl]
              have hcost : (if n < l then (1 : ℕ) else n + 1) = 1 := by simp [hnl]
              have hphi : dynTab1Phi (n + 1, l) = dynTab1Phi (n, l) + 2 := by
                simp only [dynTab1Phi]
                push_cast
                ring
              rw [hexec, hcost, hphi]
              push_cast
              linarith
            · have hnl' : n = l := by omega
              subst hnl'
              have hexec : (n + 1, if n < n then n else if n = 0 then 1 else 2 * n) = (n + 1, 2 * n) := by
                simp [hl]
              have hcost : (if n < n then (1 : ℕ) else n + 1) = n + 1 := by simp
              have hphi : dynTab1Phi (n + 1, 2 * n) = 2 := by
                simp only [dynTab1Phi]
                push_cast
                ring
              have hphi2 : dynTab1Phi (n, n) = (n : ℝ) := by
                simp only [dynTab1Phi]
                ring
              rw [hexec, hcost, hphi, hphi2]
              push_cast
              linarith
        | cons _ _ => simp [dynTab1Arity] at hlen

/- ### Queue (`Queue`, after Okasaki) -/

inductive QueueOp (β : Type u) where
  | empty : QueueOp β
  | enq : β → QueueOp β
  | deq : QueueOp β

def queueArity : QueueOp β → ℕ
  | .empty => 0
  | .enq _ => 1
  | .deq => 1

/-- The queue is `(xs, ys)`: `xs` in reverse order of arrival,
`ys` in order. `deq` moves `xs` over when `ys` is empty. -/
def queueExec : QueueOp β → List (List β × List β) → List β × List β
  | .empty, _ => ([], [])
  | .enq x, [(xs, ys)] => (x :: xs, ys)
  | .deq, [(xs, ys)] => if ys = [] then ([], (xs.reverse).tail) else (xs, ys.tail)
  | _, _ => ([], [])

def queueCost : QueueOp β → List (List β × List β) → ℕ
  | .empty, _ => 0
  | .enq _, [(_xs, _ys)] => 1
  | .deq, [(xs, ys)] => if ys = [] then xs.length else 0
  | _, _ => 0

/-- `Φ (xs, ys) = length xs`: the elements waiting to be moved over. -/
def queuePhi : List β × List β → ℝ := fun q => (q.1.length : ℝ)

def queueU : QueueOp β → List (List β × List β) → ℝ
  | .empty, _ => 0
  | .enq _, _ => 2
  | .deq, _ => 0

theorem queueExec_empty : queueExec (QueueOp.empty : QueueOp β) [] = ([], []) := by
  simp [queueExec]

theorem queueExec_enq (x : β) (xs ys : List β) :
    queueExec (.enq x) [(xs, ys)] = (x :: xs, ys) := by simp [queueExec]

theorem queueExec_deq (xs ys : List β) :
    queueExec .deq [(xs, ys)] =
      if ys = [] then ([], (xs.reverse).tail) else (xs, ys.tail) := by simp [queueExec]

theorem queueCost_empty : queueCost (QueueOp.empty : QueueOp β) [] = 0 := by simp [queueCost]

theorem queueCost_enq (x : β) (xs ys : List β) :
    queueCost (.enq x) [(xs, ys)] = 1 := by simp [queueCost]

theorem queueCost_deq (xs ys : List β) :
    queueCost .deq [(xs, ys)] = if ys = [] then xs.length else 0 := by simp [queueCost]

theorem queueU_empty : queueU (QueueOp.empty : QueueOp β) [] = 0 := by simp [queueU]

theorem queueU_enq (x : β) (ss : List (List β × List β)) : queueU (.enq x) ss = 2 := by
  simp [queueU]

theorem queueU_deq (ss : List (List β × List β)) : queueU .deq ss = 0 := by simp [queueU]

/-- The `interpretation Amortized` for the two-list queue. -/
def queueAmortized : AmortizedData (QueueOp β) (List β × List β) where
  arity := queueArity
  exec := queueExec
  inv := fun _ => True
  cost := queueCost
  Phi := queuePhi
  U := queueU
  inv_exec := by intro f ss _ _; trivial
  ppos := by
    intro s _
    simp [queuePhi]
  U_bound := by
    intro f ss _ hlen
    cases f with
    | empty =>
      cases ss with
      | nil =>
        rw [queueExec_empty, queueCost_empty, queueU_empty]
        simp only [List.map_nil, List.sum_nil]
        simp [queuePhi]
      | cons s ss => simp [queueArity] at hlen
    | enq x =>
      cases ss with
      | nil => simp [queueArity] at hlen
      | cons q ss =>
        cases ss with
        | nil =>
          obtain ⟨xs, ys⟩ := q
          rw [queueExec_enq, queueCost_enq, queueU_enq]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          have hphi : queuePhi (x :: xs, ys) = queuePhi (xs, ys) + 1 := by
            simp only [queuePhi, List.length_cons]
            push_cast
            ring
          rw [hphi]
          push_cast
          linarith
        | cons _ _ => simp [queueArity] at hlen
    | deq =>
      cases ss with
      | nil => simp [queueArity] at hlen
      | cons q ss =>
        cases ss with
        | nil =>
          obtain ⟨xs, ys⟩ := q
          rw [queueExec_deq, queueCost_deq, queueU_deq]
          simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
          have hphi : queuePhi (xs, ys) = (xs.length : ℝ) := rfl
          rw [hphi]
          by_cases hys : ys = []
          · have hexec : (if ys = [] then ([], (xs.reverse).tail) else (xs, ys.tail)) =
                ([], (xs.reverse).tail) := by simp [hys]
            have hcost : (if ys = [] then xs.length else 0) = xs.length := by simp [hys]
            have hphi2 : queuePhi ([], (xs.reverse).tail) = 0 := by simp [queuePhi]
            rw [hexec, hcost, hphi2]
            linarith
          · have hexec : (if ys = [] then ([], (xs.reverse).tail) else (xs, ys.tail)) =
                (xs, ys.tail) := by simp [hys]
            have hcost : (if ys = [] then xs.length else 0) = 0 := by simp [hys]
            have hphi2 : queuePhi (xs, ys.tail) = (xs.length : ℝ) := rfl
            rw [hexec, hcost, hphi2]
            push_cast
            linarith
        | cons _ _ => simp [queueArity] at hlen


end Amortized

end Cslib.Algorithms.Lean
