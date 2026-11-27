/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Online.CompetitiveFramework
public import CSLibExt.Algorithms.Lean.Online.ListUpdate
import Mathlib.Basic.ENNReal.Inv
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

@[expose] public section

namespace Cslib.Algorithms.Lean.Online.CompetitiveFramework

open ListUpdate
open ListUpdate.OnlineListUpdate

/-- Cost of one list-update step: the access cost plus the least inversion count (comparing
first occurrences) between the next list and a free forward move of the accessed item, minimized
over free-move targets. For a list without repeated items this is the number of paid exchanges;
with repeats it can be smaller. -/
def stepCost {α : Type*} [DecidableEq α] (L : List α) (x : α) (L' : List α) :
    ℕ :=
  accessCost L x
    + ((List.range (L.length + 1)).map
        (fun j => inv (freeMove L x j) L')).min?.getD 0

/-- Running cost of a trace of lists: fold `stepCost` from the initial
list over the request/answer trace (answers are successive lists). -/
def traceCost {α : Type*} [DecidableEq α] (M : List α) :
    List (α × List α) → ℕ
  | [] => 0
  | (x, L') :: τ => stepCost M x L' + traceCost L' τ

/-- List update as an online problem over a fixed item list `M` (any list; the lower bound
assumes it nonempty and duplicate-free): legal requests are items of `M`; answers are the list
after serving and rearranging, always a permutation of `M`; the cost of a step is `stepCost`,
which counts paid exchanges when `M` has no repeated items. -/
def listUpdateProblem {α : Type*} [DecidableEq α] (M : List α) :
    OnlineProblem α (List α) where
  legal := fun σ => ∀ x ∈ σ, x ∈ M
  legal_nil := by simp
  legal_prefix := by
    intro σ τ h x hx
    exact h x (List.mem_append.mpr (Or.inl hx))
  feasible := fun τ => (∀ p ∈ τ, p.2.Perm M) ∧ ∀ p ∈ τ, p.1 ∈ M
  feasible_nil := by simp
  feasible_prefix := by
    intro τ τ' h
    exact ⟨fun p hp => h.1 p (List.mem_append.mpr (Or.inl hp)),
      fun p hp => h.2 p (List.mem_append.mpr (Or.inl hp))⟩
  feasible_requests := by
    intro τ h x hx
    rw [List.mem_map] at hx
    obtain ⟨p, hp, rfl⟩ := hx
    exact h.2 p hp
  nonblocking := by
    intro τ r hτ hleg
    refine ⟨M, ?_, ?_⟩
    · intro p hp
      rw [List.mem_append] at hp
      cases hp with
      | inl h => exact hτ.1 p h
      | inr h =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          subst h
          exact List.Perm.refl M
    · intro p hp
      rw [List.mem_append] at hp
      cases hp with
      | inl h => exact hτ.2 p h
      | inr h =>
          simp only [List.mem_cons, List.not_mem_nil, or_false] at h
          subst h
          exact hleg r (List.mem_append.mpr
            (Or.inr (List.mem_singleton.mpr rfl)))
  cost := fun τ => (traceCost M τ : ℝ)
  cost_nonneg := fun _ => by positivity

/-- The list move-to-front holds after serving a request sequence. -/
def mtfListAfter {α : Type*} [DecidableEq α] (M : List α) :
    List α → List α
  | [] => M
  | x :: σ => mtfListAfter (mtf M x) σ

private theorem mtfListAfter_perm {α : Type*} [DecidableEq α]
    (M past : List α) :
    (∀ x ∈ past, x ∈ M) → (mtfListAfter M past).Perm M := by
  induction past generalizing M with
  | nil =>
      intro _
      exact List.Perm.refl M
  | cons x σ ih =>
      intro h
      simp only [mtfListAfter]
      have hx : x ∈ M := h x (List.mem_cons.mpr (Or.inl rfl))
      have hperm : (mtf M x).Perm M := mtf_perm hx
      have hσ : ∀ y ∈ σ, y ∈ mtf M x := fun y hy =>
        (List.Perm.mem_iff hperm.symm).mp
          (h y (List.mem_cons.mpr (Or.inr hy)))
      exact (ih (mtf M x) hσ).trans hperm

private theorem mtfListAfter_append_singleton {α : Type*} [DecidableEq α]
    (M past : List α) (r : α) :
    mtfListAfter M (past ++ [r]) = mtf (mtfListAfter M past) r := by
  induction past generalizing M with
  | nil =>
      change mtfListAfter M [r] = mtf (mtfListAfter M []) r
      simp only [mtfListAfter]
  | cons x σ ih =>
      change mtfListAfter M (x :: (σ ++ [r]))
        = mtf (mtfListAfter M (x :: σ)) r
      simp only [mtfListAfter, ih]

/-- Move-to-front as a causal framework strategy. -/
def mtfStrategy {α : Type*} [DecidableEq α] (M : List α) :
    Strategy α (List α) :=
  fun σ => match σ.reverse with
    | [] => M
    | r :: pastRev => mtf (mtfListAfter M pastRev.reverse) r

private theorem mtfStrategy_append_singleton {α : Type*} [DecidableEq α]
    (M past : List α) (r : α) :
    mtfStrategy M (past ++ [r]) = mtf (mtfListAfter M past) r := by
  have h : (past ++ [r]).reverse = r :: past.reverse := by simp
  unfold mtfStrategy
  rw [h]
  dsimp only
  rw [List.reverse_reverse]

private theorem runFrom_mtf_perm {α : Type*} [DecidableEq α] (M past : List α)
    (σ : List α) : (∀ x ∈ past ++ σ, x ∈ M) →
    ∀ p ∈ runFrom (mtfStrategy M) past σ, p.2.Perm M := by
  induction σ generalizing past with
  | nil =>
      intro _ p hp
      simp only [runFrom] at hp
      simp at hp
  | cons r σ ih =>
      intro h p hp
      simp only [runFrom] at hp
      rw [List.mem_cons] at hp
      cases hp with
      | inl hhead =>
          rw [hhead]
          change (mtfStrategy M (past ++ [r])).Perm M
          rw [mtfStrategy_append_singleton]
          have hrM : r ∈ M := h r
            (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
          have hpast : ∀ y ∈ past, y ∈ M :=
            fun y hy => h y (List.mem_append.mpr (Or.inl hy))
          have hcur := mtfListAfter_perm M past hpast
          have hrmem : r ∈ mtfListAfter M past :=
            (List.Perm.mem_iff hcur.symm).mp hrM
          exact (mtf_perm hrmem).trans hcur
      | inr htail =>
          have h' : ∀ y ∈ (past ++ [r]) ++ σ, y ∈ M := by
            intro y hy
            rw [List.append_assoc] at hy
            exact h y hy
          exact ih (past ++ [r]) h' p htail

theorem mtfStrategy_feasible {α : Type*} [DecidableEq α] (M : List α) :
    StrategyFeasible (listUpdateProblem M) (mtfStrategy M) := by
  intro σ hσ
  have hσ' : ∀ x ∈ σ, x ∈ M := hσ
  refine ⟨?_, ?_⟩
  · intro p hp
    exact runFrom_mtf_perm M [] σ (fun x hx => hσ' x hx) p hp
  · intro p hp
    have hmem : p.1 ∈ (run (mtfStrategy M) σ).map Prod.fst :=
      List.mem_map.mpr ⟨p, hp, rfl⟩
    rw [run_map_fst] at hmem
    exact hσ' p.1 hmem

private theorem min_getD_zero_of_mem (l : List ℕ) (hmem : 0 ∈ l) :
    l.min?.getD 0 = 0 := by
  have h : l.min? = some 0 :=
    List.min?_eq_some_iff.mpr ⟨hmem, fun b _ => Nat.zero_le b⟩
  simp [h]

private theorem findIdx_go_ge {α : Type*} (p : α → Bool) (l : List α)
    (n : ℕ) : n ≤ List.findIdx.go p l n := by
  induction l generalizing n with
  | nil => exact le_rfl
  | cons x xs ih =>
      simp only [List.findIdx.go]
      cases hb : p x with
      | true =>
          simp
      | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          exact le_trans (Nat.le_succ n) (ih (n + 1))

private theorem eq_of_idxOf_zero {α : Type*} [DecidableEq α] (L : List α)
    (x : α) (hx : x ∈ L) (h0 : L.idxOf x = 0) :
    x :: L.erase x = L := by
  cases L with
  | nil => simp at hx
  | cons a t =>
      simp only [List.idxOf, List.findIdx, List.findIdx.go] at h0
      cases hb : (a == x) with
      | true =>
          have hax : a = x := beq_iff_eq.mp hb
          subst hax
          simp
      | false =>
          simp only [hb, Bool.false_eq_true, ↓reduceIte, zero_add] at h0
          have h0' : List.findIdx.go (fun y => y == x) t 1 = 0 := h0
          have hge := findIdx_go_ge (fun y => y == x) t 1
          omega

private theorem freeMove_zero_eq_mtf_of_mem {α : Type*} [DecidableEq α]
    (L : List α) (x : α) (hx : x ∈ L) : freeMove L x 0 = mtf L x := by
  simp only [freeMove, mtf]
  by_cases h : L.idxOf x ≤ 0
  · rw [ite_eq_left h]
    exact (eq_of_idxOf_zero L x hx (Nat.le_zero.mp h)).symm
  · rw [ite_eq_right h]
    simp

private theorem stepCost_mtf {α : Type*} [DecidableEq α] (L : List α)
    (x : α) (hx : x ∈ L) : stepCost L x (mtf L x) = accessCost L x := by
  have h0mem : (0 : ℕ) ∈ List.range (L.length + 1) :=
    List.mem_range.mpr (Nat.succ_pos _)
  have hval : inv (freeMove L x 0) (mtf L x) = 0 := by
    rw [freeMove_zero_eq_mtf_of_mem L x hx, inv_self]
  have hmem : inv (freeMove L x 0) (mtf L x) ∈
      ((List.range (L.length + 1)).map fun j =>
        inv (freeMove L x j) (mtf L x)) :=
    List.mem_map.mpr ⟨0, h0mem, rfl⟩
  rw [hval] at hmem
  have hmin : (((List.range (L.length + 1)).map fun j =>
      inv (freeMove L x j) (mtf L x))).min?.getD 0 = 0 :=
    min_getD_zero_of_mem _ hmem
  simp only [stepCost]
  rw [hmin, add_zero]

private theorem traceCost_runFrom_mtf {α : Type*} [DecidableEq α]
    (M past : List α) (σ : List α) : (∀ x ∈ past ++ σ, x ∈ M) →
    traceCost (mtfListAfter M past) (runFrom (mtfStrategy M) past σ)
      = mtfCost (mtfListAfter M past) σ := by
  induction σ generalizing past with
  | nil =>
      intro _
      simp only [runFrom, traceCost, mtfCost]
  | cons r σ ih =>
      intro h
      simp only [runFrom, traceCost, mtfCost]
      rw [mtfStrategy_append_singleton]
      have hrM : r ∈ M := h r
        (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
      have hpast : ∀ y ∈ past, y ∈ M :=
        fun y hy => h y (List.mem_append.mpr (Or.inl hy))
      have hcur := mtfListAfter_perm M past hpast
      have hrmem : r ∈ mtfListAfter M past :=
        (List.Perm.mem_iff hcur.symm).mp hrM
      rw [stepCost_mtf _ _ hrmem, ← mtfListAfter_append_singleton]
      have h' : ∀ y ∈ (past ++ [r]) ++ σ, y ∈ M := by
        intro y hy
        rw [List.append_assoc] at hy
        exact h y hy
      rw [ih (past ++ [r]) h']

theorem algCost_mtfStrategy {α : Type*} [DecidableEq α] (M : List α)
    (σ : List α) (hσ : ∀ x ∈ σ, x ∈ M) :
    algCost (listUpdateProblem M) (mtfStrategy M) σ
      = (mtfCost M σ : ℝ) := by
  change ((traceCost M (run (mtfStrategy M) σ) : ℕ) : ℝ) = (mtfCost M σ : ℝ)
  congr 1
  exact traceCost_runFrom_mtf M [] σ (fun x hx => hσ x hx)

private def scheduleTrace {α : Type*} (L : ℕ → List α) :
    List α → List (α × List α)
  | [] => []
  | x :: σ => (x, L 1) :: scheduleTrace (fun t => L (t + 1)) σ

private theorem scheduleTrace_map_fst {α : Type*} (L : ℕ → List α)
    (σ : List α) : (scheduleTrace L σ).map Prod.fst = σ := by
  induction σ generalizing L with
  | nil => rfl
  | cons x σ ih => simp only [scheduleTrace, List.map_cons, ih]

private theorem scheduleTrace_feasible {α : Type*} [DecidableEq α]
    {M : List α} (L : ℕ → List α) (hL : ∀ t, (L t).Perm M) (σ : List α) :
    (∀ x ∈ σ, x ∈ M) → (listUpdateProblem M).feasible (scheduleTrace L σ) := by
  induction σ generalizing L with
  | nil =>
      intro _
      simp only [scheduleTrace]
      refine ⟨?_, ?_⟩
      · intro p hp
        simp at hp
      · intro p hp
        simp at hp
  | cons x σ ih =>
      intro hσ
      have hxM : x ∈ M := hσ x (List.mem_cons.mpr (Or.inl rfl))
      have hσ' : ∀ y ∈ σ, y ∈ M :=
        fun y hy => hσ y (List.mem_cons.mpr (Or.inr hy))
      have hL' : ∀ t, ((fun t => L (t + 1)) t).Perm M := fun t => hL (t + 1)
      have hIH := ih (fun t => L (t + 1)) hL' hσ'
      simp only [scheduleTrace]
      refine ⟨?_, ?_⟩
      · intro p hp
        simp only [List.mem_cons] at hp
        cases hp with
        | inl h =>
            rw [h]
            exact hL 1
        | inr h => exact hIH.1 p h
      · intro p hp
        simp only [List.mem_cons] at hp
        cases hp with
        | inl h =>
            rw [h]
            exact hxM
        | inr h => exact hIH.2 p h

private theorem getD_min_le_of_mem (f : ℕ → ℕ) (n j : ℕ)
    (hj : j ∈ List.range (n + 1)) :
    ((List.range (n + 1)).map f).min?.getD 0 ≤ f j := by
  have hmem : f j ∈ ((List.range (n + 1)).map f) :=
    List.mem_map.mpr ⟨j, hj, rfl⟩
  cases hm : (((List.range (n + 1)).map f).min?) with
  | none =>
      have hempty := List.min?_eq_none_iff.mp hm
      rw [hempty] at hmem
      simp at hmem
  | some a =>
      have hall := (List.min?_eq_some_iff.mp hm).2
      simp only [Option.getD_some]
      exact hall (f j) hmem

private theorem findIdx_go_le_length {α : Type*} (p : α → Bool) (l : List α)
    (n : ℕ) : List.findIdx.go p l n ≤ n + l.length := by
  induction l generalizing n with
  | nil => exact le_rfl
  | cons x xs ih =>
      simp only [List.findIdx.go]
      cases hb : p x with
      | true =>
          simp
      | false =>
          simp
          have h := ih (n + 1)
          omega

private theorem freeMove_eq_self_of_le_length {α : Type*} [DecidableEq α]
    (L : List α) (x : α) (j : ℕ) (hj : L.length ≤ j) :
    freeMove L x j = L := by
  have hle : L.idxOf x ≤ L.length := List.idxOf_le_length
  simp only [freeMove]
  rw [ite_eq_left (le_trans hle hj)]

private theorem min_freeMove_le {α : Type*} [DecidableEq α] (L : List α)
    (x : α) (L' : List α) (j : ℕ) :
    (((List.range (L.length + 1)).map fun k =>
      inv (freeMove L x k) L').min?.getD 0) ≤
      inv (freeMove L x j) L' := by
  by_cases hj : j < L.length + 1
  · exact getD_min_le_of_mem _ _ _ (List.mem_range.mpr hj)
  · have hj' : L.length ≤ j := by omega
    have hstab : freeMove L x j = L :=
      freeMove_eq_self_of_le_length _ _ _ hj'
    have hstab2 : freeMove L x L.length = L :=
      freeMove_eq_self_of_le_length _ _ _ le_rfl
    have hlen : L.length ∈ List.range (L.length + 1) :=
      List.mem_range.mpr (Nat.lt_succ_self _)
    have hle : (((List.range (L.length + 1)).map fun k =>
        inv (freeMove L x k) L').min?.getD 0) ≤
        inv (freeMove L x L.length) L' :=
      getD_min_le_of_mem _ _ _ hlen
    have heq : inv (freeMove L x L.length) L'
        = inv (freeMove L x j) L' := by
      rw [hstab2, hstab]
    exact le_trans hle (le_of_eq heq)

private theorem traceCost_scheduleTrace_le {α : Type*} [DecidableEq α]
    {M : List α} (L : ℕ → List α) (J : ℕ → ℕ) (h0 : L 0 = M)
    (hL : ∀ t, (L t).Perm M) (σ : List α) :
    (∀ x ∈ σ, x ∈ M) → traceCost M (scheduleTrace L σ) ≤
      offlineCostFree L J σ := by
  induction σ generalizing L J M with
  | nil =>
      intro _
      exact le_rfl
  | cons x σ ih =>
      intro hσ
      simp only [scheduleTrace, traceCost, stepCost, offlineCostFree]
      rw [h0]
      have hmin : (((List.range (M.length + 1)).map fun k =>
          inv (freeMove M x k) (L 1)).min?.getD 0) ≤
          inv (freeMove M x (J 0)) (L 1) :=
        min_freeMove_le M x (L 1) (J 0)
      have hL1 : (L 1).Perm M := hL 1
      have hL'' : ∀ t, ((fun t => L (t + 1)) t).Perm (L 1) :=
        fun t => (hL (t + 1)).trans hL1.symm
      have hσ'' : ∀ y ∈ σ, y ∈ L 1 :=
        fun y hy => (List.Perm.mem_iff hL1.symm).mp
          (hσ y (List.mem_cons.mpr (Or.inr hy)))
      have h0' : (fun t => L (t + 1)) 0 = L 1 := rfl
      have hIH := ih (fun t => L (t + 1)) (fun t => J (t + 1)) (M := L 1) h0'
        hL'' hσ''
      exact add_le_add (add_le_add_right hmin _) hIH

theorem optCost_le_offlineCostFree {α : Type*} [DecidableEq α] (M : List α)
    (L : ℕ → List α) (J : ℕ → ℕ) (h0 : L 0 = M) (hL : ∀ t, (L t).Perm M)
    (σ : List α) (hσ : ∀ x ∈ σ, x ∈ M) :
    optCost (listUpdateProblem M) σ
      ≤ ENNReal.ofReal (offlineCostFree L J σ : ℝ) := by
  have hτ : (listUpdateProblem M).feasible (scheduleTrace L σ) :=
    scheduleTrace_feasible L hL σ hσ
  have hmap : (scheduleTrace L σ).map Prod.fst = σ :=
    scheduleTrace_map_fst L σ
  have hle : optCost (listUpdateProblem M) σ ≤
      ENNReal.ofReal ((listUpdateProblem M).cost (scheduleTrace L σ)) :=
    optCost_le _ hτ hmap
  have hcost : traceCost M (scheduleTrace L σ) ≤ offlineCostFree L J σ :=
    traceCost_scheduleTrace_le L J h0 hL σ hσ
  have hcostR : ((listUpdateProblem M).cost (scheduleTrace L σ)) ≤
      (offlineCostFree L J σ : ℝ) :=
    Nat.cast_le.mpr hcost
  have hnn2 : (0 : ℝ) ≤ (offlineCostFree L J σ : ℝ) := Nat.cast_nonneg _
  have h2 : ENNReal.ofReal ((listUpdateProblem M).cost (scheduleTrace L σ)) ≤
      ENNReal.ofReal (offlineCostFree L J σ : ℝ) :=
    (ENNReal.ofReal_le_ofReal_iff hnn2).mpr hcostR
  exact le_trans hle h2

private def minTerm {α : Type*} [DecidableEq α] (L : List α) (x : α)
    (L' : List α) : ℕ :=
  ((List.range (L.length + 1)).map fun j =>
    inv (freeMove L x j) L').min?.getD 0

private theorem stepCost_eq {α : Type*} [DecidableEq α] (L : List α)
    (x : α) (L' : List α) :
    stepCost L x L' = accessCost L x + minTerm L x L' := rfl

private def Aligned {α : Type*} [DecidableEq α] (M : List α) :
    List (α × List α) → (ℕ → List α) → (ℕ → ℕ) → Prop
  | [], L, _ => ∀ t, (L t).Perm M
  | (x, L') :: τ', L, J => (∀ t, (L t).Perm M) ∧ L 1 = L' ∧
      inv (freeMove (L 0) x (J 0)) L' = minTerm (L 0) x L' ∧
      Aligned M τ' (fun t => L (t + 1)) (fun t => J (t + 1))

private theorem Aligned.perm {α : Type*} [DecidableEq α] (M : List α)
    (τ : List (α × List α)) (L : ℕ → List α) (J : ℕ → ℕ) :
    Aligned M τ L J → ∀ t, (L t).Perm M := by
  cases τ with
  | nil => intro hA; exact hA
  | cons hd tl =>
      obtain ⟨x, L'⟩ := hd
      intro hA
      exact hA.1

private theorem argmin_exists {α : Type*} [DecidableEq α]
    (B : List α) (x : α) (L' : List α) :
    ∃ j, inv (freeMove B x j) L' = minTerm B x L' := by
  have h0mem : (0 : ℕ) ∈ List.range (B.length + 1) :=
    List.mem_range.mpr (Nat.succ_pos _)
  have hmem : inv (freeMove B x 0) L' ∈
      ((List.range (B.length + 1)).map fun j =>
        inv (freeMove B x j) L') :=
    List.mem_map.mpr ⟨0, h0mem, rfl⟩
  cases hm : ((((List.range (B.length + 1)).map fun j =>
      inv (freeMove B x j) L')).min?) with
  | none =>
      have hempty := List.min?_eq_none_iff.mp hm
      rw [hempty] at hmem
      simp at hmem
  | some a =>
      have hmem2 : a ∈ ((List.range (B.length + 1)).map fun j =>
          inv (freeMove B x j) L') :=
        (List.min?_eq_some_iff.mp hm).1
      obtain ⟨j0, -, rfl⟩ := List.mem_map.mp hmem2
      refine ⟨j0, ?_⟩
      simp [minTerm, hm]

private theorem exists_aligned {α : Type*} [DecidableEq α] {M : List α}
    (B : List α) (hB : B.Perm M) (τ : List (α × List α)) :
    (∀ p ∈ τ, p.2.Perm M) → ∃ L J, L 0 = B ∧ Aligned M τ L J := by
  induction τ generalizing B with
  | nil =>
      intro _
      exact ⟨fun _ => B, fun _ => 0, rfl, fun _ => hB⟩
  | cons hd tl ih =>
      obtain ⟨x, L'⟩ := hd
      intro hτ
      have hL'perm : L'.Perm M :=
        hτ (x, L') (List.mem_cons.mpr (Or.inl rfl))
      have hτ'perm : ∀ p ∈ tl, p.2.Perm M :=
        fun p hp => hτ p (List.mem_cons.mpr (Or.inr hp))
      obtain ⟨j0, hj0⟩ := argmin_exists B x L'
      obtain ⟨L'', J'', hL''0, hA''⟩ := ih L' hL'perm hτ'perm
      refine ⟨fun t => match t with | 0 => B | n + 1 => L'' n,
        fun t => match t with | 0 => j0 | n + 1 => J'' n, rfl, ?_⟩
      simp only [Aligned]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro t
        cases t with
        | zero => exact hB
        | succ t => exact (Aligned.perm M tl L'' J'' hA'') t
      · exact hL''0
      · exact hj0
      · exact hA''

private theorem bridge_eq {α : Type*} [DecidableEq α] (M : List α)
    (τ : List (α × List α)) (L : ℕ → List α) (J : ℕ → ℕ) :
    Aligned M τ L J →
      offlineCostFree L J (τ.map Prod.fst) = traceCost (L 0) τ := by
  induction τ generalizing L J with
  | nil =>
      intro _
      rfl
  | cons hd tl ih =>
      obtain ⟨x, L'⟩ := hd
      intro hA
      obtain ⟨_, hL1, hJ, hA'⟩ := hA
      have hIH := ih _ _ hA'
      rw [hL1] at hIH
      simp only [List.map_cons, offlineCostFree, traceCost, stepCost_eq]
      rw [hL1, hJ, hIH]

theorem exists_offlineCostFree_eq {α : Type*} [DecidableEq α] (M : List α)
    (τ : List (α × List α)) (hτ : (listUpdateProblem M).feasible τ) :
    ∃ (L : ℕ → List α) (J : ℕ → ℕ), L 0 = M ∧ (∀ t, (L t).Perm M) ∧
      offlineCostFree L J (τ.map Prod.fst) = traceCost M τ := by
  obtain ⟨L, J, hL0, hA⟩ := exists_aligned M (List.Perm.refl M) τ hτ.1
  refine ⟨L, J, hL0, Aligned.perm M τ L J hA, ?_⟩
  have hbr := bridge_eq M τ L J hA
  rw [hL0] at hbr
  exact hbr

theorem mtf_strictCompetitive {α : Type*} [DecidableEq α] {M : List α}
    (hnd : M.Nodup) :
    StrictCompetitive (listUpdateProblem M) (mtfStrategy M) 2 := by
  refine ⟨by norm_num, le_rfl, mtfStrategy_feasible M, fun σ hσ => ?_⟩
  have hσ' : ∀ x ∈ σ, x ∈ M := hσ
  have halg : algCost (listUpdateProblem M) (mtfStrategy M) σ
      = ((mtfCost M σ : ℕ) : ℝ) :=
    algCost_mtfStrategy M σ hσ'
  have hper : ∀ τ ∈ {τ : List (α × List α) |
      (listUpdateProblem M).feasible τ ∧ τ.map Prod.fst = σ},
      ENNReal.ofReal ((mtfCost M σ : ℕ) : ℝ) ≤
        ENNReal.ofReal 2 * ENNReal.ofReal ((listUpdateProblem M).cost τ) := by
    intro τ hτmem
    obtain ⟨hτfeas, hτmap⟩ := hτmem
    obtain ⟨L, J, hL0, hLperm, hcost⟩ :=
      exists_offlineCostFree_eq M τ hτfeas
    rw [hτmap] at hcost
    have hmtf := mtfCost_le_free σ hnd L J hLperm hL0 hσ'
    have hle : mtfCost M σ ≤ 2 * offlineCostFree L J σ :=
      le_trans (Nat.le_add_right _ _) hmtf
    have hR : ((mtfCost M σ : ℕ) : ℝ) ≤
        2 * ((offlineCostFree L J σ : ℕ) : ℝ) := by
      exact_mod_cast hle
    have hcostτ : (listUpdateProblem M).cost τ
        = ((offlineCostFree L J σ : ℕ) : ℝ) :=
      congrArg (Nat.cast : ℕ → ℝ) hcost.symm
    have hnn2 : (0 : ℝ) ≤ 2 * ((offlineCostFree L J σ : ℕ) : ℝ) := by
      positivity
    have hle2 : ENNReal.ofReal ((mtfCost M σ : ℕ) : ℝ) ≤
        ENNReal.ofReal (2 * ((offlineCostFree L J σ : ℕ) : ℝ)) :=
      (ENNReal.ofReal_le_ofReal_iff hnn2).mpr hR
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)] at hle2
    rw [← hcostτ] at hle2
    exact hle2
  have hne0 : (ENNReal.ofReal 2 : ENNReal) ≠ 0 := by
    have h : (0 : ENNReal) < ENNReal.ofReal 2 := by
      rw [ENNReal.ofReal_pos]
      norm_num
    exact ne_of_gt h
  have hneTop : (ENNReal.ofReal 2 : ENNReal) ≠ ⊤ := ENNReal.ofReal_ne_top
  have hmul : (⨅ τ ∈ {τ : List (α × List α) |
      (listUpdateProblem M).feasible τ ∧ τ.map Prod.fst = σ},
      (ENNReal.ofReal 2 * ENNReal.ofReal ((listUpdateProblem M).cost τ)))
      = ENNReal.ofReal 2 * optCost (listUpdateProblem M) σ := by
    simp only [optCost, ← ENNReal.mul_iInf_of_ne hne0 hneTop]
  have hmain : ENNReal.ofReal ((mtfCost M σ : ℕ) : ℝ) ≤
      ENNReal.ofReal 2 * optCost (listUpdateProblem M) σ := by
    rw [← hmul]
    refine le_iInf fun τ => le_iInf fun hτ => hper τ hτ
  rw [halg]
  exact le_trans hmain (le_add_of_nonneg_right (by positivity))

private theorem mem_append_singleton_of_mem {α : Type*}
    {M : List α} (q : { q : List α // ∀ x ∈ q, x ∈ M }) {x : α}
    (hx : x ∈ M) : ∀ y ∈ q.1 ++ [x], y ∈ M := by
  intro y hy
  rw [List.mem_append] at hy
  cases hy with
  | inl h1 => exact q.2 y h1
  | inr h2 =>
      rw [List.mem_singleton.mp h2]
      exact hx

private theorem nil_mem_all {α : Type*} {M : List α} :
    ∀ x ∈ ([] : List α), x ∈ M := by
  intro x hx
  simp at hx

private def olist {α : Type*} [DecidableEq α] {M : List α}
    (A : Strategy α (List α)) (q : { q : List α // ∀ x ∈ q, x ∈ M }) :
    List α :=
  if q.1 = [] then M else A q.1

private def ostep {α : Type*} [DecidableEq α] {M : List α}
    (_A : Strategy α (List α)) (q : { q : List α // ∀ x ∈ q, x ∈ M })
    (x : α) : { q : List α // ∀ x ∈ q, x ∈ M } :=
  if h : x ∈ M then ⟨q.1 ++ [x], mem_append_singleton_of_mem q h⟩ else q

private theorem strategy_answer_perm {α : Type*} [DecidableEq α]
    {M : List α} (A : Strategy α (List α))
    (hA : StrategyFeasible (listUpdateProblem M) A) (q : List α)
    (hq : ∀ x ∈ q, x ∈ M) (hne : q ≠ []) : (A q).Perm M := by
  have hrev : q.reverse ≠ [] := by
    intro hcon
    apply hne
    have h2 := congrArg List.reverse hcon
    rw [List.reverse_reverse] at h2
    simpa using h2
  cases hr : q.reverse with
  | nil => exact absurd hr hrev
  | cons r rest =>
      have hqeq : q = rest.reverse ++ [r] := by
        have h2 := congrArg List.reverse hr
        rw [List.reverse_reverse] at h2
        rw [h2, show (r :: rest) = [r] ++ rest from rfl,
          List.reverse_append, show ([r].reverse) = [r] from rfl]
      rw [hqeq]
      have hlegal : (listUpdateProblem M).legal (rest.reverse ++ [r]) := by
        rw [← hqeq]
        exact hq
      have hmem : (r, A (rest.reverse ++ [r])) ∈
          run A (rest.reverse ++ [r]) := by
        simp only [run, runFrom_append]
        rw [show ([] : List α) ++ rest.reverse = rest.reverse from rfl]
        simp only [runFrom]
        exact List.mem_append.mpr
          (Or.inr (List.mem_cons.mpr (Or.inl rfl)))
      exact (hA _ hlegal).1 _ hmem

private abbrev strategyToOnline {α : Type*} [DecidableEq α] {M : List α}
    (A : Strategy α (List α))
    (hA : StrategyFeasible (listUpdateProblem M) A) :
    OnlineListUpdate α M where
  State := { q : List α // ∀ x ∈ q, x ∈ M }
  init := ⟨[], nil_mem_all⟩
  list := olist A
  step := ostep A
  perm := fun q => by
    by_cases hq : q.1 = []
    · simp only [olist]
      rw [ite_eq_left hq]
    · simp only [olist]
      rw [ite_eq_right hq]
      exact strategy_answer_perm A hA q.1 q.2 hq

private theorem strategyToOnline_list {α : Type*} [DecidableEq α]
    {M : List α} (A : Strategy α (List α))
    (hA : StrategyFeasible (listUpdateProblem M) A)
    (q : (strategyToOnline A hA).State) :
    (strategyToOnline A hA).list q = olist A q :=
  rfl

private theorem strategyToOnline_step {α : Type*} [DecidableEq α]
    {M : List α} (A : Strategy α (List α))
    (hA : StrategyFeasible (listUpdateProblem M) A)
    (q : (strategyToOnline A hA).State) (x : α) :
    (strategyToOnline A hA).step q x = ostep A q x :=
  rfl

private theorem olist_snoc {α : Type*} [DecidableEq α] {M : List α}
    (A : Strategy α (List α)) (h : List α) (x : α)
    (hh' : ∀ y ∈ h ++ [x], y ∈ M) :
    olist A ⟨h ++ [x], hh'⟩ = A (h ++ [x]) := by
  simp only [olist]
  have hne : h ++ [x] ≠ [] := by
    intro hcon
    have hmem : x ∈ h ++ [x] :=
      List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))
    rw [hcon] at hmem
    simp at hmem
  rw [ite_eq_right hne]

private theorem cost_le_traceCost {α : Type*} [DecidableEq α] {M : List α}
    (A : Strategy α (List α)) (hA : StrategyFeasible (listUpdateProblem M) A)
    (h : List α) (hh : ∀ x ∈ h, x ∈ M) (σ : List α) :
    (∀ x ∈ h ++ σ, x ∈ M) →
    OnlineListUpdate.cost (strategyToOnline A hA) ⟨h, hh⟩ σ ≤
      traceCost (olist A ⟨h, hh⟩) (runFrom A h σ) := by
  induction σ generalizing h hh with
  | nil =>
      intro _
      exact le_rfl
  | cons x σ ih =>
      intro hσ
      simp only [OnlineListUpdate.cost, ostep, runFrom, traceCost, stepCost]
      have hxM : x ∈ M := hσ x
        (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl))))
      rw [dite_eq_left hxM]
      have hσ' : ∀ y ∈ (h ++ [x]) ++ σ, y ∈ M := by
        intro y hy
        rw [List.append_assoc] at hy
        exact hσ y hy
      have hh'h : ∀ y ∈ h ++ [x], y ∈ M :=
        fun y hy => hσ' y (List.mem_append.mpr (Or.inl hy))
      have hIH := ih (h ++ [x]) hh'h hσ'
      rw [olist_snoc] at hIH
      refine le_trans (add_le_add_right hIH _) ?_
      omega

/-- Karp–Raghavan/Irani lower bound in framework form: no deterministic
strategy is additively better than `2ℓ/(ℓ+1)` on an `ℓ`-item list. -/
theorem listUpdate_additiveLowerBound {α : Type*} [DecidableEq α]
    {M : List α} (hnd : M.Nodup) (hM : M ≠ []) :
    AdditiveLowerBound (listUpdateProblem M)
      ((2 * M.length : ℝ) / (M.length + 1)) := by
  intro A hA c b hc0 hclt hb0
  have hlenpos : (0 : ℝ) < (M.length : ℝ) + 1 := by positivity
  have hmul : c * ((M.length : ℝ) + 1) < 2 * (M.length : ℝ) :=
    (lt_div_iff₀ hlenpos).mp hclt
  set δ : ℝ := 2 * (M.length : ℝ) - c * ((M.length : ℝ) + 1) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    linarith
  obtain ⟨d, hd⟩ := exists_nat_gt (2 * ((M.length : ℝ) + 1) / δ)
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  have h2 : 2 * ((M.length : ℝ) + 1) < (d : ℝ) * δ :=
    (div_lt_iff₀ hδpos).mp hd
  have hcd0 : (0 : ℝ) ≤ c * (d : ℝ) := mul_nonneg hc0 hd0
  obtain ⟨c', hc'd, hc'ub⟩ : ∃ c' : ℕ,
      c * (d : ℝ) < (c' : ℝ) ∧ (c' : ℝ) < c * (d : ℝ) + 2 :=
    ⟨⌈c * (d : ℝ)⌉₊ + 1, by
      push_cast
      linarith [Nat.le_ceil (c * (d : ℝ))], by
      push_cast
      have hceil := Nat.ceil_lt_add_one hcd0
      linarith⟩
  have hδ' : (d : ℝ) * δ = 2 * (M.length : ℝ) * (d : ℝ) -
      c * (d : ℝ) * ((M.length : ℝ) + 1) := by
    rw [hδdef]
    ring
  have hreal : (c' : ℝ) * ((M.length : ℝ) + 1)
      < 2 * (M.length : ℝ) * (d : ℝ) := by
    have hexp : (c * (d : ℝ) + 2) * ((M.length : ℝ) + 1)
        = c * (d : ℝ) * ((M.length : ℝ) + 1)
          + 2 * ((M.length : ℝ) + 1) := by
      ring
    have hmul' : (c' : ℝ) * ((M.length : ℝ) + 1)
        < (c * (d : ℝ) + 2) * ((M.length : ℝ) + 1) :=
      mul_lt_mul_of_pos_right hc'ub hlenpos
    linarith [hexp, hmul', h2, hδ']
  have hc'bd : c' * (M.length + 1) < 2 * M.length * d := by
    exact_mod_cast hreal
  set b' : ℕ := ⌈b⌉₊ with hb'def
  have hb' : b ≤ (b' : ℝ) := by
    rw [hb'def]
    exact Nat.le_ceil b
  obtain ⟨σ, hσM, L, hL0, hLperm, hineq⟩ :=
    not_competitive hnd hM (strategyToOnline A hA) (b := b')
      hc'bd
  set S : OnlineListUpdate α M := strategyToOnline A hA with hSdef
  have hlegal : (listUpdateProblem M).legal σ := hσM
  have hlen : ∀ t, (L t).length ≤ M.length :=
    fun t => le_of_eq ((hLperm t).length_eq)
  have hopt : optCost (listUpdateProblem M) σ ≤
      ENNReal.ofReal ((offlineCost L σ : ℕ) : ℝ) := by
    have h := optCost_le_offlineCostFree M L (fun _ => M.length) hL0 hLperm
      σ hσM
    rw [offlineCostFree_noMove σ L hlen] at h
    exact h
  have hON : ((OnlineListUpdate.cost S S.init σ : ℕ) : ℝ) ≤
      algCost (listUpdateProblem M) A σ := by
    have h := cost_le_traceCost A hA [] nil_mem_all σ (fun x hx => hσM x hx)
    have holist : olist (M := M) A ⟨[], nil_mem_all (M := M)⟩ = M := by
      simp [olist]
    rw [holist] at h
    rw [hSdef]
    change ((OnlineListUpdate.cost (strategyToOnline A hA)
      ⟨[], nil_mem_all (M := M)⟩ σ : ℕ) : ℝ) ≤
      ((traceCost M (runFrom A [] σ) : ℕ) : ℝ)
    exact_mod_cast h
  have hR : (c' : ℝ) * ((offlineCost L σ : ℕ) : ℝ) + (d : ℝ) * (b' : ℝ)
      < (d : ℝ) * ((OnlineListUpdate.cost S S.init σ : ℕ) : ℝ) := by
    exact_mod_cast hineq
  have halg0 : (0 : ℝ) ≤ algCost (listUpdateProblem M) A σ :=
    (listUpdateProblem M).cost_nonneg _
  have hOFF0 : (0 : ℝ) ≤ ((offlineCost L σ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hXd : (c * ((offlineCost L σ : ℕ) : ℝ) + (b' : ℝ)) * (d : ℝ)
      < algCost (listUpdateProblem M) A σ * (d : ℝ) := by
    have e1 : (c * ((offlineCost L σ : ℕ) : ℝ) + (b' : ℝ)) * (d : ℝ)
        = c * (d : ℝ) * ((offlineCost L σ : ℕ) : ℝ) + (d : ℝ) * (b' : ℝ) := by
      ring
    have e2 : algCost (listUpdateProblem M) A σ * (d : ℝ)
        = (d : ℝ) * algCost (listUpdateProblem M) A σ := by
      ring
    rw [e1, e2]
    have g1 : c * (d : ℝ) * ((offlineCost L σ : ℕ) : ℝ)
        ≤ (c' : ℝ) * ((offlineCost L σ : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_right (le_of_lt hc'd) hOFF0
    have g2 : c * (d : ℝ) * ((offlineCost L σ : ℕ) : ℝ) + (d : ℝ) * (b' : ℝ)
        ≤ (c' : ℝ) * ((offlineCost L σ : ℕ) : ℝ) + (d : ℝ) * (b' : ℝ) :=
      add_le_add_left g1 _
    have g3 : (d : ℝ) * ((OnlineListUpdate.cost S S.init σ : ℕ) : ℝ)
        ≤ (d : ℝ) * algCost (listUpdateProblem M) A σ :=
      mul_le_mul_of_nonneg_left hON hd0
    exact lt_of_lt_of_le (lt_of_le_of_lt g2 hR) g3
  have hfin : c * ((offlineCost L σ : ℕ) : ℝ) + (b' : ℝ)
      < algCost (listUpdateProblem M) A σ := by
    by_contra hcon
    push Not at hcon
    have hle := mul_le_mul_of_nonneg_right hcon hd0
    linarith [hXd, hle]
  have hnn : (0 : ℝ) ≤ c * ((offlineCost L σ : ℕ) : ℝ) + (b' : ℝ) :=
    add_nonneg (mul_nonneg hc0 hOFF0) (Nat.cast_nonneg _)
  have step1 : ENNReal.ofReal c * optCost (listUpdateProblem M) σ +
        ENNReal.ofReal b ≤ ENNReal.ofReal c *
          ENNReal.ofReal ((offlineCost L σ : ℕ) : ℝ) +
        ENNReal.ofReal ((b' : ℕ) : ℝ) :=
    add_le_add (mul_le_mul_of_nonneg_left hopt (by positivity))
      ((ENNReal.ofReal_le_ofReal_iff (Nat.cast_nonneg _)).mpr hb')
  have step2 : ENNReal.ofReal c *
        ENNReal.ofReal ((offlineCost L σ : ℕ) : ℝ) +
        ENNReal.ofReal ((b' : ℕ) : ℝ) =
      ENNReal.ofReal (c * ((offlineCost L σ : ℕ) : ℝ) + (b' : ℝ)) := by
    rw [← ENNReal.ofReal_mul hc0,
      ← ENNReal.ofReal_add (mul_nonneg hc0 hOFF0) (Nat.cast_nonneg _)]
  have halg_pos : (0 : ℝ) < algCost (listUpdateProblem M) A σ :=
    lt_of_le_of_lt hnn hfin
  have step3 : ENNReal.ofReal (c * ((offlineCost L σ : ℕ) : ℝ) + (b' : ℝ)) <
      ENNReal.ofReal (algCost (listUpdateProblem M) A σ) :=
    (ENNReal.ofReal_lt_ofReal_iff halg_pos).mpr hfin
  refine ⟨σ, hlegal, ?_⟩
  calc ENNReal.ofReal c * optCost (listUpdateProblem M) σ + ENNReal.ofReal b
      ≤ ENNReal.ofReal c * ENNReal.ofReal ((offlineCost L σ : ℕ) : ℝ) +
          ENNReal.ofReal ((b' : ℕ) : ℝ) := step1
    _ = ENNReal.ofReal (c * ((offlineCost L σ : ℕ) : ℝ) + (b' : ℝ)) := step2
    _ < ENNReal.ofReal (algCost (listUpdateProblem M) A σ) := step3

end Cslib.Algorithms.Lean.Online.CompetitiveFramework

end
public section
