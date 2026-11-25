/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Topology.Order.MonotoneConvergence
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.MetricSpace.Basic
public import Mathlib.Topology.Algebra.Group.Basic
public import Mathlib.Data.Rat.BigOperators
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Topology.Order.Real
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Order.ConditionallyCompleteLattice.Indexed
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.LinearAlgebra.Matrix.Stochastic

/-!
# Reachability probabilities for finite Markov chains

For a finite discrete-time Markov chain with rational transition
probabilities, given as an element of Mathlib's `Matrix.rowStochastic`,
the probability of the until event `A U B` over a finite
horizon is defined by summing path weights over first-hit paths; it is
not defined as a Bellman solution. The horizon probabilities satisfy
the Bellman recursion and increase with the horizon. The unbounded
reachability probability is defined as their supremum, and it is the
least nonnegative pre-fixed point of the Bellman operator (in
particular, the least nonnegative fixed point). Background:
C. Baier and J.-P. Katoen, *Principles of Model Checking*, MIT Press,
2008, Chapter 10.
-/

@[expose] public section

namespace Cslib.Probability

open scoped Classical



/-- A finite discrete-time Markov chain with rational transitions: a
row-stochastic rational matrix, as an element of Mathlib's
`Matrix.rowStochastic`. -/
abbrev DTMC (S : Type*) [Fintype S] [DecidableEq S] : Type _ :=
  Matrix.rowStochastic ℚ S

variable {S : Type*} [Fintype S] [DecidableEq S] (D : DTMC S) (A B : Finset S)

/-- The transition probabilities of a chain, from the first state to the
second: its matrix. -/
abbrev DTMC.P : S → S → ℚ :=
  D.1

/-- Transition probabilities are nonnegative. -/
theorem DTMC.nonneg (s t : S) : 0 ≤ D.P s t :=
  Matrix.nonneg_of_mem_rowStochastic D.2

/-- The transition probabilities out of each state sum to `1`. -/
theorem DTMC.row_sum (s : S) : ∑ t, D.P s t = 1 :=
  Matrix.sum_row_of_mem_rowStochastic D.2 s


/-- First visit to `B` along a finite path, with all earlier positions
in `A` and outside `B`. -/
def FirstHit {n : ℕ} (A B : Finset S) (p : Fin (n + 1) → S) : Prop :=
  ∃ k : Fin (n + 1), p k ∈ B ∧
    ∀ j : Fin (n + 1), (j : ℕ) < (k : ℕ) → p j ∉ B ∧ p j ∈ A

/-- The product of transition probabilities along a finite path. -/
def DTMC.pathWeight {n : ℕ} (p : Fin (n + 1) → S) : ℚ :=
  ∏ i : Fin n, D.P (p i.castSucc) (p i.succ)

/-- Until probability over horizon `n`, by path sums. -/
noncomputable def DTMC.hitProb (n : ℕ) (s : S) : ℚ :=
  ∑ p : Fin (n + 1) → S,
    if p 0 = s ∧ FirstHit A B p then D.pathWeight p else 0

/-- The Bellman operator on real-valued functions. -/
noncomputable def DTMC.bellman (x : S → ℝ) : S → ℝ :=
  fun s => if s ∈ B then 1 else if s ∉ A then 0
    else ∑ t, (D.P s t : ℝ) * x t

/-- Unbounded reachability probability: supremum over horizons. -/
noncomputable def DTMC.reachProb (s : S) : ℝ :=
  ⨆ n, (D.hitProb A B n s : ℝ)

private theorem fin_one_eq_zero (k : Fin (0 + 1)) : k = 0 := by
  have h : (k : ℕ) = 0 := by
    have hk := k.isLt
    omega
  exact Fin.ext (by omega)

theorem firstHit_zero_iff {S : Type*} [Fintype S]
    (A B : Finset S) (p : Fin (0 + 1) → S) :
    FirstHit A B p ↔ p 0 ∈ B := by
  constructor
  · rintro ⟨k, hkB, _⟩
    have : k = 0 := fin_one_eq_zero k
    rw [this] at hkB
    exact hkB
  · intro h
    exact ⟨0, h, fun j hj => absurd hj (by simp)⟩

theorem pathWeight_nonneg {S : Type*} [Fintype S] [DecidableEq S] (D : DTMC S)
    {n : ℕ} (p : Fin (n + 1) → S) : 0 ≤ D.pathWeight p := by
  unfold DTMC.pathWeight
  apply Finset.prod_nonneg
  intro i _
  exact D.nonneg _ _

private theorem hitProb_nonneg_aux {S : Type*} [Fintype S] [DecidableEq S] (D : DTMC S)
    (A B : Finset S) (n : ℕ) (s : S) : 0 ≤ D.hitProb A B n s := by
  unfold DTMC.hitProb
  apply Finset.sum_nonneg
  intro p _
  split
  · exact pathWeight_nonneg D p
  · exact le_rfl

theorem pathWeight_cons {S : Type*} [Fintype S] [DecidableEq S] (D : DTMC S) (n : ℕ)
    (s0 : S) (tail : Fin (n + 1) → S) :
    D.pathWeight (n := n + 1)
        (Fin.cons (n := n + 1) (α := fun _ : Fin (n + 1 + 1) => S) s0 tail)
      = D.P s0 (tail 0) * D.pathWeight (n := n) tail := by
  unfold DTMC.pathWeight
  rw [Fin.prod_univ_succ]
  have h0c : ((0 : Fin (n + 1)).castSucc : Fin (n + 1 + 1)) = 0 := by
    ext
    simp
  have h0 : D.P ((Fin.cons (n := n + 1) (α := fun _ : Fin (n + 1 + 1) => S) s0 tail)
        (0 : Fin (n+1)).castSucc)
      ((Fin.cons (n := n + 1) (α := fun _ : Fin (n + 1 + 1) => S) s0 tail)
        (0 : Fin (n+1)).succ) = D.P s0 (tail 0) := by
    rw [h0c]
    simp only [Fin.cons_zero, Fin.cons_succ]
  have htail : (∏ i : Fin n, D.P ((Fin.cons (n := n + 1)
          (α := fun _ : Fin (n + 1 + 1) => S) s0 tail) (i.succ).castSucc)
      ((Fin.cons (n := n + 1) (α := fun _ : Fin (n + 1 + 1) => S) s0 tail)
        (i.succ).succ))
      = ∏ i : Fin n, D.P (tail i.castSucc) (tail i.succ) := by
    apply Finset.prod_congr rfl
    intro i _
    have hc : (i.succ.castSucc : Fin (n + 1 + 1)) = i.castSucc.succ :=
      Fin.castSucc_succ i
    rw [hc]
    simp only [Fin.cons_succ]
  rw [h0, htail]

theorem firstHit_cons_of_mem {S : Type*} [Fintype S]
    (A B : Finset S) (n : ℕ) (s0 : S) (tail : Fin (n + 1) → S)
    (hs : s0 ∈ B) :
    FirstHit A B (Fin.cons (n := n + 1) (α := fun _ : Fin (n + 1 + 1) => S)
      s0 tail) := by
  refine ⟨0, ?_, ?_⟩
  · simp only [Fin.cons_zero]
    exact hs
  · intro j hj
    have hz : ((0 : Fin (n + 1 + 1)) : ℕ) = 0 := Fin.val_zero _
    omega

theorem firstHit_cons_iff {S : Type*} [Fintype S]
    (A B : Finset S) (n : ℕ) (s0 : S) (tail : Fin (n + 1) → S)
    (hs : s0 ∉ B) :
    FirstHit A B (Fin.cons (n := n + 1) (α := fun _ : Fin (n + 1 + 1) => S)
        s0 tail)
      ↔ (s0 ∈ A ∧ FirstHit A B tail) := by
  constructor
  · rintro ⟨k, hkB, hkpre⟩
    have hk0 : k ≠ 0 := by
      intro heq
      rw [heq] at hkB
      simp only [Fin.cons_zero] at hkB
      exact hs hkB
    obtain ⟨j, rfl⟩ := (Fin.eq_zero_or_eq_succ k).resolve_left hk0
    have hjB : tail j ∈ B := by
      simp only [Fin.cons_succ] at hkB
      exact hkB
    have h0lt : ((0 : Fin (n + 1 + 1)) : ℕ)
        < (((j.succ : Fin (n + 1 + 1))) : ℕ) := by
      have hvs := Fin.val_succ j
      have hz : ((0 : Fin (n + 1 + 1)) : ℕ) = 0 := Fin.val_zero _
      omega
    have h0pre := hkpre 0 h0lt
    simp only [Fin.cons_zero] at h0pre
    refine ⟨h0pre.2, j, hjB, ?_⟩
    intro j' hj'lt
    have hlt : (((j'.succ : Fin (n + 1 + 1))) : ℕ)
        < (((j.succ : Fin (n + 1 + 1))) : ℕ) := by
      have h1 := Fin.val_succ j'
      have h2 := Fin.val_succ j
      omega
    have hpre := hkpre j'.succ hlt
    simp only [Fin.cons_succ] at hpre
    exact hpre
  · rintro ⟨hsA, k', hk'B, hk'pre⟩
    refine ⟨k'.succ, ?_, ?_⟩
    · simp only [Fin.cons_succ]
      exact hk'B
    · intro j hjlt
      rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · simp only [Fin.cons_zero]
        exact ⟨hs, hsA⟩
      · have hj'lt : (j' : ℕ) < (k' : ℕ) := by
          have h1 := Fin.val_succ j'
          have h2 := Fin.val_succ k'
          omega
        have hpre := hk'pre j' hj'lt
        simp only [Fin.cons_succ]
        exact hpre

private theorem hitProb_succ_unfold {S : Type*} [Fintype S] [DecidableEq S] (D : DTMC S)
    (A B : Finset S) (n : ℕ) (s : S) :
    D.hitProb A B (n + 1) s = ∑ tail : Fin (n + 1) → S,
      (if FirstHit A B (Fin.cons (n := n + 1)
        (α := fun _ : Fin (n + 1 + 1) => S) s tail)
      then D.pathWeight (n := n + 1) (Fin.cons (n := n + 1)
        (α := fun _ : Fin (n + 1 + 1) => S) s tail) else 0) := by
  unfold DTMC.hitProb
  let e := Fin.consEquiv (n := n + 1) (fun _ : Fin (n + 1 + 1) => S)
  have hsum : (∑ p : Fin (n + 1 + 1) → S,
      (if p 0 = s ∧ FirstHit A B p then D.pathWeight p else 0))
      = ∑ x : S × (Fin (n + 1) → S),
        (if (e x) 0 = s ∧ FirstHit A B (e x) then D.pathWeight (e x) else 0) := by
    rw [← Equiv.sum_comp e]
  rw [hsum, Fintype.sum_prod_type]
  have heq : ∀ s0 : S, ∀ tail : Fin (n + 1) → S,
      e (s0, tail) = Fin.cons (n := n + 1)
        (α := fun _ : Fin (n + 1 + 1) => S) s0 tail := by
    intro s0 tail
    funext i
    simp only [e, Fin.consEquiv_apply]
  have hterm : ∀ s0 : S, ∀ tail : Fin (n + 1) → S,
      (if (e (s0, tail)) 0 = s ∧ FirstHit A B (e (s0, tail))
        then D.pathWeight (e (s0, tail)) else (0 : ℚ))
      = (if s0 = s ∧ FirstHit A B (Fin.cons (n := n + 1)
          (α := fun _ : Fin (n + 1 + 1) => S) s0 tail)
        then D.pathWeight (Fin.cons (n := n + 1)
          (α := fun _ : Fin (n + 1 + 1) => S) s0 tail) else 0) := by
    intro s0 tail
    rw [heq s0 tail]
    have h0 : ((Fin.cons (n := n + 1) (α := fun _ : Fin (n + 1 + 1) => S)
      s0 tail) 0) = s0 := by simp only [Fin.cons_zero]
    rw [h0]
  have hcongr : (∑ s0 : S, ∑ tail : Fin (n + 1) → S,
      (if (e (s0, tail)) 0 = s ∧ FirstHit A B (e (s0, tail))
        then D.pathWeight (e (s0, tail)) else (0 : ℚ)))
      = ∑ s0 : S, ∑ tail : Fin (n + 1) → S,
        (if s0 = s ∧ FirstHit A B (Fin.cons (n := n + 1)
          (α := fun _ : Fin (n + 1 + 1) => S) s0 tail)
        then D.pathWeight (Fin.cons (n := n + 1)
          (α := fun _ : Fin (n + 1 + 1) => S) s0 tail) else 0) := by
    apply Finset.sum_congr rfl
    intro s0 _
    apply Finset.sum_congr rfl
    intro tail _
    exact hterm s0 tail
  rw [hcongr]
  rw [Fintype.sum_eq_single s]
  · apply Finset.sum_congr rfl
    intro tail _
    by_cases hFH : FirstHit A B (Fin.cons (n := n + 1)
      (α := fun _ : Fin (n + 1 + 1) => S) s tail)
    · have h : (s = s ∧ FirstHit A B (Fin.cons (n := n + 1)
        (α := fun _ : Fin (n + 1 + 1) => S) s tail)) := ⟨rfl, hFH⟩
      rw [ite_eq_left h, ite_eq_left hFH]
    · have h : ¬ (s = s ∧ FirstHit A B (Fin.cons (n := n + 1)
        (α := fun _ : Fin (n + 1 + 1) => S) s tail)) :=
        fun h => hFH h.2
      rw [ite_eq_right h, ite_eq_right hFH]
  · intro s0 hs0
    apply Finset.sum_eq_zero
    intro tail _
    have h : ¬ (s0 = s ∧ FirstHit A B (Fin.cons (n := n + 1)
      (α := fun _ : Fin (n + 1 + 1) => S) s0 tail)) :=
      fun h => hs0 h.1
    rw [ite_eq_right h]

private theorem sum_weight_fiber {S : Type*} [Fintype S] [DecidableEq S] (D : DTMC S) (n : ℕ)
    (f : S → ℚ) :
    (∑ tail : Fin (n + 1) → S, f (tail 0) * D.pathWeight tail)
      = ∑ t, f t * (∑ tail : Fin (n + 1) → S,
        if tail 0 = t then D.pathWeight tail else 0) := by
  have hrw : ∀ t : S, f t * (∑ tail : Fin (n + 1) → S,
      if tail 0 = t then D.pathWeight tail else 0)
      = ∑ tail : Fin (n + 1) → S,
        (if tail 0 = t then f t * D.pathWeight tail else 0) := by
    intro t
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro tail _
    by_cases h : tail 0 = t
    · rw [ite_eq_left h, ite_eq_left h]
    · rw [ite_eq_right h, ite_eq_right h, mul_zero]
  rw [Finset.sum_congr rfl (fun t _ => hrw t)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro tail _
  have hsingle : (∑ t : S,
      (if tail 0 = t then f t * D.pathWeight tail else (0 : ℚ)))
      = f (tail 0) * D.pathWeight tail := by
    have h0 : (∑ t : S,
        (if tail 0 = t then f t * D.pathWeight tail else (0 : ℚ)))
        = (if tail 0 = tail 0 then f (tail 0) * D.pathWeight tail
          else (0 : ℚ)) :=
      Fintype.sum_eq_single (tail 0) (fun t ht => by
        have h : tail 0 ≠ t := fun heq => ht heq.symm
        exact ite_eq_right h)
    have h2 : (if tail 0 = tail 0 then f (tail 0) * D.pathWeight tail
        else (0 : ℚ)) = f (tail 0) * D.pathWeight tail := ite_eq_left rfl
    rw [h2] at h0
    exact h0
  exact hsingle.symm

private theorem sum_weight_succ_unfold {S : Type*} [Fintype S] [DecidableEq S] (D : DTMC S)
    (n : ℕ) (s : S) :
    (∑ p : Fin (n + 1 + 1) → S,
      (if p 0 = s then D.pathWeight (n := n + 1) p else (0 : ℚ)))
      = ∑ tail : Fin (n + 1) → S,
        D.pathWeight (n := n + 1) (Fin.cons (n := n + 1)
          (α := fun _ : Fin (n + 1 + 1) => S) s tail) := by
  let e := Fin.consEquiv (n := n + 1) (fun _ : Fin (n + 1 + 1) => S)
  have hsum : (∑ p : Fin (n + 1 + 1) → S,
      (if p 0 = s then D.pathWeight (n := n + 1) p else (0 : ℚ)))
      = ∑ x : S × (Fin (n + 1) → S),
        (if (e x) 0 = s then D.pathWeight (n := n + 1) (e x) else 0) := by
    rw [← Equiv.sum_comp e]
  rw [hsum, Fintype.sum_prod_type]
  have heq : ∀ s0 : S, ∀ tail : Fin (n + 1) → S,
      e (s0, tail) = Fin.cons (n := n + 1)
        (α := fun _ : Fin (n + 1 + 1) => S) s0 tail := by
    intro s0 tail
    funext i
    simp only [e, Fin.consEquiv_apply]
  have hterm : ∀ s0 : S, ∀ tail : Fin (n + 1) → S,
      (if (e (s0, tail)) 0 = s
        then D.pathWeight (n := n + 1) (e (s0, tail)) else (0 : ℚ))
      = (if s0 = s
        then D.pathWeight (n := n + 1) (Fin.cons (n := n + 1)
          (α := fun _ : Fin (n + 1 + 1) => S) s0 tail) else 0) := by
    intro s0 tail
    rw [heq s0 tail]
    have h0 : ((Fin.cons (n := n + 1) (α := fun _ : Fin (n + 1 + 1) => S)
      s0 tail) 0) = s0 := by simp only [Fin.cons_zero]
    rw [h0]
  have hcongr : (∑ s0 : S, ∑ tail : Fin (n + 1) → S,
      (if (e (s0, tail)) 0 = s
        then D.pathWeight (n := n + 1) (e (s0, tail)) else (0 : ℚ)))
      = ∑ s0 : S, ∑ tail : Fin (n + 1) → S,
        (if s0 = s
        then D.pathWeight (n := n + 1) (Fin.cons (n := n + 1)
          (α := fun _ : Fin (n + 1 + 1) => S) s0 tail) else 0) := by
    apply Finset.sum_congr rfl
    intro s0 _
    apply Finset.sum_congr rfl
    intro tail _
    exact hterm s0 tail
  rw [hcongr]
  rw [Fintype.sum_eq_single s]
  · apply Finset.sum_congr rfl
    intro tail _
    rw [ite_eq_left rfl]
  · intro s0 hs0
    apply Finset.sum_eq_zero
    intro tail _
    rw [ite_eq_right hs0]

theorem sum_pathWeight_eq_one {S : Type*} [Fintype S] [DecidableEq S] (D : DTMC S)
    (n : ℕ) (s : S) :
    (∑ p : Fin (n + 1) → S,
      (if p 0 = s then D.pathWeight p else (0 : ℚ))) = 1 := by
  induction n generalizing s with
  | zero =>
    have hw : ∀ p : Fin (0 + 1) → S, D.pathWeight (n := 0) p = 1 := by
      intro p
      unfold DTMC.pathWeight
      simp
    have h1 : ∀ p : Fin (0 + 1) → S,
        (if p 0 = s then D.pathWeight (n := 0) p else (0 : ℚ))
        = (if p 0 = s then (1 : ℚ) else 0) := by
      intro p
      by_cases h : p 0 = s
      · rw [ite_eq_left h, ite_eq_left h, hw p]
      · rw [ite_eq_right h, ite_eq_right h]
    rw [Finset.sum_congr rfl (fun p _ => h1 p)]
    rw [Fintype.sum_eq_single (fun _ => s)]
    · simp
    · intro p hp
      have hne : p 0 ≠ s := fun heq => hp (funext fun i => by
        have hi : i = 0 := fin_one_eq_zero i
        rw [hi, heq])
      rw [ite_eq_right hne]
  | succ n IH =>
    rw [sum_weight_succ_unfold D n s]
    have hcons : ∀ tail : Fin (n + 1) → S,
        D.pathWeight (n := n + 1) (Fin.cons (n := n + 1)
          (α := fun _ : Fin (n + 1 + 1) => S) s tail)
          = D.P s (tail 0) * D.pathWeight tail :=
      fun tail => pathWeight_cons D n s tail
    rw [Finset.sum_congr rfl (fun tail _ => hcons tail)]
    rw [sum_weight_fiber D n (fun t => D.P s t)]
    have hIH : ∀ t : S, (∑ tail : Fin (n + 1) → S,
        if tail 0 = t then D.pathWeight tail else 0) = 1 :=
      fun t => IH t
    rw [Finset.sum_congr rfl (fun t _ => by rw [hIH t, mul_one])]
    exact D.row_sum s

private theorem sum_hit_fiber {S : Type*} [Fintype S] [DecidableEq S] (D : DTMC S)
    (A B : Finset S) (n : ℕ) (f : S → ℚ) :
    (∑ tail : Fin (n + 1) → S,
      (if FirstHit A B tail then f (tail 0) * D.pathWeight tail else (0 : ℚ)))
      = ∑ t, f t * D.hitProb A B n t := by
  have hrw : ∀ t : S, f t * D.hitProb A B n t
      = ∑ tail : Fin (n + 1) → S,
        (if tail 0 = t ∧ FirstHit A B tail
          then f t * D.pathWeight tail else (0 : ℚ)) := by
    intro t
    unfold DTMC.hitProb
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro tail _
    by_cases h : tail 0 = t ∧ FirstHit A B tail
    · rw [ite_eq_left h, ite_eq_left h]
    · have e1 : (if tail 0 = t ∧ FirstHit A B tail then D.pathWeight tail
          else (0 : ℚ)) = 0 := ite_eq_right h
      have e2 : (if tail 0 = t ∧ FirstHit A B tail
          then f t * D.pathWeight tail else (0 : ℚ)) = 0 := ite_eq_right h
      rw [e1, e2, mul_zero]
  have hmain : (∑ t, f t * D.hitProb A B n t)
      = ∑ tail : Fin (n + 1) → S,
        (if FirstHit A B tail then f (tail 0) * D.pathWeight tail
          else (0 : ℚ)) := by
    rw [Finset.sum_congr rfl (fun t _ => hrw t), Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro tail _
    by_cases hFH : FirstHit A B tail
    · have hsingle : (∑ t : S, (if tail 0 = t ∧ FirstHit A B tail
          then f t * D.pathWeight tail else (0 : ℚ)))
          = f (tail 0) * D.pathWeight tail := by
        have h0 : (∑ t : S, (if tail 0 = t ∧ FirstHit A B tail
            then f t * D.pathWeight tail else (0 : ℚ)))
            = (if tail 0 = tail 0 ∧ FirstHit A B tail
              then f (tail 0) * D.pathWeight tail else (0 : ℚ)) :=
          Fintype.sum_eq_single (tail 0) (fun t ht => by
            have h : ¬ (tail 0 = t ∧ FirstHit A B tail) :=
              fun h => ht h.1.symm
            exact ite_eq_right h)
        have h2 : (if tail 0 = tail 0 ∧ FirstHit A B tail
            then f (tail 0) * D.pathWeight tail else (0 : ℚ))
            = f (tail 0) * D.pathWeight tail :=
          ite_eq_left ⟨rfl, hFH⟩
        rw [h2] at h0
        exact h0
      rw [ite_eq_left hFH]
      exact hsingle
    · have hRHS : (if FirstHit A B tail then f (tail 0) * D.pathWeight tail
          else (0 : ℚ)) = 0 := ite_eq_right hFH
      rw [hRHS]
      apply Finset.sum_eq_zero
      intro t _
      exact ite_eq_right (fun h => hFH h.2)
  exact hmain.symm

/-- Horizon zero: hit exactly when starting in `B`. -/
theorem hitProb_zero (s : S) :
    D.hitProb A B 0 s = if s ∈ B then 1 else 0 := by
  unfold DTMC.hitProb
  have h1 : ∀ p : Fin (0 + 1) → S,
      (if p 0 = s ∧ FirstHit A B p then D.pathWeight p else 0)
      = (if p 0 = s ∧ p 0 ∈ B then (1 : ℚ) else 0) := by
    intro p
    have hw : D.pathWeight (n := 0) p = 1 := by
      unfold DTMC.pathWeight
      simp
    have hf : FirstHit A B p ↔ p 0 ∈ B := firstHit_zero_iff A B p
    by_cases h2 : (p 0 = s ∧ p 0 ∈ B)
    · have h : (p 0 = s ∧ FirstHit A B p) := ⟨h2.1, hf.mpr h2.2⟩
      rw [ite_eq_left h, ite_eq_left h2, hw]
    · have h : ¬ (p 0 = s ∧ FirstHit A B p) :=
        fun h => h2 ⟨h.1, hf.mp h.2⟩
      rw [ite_eq_right h, ite_eq_right h2]
  rw [Finset.sum_congr rfl (fun p _ => h1 p)]
  by_cases hs : s ∈ B
  · rw [ite_eq_left hs]
    have hsum : (∑ p : Fin (0 + 1) → S, (if p 0 = s ∧ p 0 ∈ B then (1 : ℚ) else 0))
        = ∑ p : Fin (0 + 1) → S, (if p 0 = s then (1 : ℚ) else 0) := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p 0 = s
      · have h2 : (p 0 = s ∧ p 0 ∈ B) := ⟨hp, by rw [hp]; exact hs⟩
        rw [ite_eq_left h2, ite_eq_left hp]
      · have h2 : ¬ (p 0 = s ∧ p 0 ∈ B) := fun h => hp h.1
        rw [ite_eq_right h2, ite_eq_right hp]
    rw [hsum]
    rw [Fintype.sum_eq_single (fun _ => s)]
    · simp
    · intro p hp
      have hne : p 0 ≠ s := fun heq => hp (funext fun i => by
        have hi : i = 0 := fin_one_eq_zero i
        rw [hi, heq])
      rw [ite_eq_right hne]
  · rw [ite_eq_right hs]
    apply Finset.sum_eq_zero
    intro p _
    have h2 : ¬ (p 0 = s ∧ p 0 ∈ B) := by
      intro h
      rw [h.1] at h
      exact hs h.2
    rw [ite_eq_right h2]

/-- The path-sum probabilities satisfy the Bellman recursion. -/
theorem hitProb_succ (n : ℕ) (s : S) :
    D.hitProb A B (n + 1) s =
      if s ∈ B then 1 else if s ∉ A then 0
        else ∑ t, D.P s t * D.hitProb A B n t := by
  by_cases hsB : s ∈ B
  · simp [hsB]
    rw [hitProb_succ_unfold D A B n s]
    have hterm : ∀ tail : Fin (n + 1) → S,
        (if FirstHit A B (Fin.cons (n := n + 1)
            (α := fun _ : Fin (n + 1 + 1) => S) s tail)
          then D.pathWeight (n := n + 1) (Fin.cons (n := n + 1)
            (α := fun _ : Fin (n + 1 + 1) => S) s tail) else (0 : ℚ))
        = D.P s (tail 0) * D.pathWeight tail := by
      intro tail
      have hFH : FirstHit A B (Fin.cons (n := n + 1)
        (α := fun _ : Fin (n + 1 + 1) => S) s tail) :=
        firstHit_cons_of_mem A B n s tail hsB
      rw [ite_eq_left hFH, pathWeight_cons D n s tail]
    rw [Finset.sum_congr rfl (fun tail _ => hterm tail)]
    rw [sum_weight_fiber D n (fun t => D.P s t)]
    have hW : ∀ t : S, (∑ tail : Fin (n + 1) → S,
        if tail 0 = t then D.pathWeight tail else 0) = 1 :=
      fun t => sum_pathWeight_eq_one D n t
    rw [Finset.sum_congr rfl (fun t _ => by rw [hW t, mul_one])]
    exact D.row_sum s
  · by_cases hsA : s ∈ A
    · simp [hsB, hsA]
      rw [hitProb_succ_unfold D A B n s]
      have hterm : ∀ tail : Fin (n + 1) → S,
          (if FirstHit A B (Fin.cons (n := n + 1)
              (α := fun _ : Fin (n + 1 + 1) => S) s tail)
            then D.pathWeight (n := n + 1) (Fin.cons (n := n + 1)
              (α := fun _ : Fin (n + 1 + 1) => S) s tail) else (0 : ℚ))
          = (if FirstHit A B tail then D.P s (tail 0) * D.pathWeight tail
            else 0) := by
        intro tail
        have hiff : FirstHit A B (Fin.cons (n := n + 1)
            (α := fun _ : Fin (n + 1 + 1) => S) s tail)
            ↔ (s ∈ A ∧ FirstHit A B tail) :=
          firstHit_cons_iff A B n s tail hsB
        have hw : D.pathWeight (n := n + 1) (Fin.cons (n := n + 1)
            (α := fun _ : Fin (n + 1 + 1) => S) s tail)
            = D.P s (tail 0) * D.pathWeight tail :=
          pathWeight_cons D n s tail
        by_cases hFH : FirstHit A B tail
        · have h : FirstHit A B (Fin.cons (n := n + 1)
            (α := fun _ : Fin (n + 1 + 1) => S) s tail) :=
            hiff.mpr ⟨hsA, hFH⟩
          rw [ite_eq_left h, ite_eq_left hFH, hw]
        · have h : ¬ FirstHit A B (Fin.cons (n := n + 1)
            (α := fun _ : Fin (n + 1 + 1) => S) s tail) :=
            fun h => hFH (hiff.mp h).2
          rw [ite_eq_right h, ite_eq_right hFH]
      rw [Finset.sum_congr rfl (fun tail _ => hterm tail)]
      exact sum_hit_fiber D A B n (fun t => D.P s t)
    · simp [hsB, hsA]
      rw [hitProb_succ_unfold D A B n s]
      apply Finset.sum_eq_zero
      intro tail _
      have hiff : FirstHit A B (Fin.cons (n := n + 1)
          (α := fun _ : Fin (n + 1 + 1) => S) s tail)
          ↔ (s ∈ A ∧ FirstHit A B tail) :=
        firstHit_cons_iff A B n s tail hsB
      have h : ¬ FirstHit A B (Fin.cons (n := n + 1)
          (α := fun _ : Fin (n + 1 + 1) => S) s tail) :=
        fun h => hsA (hiff.mp h).1
      rw [ite_eq_right h]

/-- Horizon probabilities increase with the horizon. -/
theorem hitProb_mono (s : S) : Monotone (D.hitProb A B · s) := by
  have hstep : ∀ n s, D.hitProb A B n s ≤ D.hitProb A B (n + 1) s := by
    intro n
    induction n with
    | zero =>
      intro s
      by_cases hsB : s ∈ B
      · rw [hitProb_zero, hitProb_succ]
        simp [hsB]
      · have h0 : D.hitProb A B 0 s = 0 := by
          rw [hitProb_zero]
          simp [hsB]
        rw [h0]
        exact hitProb_nonneg_aux D A B 1 s
    | succ n IH =>
      intro s
      rw [hitProb_succ, hitProb_succ]
      by_cases hsB : s ∈ B
      · simp [hsB]
      · by_cases hsA : s ∈ A
        · simp [hsB, hsA]
          apply Finset.sum_le_sum
          intro t _
          exact mul_le_mul_of_nonneg_left (IH t) (D.nonneg s t)
        · simp [hsB, hsA]
  exact monotone_nat_of_le_succ (fun n => hstep n s)

/-- Horizon probabilities are at most one. -/
theorem hitProb_le_one (n : ℕ) (s : S) : D.hitProb A B n s ≤ 1 := by
  induction n generalizing s with
  | zero =>
    rw [hitProb_zero]
    by_cases hs : s ∈ B
    · simp [hs]
    · simp [hs]
  | succ n IH =>
    rw [hitProb_succ]
    by_cases hsB : s ∈ B
    · simp [hsB]
    · by_cases hsA : s ∈ A
      · simp [hsB, hsA]
        calc ∑ t, D.P s t * D.hitProb A B n t
            ≤ ∑ t, D.P s t * 1 := by
              apply Finset.sum_le_sum
              intro t _
              exact mul_le_mul_of_nonneg_left (IH t) (D.nonneg s t)
          _ = ∑ t, D.P s t := by simp [mul_one]
          _ = 1 := D.row_sum s
      · simp [hsB, hsA]



/-- Horizon probabilities are nonnegative. -/
theorem hitProb_nonneg (n : ℕ) (s : S) : 0 ≤ D.hitProb A B n s := by
  exact hitProb_nonneg_aux D A B n s

/-- Every horizon probability is below the unbounded reachability
probability. -/
theorem DTMC.hitProb_le_reachProb (n : ℕ) (s : S) :
    (D.hitProb A B n s : ℝ) ≤ D.reachProb A B s := by
  have hbdd : BddAbove (Set.range (fun n => (D.hitProb A B n s : ℝ))) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    change (D.hitProb A B n s : ℝ) ≤ 1
    exact_mod_cast hitProb_le_one D A B n s
  unfold DTMC.reachProb
  exact le_ciSup hbdd n

/-- The horizon probabilities converge to the unbounded reachability
probability. -/
theorem DTMC.tendsto_hitProb_reachProb (s : S) :
    Filter.Tendsto (fun n => (D.hitProb A B n s : ℝ)) Filter.atTop
      (nhds (D.reachProb A B s)) := by
  have hmono : Monotone (fun n => (D.hitProb A B n s : ℝ)) := by
    intro a b hab
    change (D.hitProb A B a s : ℝ) ≤ (D.hitProb A B b s : ℝ)
    exact_mod_cast (hitProb_mono D A B s) hab
  have hbdd : BddAbove (Set.range (fun n => (D.hitProb A B n s : ℝ))) := by
    refine ⟨1, ?_⟩
    rintro _ ⟨n, rfl⟩
    change (D.hitProb A B n s : ℝ) ≤ 1
    exact_mod_cast hitProb_le_one D A B n s
  unfold DTMC.reachProb
  exact tendsto_atTop_ciSup hmono hbdd

theorem DTMC.hitProb_cast_bdd {S : Type*} [Fintype S] [DecidableEq S] (D : DTMC S)
    (A B : Finset S) (s : S) :
    BddAbove (Set.range (fun n => (D.hitProb A B n s : ℝ))) := by
  refine ⟨1, ?_⟩
  rintro y ⟨n, rfl⟩
  have h := hitProb_le_one (S := S) D A B n s
  have hc : ((D.hitProb A B n s : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := by
    exact_mod_cast h
  simpa using hc

theorem DTMC.hitProb_cast_mono {S : Type*} [Fintype S] [DecidableEq S] (D : DTMC S)
    (A B : Finset S) (s : S) :
    Monotone (fun n => (D.hitProb A B n s : ℝ)) := by
  intro m n hmn
  have h : D.hitProb A B m s ≤ D.hitProb A B n s :=
    hitProb_mono (S := S) D A B s hmn
  change ((D.hitProb A B m s : ℚ) : ℝ) ≤ ((D.hitProb A B n s : ℚ) : ℝ)
  exact_mod_cast h

/-- The reachability probability is a Bellman fixed point. -/
theorem reachProb_apply (s : S) :
    D.reachProb A B s = D.bellman A B (D.reachProb A B) s := by
  by_cases hsB : s ∈ B
  · have h1 : ∀ n, D.hitProb A B n s = 1 := by
      intro n
      cases n with
      | zero =>
        have hz := hitProb_zero (S := S) D A B s
        rw [ite_eq_left hsB] at hz
        exact hz
      | succ n =>
        have hs := hitProb_succ (S := S) D A B n s
        rw [ite_eq_left hsB] at hs
        exact hs
    have hreach : D.reachProb A B s = 1 := by
      have hconst : (fun n => ((D.hitProb A B n s : ℚ) : ℝ)) = fun _ => (1 : ℝ) := by
        funext n
        have h := h1 n
        have hc : ((D.hitProb A B n s : ℚ) : ℝ) = ((1 : ℚ) : ℝ) := by
          exact_mod_cast h
        simpa using hc
      unfold DTMC.reachProb
      rw [hconst]
      exact ciSup_const
    have hbell : D.bellman A B (D.reachProb A B) s = 1 := by
      unfold DTMC.bellman
      simp only [hsB, ite_true]
    rw [hreach, hbell]
  · by_cases hsA : s ∈ A
    · have hsA' : ¬ s ∉ A := by simpa using hsA
      have hbell : D.bellman A B (D.reachProb A B) s
          = ∑ t, (D.P s t : ℝ) * D.reachProb A B t := by
        unfold DTMC.bellman
        rw [ite_eq_right hsB, ite_eq_right hsA']
      have hrec : ∀ n, ((D.hitProb A B (n + 1) s : ℚ) : ℝ)
          = ∑ t, (D.P s t : ℝ) * ((D.hitProb A B n t : ℚ) : ℝ) := by
        intro n
        have hs := hitProb_succ (S := S) D A B n s
        rw [ite_eq_right hsB, ite_eq_right hsA'] at hs
        have hcast : ((D.hitProb A B (n + 1) s : ℚ) : ℝ)
            = ((∑ t, D.P s t * D.hitProb A B n t : ℚ) : ℝ) := by
          exact_mod_cast hs
        rw [hcast]
        simp only [Rat.cast_sum, Rat.cast_mul]
      have hmono : Monotone (fun n => ((D.hitProb A B n s : ℚ) : ℝ)) :=
        DTMC.hitProb_cast_mono D A B s
      have hbdd : BddAbove (Set.range (fun n => ((D.hitProb A B n s : ℚ) : ℝ))) :=
        DTMC.hitProb_cast_bdd D A B s
      have htend : Filter.Tendsto (fun n => ((D.hitProb A B n s : ℚ) : ℝ))
          Filter.atTop (nhds (⨆ n, ((D.hitProb A B n s : ℚ) : ℝ))) :=
        tendsto_atTop_ciSup hmono hbdd
      have htend_each : ∀ t : S, Filter.Tendsto
          (fun n => ((D.hitProb A B n t : ℚ) : ℝ))
          Filter.atTop (nhds (⨆ n, ((D.hitProb A B n t : ℚ) : ℝ))) := by
        intro t
        exact tendsto_atTop_ciSup (DTMC.hitProb_cast_mono D A B t)
          (DTMC.hitProb_cast_bdd D A B t)
      have hsum_tend : Filter.Tendsto
          (fun n => ∑ t, (D.P s t : ℝ) * ((D.hitProb A B n t : ℚ) : ℝ))
          Filter.atTop
          (nhds (∑ t, (D.P s t : ℝ) * (⨆ n, ((D.hitProb A B n t : ℚ) : ℝ)))) := by
        have h := tendsto_finsetSum (s := Finset.univ)
          (fun t _ => Filter.Tendsto.const_mul (D.P s t : ℝ) (htend_each t))
        simpa using h
      have hshift : Filter.Tendsto (fun n => ((D.hitProb A B (n + 1) s : ℚ) : ℝ))
          Filter.atTop (nhds (⨆ n, ((D.hitProb A B n s : ℚ) : ℝ))) := by
        have h := (Filter.tendsto_add_atTop_iff_nat 1).mpr htend
        simpa using h
      have hshift2 : Filter.Tendsto (fun n => ((D.hitProb A B (n + 1) s : ℚ) : ℝ))
          Filter.atTop
          (nhds (∑ t, (D.P s t : ℝ) * (⨆ n, ((D.hitProb A B n t : ℚ) : ℝ)))) := by
        have heq : (fun n => ((D.hitProb A B (n + 1) s : ℚ) : ℝ))
            = fun n => ∑ t, (D.P s t : ℝ) * ((D.hitProb A B n t : ℚ) : ℝ) := by
          funext n
          exact hrec n
        rw [heq]
        exact hsum_tend
      have heq : (⨆ n, ((D.hitProb A B n s : ℚ) : ℝ))
          = ∑ t, (D.P s t : ℝ) * (⨆ n, ((D.hitProb A B n t : ℚ) : ℝ)) :=
        tendsto_nhds_unique hshift hshift2
      have hreach : D.reachProb A B s = ⨆ n, ((D.hitProb A B n s : ℚ) : ℝ) := rfl
      have hbell2 : (∑ t, (D.P s t : ℝ) * D.reachProb A B t)
          = ∑ t, (D.P s t : ℝ) * (⨆ n, ((D.hitProb A B n t : ℚ) : ℝ)) := rfl
      rw [hreach, hbell, hbell2]
      exact heq
    · have h0 : ∀ n, D.hitProb A B n s = 0 := by
        intro n
        induction n with
        | zero =>
          have hz := hitProb_zero (S := S) D A B s
          rw [ite_eq_right hsB] at hz
          exact hz
        | succ n IH =>
          have hs := hitProb_succ (S := S) D A B n s
          rw [ite_eq_right hsB, ite_eq_left hsA] at hs
          exact hs
      have hreach : D.reachProb A B s = 0 := by
        have hconst : (fun n => ((D.hitProb A B n s : ℚ) : ℝ)) = fun _ => (0 : ℝ) := by
          funext n
          have h := h0 n
          exact_mod_cast h
        unfold DTMC.reachProb
        rw [hconst]
        exact ciSup_const
      have hbell : D.bellman A B (D.reachProb A B) s = 0 := by
        unfold DTMC.bellman
        rw [ite_eq_right hsB, ite_eq_left hsA]
      rw [hreach, hbell]

/-- The reachability probability is the least nonnegative pre-fixed
point: any nonnegative function pointwise above its Bellman image is
pointwise above it. -/
theorem reachProb_least (x : S → ℝ)
    (hx0 : ∀ s, 0 ≤ x s) (hx : ∀ s, D.bellman A B x s ≤ x s) (s : S) :
    D.reachProb A B s ≤ x s := by
  have hall : ∀ n st, ((D.hitProb A B n st : ℚ) : ℝ) ≤ x st := by
    intro n
    induction n with
    | zero =>
      intro st
      have hz := hitProb_zero (S := S) D A B st
      by_cases hsB : st ∈ B
      · rw [hz]
        simp only [hsB, ite_true]
        have hbx := hx st
        unfold DTMC.bellman at hbx
        simp only [hsB, ite_true] at hbx
        simpa using hbx
      · rw [hz]
        simp only [hsB, ite_false]
        simpa using hx0 st
    | succ n IH =>
      intro st
      have hs := hitProb_succ (S := S) D A B n st
      by_cases hsB : st ∈ B
      · rw [hs]
        simp only [hsB, ite_true]
        have hbx := hx st
        unfold DTMC.bellman at hbx
        simp only [hsB, ite_true] at hbx
        simpa using hbx
      · by_cases hsA : st ∈ A
        · have hsA' : ¬ st ∉ A := by simpa using hsA
          rw [hs, ite_eq_right hsB, ite_eq_right hsA']
          have hbx := hx st
          unfold DTMC.bellman at hbx
          rw [ite_eq_right hsB, ite_eq_right hsA'] at hbx
          have hsum : ((∑ t, D.P st t * D.hitProb A B n t : ℚ) : ℝ)
              = ∑ t, (D.P st t : ℝ) * ((D.hitProb A B n t : ℚ) : ℝ) := by
            simp only [Rat.cast_sum, Rat.cast_mul]
          rw [hsum]
          calc ∑ t, (D.P st t : ℝ) * ((D.hitProb A B n t : ℚ) : ℝ)
              ≤ ∑ t, (D.P st t : ℝ) * x t := by
                apply Finset.sum_le_sum
                intro t _
                have hPt : (0 : ℝ) ≤ (D.P st t : ℝ) := by
                  exact_mod_cast D.nonneg st t
                exact mul_le_mul_of_nonneg_left (IH t) hPt
            _ ≤ x st := hbx
        · rw [hs, ite_eq_right hsB, ite_eq_left hsA]
          simpa using hx0 st
  unfold DTMC.reachProb
  exact ciSup_le (fun n => hall n s)

/-- The reachability probability is a genuine probability value. -/
theorem reachProb_nonneg (s : S) : 0 ≤ D.reachProb A B s := by
  unfold DTMC.reachProb
  have hb := DTMC.hitProb_cast_bdd D A B s
  have h0 : (0 : ℝ) ≤ ((D.hitProb A B 0 s : ℚ) : ℝ) := by
    have h := hitProb_nonneg (S := S) D A B 0 s
    exact_mod_cast h
  calc (0 : ℝ) ≤ ((D.hitProb A B 0 s : ℚ) : ℝ) := h0
    _ ≤ ⨆ n, ((D.hitProb A B n s : ℚ) : ℝ) := le_ciSup hb 0

/-- The reachability probability is at most one. -/
theorem reachProb_le_one (s : S) : D.reachProb A B s ≤ 1 := by
  unfold DTMC.reachProb
  apply ciSup_le
  intro n
  have h := hitProb_le_one (S := S) D A B n s
  have hc : ((D.hitProb A B n s : ℚ) : ℝ) ≤ ((1 : ℚ) : ℝ) := by
    exact_mod_cast h
  simpa using hc

end Cslib.Probability
