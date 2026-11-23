/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

@[expose] public section

/-!
# Russian-roulette path weights and masses

This module is the finite-level layer only: it defines raw weights and masses of
fixed-length paths in a finite state space. It does not by itself define a
probability law or an estimator expectation.

A path is `x : Fin (n + 1) → S` with `n` transitions, starting at `x 0`; the
level-`n` sums run over such paths with `x 0 = i`.

Here `q` is the stop (termination) probability and `P` the conditional next-state
kernel given survival, so the survival kernel is `Q = (1 − q) • P` entrywise
(`stepKernel`), and the stop factor `q` is applied at the path's final state. This
is the termination-probability convention, not a continuation probability.

This is the finite translation of Kong and Spanier, "A new proof of geometric
convergence for general transport problems based on sequential correlated sampling
methods", Journal of Computational Physics 227(23), 2008, pp. 9762–9777,
DOI 10.1016/j.jcp.2008.07.016: their equations (8)–(9) (substochastic kernel with
row mass `1 − p̂`, conditional law, termination probability `p̂`, here `p̂ ↦ q`,
kernel ↦ `Q`, conditional law ↦ `P`); equation (11)'s accumulated-score estimator
is formalized in downstream modules, not here. See also M. Pharr, W. Jakob and
G. Humphreys, Physically Based Rendering, 4th edition, MIT Press, 2023, §2.2.4
(Russian Roulette), which uses the same termination-probability convention.
-/

namespace RussianRoulette

/-- Continuation (survival) kernel `Q i j = (1 - q i) * P i j`, where `q` is the
stop probability and `P` the conditional next-state kernel. -/
def stepKernel {S : Type*} (q : S → ℝ) (P : S → S → ℝ) (i j : S) : ℝ :=
  (1 - q i) * P i j

/-- Weight of a fixed-length path `x : Fin (n+1) → S` under the survival kernel:
the product of `Q` along its `n` transitions. Raw weight, not a probability
law. -/
def survivalWeight {S : Type*} (Q : S → S → ℝ) {n : ℕ} (x : Fin (n + 1) → S) : ℝ :=
  ∏ k : Fin n, Q (x k.castSucc) (x k.succ)

/-- Completed-path weight: survival weight times the stop probability at the
final state. -/
def completedWeight {S : Type*} (q : S → ℝ) (Q : S → S → ℝ) {n : ℕ}
    (x : Fin (n + 1) → S) : ℝ :=
  q (x (Fin.last n)) * survivalWeight Q x

/-- Total survival weight of length-`n` prefixes starting at `i` (raw mass of
paths that have not stopped in the first `n` transitions). -/
noncomputable def survivalMass {S : Type*} [Fintype S] [DecidableEq S] (Q : S → S → ℝ) (i : S)
    (n : ℕ) : ℝ :=
  ∑ x : Fin (n + 1) → S, if x 0 = i then survivalWeight Q x else 0

/-- Total completed-path weight of paths from `i` with exactly `n` transitions
(raw stopped mass at level `n`). -/
noncomputable def stoppedMass {S : Type*} [Fintype S] [DecidableEq S] (q : S → ℝ) (Q : S → S → ℝ)
    (i : S) (n : ℕ) : ℝ :=
  ∑ x : Fin (n + 1) → S, if x 0 = i then completedWeight q Q x else 0

/-- Appending a final state preserves a path's initial state. -/
private theorem snoc_apply_zero {S : Type*} (n : ℕ) (x : Fin (n + 1) → S) (j : S) :
    Fin.snoc (α := fun _ => S) x j 0 = x 0 := by
  rw [← Fin.castSucc_zero, Fin.snoc_castSucc]

/-- Survival weight factors over the appended last transition. -/
theorem survivalWeight_snoc {S : Type*} (Q : S → S → ℝ)
    (n : ℕ) (x : Fin (n + 1) → S) (j : S) :
    survivalWeight Q (Fin.snoc (α := fun _ => S) x j) =
      survivalWeight Q x * Q (x (Fin.last n)) j := by
  have hcast : ∀ k : Fin n, k.castSucc.succ = k.succ.castSucc := fun k => by ext; simp
  have hlast : (Fin.last n).succ = Fin.last (n + 1) := by ext; simp
  unfold survivalWeight
  rw [Fin.prod_univ_castSucc]
  rw [hlast]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, hcast]

/-- One-step extension: survival mass at level `n + 1`, factored over
length-`n` prefixes times the row mass at each prefix's final state. -/
private theorem survivalMass_succ_eq {S : Type*} [Fintype S] [DecidableEq S]
    (Q : S → S → ℝ) (i : S) (n : ℕ) :
    survivalMass Q i (n + 1) =
      ∑ x : Fin (n + 1) → S,
        if x 0 = i then survivalWeight Q x * (∑ k : S, Q (x (Fin.last n)) k) else 0 := by
  unfold survivalMass
  let e : (Fin (n + 1) → S) × S ≃ (Fin (n + 1 + 1) → S) :=
    (Equiv.prodComm _ _).trans (Fin.snocEquiv fun _ => S)
  have he : ∀ (a : Fin (n + 1) → S) (b : S) (t : Fin (n + 1 + 1)),
      e (a, b) t = Fin.snoc (α := fun _ => S) a b t := by
    intro a b t
    change (Fin.snocEquiv fun _ => S) (b, a) t
      = Fin.snoc (α := fun _ => S) a b t
    exact congrFun (Fin.snocEquiv_apply _ _) t
  have hef : ∀ a b, e (a, b) = Fin.snoc (α := fun _ => S) a b :=
    fun a b => funext (he a b)
  calc ∑ y : Fin (n + 1 + 1) → S, (if y 0 = i then survivalWeight Q y else 0)
      = ∑ _p : (Fin (n + 1) → S) × S,
          (if (e _p) 0 = i then survivalWeight Q (e _p) else 0) :=
        (Equiv.sum_comp e _).symm
    _ = ∑ x : Fin (n + 1) → S, ∑ j : S,
          (if (e (x, j)) 0 = i then survivalWeight Q (e (x, j)) else 0) :=
        Fintype.sum_prod_type _
    _ = ∑ x : Fin (n + 1) → S, ∑ j : S,
          (if x 0 = i then survivalWeight Q x * Q (x (Fin.last n)) j else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        apply Finset.sum_congr rfl
        intro j _
        show (if (e (x, j)) 0 = i then survivalWeight Q (e (x, j)) else 0) =
          (if x 0 = i then survivalWeight Q x * Q (x (Fin.last n)) j else 0)
        rw [hef, snoc_apply_zero, survivalWeight_snoc]
    _ = ∑ x : Fin (n + 1) → S,
          (if x 0 = i then survivalWeight Q x * (∑ k : S, Q (x (Fin.last n)) k) else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x 0 = i
        · simp only [ite_eq_left hx, ← Finset.mul_sum]
        · simp [hx]

theorem survivalMass_zero {S : Type*} [Fintype S] [DecidableEq S] (Q : S → S → ℝ) (i : S) :
    survivalMass Q i 0 = 1 := by
  have hprod : ∀ x : Fin (0 + 1) → S, survivalWeight Q x = 1 := by
    intro x
    unfold survivalWeight
    simp
  unfold survivalMass
  simp only [hprod]
  change ∑ x : Fin 1 → S, (if x 0 = i then (1 : ℝ) else 0) = 1
  have h : ∀ x : Fin 1 → S, x ≠ (fun _ => i) → (if x 0 = i then (1 : ℝ) else 0) = 0 := by
    intro x hx
    have hxi : ¬(x 0 = i) := by
      intro hcon
      apply hx
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      rw [hj]
      exact hcon
    simp [hxi]
  rw [Fintype.sum_eq_single _ h]
  simp

theorem survivalMass_stoppedMass {S : Type*} [Fintype S] [DecidableEq S] (q : S → ℝ) (Q : S → S → ℝ)
    (hrow : ∀ j : S, q j + ∑ k : S, Q j k = 1) (i : S) (n : ℕ) :
    stoppedMass q Q i n + survivalMass Q i (n + 1) = survivalMass Q i n := by
  rw [survivalMass_succ_eq Q i n]
  unfold stoppedMass survivalMass
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases hx : x 0 = i
  · simp only [ite_eq_left hx]
    unfold completedWeight
    have h1 := hrow (x (Fin.last n))
    have hfactor : q (x (Fin.last n)) * survivalWeight Q x
          + survivalWeight Q x * (∑ k, Q (x (Fin.last n)) k)
        = survivalWeight Q x * (q (x (Fin.last n)) + ∑ k, Q (x (Fin.last n)) k) := by
      ring
    rw [hfactor, h1, mul_one]
  · simp [hx]

theorem sum_stoppedMass_add_survival {S : Type*} [Fintype S] [DecidableEq S] (q : S → ℝ)
    (Q : S → S → ℝ) (hrow : ∀ j : S, q j + ∑ k : S, Q j k = 1) (i : S) (n : ℕ) :
    (∑ k ∈ Finset.range n, stoppedMass q Q i k) + survivalMass Q i n = 1 := by
  induction n with
  | zero =>
      rw [Finset.sum_range_zero, survivalMass_zero, zero_add]
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have h := survivalMass_stoppedMass q Q hrow i n
      linear_combination ih + h

theorem survivalMass_nonneg {S : Type*} [Fintype S] [DecidableEq S] (Q : S → S → ℝ)
    (hQ : ∀ a b : S, 0 ≤ Q a b) (i : S) (n : ℕ) :
    0 ≤ survivalMass Q i n := by
  unfold survivalMass
  apply Finset.sum_nonneg
  intro x _
  split_ifs with h
  · unfold survivalWeight
    exact Finset.prod_nonneg fun k _ => hQ _ _
  · exact le_rfl

theorem stoppedMass_nonneg {S : Type*} [Fintype S] [DecidableEq S] (q : S → ℝ) (Q : S → S → ℝ)
    (hq : ∀ a : S, 0 ≤ q a) (hQ : ∀ a b : S, 0 ≤ Q a b) (i : S) (n : ℕ) :
    0 ≤ stoppedMass q Q i n := by
  unfold stoppedMass
  apply Finset.sum_nonneg
  intro x _
  split_ifs with h
  · unfold completedWeight survivalWeight
    exact mul_nonneg (hq _) (Finset.prod_nonneg fun k _ => hQ _ _)
  · exact le_rfl

theorem survivalMass_le_pow {S : Type*} [Fintype S] [DecidableEq S] (Q : S → S → ℝ) (c : ℝ)
    (hQ : ∀ a b : S, 0 ≤ Q a b) (hrow : ∀ a : S, ∑ b : S, Q a b ≤ c) (i : S)
    (n : ℕ) :
    survivalMass Q i n ≤ c ^ n := by
  have h0 : (0 : ℝ) ≤ ∑ b : S, Q i b := Finset.sum_nonneg fun b _ => hQ i b
  have hc : 0 ≤ c := le_trans h0 (hrow i)
  induction n with
  | zero =>
      rw [survivalMass_zero]
      simp
  | succ n ih =>
      rw [survivalMass_succ_eq Q i n]
      have hterm : ∀ x : Fin (n + 1) → S,
          (if x 0 = i then survivalWeight Q x * (∑ k, Q (x (Fin.last n)) k) else 0)
          ≤ (if x 0 = i then survivalWeight Q x * c else 0) := by
        intro x
        by_cases hx : x 0 = i
        · simp only [ite_eq_left hx]
          apply mul_le_mul_of_nonneg_left
          · exact hrow _
          · unfold survivalWeight
            exact Finset.prod_nonneg fun k _ => hQ _ _
        · simp [hx]
      calc ∑ x : Fin (n + 1) → S,
            (if x 0 = i then survivalWeight Q x * (∑ k, Q (x (Fin.last n)) k) else 0)
          ≤ ∑ x : Fin (n + 1) → S, (if x 0 = i then survivalWeight Q x * c else 0) :=
            Finset.sum_le_sum fun x _ => hterm x
        _ = c * survivalMass Q i n := by
            unfold survivalMass
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            by_cases hx : x 0 = i
            · simp only [ite_eq_left hx]
              exact mul_comm _ _
            · simp [hx]
        _ ≤ c * c ^ n := mul_le_mul_of_nonneg_left ih hc
        _ = c ^ (n + 1) := (pow_succ' c n).symm

theorem sum_survivalMass_le {S : Type*} [Fintype S] [DecidableEq S] (q : S → ℝ) (P : S → S → ℝ)
    (qmin : ℝ) (hq0 : 0 < qmin)
    (hq : ∀ a : S, qmin ≤ q a ∧ q a ≤ 1)
    (hP : ∀ a b : S, 0 ≤ P a b) (hProw : ∀ a : S, ∑ b : S, P a b = 1) (i : S)
    (n : ℕ) :
    ∑ k ∈ Finset.range n, survivalMass (stepKernel q P) i k ≤ 1 / qmin := by
  have hq1 : qmin ≤ 1 := (hq i).1.trans (hq i).2
  have hQ : ∀ a b : S, 0 ≤ stepKernel q P a b := by
    intro a b
    unfold stepKernel
    apply mul_nonneg
    · have ha := (hq a).2
      linarith
    · exact hP a b
  have hrowQ : ∀ a : S, ∑ b : S, stepKernel q P a b = 1 - q a := by
    intro a
    unfold stepKernel
    rw [← Finset.mul_sum, hProw a, mul_one]
  have hterm : ∀ k : ℕ, survivalMass (stepKernel q P) i k ≤ (1 - qmin) ^ k := by
    intro k
    refine survivalMass_le_pow _ _ hQ ?_ i k
    intro a
    rw [hrowQ a]
    have ha := (hq a).1
    linarith
  calc ∑ k ∈ Finset.range n, survivalMass (stepKernel q P) i k
      ≤ ∑ k ∈ Finset.range n, (1 - qmin) ^ k :=
        Finset.sum_le_sum fun k _ => hterm k
    _ ≤ 1 / qmin := by
        have hgeom := geom_sum_mul (1 - qmin) n
        have hpow : (0 : ℝ) ≤ (1 - qmin) ^ n := pow_nonneg (by linarith) n
        have hSmul : (∑ k ∈ Finset.range n, (1 - qmin) ^ k) * qmin
            = 1 - (1 - qmin) ^ n := by
          linear_combination -hgeom
        rw [le_div_iff₀ hq0, hSmul]
        linarith [hpow]

end RussianRoulette

end
public section
