/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.RoulettePathMass
public import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

@[expose] public section

namespace RussianRoulette

/-- Accumulated likelihood-ratio weight along a fixed-length path: the
product of `T / Q` over its transitions. Ratios at zero-denominator edges
are totalized to zero by real division. -/
noncomputable def ratioWeight {S : Type*} (T Q : S → S → ℝ) {n : ℕ} (x : Fin (n + 1) → S) : ℝ :=
  ∏ k : Fin n, (T (x k.castSucc) (x k.succ) / Q (x k.castSucc) (x k.succ))

/-- Under the support condition, sampling and ratio weights cancel along
every fixed-length path. -/
theorem survivalWeight_mul_ratioWeight {S : Type*} (T Q : S → S → ℝ)
    (hsupp : ∀ a b : S, Q a b = 0 → T a b = 0) {n : ℕ} (x : Fin (n + 1) → S) :
    survivalWeight Q x * ratioWeight T Q x = survivalWeight T x := by
  unfold survivalWeight ratioWeight
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  by_cases h : Q (x k.castSucc) (x k.succ) = 0
  · have hT := hsupp _ _ h
    simp [h, hT]
  · field_simp

/-- Path-sum expansion of matrix powers, with the emission vector and start
state generalized for the induction step. -/
private theorem sum_survivalWeight_aux {S : Type*} [Fintype S] [DecidableEq S]
    (T : S → S → ℝ) (n : ℕ) (E : S → ℝ) (i : S) :
    (∑ x : Fin (n + 1) → S,
      if x 0 = i then survivalWeight T x * E (x (Fin.last n)) else 0)
      = ((Matrix.of T) ^ n).mulVec E i := by
  induction n generalizing E i with
  | zero =>
      have hsw : ∀ x : Fin (0 + 1) → S, survivalWeight T x = 1 := by
        intro x
        unfold survivalWeight
        simp
      have hlast : ∀ x : Fin (0 + 1) → S, x (Fin.last 0) = x 0 :=
        fun x => congrArg x rfl
      simp only [hsw, hlast, one_mul]
      change (∑ x : Fin 1 → S, (if x 0 = i then E (x 0) else 0))
        = ((Matrix.of T) ^ 0).mulVec E i
      have h : ∀ x : Fin 1 → S, x ≠ (fun _ => i) →
          (if x 0 = i then E (x 0) else 0) = 0 := by
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
  | succ n ih =>
      have hE' : ∀ k : S, (Matrix.of T).mulVec E k = ∑ j, T k j * E j := by
        intro k
        simp only [Matrix.mulVec_apply_eq_sum, Matrix.of_apply]
      have hfactor : (∑ y : Fin (n + 1 + 1) → S,
            if y 0 = i then survivalWeight T y * E (y (Fin.last (n + 1))) else 0)
          = (∑ x : Fin (n + 1) → S,
            if x 0 = i then survivalWeight T x * (Matrix.of T).mulVec E (x (Fin.last n))
            else 0) := by
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
        calc ∑ y : Fin (n + 1 + 1) → S,
                (if y 0 = i then survivalWeight T y * E (y (Fin.last (n + 1))) else 0)
            = ∑ _p : (Fin (n + 1) → S) × S,
                (if (e _p) 0 = i then survivalWeight T (e _p)
                  * E ((e _p) (Fin.last (n + 1))) else 0) :=
              (Equiv.sum_comp e _).symm
          _ = ∑ x : Fin (n + 1) → S, ∑ j : S,
                (if (e (x, j)) 0 = i then survivalWeight T (e (x, j))
                  * E ((e (x, j)) (Fin.last (n + 1))) else 0) :=
              Fintype.sum_prod_type _
          _ = ∑ x : Fin (n + 1) → S, ∑ j : S,
                (if x 0 = i then survivalWeight T x * T (x (Fin.last n)) j * E j
                else 0) := by
              apply Finset.sum_congr rfl
              intro x _
              apply Finset.sum_congr rfl
              intro j _
              rw [hef, Fin.snoc_apply_zero, survivalWeight_snoc, Fin.snoc_last]
          _ = ∑ x : Fin (n + 1) → S,
                (if x 0 = i then survivalWeight T x * (Matrix.of T).mulVec E (x (Fin.last n))
                else 0) := by
              apply Finset.sum_congr rfl
              intro x _
              by_cases hx : x 0 = i
              · simp only [ite_eq_left hx, hE', Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _
                rw [mul_assoc]
              · simp [hx]
      rw [hfactor]
      have hrhs : ((Matrix.of T) ^ (n + 1)).mulVec E i
          = ((Matrix.of T) ^ n).mulVec ((Matrix.of T).mulVec E) i := by
        rw [pow_succ, ← Matrix.mulVec_mulVec]
      rw [hrhs]
      exact ih _ _

/-- Fixed-length path sums of a kernel against an emission vector are the
entries of the corresponding matrix power applied to the vector. -/
theorem sum_survivalWeight_eq_pow_mulVec {S : Type*} [Fintype S] [DecidableEq S]
    (T : S → S → ℝ) (E : S → ℝ) (i : S) (n : ℕ) :
    (∑ x : Fin (n + 1) → S,
      if x 0 = i then survivalWeight T x * E (x (Fin.last n)) else 0)
      = ((Matrix.of T) ^ n).mulVec E i :=
  sum_survivalWeight_aux T n E i

/-- The level-`n` contribution of the accumulated-score estimator, summed
over all length-`n` prefixes weighted by their survival mass, is the `n`-th
Neumann term. Finite identity; no convergence claim. -/
theorem sum_prefixContribution_eq_pow_mulVec {S : Type*} [Fintype S] [DecidableEq S]
    (T Q : S → S → ℝ) (hsupp : ∀ a b : S, Q a b = 0 → T a b = 0) (E : S → ℝ)
    (i : S) (n : ℕ) :
    (∑ x : Fin (n + 1) → S,
      if x 0 = i then survivalWeight Q x * ratioWeight T Q x * E (x (Fin.last n))
      else 0)
      = ((Matrix.of T) ^ n).mulVec E i := by
  calc (∑ x : Fin (n + 1) → S,
          if x 0 = i then survivalWeight Q x * ratioWeight T Q x * E (x (Fin.last n))
          else 0)
      = (∑ x : Fin (n + 1) → S,
          if x 0 = i then survivalWeight T x * E (x (Fin.last n)) else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x 0 = i
        · simp only [ite_eq_left hx]
          rw [survivalWeight_mul_ratioWeight T Q hsupp x]
        · simp [hx]
    _ = ((Matrix.of T) ^ n).mulVec E i :=
        sum_survivalWeight_eq_pow_mulVec T E i n

end RussianRoulette

end
public section
