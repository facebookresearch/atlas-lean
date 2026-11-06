/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Star.Real

@[expose] public section

open Finset BigOperators

namespace MathlibExt.Probability.EfronStein

/-!
# Efron–Stein inequality (finite iid specialization)
-/

/-- Variance about the mean equals mean of squares minus square of mean. -/
private theorem var_eq_mean_sq_sub
    (ι : Type*) [Fintype ι]
    (w z : ι → ℝ)
    (hw_sum : ∑ a : ι, w a = 1) :
    ∑ a : ι, w a * (z a - (∑ b : ι, w b * z b)) ^ 2
      = (∑ a : ι, w a * (z a) ^ 2) - (∑ a : ι, w a * z a) ^ 2 := by
  have expand : ∀ a : ι, w a * (z a - (∑ b : ι, w b * z b)) ^ 2
      = w a * (z a) ^ 2 - (2 * (∑ b : ι, w b * z b)) * (w a * z a)
        + ((∑ b : ι, w b * z b) ^ 2) * w a := by
    intro a
    ring
  rw [Finset.sum_congr rfl (fun a _ => expand a)]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h1 : (∑ a : ι, (2 * (∑ b : ι, w b * z b)) * (w a * z a))
      = 2 * (∑ a : ι, w a * z a) ^ 2 := by
    rw [← Finset.mul_sum]
    ring
  have h2 : (∑ a : ι, (∑ b : ι, w b * z b) ^ 2 * w a)
      = (∑ a : ι, w a * z a) ^ 2 := by
    rw [← Finset.mul_sum]
    rw [hw_sum, mul_one]
  rw [h1, h2]
  ring

/-- Finite Jensen for the square: (E Z)^2 ≤ E Z^2. -/
private theorem sq_mean_le_mean_sq
    (ι : Type*) [Fintype ι]
    (w z : ι → ℝ)
    (hw_nonneg : ∀ a : ι, 0 ≤ w a)
    (hw_sum : ∑ a : ι, w a = 1) :
    (∑ a : ι, w a * z a) ^ 2 ≤ ∑ a : ι, w a * (z a) ^ 2 := by
  have hnn : 0 ≤ ∑ a : ι, w a * (z a - (∑ b : ι, w b * z b)) ^ 2 := by
    apply Finset.sum_nonneg
    intro a _
    apply mul_nonneg (hw_nonneg a)
    exact sq_nonneg _
  rw [var_eq_mean_sq_sub ι w z hw_sum] at hnn
  linarith

/-- Variance equals half the expected squared pairwise difference. -/
private theorem var_eq_half_pair
    (ι : Type*) [Fintype ι]
    (w z : ι → ℝ)
    (hw_sum : ∑ a : ι, w a = 1) :
    ∑ a : ι, w a * (z a - (∑ b : ι, w b * z b)) ^ 2
      = (1 / 2 : ℝ) * ∑ a : ι, ∑ b : ι, w a * w b * (z a - z b) ^ 2 := by
  have expand : ∀ a b : ι, w a * w b * (z a - z b) ^ 2
      = (w a * (z a) ^ 2 * w b) - ((2 * (w a * z a)) * (w b * z b))
        + (w a * (w b * (z b) ^ 2)) := by
    intros a b
    ring
  have e1 : (∑ a : ι, ∑ b : ι, w a * (z a) ^ 2 * w b)
      = ∑ a : ι, w a * (z a) ^ 2 := by
    have hinner : ∀ a : ι, (∑ b : ι, w a * (z a) ^ 2 * w b) = w a * (z a) ^ 2 := by
      intro a
      rw [← Finset.mul_sum, hw_sum, mul_one]
    rw [Finset.sum_congr rfl (fun a _ => hinner a)]
  have e2 : (∑ a : ι, ∑ b : ι, (2 * (w a * z a)) * (w b * z b))
      = 2 * (∑ a : ι, w a * z a) ^ 2 := by
    have hinner : ∀ a : ι, (∑ b : ι, (2 * (w a * z a)) * (w b * z b))
        = (2 * (w a * z a)) * (∑ b : ι, w b * z b) := by
      intro a
      rw [← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun a _ => hinner a)]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have e3 : (∑ a : ι, ∑ b : ι, w a * (w b * (z b) ^ 2))
      = ∑ a : ι, w a * (z a) ^ 2 := by
    have hinner : ∀ a : ι, (∑ b : ι, w a * (w b * (z b) ^ 2))
        = w a * (∑ b : ι, w b * (z b) ^ 2) := by
      intro a
      rw [← Finset.mul_sum]
    rw [Finset.sum_congr rfl (fun a _ => hinner a)]
    rw [← Finset.sum_mul, hw_sum, one_mul]
  have step : (∑ a : ι, ∑ b : ι, w a * w b * (z a - z b) ^ 2)
      = (∑ a : ι, ∑ b : ι, ((w a * (z a) ^ 2 * w b) - ((2 * (w a * z a)) * (w b * z b))
          + (w a * (w b * (z b) ^ 2)))) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intros b _
    exact expand a b
  have hpair : (∑ a : ι, ∑ b : ι, w a * w b * (z a - z b) ^ 2)
      = 2 * (∑ a : ι, w a * (z a) ^ 2) - 2 * (∑ a : ι, w a * z a) ^ 2 := by
    rw [step]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [e1, e2, e3]
    ring
  rw [var_eq_mean_sq_sub ι w z hw_sum, hpair]
  ring

/-- The product weight sums to one. -/
private theorem sum_eweight_eq_one
    (α : Type*) [Fintype α] [Nonempty α]
    (n : ℕ)
    (p : α → ℝ)
    (hp_sum : ∑ a : α, p a = 1) :
    ∑ x : Fin n → α, (∏ i : Fin n, p (x i)) = 1 := by
  induction n with
  | zero =>
    rw [Fintype.sum_unique]
    simp
  | succ n ih =>
    rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => α))
      (fun x => ∏ i : Fin (n + 1), p (x i))]
    rw [Fintype.sum_prod_type]
    have hterm : ∀ (a : α) (y : Fin n → α),
        (∏ i : Fin (n + 1), p ((Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) i))
          = p a * (∏ i : Fin n, p (y i)) := by
      intro a y
      rw [Fin.prod_univ_succ]
      simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]
    have hsplit : (∑ a : α, ∑ y : Fin n → α,
          (∏ i : Fin (n + 1), p ((Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) i)))
        = (∑ a : α, ∑ y : Fin n → α, p a * (∏ i : Fin n, p (y i))) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro y _
      exact hterm a y
    have hfac : (∑ a : α, ∑ y : Fin n → α, p a * (∏ i : Fin n, p (y i)))
        = (∑ a : α, p a) * (∑ y : Fin n → α, ∏ i : Fin n, p (y i)) := by
      rw [Fintype.sum_mul_sum]
    rw [hsplit, hfac, hp_sum, ih, mul_one]

private theorem update_cons_zero
    (α : Type*) [Nonempty α]
    (n : ℕ)
    (a b : α) (y : Fin n → α) :
    Function.update (Fin.cons (α := fun _ : Fin (n + 1) => α) a y) 0 b
      = Fin.cons (α := fun _ : Fin (n + 1) => α) b y := by
  funext j
  refine Fin.cases ?_ ?_ j
  · rw [Function.update_self, Fin.cons_zero]
  · intro m
    have hne : m.succ ≠ (0 : Fin (n + 1)) := by simp
    rw [Function.update_of_ne hne]
    simp only [Fin.cons_succ]

private theorem update_cons_succ
    (α : Type*) [Nonempty α]
    (n : ℕ)
    (k : Fin n) (a b : α) (y : Fin n → α) :
    Function.update (Fin.cons (α := fun _ : Fin (n + 1) => α) a y) k.succ b
      = Fin.cons (α := fun _ : Fin (n + 1) => α) a (Function.update y k b) := by
  funext j
  refine Fin.cases ?_ ?_ j
  · have h1 : k.succ ≠ (0 : Fin (n + 1)) := by simp
    have hne : (0 : Fin (n + 1)) ≠ k.succ := Ne.symm h1
    rw [Function.update_of_ne hne, Fin.cons_zero, Fin.cons_zero]
  · intro m
    have hiff : (m.succ = k.succ) ↔ (m = k) := Fin.succ_inj
    simp only [Function.update_apply, Fin.cons_succ, hiff]

-- E-versions by defeq
private theorem update_consEquiv_zero
    (α : Type*) [Nonempty α]
    (n : ℕ)
    (a b : α) (y : Fin n → α) :
    Function.update (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) 0 b
      = Fin.consEquiv (fun _ : Fin (n + 1) => α) (b, y) :=
  update_cons_zero α n a b y

private theorem update_consEquiv_succ
    (α : Type*) [Nonempty α]
    (n : ℕ)
    (k : Fin n) (a b : α) (y : Fin n → α) :
    Function.update (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) k.succ b
      = Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, Function.update y k b) :=
  update_cons_succ α n k a b y

private theorem weight_consEquiv
    (α : Type*) [Nonempty α]
    (n : ℕ)
    (p : α → ℝ)
    (a : α) (y : Fin n → α) :
    (∏ i : Fin (n + 1), p ((Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) i))
      = p a * (∏ i : Fin n, p (y i)) := by
  rw [Fin.prod_univ_succ]
  simp only [Fin.consEquiv_apply, Fin.cons_zero, Fin.cons_succ]

/-- Law of total variance for finite product weights (nested form). -/
private theorem total_variance_nested
    (β γ : Type*) [Fintype β] [Fintype γ]
    (u : β → ℝ) (v : γ → ℝ) (F : β → γ → ℝ)
    (hv : ∑ c : γ, v c = 1) :
    (∑ b : β, ∑ c : γ, (u b * v c) * (F b c - ∑ b' : β, u b' * (∑ c : γ, v c * F b' c)) ^ 2)
    = (∑ b : β, u b * (∑ c : γ, v c * (F b c - ∑ c' : γ, v c' * F b c') ^ 2))
      + (∑ b : β, u b * ((∑ c' : γ, v c' * F b c') - ∑ b' : β, u b' *
          (∑ c : γ, v c * F b' c)) ^ 2) := by
  have expand : ∀ b : β, ∀ c : γ, (u b * v c) * (F b c - ∑ b' : β, u b' *
      (∑ c : γ, v c * F b' c)) ^ 2 = (u b * (v c * (F b c - ∑ c' : γ, v c' * F b c') ^ 2)) +
      (u b * (v c * (2 * (F b c - ∑ c' : γ, v c' * F b c') *
      (∑ c' : γ, v c' * F b c' - ∑ b' : β, u b' * (∑ c : γ, v c * F b' c))))) +
      (u b * (v c * (∑ c' : γ, v c' * F b c' - ∑ b' : β, u b' * (∑ c : γ, v c * F b' c)) ^ 2)) := by
    intros b c
    ring
  have step : (∑ b : β, ∑ c : γ, (u b * v c) * (F b c - ∑ b' : β, u b' *
      (∑ c : γ, v c * F b' c)) ^ 2)
      = (∑ b : β, ∑ c : γ, ((u b * (v c * (F b c - ∑ c' : γ, v c' * F b c') ^ 2)) +
          (u b * (v c * (2 * (F b c - ∑ c' : γ, v c' * F b c') *
          (∑ c' : γ, v c' * F b c' - ∑ b' : β, u b' * (∑ c : γ, v c * F b' c))))) +
          (u b * (v c * (∑ c' : γ, v c' * F b c' - ∑ b' : β, u b' *
          (∑ c : γ, v c * F b' c)) ^ 2)))) := by
    apply Finset.sum_congr rfl
    intro b _
    apply Finset.sum_congr rfl
    intros c _
    exact expand b c
  have hT1 : (∑ b : β, ∑ c : γ, (u b * (v c * (F b c - ∑ c' : γ, v c' * F b c') ^ 2)))
      = (∑ b : β, u b * (∑ c : γ, v c * (F b c - ∑ c' : γ, v c' * F b c') ^ 2)) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [← Finset.mul_sum]
  have hzero : ∀ b : β, (∑ c : γ, (v c * (F b c - ∑ c' : γ, v c' * F b c'))) = 0 := by
    intro b
    have hexpand : ∀ c : γ, (v c * (F b c - ∑ c' : γ, v c' * F b c')) = v c * F b c -
        (∑ c' : γ, v c' * F b c') * v c := by
      intro c
      ring
    rw [Finset.sum_congr rfl (fun c _ => hexpand c)]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hv, mul_one, sub_self]
  have hT2 : (∑ b : β, ∑ c : γ, (u b * (v c * (2 * (F b c - ∑ c' : γ, v c' * F b c') *
      (∑ c' : γ, v c' * F b c' - ∑ b' : β, u b' * (∑ c : γ, v c * F b' c)))))) = 0 := by
    have hinner : ∀ b : β, (∑ c : γ, (u b * (v c * (2 * (F b c - ∑ c' : γ, v c' * F b c') *
        (∑ c' : γ, v c' * F b c' - ∑ b' : β, u b' * (∑ c : γ, v c * F b' c)))))) = 0 := by
      intro b
      rw [← Finset.mul_sum]
      have hsum : (∑ c : γ, v c * (2 * (F b c - ∑ c' : γ, v c' * F b c') *
          ((∑ c' : γ, v c' * F b c') - ∑ b' : β, u b' * (∑ c : γ, v c * F b' c))))
          = (2 * ((∑ c' : γ, v c' * F b c') - ∑ b' : β, u b' * (∑ c : γ, v c * F b' c))) *
              (∑ c : γ, (v c * (F b c - ∑ c' : γ, v c' * F b c'))) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro c _
        ring
      rw [hsum, hzero b, mul_zero, mul_zero]
    rw [Finset.sum_congr rfl (fun b _ => hinner b)]
    simp
  have hT3 : (∑ b : β, ∑ c : γ, (u b * (v c * (∑ c' : γ, v c' * F b c' - ∑ b' : β, u b' *
      (∑ c : γ, v c * F b' c)) ^ 2)))
      = (∑ b : β, u b * ((∑ c' : γ, v c' * F b c') - ∑ b' : β, u b' *
          (∑ c : γ, v c * F b' c)) ^ 2) := by
    apply Finset.sum_congr rfl
    intro b _
    rw [← Finset.mul_sum]
    have hinner : (∑ c : γ, v c * ((∑ c' : γ, v c' * F b c') - ∑ b' : β, u b' *
        (∑ c : γ, v c * F b' c)) ^ 2) = ((∑ c' : γ, v c' * F b c') - ∑ b' : β, u b' *
        (∑ c : γ, v c * F b' c)) ^ 2 := by
      rw [← Finset.sum_mul, hv, one_mul]
    rw [hinner]
  rw [step]
  simp only [Finset.sum_add_distrib]
  rw [hT1, hT2, hT3, add_zero]

/-- Fiber form of total variance, with explicit cons expressions. -/
private theorem fiber_total_variance
    (α : Type*) [Fintype α] [Nonempty α]
    (n : ℕ)
    (p : α → ℝ)
    (f : (Fin (n + 1) → α) → ℝ)
    (hv : (∑ y : Fin n → α, (∏ i : Fin n, p (y i))) = 1) :
    ∑ a : α, ∑ y : Fin n → α, (p a * (∏ i : Fin n, p (y i))) *
        (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) - ∑ a : α, p a *
        (∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)))) ^ 2 = ∑ a : α, p a *
        (∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) - ∑ y : Fin n → α,
        (∏ i : Fin n, p (y i)) * f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y))) ^ 2) +
        ∑ a : α, p a * ((∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y))) - ∑ a : α, p a *
        (∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)))) ^ 2 := by
  exact total_variance_nested α (Fin n → α) p
    (fun y : Fin n → α => ∏ i : Fin n, p (y i))
    (fun a y => f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y))) hv
/-- Inductive core of the Efron–Stein inequality. -/
private theorem efron_stein_aux
    (α : Type*) [Fintype α] [Nonempty α]
    (n : ℕ)
    (p : α → ℝ)
    (hp_nonneg : ∀ a, 0 ≤ p a)
    (hp_sum : ∑ a : α, p a = 1)
    (f : (Fin n → α) → ℝ) :
    (∑ x : Fin n → α, (∏ i : Fin n, p (x i)) * (f x - ∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        f y) ^ 2)
      ≤ (1 / 2 : ℝ) * ∑ i : Fin n, ∑ x : Fin n → α, ∑ a : α, (∏ j : Fin n, p (x j)) * p a *
          (f x - f (Function.update x i a)) ^ 2 := by
  revert f
  induction n with
  | zero =>
    intro f
    have hRHS : ((1 / 2 : ℝ) * ∑ i : Fin 0, ∑ x : Fin 0 → α, ∑ a : α, (∏ j : Fin 0, p (x j)) * p a *
        (f x - f (Function.update x i a)) ^ 2) = 0 := by
      simp
    have hmu : (∑ y : Fin 0 → α, (∏ i : Fin 0, p (y i)) * f y) = f default := by
      rw [Fintype.sum_unique]
      simp
    have hvar : (∑ x : Fin 0 → α, (∏ i : Fin 0, p (x i)) *
        (f x - ∑ y : Fin 0 → α, (∏ i : Fin 0, p (y i)) * f y) ^ 2) = 0 := by
      apply Finset.sum_eq_zero
      intro x _
      have hx : x = default := Unique.eq_default x
      rw [hx, hmu]
      simp
    rw [hRHS, hvar]
  | succ n ih =>
    intro f
    show ∑ x : Fin (n + 1) → α, (∏ i : Fin (n + 1), p (x i)) *
        (f x - ∑ x : Fin (n + 1) → α, (∏ i : Fin (n + 1), p (x i)) * f x) ^ 2 ≤ (1 / 2 : ℝ) *
        ∑ j : Fin (n + 1), ∑ x : Fin (n + 1) → α, ∑ c : α, (∏ i : Fin (n + 1), p (x i)) * p c *
        (f x - f (Function.update x j c)) ^ 2
    have hW1 : (∑ y : Fin n → α, (∏ i : Fin n, p (y i))) = 1 :=
      sum_eweight_eq_one α n p hp_sum
    have hWnn : ∀ y : Fin n → α, 0 ≤ (∏ i : Fin n, p (y i)) := by
      intro y
      apply Finset.prod_nonneg
      intro i _
      exact hp_nonneg _
    have hM : (∑ x : Fin (n + 1) → α, (∏ i : Fin (n + 1), p (x i)) * f x) =
        (∑ a : α, p a * (∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)))) := by
      rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => α)) (fun x : Fin (n + 1) → α =>
          (∏ i, p (x i)) * f x)]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      rw [weight_consEquiv α n p a y]
      ring
    have hV : (∑ x : Fin (n + 1) → α, (∏ i : Fin (n + 1), p (x i)) *
        (f x - ∑ x : Fin (n + 1) → α, (∏ i : Fin (n + 1), p (x i)) * f x) ^ 2) =
        (∑ a : α, ∑ y : Fin n → α, (p a * (∏ i : Fin n, p (y i))) *
        (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) - ∑ a : α, p a *
        (∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)))) ^ 2) := by
      rw [hM]
      rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => α)) (fun x : Fin (n + 1) → α =>
          (∏ i, p (x i)) * (f x - (∑ a : α, p a * (∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
          f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y))))) ^ 2)]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro y _
      rw [weight_consEquiv α n p a y]
    have hTV : (∑ a : α, ∑ y : Fin n → α, (p a * (∏ i : Fin n, p (y i))) *
        (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) - ∑ a : α, p a *
        (∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)))) ^ 2) =
        (∑ a : α, p a * (∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) - ∑ y : Fin n → α,
        (∏ i : Fin n, p (y i)) * f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y))) ^ 2)) +
        (∑ a : α, p a * ((∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y))) - ∑ a : α, p a *
        (∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)))) ^ 2) :=
      fiber_total_variance α n p f hW1
    have hA1 : (∑ a : α, p a * (∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) - ∑ y : Fin n → α,
        (∏ i : Fin n, p (y i)) * f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y))) ^ 2)) ≤
        ∑ a : α, p a * ((1 / 2 : ℝ) * (∑ i : Fin n, ∑ y : Fin n → α, ∑ b : α,
        (∏ i : Fin n, p (y i)) * p b * (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, Function.update y i b))) ^ 2)) := by
      apply Finset.sum_le_sum
      intro a _
      exact mul_le_mul_of_nonneg_left (ih (fun y : Fin n → α =>
          f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)))) (hp_nonneg a)
    have eA : ∀ a : α, p a * ((1 / 2 : ℝ) * (∑ i : Fin n, ∑ y : Fin n → α, ∑ b : α,
        (∏ i : Fin n, p (y i)) * p b * (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, Function.update y i b))) ^ 2)) =
        (1 / 2 : ℝ) * (∑ i : Fin n, p a * (∑ y : Fin n → α, ∑ b : α, (∏ i : Fin n, p (y i)) * p b *
        (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, Function.update y i b))) ^ 2)) := by
      intro a
      have h : (∑ i : Fin n, p a * (∑ y : Fin n → α, ∑ b : α, (∏ i : Fin n, p (y i)) * p b *
          (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
          f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, Function.update y i b))) ^ 2)) = p a *
          (∑ i : Fin n, ∑ y : Fin n → α, ∑ b : α, (∏ i : Fin n, p (y i)) * p b *
          (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
          f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, Function.update y i b))) ^ 2) := by
        rw [← Finset.mul_sum]
      rw [h]
      ring
    have hA2 : (∑ a : α, p a * ((1 / 2 : ℝ) * (∑ i : Fin n, ∑ y : Fin n → α, ∑ b : α,
        (∏ i : Fin n, p (y i)) * p b * (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, Function.update y i b))) ^ 2))) =
        (1 / 2 : ℝ) * (∑ i : Fin n, ∑ a : α, p a * (∑ y : Fin n → α, ∑ b : α,
        (∏ i : Fin n, p (y i)) * p b * (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, Function.update y i b))) ^ 2)) := by
      have e1 : (∑ a : α, p a * ((1 / 2 : ℝ) * (∑ i : Fin n, ∑ y : Fin n → α, ∑ b : α,
          (∏ i : Fin n, p (y i)) * p b * (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
          f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, Function.update y i b))) ^ 2))) = ∑ a : α,
          (1 / 2 : ℝ) * (∑ i : Fin n, p a * (∑ y : Fin n → α, ∑ b : α, (∏ i : Fin n, p (y i)) *
          p b * (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
          f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, Function.update y i b))) ^ 2)) :=
        Finset.sum_congr rfl (fun a _ => eA a)
      have hcomm : (∑ a : α, ∑ i : Fin n, p a * (∑ y : Fin n → α, ∑ b : α, (∏ i : Fin n, p (y i)) *
          p b * (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
          f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, Function.update y i b))) ^ 2)) =
          (∑ i : Fin n, ∑ a : α, p a * (∑ y : Fin n → α, ∑ b : α, (∏ i : Fin n, p (y i)) * p b *
          (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
          f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, Function.update y i b))) ^ 2)) :=
        Finset.sum_comm (f := fun a i => p a * (∑ y : Fin n → α, ∑ b : α, (∏ i : Fin n, p (y i)) *
            p b * (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
            f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, Function.update y i b))) ^ 2))
      rw [e1, ← Finset.mul_sum, hcomm]
    have hslice : ∀ i : Fin n, (∑ a : α, p a * (∑ y : Fin n → α, ∑ b : α, (∏ i : Fin n, p (y i)) *
        p b * (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, Function.update y i b))) ^ 2)) =
        (∑ x : Fin (n + 1) → α, ∑ c : α, (∏ i : Fin (n + 1), p (x i)) * p c *
        (f x - f (Function.update x i.succ c)) ^ 2) := by
      intro i
      have hund : (∑ a : α, p a * (∑ y : Fin n → α, ∑ b : α, (∏ i : Fin n, p (y i)) * p b *
          (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
          f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, Function.update y i b))) ^ 2)) =
          (∑ a : α, ∑ y : Fin n → α, ∑ b : α, (p a * (∏ i : Fin n, p (y i))) * p b *
          (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
          f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, Function.update y i b))) ^ 2) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
      have hre : (∑ x : Fin (n + 1) → α, ∑ c : α, (∏ i : Fin (n + 1), p (x i)) * p c *
          (f x - f (Function.update x i.succ c)) ^ 2) =
          (∑ a : α, ∑ y : Fin n → α, ∑ b : α, (p a * (∏ i : Fin n, p (y i))) * p b *
          (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
          f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, Function.update y i b))) ^ 2) := by
        rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => α)) (fun x : Fin (n + 1) → α =>
            ∑ c : α, (∏ i, p (x i)) * p c * (f x - f (Function.update x i.succ c)) ^ 2)]
        rw [Fintype.sum_prod_type]
        apply Finset.sum_congr rfl
        intro a _
        apply Finset.sum_congr rfl
        intro y _
        apply Finset.sum_congr rfl
        intro c _
        rw [weight_consEquiv α n p a y, update_consEquiv_succ α n i a c y]
      exact hund.trans hre.symm
    have hBoundA : (∑ a : α, p a * (∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) - ∑ y : Fin n → α,
        (∏ i : Fin n, p (y i)) * f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y))) ^ 2)) ≤
        (1 / 2 : ℝ) * (∑ i : Fin n, (∑ x : Fin (n + 1) → α, ∑ c : α, (∏ i : Fin (n + 1), p (x i)) *
        p c * (f x - f (Function.update x i.succ c)) ^ 2)) := by
      have hle : (∑ i : Fin n, ∑ a : α, p a * (∑ y : Fin n → α, ∑ b : α, (∏ i : Fin n, p (y i)) *
          p b * (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
          f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, Function.update y i b))) ^ 2)) ≤
          (∑ i : Fin n, (∑ x : Fin (n + 1) → α, ∑ c : α, (∏ i : Fin (n + 1), p (x i)) * p c *
          (f x - f (Function.update x i.succ c)) ^ 2)) := by
        apply Finset.sum_le_sum
        intro i _
        exact le_of_eq (hslice i)
      calc (∑ a : α, p a * (∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
          (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) - ∑ y : Fin n → α,
          (∏ i : Fin n, p (y i)) * f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y))) ^ 2))
          ≤ ∑ a : α, p a * ((1 / 2 : ℝ) * (∑ i : Fin n, ∑ y : Fin n → α, ∑ b : α,
              (∏ i : Fin n, p (y i)) * p b * (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
              f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, Function.update y i b))) ^ 2)) := hA1
        _ = (1 / 2 : ℝ) * (∑ i : Fin n, ∑ a : α, p a *
            (∑ y : Fin n → α, ∑ b : α, (∏ i : Fin n, p (y i)) * p b *
            (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
            f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, Function.update y i b))) ^ 2)) := hA2
        _ ≤ (1 / 2 : ℝ) * (∑ i : Fin n, (∑ x : Fin (n + 1) → α, ∑ c : α,
            (∏ i : Fin (n + 1), p (x i)) * p c * (f x - f (Function.update x i.succ c)) ^ 2)) :=
          mul_le_mul_of_nonneg_left hle (by norm_num)
    have hB1 : (∑ a : α, p a * ((∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y))) - ∑ a : α, p a *
        (∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)))) ^ 2) = (1 / 2 : ℝ) *
        (∑ a : α, ∑ b : α, p a * p b * ((∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y))) -
        (∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (b, y)))) ^ 2) :=
      var_eq_half_pair α p (fun b : α => ∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
          f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (b, y))) hp_sum
    have hmd : ∀ a b : α, ((∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y))) -
        (∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (b, y)))) = ∑ y : Fin n → α,
        (∏ i : Fin n, p (y i)) * ((f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y))) -
        (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (b, y)))) := by
      intro a b
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro y _
      ring
    have hdiff : ∀ a b : α, ((∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y))) -
        (∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (b, y)))) ^ 2 ≤ ∑ y : Fin n → α,
        (∏ i : Fin n, p (y i)) * (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (b, y))) ^ 2 := by
      intro a b
      rw [hmd a b]
      exact sq_mean_le_mean_sq _ _ _ hWnn hW1
    have hBle : (∑ a : α, ∑ b : α, p a * p b * ((∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y))) -
        (∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (b, y)))) ^ 2) ≤
        (∑ a : α, ∑ b : α, p a * p b * (∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (b, y))) ^ 2)) := by
      apply Finset.sum_le_sum
      intro a _
      apply Finset.sum_le_sum
      intro b _
      exact mul_le_mul_of_nonneg_left (hdiff a b) (mul_nonneg (hp_nonneg a) (hp_nonneg b))
    have hRe : (∑ x : Fin (n + 1) → α, ∑ c : α, (∏ i : Fin (n + 1), p (x i)) * p c *
        (f x - f (Function.update x 0 c)) ^ 2) = (∑ a : α, ∑ y : Fin n → α, ∑ c : α,
        (p a * (∏ i : Fin n, p (y i))) * p c *
        (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (c, y))) ^ 2) := by
      rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (n + 1) => α)) (fun x : Fin (n + 1) → α =>
          ∑ c : α, (∏ i, p (x i)) * p c * (f x - f (Function.update x 0 c)) ^ 2)]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro c _
      rw [weight_consEquiv α n p a y, update_consEquiv_zero α n a c y]
    have hSwap : (∑ a : α, ∑ y : Fin n → α, ∑ c : α, (p a * (∏ i : Fin n, p (y i))) * p c *
        (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (c, y))) ^ 2) =
        (∑ a : α, ∑ b : α, ∑ y : Fin n → α, (p a * (∏ i : Fin n, p (y i))) * p b *
        (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (b, y))) ^ 2) := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_comm (f := fun y c => (p a * (∏ i : Fin n, p (y i))) * p c *
          (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
          f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (c, y))) ^ 2)
    have hUnd : (∑ a : α, ∑ b : α, ∑ y : Fin n → α, (p a * (∏ i : Fin n, p (y i))) * p b *
        (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (b, y))) ^ 2) =
        (∑ a : α, ∑ b : α, p a * p b * (∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (b, y))) ^ 2)) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    have hS0 : (∑ x : Fin (n + 1) → α, ∑ c : α, (∏ i : Fin (n + 1), p (x i)) * p c *
        (f x - f (Function.update x 0 c)) ^ 2) = (∑ a : α, ∑ b : α, p a * p b *
        (∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) -
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (b, y))) ^ 2)) := hRe.trans (hSwap.trans hUnd)
    have hBoundB : (∑ a : α, p a * ((∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y))) - ∑ a : α, p a *
        (∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)))) ^ 2) ≤ (1 / 2 : ℝ) *
        (∑ x : Fin (n + 1) → α, ∑ c : α, (∏ i : Fin (n + 1), p (x i)) * p c *
        (f x - f (Function.update x 0 c)) ^ 2) := by
      rw [hB1, hS0]
      exact mul_le_mul_of_nonneg_left hBle (by norm_num)
    have hRHS : (∑ j : Fin (n + 1), ∑ x : Fin (n + 1) → α, ∑ c : α, (∏ i : Fin (n + 1), p (x i)) *
        p c * (f x - f (Function.update x j c)) ^ 2) =
        (∑ x : Fin (n + 1) → α, ∑ c : α, (∏ i : Fin (n + 1), p (x i)) * p c *
        (f x - f (Function.update x 0 c)) ^ 2) + (∑ i : Fin n,
        (∑ x : Fin (n + 1) → α, ∑ c : α, (∏ i : Fin (n + 1), p (x i)) * p c *
        (f x - f (Function.update x i.succ c)) ^ 2)) :=
      Fin.sum_univ_succ _
    rw [hV, hTV, hRHS]
    have hfin : (∑ a : α, p a * (∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        (f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)) - ∑ y : Fin n → α,
        (∏ i : Fin n, p (y i)) * f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y))) ^ 2)) +
        (∑ a : α, p a * ((∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y))) - ∑ a : α, p a *
        (∑ y : Fin n → α, (∏ i : Fin n, p (y i)) *
        f (Fin.consEquiv (fun _ : Fin (n + 1) => α) (a, y)))) ^ 2) ≤
        ((1 / 2 : ℝ) * (∑ i : Fin n, (∑ x : Fin (n + 1) → α, ∑ c : α, (∏ i : Fin (n + 1), p (x i)) *
        p c * (f x - f (Function.update x i.succ c)) ^ 2))) +
        ((1 / 2 : ℝ) * (∑ x : Fin (n + 1) → α, ∑ c : α, (∏ i : Fin (n + 1), p (x i)) * p c *
        (f x - f (Function.update x 0 c)) ^ 2)) :=
      add_le_add hBoundA hBoundB
    have heq : (1 / 2 : ℝ) * ((∑ x : Fin (n + 1) → α, ∑ c : α, (∏ i : Fin (n + 1), p (x i)) * p c *
        (f x - f (Function.update x 0 c)) ^ 2) + (∑ i : Fin n,
        (∑ x : Fin (n + 1) → α, ∑ c : α, (∏ i : Fin (n + 1), p (x i)) * p c *
        (f x - f (Function.update x i.succ c)) ^ 2))) =
        ((1 / 2 : ℝ) * (∑ i : Fin n, (∑ x : Fin (n + 1) → α, ∑ c : α, (∏ i : Fin (n + 1), p (x i)) *
        p c * (f x - f (Function.update x i.succ c)) ^ 2))) +
        ((1 / 2 : ℝ) * (∑ x : Fin (n + 1) → α, ∑ c : α, (∏ i : Fin (n + 1), p (x i)) * p c *
        (f x - f (Function.update x 0 c)) ^ 2)) := by
      ring
    rw [heq]
    exact hfin
/-- **Efron–Stein inequality for a finite product weight.** Let $\alpha$ be a finite nonempty set,
let $p : \alpha \to \mathbb{R}$ satisfy $p(a) \ge 0$ for every $a \in \alpha$ and
$\sum_{a \in \alpha} p(a) = 1$, let $n \in \mathbb{N}$ and let $f : \alpha^n \to \mathbb{R}$. For
$x = (x_1, \dots, x_n) \in \alpha^n$ write $w(x) = \prod_{j=1}^{n} p(x_j)$, and for a coordinate
$i \in \{1, \dots, n\}$ and $a \in \alpha$ let $x^{(i,a)}$ be $x$ with its $i$-th coordinate
replaced by $a$. Let $\mu = \sum_{x \in \alpha^n} w(x) f(x)$. Then
$$
\sum_{x \in \alpha^n} w(x) \bigl(f(x) - \mu\bigr)^2 \le \frac{1}{2} \sum_{i=1}^{n}
\sum_{x \in \alpha^n} \sum_{a \in \alpha} w(x)\, p(a) \bigl(f(x) - f(x^{(i,a)})\bigr)^2.
$$ -/
theorem efron_stein_finite_iid_general
    {α : Type*} [Fintype α] [Nonempty α]
    {n : ℕ}
    (p : α → ℝ)
    (hp_nonneg : ∀ a, 0 ≤ p a)
    (hp_sum : ∑ a : α, p a = 1)
    (f : (Fin n → α) → ℝ) :
    let μ : ℝ := ∑ x : Fin n → α, (∏ i : Fin n, p (x i)) * f x
    let var_ : ℝ :=
      ∑ x : Fin n → α, (∏ i : Fin n, p (x i)) * (f x - μ) ^ 2
    var_ ≤ (1 / 2 : ℝ) *
      ∑ i : Fin n, ∑ x : Fin n → α, ∑ a : α,
        (∏ j : Fin n, p (x j)) * p a *
          (f x - f (Function.update x i a)) ^ 2 := by
  change (∑ x : Fin n → α, (∏ i : Fin n, p (x i)) *
      (f x - ∑ y : Fin n → α, (∏ i : Fin n, p (y i)) * f y) ^ 2)
    ≤ (1 / 2 : ℝ) * ∑ i : Fin n, ∑ x : Fin n → α, ∑ a : α, (∏ j : Fin n, p (x j)) * p a *
        (f x - f (Function.update x i a)) ^ 2
  exact efron_stein_aux α n p hp_nonneg hp_sum f

set_option linter.unusedDecidableInType false in
/--
**Efron–Stein inequality for finite i.i.d. coordinates.** Let $\alpha$ be a finite nonempty set,
let $p : \alpha \to \mathbb{R}$ satisfy $p(a) \ge 0$ for every $a \in \alpha$ and
$\sum_{a \in \alpha} p(a) = 1$, let $n \in \mathbb{N}$ and let $f : \alpha^n \to \mathbb{R}$. For
$x = (x_1, \dots, x_n) \in \alpha^n$ write $w(x) = \prod_{j=1}^{n} p(x_j)$, and for a coordinate
$i \in \{1, \dots, n\}$ and $a \in \alpha$ let $x^{(i,a)}$ be $x$ with its $i$-th coordinate
replaced by $a$. Let $\mu = \sum_{x \in \alpha^n} w(x) f(x)$. Then
$$
\sum_{x \in \alpha^n} w(x) \bigl(f(x) - \mu\bigr)^2 \le \frac{1}{2} \sum_{i=1}^{n}
\sum_{x \in \alpha^n} \sum_{a \in \alpha} w(x)\, p(a) \bigl(f(x) - f(x^{(i,a)})\bigr)^2.
$$

In words: the variance of $f$ under the product weight is at most half the expected sum of squared
differences under independent resampling of each coordinate.

Source: B. Efron and C. Stein, "The Jackknife Estimate of Variance", Annals of Statistics 9 (1981),
DOI 10.1214/aos/1176345462.
It follows from `efron_stein_finite_iid_general`; the instance `[DecidableEq α]` is
unused and keeps the source's shape.
Proves `Wanted` entry `efron_stein_finite_iid`.
-/
theorem efron_stein_finite_iid
    {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    {n : ℕ}
    (p : α → ℝ)
    (hp_nonneg : ∀ a, 0 ≤ p a)
    (hp_sum : ∑ a : α, p a = 1)
    (f : (Fin n → α) → ℝ) :
    let μ : ℝ := ∑ x : Fin n → α, (∏ i : Fin n, p (x i)) * f x
    let var_ : ℝ :=
      ∑ x : Fin n → α, (∏ i : Fin n, p (x i)) * (f x - μ) ^ 2
    var_ ≤ (1 / 2 : ℝ) *
      ∑ i : Fin n, ∑ x : Fin n → α, ∑ a : α,
        (∏ j : Fin n, p (x j)) * p a *
          (f x - f (Function.update x i a)) ^ 2 :=
  efron_stein_finite_iid_general p hp_nonneg hp_sum f

end MathlibExt.Probability.EfronStein
