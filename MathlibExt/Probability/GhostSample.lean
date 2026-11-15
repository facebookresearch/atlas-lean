/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Pi

/-!
# Ghost-sample averaging identity

Averaging the empirical mean of `f` over all ghost samples
of size `m` gives the true mean of `f`. This is the
averaging step of the symmetrization argument; the
Rademacher bound itself is not included here.
-/

@[expose] public section

/-- Empirical mean of `f` on a sample tuple (ghost-sample
core of ML-03). -/
noncomputable def empMean {X : Type*} [Fintype X] (f : X → ℝ) (m : ℕ)
    (S : Fin m → X) : ℝ :=
  (∑ i, f (S i)) / m

private lemma sum_eval_zero {X : Type*} [Fintype X] (f : X → ℝ) (m : ℕ) :
    ∑ S' : Fin (m+1) → X, f (S' 0) = (Fintype.card X : ℝ)^m * ∑ x, f x := by
  let e := Fin.consEquiv (fun _ : Fin (m+1) => X)
  have h : (∑ S' : Fin (m+1) → X, f (S' 0))
      = ∑ p : X × (Fin m → X), f ((e p) 0) := (Equiv.sum_comp e _).symm
  rw [h]
  have h2 : ∀ p : X × (Fin m → X), f ((e p) 0) = f p.1 := by
    intro p
    simp [e, Fin.consEquiv_apply, Fin.cons_zero]
  simp only [h2]
  rw [Fintype.sum_prod_type]
  simp [Finset.sum_const, Finset.card_univ, Finset.mul_sum]

private lemma sum_eval {X : Type*} [Fintype X] (f : X → ℝ) (m : ℕ)
    (i : Fin (m+1)) :
    ∑ S' : Fin (m+1) → X, f (S' i) = (Fintype.card X : ℝ)^m * ∑ x, f x := by
  let σ := Equiv.swap i 0
  let e : (Fin (m+1) → X) ≃ (Fin (m+1) → X) :=
    { toFun := fun S' => S' ∘ σ
      invFun := fun S' => S' ∘ σ.symm
      left_inv := by
        intro S'
        funext j
        simp [σ]
      right_inv := by
        intro S'
        funext j
        simp [σ] }
  have h : (∑ S' : Fin (m+1) → X, f (S' i))
      = ∑ S' : Fin (m+1) → X, f ((e S') 0) := by
    apply Finset.sum_congr rfl
    intro S' _
    simp [e, σ]
  rw [h]
  rw [Equiv.sum_comp e (fun T => f (T 0))]
  exact sum_eval_zero f m

/-- Ghost-sample identity: averaging the empirical mean over
all ghost samples `S'` gives the true mean over `X`, for any
fixed sample size `m ≥ 1` and any `f`. This is the averaging
step of symmetrization. -/
theorem empMean_ghost_average {X : Type*} [Fintype X] [Nonempty X]
    (f : X → ℝ) {m : ℕ} (hm : 0 < m) :
    (∑ S' : Fin m → X, empMean f m S') / (Fintype.card X) ^ m
      = (∑ x, f x) / Fintype.card X := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hm)
  simp only [empMean]
  rw [← Finset.sum_div]
  have hswap : (∑ S' : Fin (k+1) → X, ∑ i, f (S' i))
      = ∑ i, ∑ S' : Fin (k+1) → X, f (S' i) := Finset.sum_comm
  rw [hswap]
  simp only [sum_eval]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  simp only [nsmul_eq_mul]
  have hC : (0:ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hm' : (0:ℝ) < ((k+1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_pos k
  field_simp
  rw [pow_succ']
  ring


end
