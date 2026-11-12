/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib












namespace StatMech.Onsager

open Matrix BigOperators





theorem ons_pow_apply_walk {E : Type*} [Fintype E] [DecidableEq E]
    (Λ : Matrix E E ℂ) :
    ∀ (n : ℕ) (i j : E),
      (Λ ^ n) i j =
        ∑ p : Fin n → E,
          (if (Fin.cons i p : Fin (n + 1) → E) (Fin.last n) = j then (1 : ℂ) else 0) *
            ∏ k : Fin n, Λ ((Fin.cons i p : Fin (n + 1) → E) k.castSucc) (p k) := by
  intro n
  induction n with
  | zero =>
    intro i j
    simp only [pow_zero, Matrix.one_apply, Fin.prod_univ_zero, mul_one]
    rw [Fintype.sum_unique]
    simp [Fin.last]
  | succ n ih =>
    intro i j
    rw [pow_succ', Matrix.mul_apply]
    simp_rw [ih _ j, Finset.mul_sum]
    rw [← Fintype.sum_prod_type']
    rw [← Equiv.sum_comp (Fin.consEquiv fun _ : Fin (n + 1) => E)]
    have hcE : ∀ (x : E × (Fin n → E)),
        (Fin.consEquiv (fun _ : Fin (n + 1) => E)) x = Fin.cons x.1 x.2 := fun _ => rfl
    refine Finset.sum_congr rfl (fun x _ => ?_)
    obtain ⟨a, q⟩ := x
    rw [hcE]
    
    rw [Fin.prod_univ_succ]
    have hcond : (Fin.cons i (Fin.cons a q) : Fin (n + 2) → E) (Fin.last (n + 1))
        = (Fin.cons a q : Fin (n + 1) → E) (Fin.last n) := by
      rw [← Fin.succ_last, Fin.cons_succ]
    rw [hcond]
    simp only [Fin.castSucc_zero, Fin.cons_zero, ← Fin.succ_castSucc, Fin.cons_succ]
    ring





theorem ons_trace_pow_eq_walk_sum {E : Type*} [Fintype E] [DecidableEq E]
    (Λ : Matrix E E ℂ) (n : ℕ) [NeZero n] (hn : 0 < n) :
    (Λ ^ n).trace = ∑ v : Fin n → E, ∏ k : Fin n, Λ (v k) (v (k + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  
  have hz : (Fin.last m : Fin (m + 1)) + 1 = 0 := Fin.last_add_one m
  
  have hcond2 : ∀ (i : E) (p : Fin (m + 1) → E),
      (Fin.cons i p : Fin (m + 2) → E) (Fin.last (m + 1)) = p (Fin.last m) := by
    intro i p
    rw [← Fin.succ_last, Fin.cons_succ]
  
  simp only [Matrix.trace, Matrix.diag_apply]
  rw [Finset.sum_congr rfl
    (fun i (_ : i ∈ (Finset.univ : Finset E)) => ons_pow_apply_walk Λ (m + 1) i i)]
  
  simp_rw [hcond2]
  rw [Finset.sum_comm]
  simp_rw [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  
  refine Finset.sum_congr rfl (fun p _ => ?_)
  rw [Fin.prod_univ_succ, Fin.prod_univ_castSucc]
  simp only [Fin.castSucc_zero, Fin.cons_zero, ← Fin.succ_castSucc, Fin.cons_succ,
    Fin.coeSucc_eq_succ, hz]
  ring

end StatMech.Onsager
