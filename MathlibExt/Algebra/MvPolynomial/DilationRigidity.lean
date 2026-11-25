/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_MvPolynomial_exists_eq_C_mul_X_add_X_pow_of_totalDegree_le_of_forall_`
`eval_eq_pow_mul_eval.lean`
and
`P2M/Sol/S_MvPolynomial_exists_eq_C_mul_X_add_X_pow_of_totalDegree_le_of_forall_`
`eval_eq_pow_mul_eval.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.MvPolynomial.Monad
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Tactic

@[expose] public section

namespace MvPolynomial

private theorem eval_bind₁_aux {σ τ R : Type*} [CommSemiring R] (x : τ → R)
    (h : σ → MvPolynomial τ R) (φ : MvPolynomial σ R) :
    eval x (bind₁ h φ) = eval (fun i => eval x (h i)) φ :=
  eval₂Hom_bind₁ _ _ _ _

private theorem coeff_bind₁_C_mul_X_aux {σ R : Type*} [CommSemiring R]
    (c : σ → R) (Q : MvPolynomial σ R) (m : σ →₀ ℕ) :
    (bind₁ (fun i => C (c i) * X i) Q).coeff m =
      (m.prod fun i e => c i ^ e) * Q.coeff m := by
  classical
  have key : ∀ (d : σ →₀ ℕ) (r : R),
      bind₁ (fun i => C (c i) * X i) (monomial d r) =
        monomial d ((d.prod fun i e => c i ^ e) * r) := by
    intro d r
    rw [bind₁_monomial]
    simp_rw [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod]
    rw [monomial_eq, Finsupp.prod, Finsupp.prod, map_mul]
    ring
  conv_lhs => rw [Q.as_sum, map_sum, coeff_sum]
  simp_rw [key, coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with hm
  · rfl
  · rw [notMem_support_iff.1 hm, mul_zero]

private theorem totalDegree_bind₁_le_aux {σ τ R : Type*} [CommSemiring R]
    (f : σ → MvPolynomial τ R) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (p : MvPolynomial σ R) : (bind₁ f p).totalDegree ≤ p.totalDegree := by
  classical
  conv_lhs => rw [p.as_sum, map_sum]
  refine totalDegree_finsetSum_le fun d hd => ?_
  rw [bind₁_monomial]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finsetProd _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun i _ => (totalDegree_pow _ _).trans
    (Nat.mul_le_mul_left _ (hf i))) ?_
  simp_rw [mul_one]
  exact le_totalDegree hd

/-- Rigidity of a binary rational polynomial under a two-eigenvalue dilation.

If `α + β = n²`, `α = β + n` with `2 ≤ n`, a polynomial `P` in two rational
variables of total degree at most `g` satisfying, for all natural `a, b`,
`P(αa + βb, βa + αb) = n ^ (2g) • P(a, b)` (as an evaluation identity), then
`P = c • (X₀ + X₁) ^ g` for some rational `c`. -/
public theorem exists_eq_C_mul_X_add_X_pow_of_totalDegree_le_of_forall_eval_eq_pow_mul_eval
    (g n : ℕ) (hn : 2 ≤ n) (α β : ℕ) (hαβ : α + β = n ^ 2) (hα : α = β + n)
    (P : MvPolynomial (Fin 2) ℚ) (hP : P.totalDegree ≤ g)
    (h : ∀ a b : ℕ,
      MvPolynomial.eval ![((α * a + β * b : ℕ) : ℚ), ((β * a + α * b : ℕ) : ℚ)] P =
        (n : ℚ) ^ (2 * g) * MvPolynomial.eval ![(a : ℚ), (b : ℚ)] P) :
    ∃ c : ℚ, P = MvPolynomial.C c * (MvPolynomial.X 0 + MvPolynomial.X 1) ^ g := by
  classical
  let φ : Fin 2 → MvPolynomial (Fin 2) ℚ :=
    ![C (α : ℚ) * X 0 + C (β : ℚ) * X 1, C (β : ℚ) * X 0 + C (α : ℚ) * X 1]
  let σ : Fin 2 → MvPolynomial (Fin 2) ℚ :=
    ![C (1 / 2 : ℚ) * (X 0 + X 1), C (1 / 2 : ℚ) * (X 0 - X 1)]
  let τ : Fin 2 → MvPolynomial (Fin 2) ℚ := ![X 0 + X 1, X 0 - X 1]
  let ψ : Fin 2 → MvPolynomial (Fin 2) ℚ := fun i => C (![((n : ℚ) ^ 2), (n : ℚ)] i) * X i
  let Q : MvPolynomial (Fin 2) ℚ := bind₁ σ P
  have h1 : bind₁ φ P = C ((n : ℚ) ^ (2 * g)) * P := by
    apply MvPolynomial.funext_set (fun _ => Set.range (Nat.cast : ℕ → ℚ))
      (fun _ => Set.infinite_range_of_injective Nat.cast_injective)
    intro x hx
    obtain ⟨a, ha⟩ := hx 0 (Set.mem_univ _)
    obtain ⟨b, hb⟩ := hx 1 (Set.mem_univ _)
    have hx' : x = ![(a : ℚ), (b : ℚ)] := by
      funext i; fin_cases i <;> simp [← ha, ← hb]
    subst hx'
    have hpt : (fun i => eval ![(a : ℚ), (b : ℚ)] (φ i)) =
        ![((α * a + β * b : ℕ) : ℚ), ((β * a + α * b : ℕ) : ℚ)] := by
      funext i; fin_cases i <;> simp [φ]
    rw [map_mul, eval_C, ← h a b, eval_bind₁_aux, hpt]
  have h2 : C (1 / 2 : ℚ) * 2 = (1 : MvPolynomial (Fin 2) ℚ) := by
    rw [← map_ofNat (C : ℚ →+* MvPolynomial (Fin 2) ℚ) 2, ← map_mul]
    norm_num
  have hαβ' : C (α : ℚ) + C (β : ℚ) = (C ((n : ℚ) ^ 2) : MvPolynomial (Fin 2) ℚ) := by
    rw [← map_add, ← Nat.cast_add, hαβ, Nat.cast_pow]
  have hα' : C (α : ℚ) = (C (β : ℚ) + C (n : ℚ) : MvPolynomial (Fin 2) ℚ) := by
    rw [← map_add, ← Nat.cast_add, ← hα]
  have hτσ : (fun i => bind₁ τ (σ i)) = X := by
    funext i; fin_cases i
    · simp only [σ, τ, Fin.zero_eta, Matrix.cons_val_zero, map_mul, bind₁_C_right,
        map_add, bind₁_X_right, Matrix.cons_val_one]
      linear_combination (X 0 : MvPolynomial (Fin 2) ℚ) * h2
    · simp only [σ, τ, Fin.mk_one, Matrix.cons_val_zero, map_mul, bind₁_C_right,
        map_sub, bind₁_X_right, Matrix.cons_val_one]
      linear_combination (X 1 : MvPolynomial (Fin 2) ℚ) * h2
  have hPQ : P = bind₁ τ Q := by
    change P = bind₁ τ (bind₁ σ P)
    rw [bind₁_bind₁, hτσ, bind₁_X_left]
    rfl
  have hρ : (fun i => bind₁ ψ (σ i)) = fun i => bind₁ σ (φ i) := by
    funext i; fin_cases i
    · simp only [σ, φ, ψ, Fin.zero_eta, Matrix.cons_val_zero, Matrix.cons_val_one,
        map_mul, map_add, bind₁_C_right, bind₁_X_right]
      linear_combination (-(C (1 / 2 : ℚ) * X 0 : MvPolynomial (Fin 2) ℚ)) * hαβ' +
        (-(C (1 / 2 : ℚ) * X 1 : MvPolynomial (Fin 2) ℚ)) * hα'
    · simp only [σ, φ, ψ, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
        map_mul, map_add, map_sub, bind₁_C_right, bind₁_X_right]
      linear_combination (-(C (1 / 2 : ℚ) * X 0 : MvPolynomial (Fin 2) ℚ)) * hαβ' +
        (C (1 / 2 : ℚ) * X 1 : MvPolynomial (Fin 2) ℚ) * hα'
  have h3 : bind₁ ψ Q = C ((n : ℚ) ^ (2 * g)) * Q := by
    change bind₁ ψ (bind₁ σ P) = C ((n : ℚ) ^ (2 * g)) * bind₁ σ P
    rw [bind₁_bind₁, hρ, ← bind₁_bind₁, h1, map_mul, bind₁_C_right]
  have hQσ : Q.totalDegree ≤ g := by
    refine (totalDegree_bind₁_le_aux σ (fun i => ?_) P).trans hP
    fin_cases i
    · simp only [σ, Fin.zero_eta, Matrix.cons_val_zero]
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      refine (totalDegree_add _ _).trans (max_le ?_ ?_) <;> exact (totalDegree_X _).le
    · simp only [σ, Fin.mk_one, Matrix.cons_val_one]
      refine (totalDegree_mul _ _).trans ?_
      rw [totalDegree_C, zero_add]
      refine (totalDegree_sub _ _).trans (max_le ?_ ?_) <;> exact (totalDegree_X _).le
  have hcoef : ∀ m : Fin 2 →₀ ℕ, Q.coeff m ≠ 0 → m = Finsupp.single 0 g := by
    intro m hm
    have hdeg : m 0 + m 1 ≤ g := by
      have hle := le_totalDegree (mem_support_iff.2 hm)
      rw [Finsupp.sum_fintype _ _ (fun _ => rfl), Fin.sum_univ_two] at hle
      exact hle.trans hQσ
    have hsc := congrArg (fun p : MvPolynomial (Fin 2) ℚ => p.coeff m) h3
    rw [show ψ = fun i => C (![((n : ℚ) ^ 2), (n : ℚ)] i) * X i from rfl,
      coeff_bind₁_C_mul_X_aux, coeff_C_mul, Finsupp.prod_pow, Fin.prod_univ_two] at hsc
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hsc
    rw [← pow_mul, ← pow_add] at hsc
    have hexp : (n : ℚ) ^ (2 * m 0 + m 1) = (n : ℚ) ^ (2 * g) := mul_right_cancel₀ hm hsc
    have hexp' : 2 * m 0 + m 1 = 2 * g := by
      have hinj := (pow_right_injective₀ (by positivity : (0 : ℚ) < n) (by
        have h2n : (2 : ℚ) ≤ n := by exact_mod_cast hn
        exact ne_of_gt (by linarith))) hexp
      exact hinj
    have h0 : m 0 = g := by omega
    have h1' : m 1 = 0 := by omega
    ext i; fin_cases i
    · simp [h0]
    · simp [h1']
  set c : ℚ := Q.coeff (Finsupp.single 0 g) with hc
  have hQ : Q = C c * X 0 ^ g := by
    rw [C_mul_X_pow_eq_monomial]
    ext m
    rw [coeff_monomial]
    split_ifs with hm
    · rw [← hm, hc]
    · by_contra hq
      exact hm (hcoef m hq).symm
  refine ⟨c, ?_⟩
  rw [hPQ, hQ, map_mul, bind₁_C_right, map_pow, bind₁_X_right]
  rfl

end MvPolynomial
