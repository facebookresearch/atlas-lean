/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.LinearModel.Sampling
public import Mathlib.Data.Fintype.Powerset

import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Least-squares contrasts in a balanced two-level factorial design -/

@[expose] public section

open Finset Matrix

namespace MathlibExt.Probability.Statistics.LinearModel

private def levelSign (b : Bool) : ℝ := if b then 1 else -1

/-- The design matrix of the full two-level experiment with `k` factors and `r` replicates
per treatment. A run is a Boolean level assignment together with a replicate index. The column
for a subset `S` is the product of the `±1` codes of the factors in `S`, with the empty subset
coding the intercept. -/
def factorialDesign (k r : ℕ) : Matrix ((Fin k → Bool) × Fin r) (Finset (Fin k)) ℝ :=
  Matrix.of fun x S => ∏ i, if i ∈ S then (if x.1 i then (1 : ℝ) else -1) else 1

private theorem factorialDesign_empty {k r : ℕ} (x : (Fin k → Bool) × Fin r) :
    factorialDesign k r x ∅ = 1 := by
  simp [factorialDesign]

private theorem factorialDesign_sign {k r : ℕ} (x : (Fin k → Bool) × Fin r) (S : Finset (Fin k)) :
    factorialDesign k r x S = 1 ∨ factorialDesign k r x S = -1 := by
  unfold factorialDesign
  rw [Matrix.of_apply]
  refine Finset.prod_induction _ (fun z : ℝ => z = 1 ∨ z = -1) ?_ (.inl rfl) ?_
  · rintro a b (rfl | rfl) (rfl | rfl) <;> norm_num
  · intro i _
    by_cases hi : i ∈ S <;> cases x.1 i <;> simp [hi]

private theorem factorialDesign_gram (k r : ℕ) :
    (factorialDesign k r)ᵀ * factorialDesign k r =
      Matrix.diagonal (fun _ : Finset (Fin k) => (r : ℝ) * 2 ^ k) := by
  classical
  ext S T
  let g (i : Fin k) (b : Bool) : ℝ :=
    (if i ∈ S then levelSign b else 1) * (if i ∈ T then levelSign b else 1)
  have hin (x : (Fin k → Bool) × Fin r) :
      factorialDesign k r x S * factorialDesign k r x T = ∏ i, g i (x.1 i) := by
    simp only [factorialDesign, Matrix.of_apply, g, levelSign, Finset.prod_mul_distrib]
  have hsep : (∑ x : Fin k → Bool, ∏ i, g i (x i)) = ∏ i, ∑ b : Bool, g i b := by
    simpa only [Fintype.piFinset_univ] using
      (Finset.sum_prod_piFinset (ι := Fin k) (s := (univ : Finset Bool)) g)
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply, hin]
  rw [Fintype.sum_prod_type_right]
  change (∑ _ : Fin r, ∑ x : Fin k → Bool, ∏ i, g i (x i)) = _
  rw [hsep, Finset.sum_const, card_univ, Fintype.card_fin]
  rw [nsmul_eq_mul]
  by_cases hST : S = T
  · subst T
    have hg (i : Fin k) : (∑ b : Bool, g i b) = 2 := by
      rw [Fintype.sum_bool]
      by_cases hi : i ∈ S <;> norm_num [g, hi, levelSign]
    simp_rw [hg]
    rw [Finset.prod_const, card_univ, Fintype.card_fin, Matrix.diagonal_apply_eq]
  · have hdiff : ∃ i : Fin k, (i ∈ S) ≠ (i ∈ T) := by
      by_contra! hn
      exact hST (Finset.ext fun i => iff_of_eq (hn i))
    obtain ⟨i, hi⟩ := hdiff
    have hg : (∑ b : Bool, g i b) = 0 := by
      rw [Fintype.sum_bool]
      by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
        simp_all [g, levelSign]
    rw [Finset.prod_eq_zero (mem_univ i) hg, mul_zero, Matrix.diagonal_apply_ne _ hST]

private theorem sum_sign_parts {m : Type*} [Fintype m] (c : m → ℝ)
    (hc : ∀ x, c x = 1 ∨ c x = -1) (y : m → ℝ) :
    let p := univ.filter fun x => c x = 1
    let n := univ.filter fun x => c x = -1
    (∑ x ∈ p, y x) + (∑ x ∈ n, y x) = ∑ x, y x ∧
      (∑ x, c x * y x) = (∑ x ∈ p, y x) - ∑ x ∈ n, y x := by
  intro p n
  classical
  have hn : (univ.filter fun x => ¬c x = 1) = n := by
    ext x
    simp only [n, mem_filter, mem_univ, true_and]
    rcases hc x with hx | hx <;> norm_num [hx]
  have hpart (f : m → ℝ) : (∑ x ∈ p, f x) + (∑ x ∈ n, f x) = ∑ x, f x := by
    rw [← hn]
    exact sum_filter_add_sum_filter_not univ (fun x => c x = 1) f
  refine ⟨hpart y, ?_⟩
  have hp : (∑ x ∈ p, c x * y x) = ∑ x ∈ p, y x := by
    apply sum_congr rfl
    intro x hx
    rw [(mem_filter.mp hx).2, one_mul]
  have hm : (∑ x ∈ n, c x * y x) = -(∑ x ∈ n, y x) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro x hx
    rw [(mem_filter.mp hx).2, neg_one_mul]
  rw [← hpart (fun x => c x * y x), hp, hm, sub_eq_add_neg]

private theorem factorial_rss_minimum {m j : Type*} [Fintype m] [Fintype j] [DecidableEq j]
    (X : Matrix m j ℝ) (y : m → ℝ) (β : j → ℝ) (N : ℝ) (hN : 0 < N)
    (hg : Xᵀ * X = Matrix.diagonal (fun _ => N)) (he : Xᵀ *ᵥ (y - X *ᵥ β) = 0)
    (b : j → ℝ) :
    let rss := fun a : j → ℝ => ∑ x, (y x - (X *ᵥ a) x) ^ 2
    rss β ≤ rss b ∧ (rss β = rss b ↔ b = β) := by
  intro rss
  let e := y - X *ᵥ β
  let d := β - b
  let v := X *ᵥ d
  have hs : y - X *ᵥ b = e + v := by
    dsimp [e, v, d]
    rw [Matrix.mulVec_sub]
    abel
  have ho : e ⬝ᵥ v = 0 := by
    change e ⬝ᵥ (X *ᵥ d) = 0
    rw [dotProduct_mulVec, show e ᵥ* X = Xᵀ *ᵥ e by
      rw [← Matrix.vecMul_transpose Xᵀ e, transpose_transpose]]
    change (Xᵀ *ᵥ (y - X *ᵥ β)) ⬝ᵥ d = 0
    rw [he, zero_dotProduct]
  have ho' : v ⬝ᵥ e = 0 := (dotProduct_comm v e).trans ho
  have hrss (a : j → ℝ) : rss a = (y - X *ᵥ a) ⬝ᵥ (y - X *ᵥ a) := by
    simp only [rss, dotProduct, Pi.sub_apply, pow_two]
  have hsplit : rss b = rss β + v ⬝ᵥ v := by
    rw [hrss b, hrss β, hs]
    change (e + v) ⬝ᵥ (e + v) = e ⬝ᵥ e + v ⬝ᵥ v
    simp only [add_dotProduct, dotProduct_add, ho, ho', add_zero, zero_add]
  have hn : 0 ≤ v ⬝ᵥ v := sum_nonneg fun x _ => mul_self_nonneg (v x)
  refine ⟨by linarith only [hsplit, hn], ?_⟩
  constructor
  · intro h
    have hv : v = 0 := dotProduct_self_eq_zero.mp (by linarith only [hsplit, h])
    have hd : N • d = 0 := by
      rw [← Matrix.diagonal_const_mulVec, ← hg, ← Matrix.mulVec_mulVec]
      change Xᵀ *ᵥ v = 0
      rw [hv, mulVec_zero]
    exact (sub_eq_zero.mp ((smul_eq_zero.mp hd).resolve_left hN.ne')).symm
  · rintro rfl
    rfl

/-- **Factorial effects from ±1 coding in a balanced two-level design.** In the full two-level
experiment with at least one replicate per treatment, the Gram matrix of the product-coded
columns is diagonal with every diagonal entry `r * 2^k`. The ordinary least-squares estimate
uniquely minimizes the residual sum of squares, and its intercept coefficient is the grand mean.
Every nonempty factor subset has equally many `+1` and `-1` runs; its least-squares
coefficient is half the difference of the two response means. The conventional factorial effect
is the difference of means, twice that coefficient. -/
theorem factorial_ols_effects {k r : ℕ} (hr : 0 < r) (y : ((Fin k → Bool) × Fin r) → ℝ) :
    let X := factorialDesign k r
    let N : ℝ := (r : ℝ) * 2 ^ k
    let β := olsEstimator X y
    let rss := fun b : Finset (Fin k) → ℝ => ∑ x, (y x - (X *ᵥ b) x) ^ 2
    Xᵀ * X = Matrix.diagonal (fun _ => N) ∧
      β ∅ = (∑ x, y x) / N ∧
      (∀ S : Finset (Fin k), S ≠ ∅ →
        let p := univ.filter fun x => X x S = 1
        let n := univ.filter fun x => X x S = -1
        let effect := (∑ x ∈ p, y x) / (p.card : ℝ) - (∑ x ∈ n, y x) / (n.card : ℝ)
        2 * (p.card : ℝ) = N ∧ 2 * (n.card : ℝ) = N ∧ β S = effect / 2 ∧ effect = 2 * β S) ∧
      (∀ b, rss β ≤ rss b ∧ (rss β = rss b ↔ b = β)) := by
  intro X N β rss
  have hN : 0 < N := by
    change 0 < (r : ℝ) * 2 ^ k
    exact mul_pos (Nat.cast_pos.mpr hr) (pow_pos (by norm_num) _)
  have hcount : (Fintype.card ((Fin k → Bool) × Fin r) : ℝ) = N := by
    simp [N, Fintype.card_prod, mul_comm]
  have hg : Xᵀ * X = Matrix.diagonal (fun _ => N) := factorialDesign_gram k r
  have hInv : (Xᵀ * X)⁻¹ = Matrix.diagonal (fun _ => N⁻¹) := by
    apply Matrix.inv_eq_left_inv
    rw [hg, Matrix.diagonal_mul_diagonal]
    simp [hN.ne']
  have hβvec : β = N⁻¹ • (Xᵀ *ᵥ y) := by
    change olsEstimator X y = _
    rw [olsEstimator, olsMatrix_eq, hInv, ← Matrix.mulVec_mulVec, Matrix.diagonal_const_mulVec]
  have hβ (S : Finset (Fin k)) : β S = (∑ x, X x S * y x) / N := by
    rw [hβvec]
    simp [Matrix.mulVec, dotProduct, div_eq_mul_inv, mul_comm]
  have he : Xᵀ *ᵥ (y - X *ᵥ β) = 0 := by
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, hg, Matrix.diagonal_const_mulVec,
      hβvec, smul_smul, mul_inv_cancel₀ hN.ne', one_smul, sub_self]
  refine ⟨hg, ?_, ?_, factorial_rss_minimum X y β N hN hg he⟩
  · rw [hβ]
    simp [X, factorialDesign_empty]
  · intro S hS p n effect
    have hc (x : (Fin k → Bool) × Fin r) : X x S = 1 ∨ X x S = -1 :=
      factorialDesign_sign x S
    have hs0 : (∑ x, X x S) = 0 := by
      have h := congrFun (congrFun hg S) ∅
      simpa [Matrix.mul_apply, X, factorialDesign_empty, Matrix.diagonal_apply_ne _ hS] using h
    obtain ⟨hadd, hsub⟩ := sum_sign_parts (fun x => X x S) hc (fun _ => 1)
    change (∑ x ∈ p, (1 : ℝ)) + (∑ x ∈ n, 1) = ∑ x, 1 at hadd
    change (∑ x, X x S * 1) = (∑ x ∈ p, (1 : ℝ)) - ∑ x ∈ n, 1 at hsub
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, card_univ, hcount] at hadd hsub
    rw [hs0] at hsub
    have hp : 2 * (p.card : ℝ) = N := by linarith
    have hn : 2 * (n.card : ℝ) = N := by linarith
    have hcoef : β S = effect / 2 := by
      have hw := (sum_sign_parts (fun x => X x S) hc y).2
      change (∑ x, X x S * y x) = (∑ x ∈ p, y x) - ∑ x ∈ n, y x at hw
      rw [hβ, hw]
      dsimp only [effect]
      rw [show (p.card : ℝ) = N / 2 by linarith, show (n.card : ℝ) = N / 2 by linarith]
      field_simp
    exact ⟨hp, hn, hcoef, by linarith⟩

end MathlibExt.Probability.Statistics.LinearModel
