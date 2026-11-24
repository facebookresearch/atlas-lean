/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
import all MathlibExt.Combinatorics.Enumerative.Partition.OddDistinctsPentagonalRecurrence
import MathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct

/-!
# A three-dissection of the Euler quotient

Splitting the alternating square theta series according to its index modulo three gives
`qEulerProduct_sq_div_three_dissection` for integer power series.
-/

open PowerSeries

namespace MetaMathlibExt

open oddDistincts_pentagonal_recurrence

namespace qEulerProduct_sq_div_three_dissection

open Analysis.SpecialFunctions.JacobiTripleProduct

/-- The Jacobi triple product at `z = -1` gives the alternating square series. -/
private lemma square_sum {q : ℂ} (h : ‖q‖ < 1) :
    HasSum (fun n : ℤ ↦ (-1 : ℂ) ^ n * q ^ (n * n))
      (eulerFunction q ^ 2 / eulerFunction (q ^ 2)) := by
  obtain ⟨hs, _, hj⟩ := jacobi_triple_product (-1) q (by norm_num) h
  have even := (hasProd_eulerFunction (norm_pow_lt h two_ne_zero)).congr_fun
    (g := fun n : ℕ ↦ 1 - q ^ (2 * n + 2)) fun n ↦ by ring
  have odd := odd_minus_prod h
  have hp := ((even.mul odd).mul odd).tprod_eq
  simp only [inv_neg, inv_one, neg_one_mul, ← sub_eq_add_neg] at hj
  rw [hp] at hj
  convert hs.hasSum using 1
  · funext n
    rw [← zpow_natCast, Int.toNat_of_nonneg (mul_self_nonneg n)]
  · rw [hj]
    field_simp [euler_ne (norm_pow_lt h two_ne_zero)]

/-- Group the odd factors in blocks with exponents `6n+1, 6n+3, 6n+5`. -/
private lemma grouped_odd_prod {q : ℂ} (h : ‖q‖ < 1) :
    HasProd (fun n : ℕ ↦ (1 - q ^ (6 * n + 1)) * (1 - q ^ (6 * n + 3)) *
      (1 - q ^ (6 * n + 5))) (eulerFunction q / eulerFunction (q ^ 2)) := by
  have hp := (Nat.divModEquiv 3).symm.hasProd_iff.mpr (odd_minus_prod h)
  refine hp.prod_fiberwise fun n ↦ ?_
  change HasProd (fun i : Fin 3 ↦ 1 - q ^ (2 * (n * 3 + i.val) + 1)) _
  convert hasProd_fintype _ using 1
  rw [Fin.prod_univ_three]
  norm_num
  ring

/-- At nome `q³` and `z = -q²`, the two odd factors have exponents `6n+1` and `6n+5`. -/
private lemma shifted_sum {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) :
    HasSum (fun n : ℤ ↦ (-1 : ℂ) ^ n * q ^ (3 * n * n + 2 * n))
      (eulerFunction q * eulerFunction (q ^ 6) ^ 2 /
        (eulerFunction (q ^ 2) * eulerFunction (q ^ 3))) := by
  have h3 := norm_pow_lt h (by decide : (3 : ℕ) ≠ 0)
  obtain ⟨hs, _, hj⟩ := jacobi_triple_product (-(q ^ 2)) (q ^ 3) (by simp [hq]) h3
  have factor (b : ℕ) : Multipliable (fun n : ℕ ↦ 1 - q ^ (6 * n + b)) := by
    simpa [sub_eq_add_neg] using multipliable_one_add_pow_lin h (-1) (by simp) 6 b (by decide)
  have h1 := (factor 1).hasProd
  have h5 := (factor 5).hasProd
  have hodd := (odd_minus_prod h3).congr_fun
    (g := fun n : ℕ ↦ 1 - q ^ (6 * n + 3)) fun n ↦ by ring
  rw [← pow_mul] at hodd
  have hgroup := ((h1.mul hodd).mul h5).unique (grouped_odd_prod h)
  have h6 := (hasProd_eulerFunction (norm_pow_lt h (by decide : (6 : ℕ) ≠ 0))).congr_fun
    (g := fun n : ℕ ↦ 1 - q ^ (6 * n + 6)) fun n ↦ by ring
  have hp := ((h6.mul h5).mul h1).congr_fun
    (g := fun n : ℕ ↦ (1 - (q ^ 3) ^ (2 * n + 2)) * (1 + -(q ^ 2) * (q ^ 3) ^ (2 * n + 1)) *
      (1 + (-(q ^ 2))⁻¹ * (q ^ 3) ^ (2 * n + 1))) fun n ↦ by
      simp only [inv_neg, neg_mul, ← sub_eq_add_neg, ← pow_mul]
      rw [show 3 * (2 * n + 1) = (6 * n + 1) + 2 by ring, pow_add]
      field_simp
      ring
  rw [hp.tprod_eq] at hj
  have hterms := hs.hasSum.congr_fun (g := fun n : ℤ ↦ (-1 : ℂ) ^ n *
    q ^ (3 * n * n + 2 * n)) fun n ↦ by
      rw [neg_eq_neg_one_mul (q ^ 2), mul_zpow, ← zpow_natCast (q ^ 3),
        Int.toNat_of_nonneg (mul_self_nonneg n)]
      change _ = (-1 : ℂ) ^ n * (q ^ (2 : ℤ)) ^ n * (q ^ (3 : ℤ)) ^ (n * n)
      rw [mul_assoc ((-1 : ℂ) ^ n), ← zpow_mul, ← zpow_mul, ← zpow_add₀ hq]
      ring_nf
  rw [hj] at hterms
  convert hterms using 1
  have h2ne := euler_ne (norm_pow_lt h two_ne_zero)
  have h3ne := euler_ne h3
  have h6ne := euler_ne (norm_pow_lt h (by decide : (6 : ℕ) ≠ 0))
  norm_num at hgroup
  field_simp at hgroup ⊢
  exact hgroup.symm

/-- The three classes, indexed so the last two are negatives of one another. -/
private def threeClasses : ℤ ⊕ (ℤ ⊕ ℤ) ≃ ℤ where
  toFun := Sum.elim (fun n ↦ 3 * n) (Sum.elim (fun n ↦ 3 * n + 1) (fun n ↦ -(3 * n + 1)))
  invFun k := if k % 3 = 0 then .inl (k / 3) else if k % 3 = 1 then .inr (.inl (k / 3))
    else .inr (.inr ((-k) / 3))
  left_inv := by
    rintro (n | n | n) <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
      split_ifs <;> simp_all <;> omega
  right_inv := by
    intro k
    dsimp only
    split_ifs <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> omega

private lemma analytic_dissection {q : ℂ} (hq : q ≠ 0) (h : ‖q‖ < 1) :
    eulerFunction q ^ 2 * eulerFunction (q ^ 6) * eulerFunction (q ^ 9) *
      eulerFunction (q ^ 18) =
    eulerFunction (q ^ 2) * eulerFunction (q ^ 6) * eulerFunction (q ^ 9) ^ 3 -
      2 * q * eulerFunction (q ^ 2) * eulerFunction (q ^ 3) * eulerFunction (q ^ 18) ^ 3 := by
  let term (n : ℤ) := (-1 : ℂ) ^ n * q ^ (n * n)
  have h0 := square_sum (norm_pow_lt h (by decide : (9 : ℕ) ≠ 0))
  have h1 := (shifted_sum (pow_ne_zero 3 hq) (norm_pow_lt h (by decide))).mul_left (-q)
  have zeroClass := h0.congr_fun (g := fun n : ℤ ↦ term (3 * n)) fun n ↦ by
    dsimp [term]
    rw [zpow_mul, show (-1 : ℂ) ^ (3 : ℤ) = -1 by norm_num]
    change _ = (-1 : ℂ) ^ n * (q ^ (9 : ℤ)) ^ (n * n)
    rw [← zpow_mul]
    ring_nf
  have plusClass := h1.congr_fun (g := fun n : ℤ ↦ term (3 * n + 1)) fun n ↦ by
    dsimp [term]
    rw [zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0), zpow_mul, zpow_one,
      show (-1 : ℂ) ^ (3 : ℤ) = -1 by norm_num]
    change _ = -q * ((-1 : ℂ) ^ n * (q ^ (3 : ℤ)) ^ (3 * n * n + 2 * n))
    rw [← zpow_mul, show (3 * n + 1) * (3 * n + 1) = 3 * (3 * n * n + 2 * n) + 1 by ring,
      zpow_add₀ hq, zpow_one]
    ring
  have minusClass := plusClass.congr_fun (g := fun n : ℤ ↦ term (-(3 * n + 1))) fun n ↦ by
    simp only [term, neg_mul_neg, zpow_neg, ← inv_zpow, inv_neg, inv_one]
  have hsum := HasSum.sum (f := term ∘ threeClasses) zeroClass (HasSum.sum plusClass minusClass)
  have he := (square_sum h).unique (threeClasses.hasSum_iff.mp hsum)
  simp only [← pow_mul] at he
  norm_num at he
  have ne (k : ℕ) (hk : k ≠ 0) := euler_ne (norm_pow_lt h hk)
  field_simp [ne 2 (by decide), ne 6 (by decide), ne 9 (by decide), ne 18 (by decide)] at he
  linear_combination he

end qEulerProduct_sq_div_three_dissection

local notation "𝔣" => qEulerProduct

/-- **A 3-dissection of a quotient of Euler products.** In the ring of integer power series in
$q$, let $f_k = \prod_{m \ge 1} (1 - q^{km})$ denote the Euler products. Then
$f_1^2 f_6 f_9 f_{18} = f_2 f_6 f_9^3 - 2q f_2 f_3 f_{18}^3$. Since every $f_k$ with $k \ge 1$ has
constant term $1$, this is the 3-dissection
$f_1^2 / f_2 = f_9^2 / f_{18} - 2q f_3 f_{18}^2 / (f_6 f_9)$ with denominators cleared.

Source: Harishkumar T, Shruthi Menezes, and M. S. Mahadeva Naika, *On [j, k]-Overpartitions with
Even Parts Distinct*, INTEGERS 25 (2025), Article A69, Lemma 3, (11)
(`integers-2025-A69-lem-3`). -/
public theorem qEulerProduct_sq_div_three_dissection :
    𝔣 1 ^ 2 * 𝔣 6 * 𝔣 9 * 𝔣 18 = 𝔣 2 * 𝔣 6 * 𝔣 9 ^ 3 - 2 * X * 𝔣 2 * 𝔣 3 * 𝔣 18 ^ 3 := by
  have h1 := represents_euler 1 one_ne_zero
  simp only [pow_one] at h1
  have h2 := represents_euler 2 two_ne_zero
  have h3 := represents_euler 3 (by decide)
  have h6 := represents_euler 6 (by decide)
  have h9 := represents_euler 9 (by decide)
  have h18 := represents_euler 18 (by decide)
  have hc : Represents 2 (fun _ ↦ 2) := by
    simpa using represents_const 2
  have hx : Represents X id := by
    intro τ
    simpa +contextual [coeff_X, apply_ite, ite_mul] using
      hasSum_ite_eq (1 : ℕ) (Function.Periodic.qParam 1 (τ : ℂ))
  have lhs := (((h1.pow 2).mul h6).mul h9).mul h18
  have main := (h2.mul h6).mul (h9.pow 3)
  have corr := (((hc.mul hx).mul h2).mul h3).mul (h18.pow 3)
  apply lhs.eq_of_eval (g := fun q ↦ _ - _) _ (fun _ ↦
    qEulerProduct_sq_div_three_dissection.analytic_dissection)
  intro τ
  simpa [sub_mul] using (main τ).sub (corr τ)

end MetaMathlibExt
