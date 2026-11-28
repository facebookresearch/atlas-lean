/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
import MathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct
import MathlibExt.Combinatorics.Enumerative.Partition.EulerQuotientSixNineIdentity
import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanOneTwo
import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanPsiFChi
import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanSummability
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-!
# The three-dissection of the reciprocal of Ramanujan's psi function

The indices of `f(q, q³)` congruent to 0 or 2 modulo 3 give `f(q³, q⁶)`;
those congruent to 1 give `q * f(q⁹, q²⁷)`. The product forms and the
cubic eta-quotient identity then give the reciprocal three-dissection.
-/

namespace MetaMathlibExt

namespace eulerFunction_one_div_two_sq_eq

open QPochhammer

local notation "P" => qPochhammerInfRaw

private lemma norm_pow_lt {x : ℂ} (hx : ‖x‖ < 1) {k : ℕ} (hk : k ≠ 0) : ‖x ^ k‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hx hk

-- As in the cubic eta-quotient identity, the diagonal product has no zero factors.
private lemma diag_ne_zero {x : ℂ} (hx : ‖x‖ < 1) : P x x ≠ 0 := by
  simp only [qPochhammerInfRaw, sub_eq_add_neg]
  apply tprod_one_add_ne_zero_of_summable
  · intro n
    rw [← sub_eq_add_neg, ← pow_succ']
    exact sub_ne_zero.mpr fun h ↦ by
      have hn := norm_pow_lt hx (Nat.succ_ne_zero n)
      simp only [← h, norm_one, lt_self_iff_false] at hn
  · simpa [norm_mul, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg x) hx).mul_left ‖x‖

private def tri (n : ℤ) : ℕ := (n * (n + 1) / 2).toNat

private lemma twice_tri (n : ℤ) : 2 * (tri n : ℤ) = n * (n + 1) := by
  have hn : 0 ≤ n * (n + 1) := by
    rcases le_or_gt 0 n with h | h
    · exact mul_nonneg h (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos h.le (by omega)
  rw [tri, Int.toNat_of_nonneg (Int.ediv_nonneg hn (by decide))]
  exact Int.two_mul_ediv_two_of_even (Int.even_mul_succ_self n)

private lemma theta_term (q : ℂ) (a b : ℕ) (n : ℤ) :
    ramanujanThetaTerm (q ^ a) (q ^ b) n = q ^ (a * tri n + b * tri (-n)) := by
  rw [ramanujanThetaTerm, tri, tri, show -n * (-n + 1) = n * (n - 1) by ring,
    pow_add, pow_mul, pow_mul]

private lemma twice_exponent (a b : ℕ) (n : ℤ) :
    2 * ((a * tri n + b * tri (-n) : ℕ) : ℤ) =
      (a : ℤ) * (n * (n + 1)) + (b : ℤ) * (n * (n - 1)) := by
  push_cast
  linear_combination (a : ℤ) * twice_tri n + (b : ℤ) * twice_tri (-n)

-- For A, the even indices map to residue 0, and the odd indices to residue 2.
-- For B, all indices map to residue 1, reversing the progression.
private def psiClasses : ℤ ⊕ ℤ ≃ ℤ where
  toFun := Sum.elim (fun n ↦ if n % 2 = 0 then 3 * (n / 2) else -3 * (n / 2) - 1)
    (fun n ↦ 1 - 3 * n)
  invFun k := if k % 3 = 0 then .inl (2 * (k / 3)) else if k % 3 = 1 then .inr (-(k / 3))
    else .inl (-2 * (k / 3) - 1)
  left_inv := by
    rintro (n | n) <;> simp only [Sum.elim_inl, Sum.elim_inr] <;>
      split_ifs <;> simp_all <;> omega
  right_inv := by
    intro k
    dsimp only
    split_ifs <;> simp only [Sum.elim_inl, Sum.elim_inr] <;> omega

private lemma hasSum_theta {a b : ℂ} (h : ‖a * b‖ < 1) :
    HasSum (ramanujanThetaTerm a b) (ramanujanThetaRaw a b) :=
  (ramanujanTheta_summable a b h).of_norm.hasSum

private lemma psi_split {q : ℂ} (hq : ‖q‖ < 1) :
    ramanujanThetaRaw q (q ^ 3) =
      ramanujanThetaRaw (q ^ 3) (q ^ 6) + q * ramanujanThetaRaw (q ^ 9) (q ^ 27) := by
  have h (k : ℕ) (hk : k ≠ 0) := norm_pow_lt hq hk
  have hψ : ‖q * q ^ 3‖ < 1 := by
    rw [show q * q ^ 3 = q ^ 4 by ring]
    exact h 4 (by decide)
  have hA : ‖q ^ 3 * q ^ 6‖ < 1 := by rw [← pow_add]; exact h 9 (by decide)
  have hB : ‖q ^ 9 * q ^ 27‖ < 1 := by rw [← pow_add]; exact h 36 (by decide)
  let term := ramanujanThetaTerm q (q ^ 3)
  have ht (n : ℤ) : term n = q ^ (1 * tri n + 3 * tri (-n)) := by
    simpa only [term, pow_one] using theta_term q 1 3 n
  have ha := (hasSum_theta hA).congr_fun (g := fun n ↦ term (psiClasses (.inl n))) fun n ↦ by
    rw [ht, theta_term]
    apply congrArg (q ^ ·)
    apply Int.ofNat_inj.mp
    apply (mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0))
    change 2 * (↑(1 * tri (if n % 2 = 0 then 3 * (n / 2) else -3 * (n / 2) - 1) +
        3 * tri (-(if n % 2 = 0 then 3 * (n / 2) else -3 * (n / 2) - 1))) : ℤ) = _
    split_ifs with hn
    · have he : n = 2 * (n / 2) := by omega
      rw [twice_exponent, twice_exponent]
      conv_rhs => rw [he]
      push_cast
      ring
    · have he : n = 2 * (n / 2) + 1 := by omega
      rw [twice_exponent, twice_exponent]
      conv_rhs => rw [he]
      push_cast
      ring
  have hb := ((hasSum_theta hB).mul_left q).congr_fun
    (g := fun n ↦ term (psiClasses (.inr n))) fun n ↦ by
      rw [ht, theta_term, ← pow_succ']
      apply congrArg (q ^ ·)
      apply Int.ofNat_inj.mp
      apply (mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0))
      change 2 * (↑(1 * tri (1 - 3 * n) + 3 * tri (-(1 - 3 * n))) : ℤ) = _
      rw [Nat.cast_add (9 * tri n + 27 * tri (-n)) 1, mul_add, twice_exponent, twice_exponent]
      push_cast
      ring
  have hs := HasSum.sum (f := term ∘ psiClasses) ha hb
  exact (hasSum_theta hψ).unique (psiClasses.hasSum_iff.mp hs)

open Analysis.SpecialFunctions.JacobiTripleProduct in
private lemma theta_neg_diag {x : ℂ} (hx : ‖x‖ < 1) :
    ramanujanThetaRaw (-x) (-x) = P (x ^ 2) (x ^ 2) * P x (x ^ 2) ^ 2 := by
  obtain ⟨-, -, hj⟩ := jacobi_triple_product 1 (-x) one_ne_zero (by simpa using hx)
  have ht (n : ℤ) : ramanujanThetaTerm (-x) (-x) n = (1 : ℂ) ^ n * (-x) ^ (n * n).toNat := by
    have he : 1 * tri n + 1 * tri (-n) = (n * n).toNat := by
      apply Int.ofNat_inj.mp
      apply (mul_left_cancel₀ (by decide : (2 : ℤ) ≠ 0))
      rw [Int.toNat_of_nonneg (mul_self_nonneg n), twice_exponent]
      ring
    rw [one_zpow, one_mul, ← he]
    simpa only [pow_one] using theta_term (-x) 1 1 n
  simp only [ramanujanThetaRaw, ht, hj]
  have h₂ := norm_pow_lt hx two_ne_zero
  have he := hasProd_qPochhammerInf (x ^ 2) (x ^ 2) h₂
  have ho := hasProd_qPochhammerInf x (x ^ 2) h₂
  rw [pow_two (P x (x ^ 2)), ← mul_assoc]
  refine (((he.mul ho).mul ho).congr_fun (fun n ↦ ?_)).tprod_eq
  rw [pow_add (-x) (2 * n) 2, pow_add (-x) (2 * n) 1, pow_mul, neg_sq, pow_one]
  simp only [inv_one, one_mul]
  ring

-- Use f(x, x²) χ(-x) = f(-x³, -x³), and split each Euler product into even and odd factors.
private lemma theta_one_two_quotient {x : ℂ} (hx : ‖x‖ < 1) :
    ramanujanThetaRaw x (x ^ 2) =
      P (x ^ 2) (x ^ 2) * P (x ^ 3) (x ^ 3) ^ 2 / (P x x * P (x ^ 6) (x ^ 6)) := by
  have h₂ := norm_pow_lt hx two_ne_zero
  have h₃ := norm_pow_lt hx three_ne_zero
  have h₆ := norm_pow_lt hx (show (6 : ℕ) ≠ 0 by decide)
  have h := ramanujanTheta_one_two hx
  rw [theta_neg_diag h₃, (ramanujan_psi_f_chi_eq_qPochhammer x hx).2.2.2,
    (ramanujan_psi_f_chi_eq_qPochhammer (x ^ 3) h₃).2.2.2, ← pow_mul] at h
  have n₁ := diag_ne_zero hx
  have n₂ := diag_ne_zero h₂
  have n₆ := diag_ne_zero h₆
  calc
    _ = (P (x ^ 6) (x ^ 6) * (P (x ^ 3) (x ^ 3) / P (x ^ 6) (x ^ 6)) ^ 2) /
        (P x x / P (x ^ 2) (x ^ 2)) := (eq_div_iff (div_ne_zero n₁ n₂)).2 h
    _ = _ := by field_simp

end eulerFunction_one_div_two_sq_eq

-- Keep the inline convergence proof in the statement, as in the wanted declaration.
set_option backward.proofsInPublic true in
open QPochhammer eulerFunction_one_div_two_sq_eq in
/-- **Three-dissection of $(q;q)_\infty / (q^2;q^2)_\infty^2$.** Let $q$ be a complex number
with $|q| < 1$, and for each integer $k \ge 1$ write $E_k = (q^k; q^k)_\infty$, the infinite
q-Pochhammer symbol $\prod_{n=0}^{\infty} (1 - q^{k(n+1)})$. Then

$$
\frac{E_1}{E_2^2} = \frac{E_3^2 E_9^3}{E_6^6} - q \, \frac{E_3^3 E_{18}^3}{E_6^7} +
  q^2 \, \frac{E_3^4 E_{18}^6}{E_6^8 E_9^3}.
$$

Source: Xue Liang, *Congruences Modulo 512 for the Overpartition Function*, INTEGERS 25 (2025),
Article A76, Lemma 1, identity (11) (`integers-2025-A76-lem-1`). -/
public theorem eulerFunction_one_div_two_sq_eq (q : ℂ) (hq : ‖q‖ < 1) :
    let E : ℕ → ℂ := fun k => if hk : k = 0 then 1 else
      QPochhammer.qPochhammerInf (q ^ k) (q ^ k)
        (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg q) hq hk)
    E 1 / E 2 ^ 2 =
      E 3 ^ 2 * E 9 ^ 3 / E 6 ^ 6 - q * (E 3 ^ 3 * E 18 ^ 3 / E 6 ^ 7) +
        q ^ 2 * (E 3 ^ 4 * E 18 ^ 6 / (E 6 ^ 8 * E 9 ^ 3)) := by
  intro E
  have hE (k : ℕ) (hk : k ≠ 0) : E k = qPochhammerInfRaw (q ^ k) (q ^ k) := by
    simp [E, hk, qPochhammerInf]
  have nE (k : ℕ) (hk : k ≠ 0) : E k ≠ 0 := by
    rw [hE k hk]
    exact diag_ne_zero (norm_pow_lt hq hk)
  have n₁ := nE 1 (by decide)
  have n₂ := nE 2 (by decide)
  have n₃ := nE 3 (by decide)
  have n₆ := nE 6 (by decide)
  have n₉ := nE 9 (by decide)
  have n₁₈ := nE 18 (by decide)
  let A := E 6 * E 9 ^ 2 / (E 3 * E 18)
  let B := E 18 ^ 2 / E 9
  let C := E 6 ^ 8 * E 9 / (E 3 ^ 4 * E 18 ^ 2)
  have hψ : E 2 ^ 2 / E 1 = A + q * B := by
    have hs := psi_split hq
    have hA := theta_one_two_quotient (norm_pow_lt hq (show (3 : ℕ) ≠ 0 by decide))
    have hB := (ramanujan_psi_f_chi_eq_qPochhammer (q ^ 9) (norm_pow_lt hq (by decide))).1
    simp only [← pow_mul] at hA hB
    rw [(ramanujan_psi_f_chi_eq_qPochhammer q hq).1, hA, hB] at hs
    simpa only [A, B, hE 1 (by decide), hE 2 (by decide), hE 3 (by decide), hE 6 (by decide),
      hE 9 (by decide), hE 18 (by decide), pow_one] using hs
  have hC : A ^ 3 + q ^ 3 * B ^ 3 = C := by
    have hc : E 6 ^ 3 * E 9 ^ 6 / (E 3 ^ 3 * E 18 ^ 3) = C - q ^ 3 * (E 18 ^ 6 / E 9 ^ 3) :=
      eulerFunction_six_cube_nine_six_div_eq q hq
    dsimp only [A, B]
    simp only [div_pow, mul_pow, ← pow_mul]
    change E 6 ^ 3 * E 9 ^ 6 / (E 3 ^ 3 * E 18 ^ 3) + q ^ 3 * (E 18 ^ 6 / E 9 ^ 3) = C
    rw [hc, sub_add_cancel]
  have hfac : (E 2 ^ 2 / E 1) * (A ^ 2 - q * A * B + q ^ 2 * B ^ 2) = C := by
    rw [hψ, ← hC]
    ring
  have nC : C ≠ 0 :=
    div_ne_zero (mul_ne_zero (pow_ne_zero _ n₆) n₉)
      (mul_ne_zero (pow_ne_zero _ n₃) (pow_ne_zero _ n₁₈))
  calc
    _ = (A ^ 2 - q * A * B + q ^ 2 * B ^ 2) / C := by
      apply (eq_div_iff nC).2
      rw [← hfac]
      field_simp
    _ = _ := by dsimp [A, B, C]; field_simp

end MetaMathlibExt
