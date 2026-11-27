/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.SpecialFunctions.QPochhammer
public import MathlibExt.NumberTheory.ModularForms.JacobiTheta.Ramanujan
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Ring.Int.Parity
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import MathlibExt.Analysis.SpecialFunctions.JacobiTripleProduct

/-!
# Ramanujan's theta function at $(q, q^2)$

The identity `ramanujanTheta_one_two` follows by applying the Jacobi triple product to
both theta series and grouping the resulting factors by their exponents modulo two and three.
-/

namespace MetaMathlibExt

open QPochhammer

local notation "P" => qPochhammerInfRaw

namespace ramanujanTheta_one_two

private lemma norm_pow_lt_one {q : ℂ} (hq : ‖q‖ < 1) {n : ℕ} (hn : n ≠ 0) :
    ‖q ^ n‖ < 1 := by
  rw [norm_pow]
  exact pow_lt_one₀ (norm_nonneg _) hq hn

private lemma twice_triangle (n : ℤ) :
    2 * (((n * (n + 1) / 2).toNat : ℕ) : ℤ) = n * (n + 1) := by
  have hn : 0 ≤ n * (n + 1) := by
    rcases le_or_gt 0 n with h | h
    · exact mul_nonneg h (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos h.le (by omega)
  rw [Int.toNat_of_nonneg (Int.ediv_nonneg hn (by decide))]
  exact Int.two_mul_ediv_two_of_even (Int.even_mul_succ_self n)

private lemma theta_term (z r : ℂ) (hz : z ≠ 0) (n : ℤ) :
    ramanujanThetaTerm (z * r) (z⁻¹ * r) n = z ^ n * r ^ (n * n).toNat := by
  let u := (n * (n + 1) / 2).toNat
  let v := (n * (n - 1) / 2).toNat
  have hu : 2 * (u : ℤ) = n * (n + 1) := twice_triangle n
  have hv : 2 * (v : ℤ) = n * (n - 1) := by
    simpa only [show -n * (-n + 1) = n * (n - 1) by ring] using twice_triangle (-n)
  have hd : (u : ℤ) - v = n := by linarith only [hu, hv]
  have hs : u + v = (n * n).toNat := by
    apply Int.ofNat_inj.mp
    rw [Nat.cast_add, Int.toNat_of_nonneg (mul_self_nonneg n)]
    linarith only [hu, hv]
  change (z * r) ^ u * (z⁻¹ * r) ^ v = _
  rw [mul_pow, mul_pow, mul_mul_mul_comm, ← pow_add, hs,
    ← zpow_natCast z u, ← zpow_natCast z⁻¹ v, inv_zpow', ← zpow_add₀ hz,
    ← sub_eq_add_neg, hd]

open Analysis.SpecialFunctions.JacobiTripleProduct in
private lemma theta_product (z r : ℂ) (hz : z ≠ 0) (hr : ‖r‖ < 1) :
    ramanujanThetaRaw (z * r) (z⁻¹ * r) =
      P (r ^ 2) (r ^ 2) * P (-(z * r)) (r ^ 2) * P (-(z⁻¹ * r)) (r ^ 2) := by
  have h₂ := norm_pow_lt_one hr two_ne_zero
  obtain ⟨-, -, hj⟩ := jacobi_triple_product z r hz hr
  simp only [ramanujanThetaRaw, theta_term z r hz, hj]
  have hp := ((hasProd_qPochhammerInf (r ^ 2) (r ^ 2) h₂).mul
    (hasProd_qPochhammerInf (-(z * r)) (r ^ 2) h₂)).mul
      (hasProd_qPochhammerInf (-(z⁻¹ * r)) (r ^ 2) h₂)
  apply (hp.congr_fun (fun n => ?_)).tprod_eq
  simp only [pow_add, pow_mul, pow_one]
  ring

private lemma one_two_product {q : ℂ} (hq : ‖q‖ < 1) :
    ramanujanThetaRaw q (q ^ 2) = P (q ^ 3) (q ^ 3) * P (-q) (q ^ 3) * P (-q ^ 2) (q ^ 3) := by
  by_cases hq0 : q = 0
  · subst q
    simpa using theta_product 1 0 one_ne_zero (by simp)
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (q ^ 3) zero_lt_two
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact (pow_ne_zero 3 hq0) (by simpa using hr.symm)
  have hr1 : ‖r‖ < 1 := (sq_lt_one_iff₀ (norm_nonneg _)).mp (by
    rw [← norm_pow, hr]
    exact norm_pow_lt_one hq (by decide))
  have ha : q / r * r = q := div_mul_cancel₀ _ hr0
  have hb : (q / r)⁻¹ * r = q ^ 2 := by
    rw [inv_div, div_mul_eq_mul_div, ← sq, hr, pow_succ, mul_div_cancel_right₀ _ hq0]
  simpa only [ha, hb, hr] using theta_product (q / r) r (div_ne_zero hq0 hr0) hr1

-- Group the factors of the Euler product by their positive residues 1, ..., d.
private lemma diagonal_split (q : ℂ) (hq : ‖q‖ < 1) (d : ℕ) [NeZero d] :
    P q q = ∏ i : Fin d, P (q ^ (i.val + 1)) (q ^ d) := by
  let e := (Equiv.prodComm (Fin d) ℕ).trans (Nat.divModEquiv d).symm
  have hp := e.hasProd_iff.mpr (hasProd_qPochhammerInf q q hq)
  have hf := hp.prod_fiberwise (g := fun i : Fin d => P (q ^ (i.val + 1)) (q ^ d)) (by
    intro i
    apply (hasProd_qPochhammerInf _ _ (norm_pow_lt_one hq (NeZero.ne d))).congr_fun
    intro n
    simp [e, pow_add, pow_mul, mul_comm n d]
    ring)
  exact hf.unique (hasProd_fintype _)

private lemma pair_product (a q : ℂ) (hq : ‖q‖ < 1) :
    P a q * P (-a) q = P (a ^ 2) (q ^ 2) := by
  have hp := (hasProd_qPochhammerInf a q hq).mul (hasProd_qPochhammerInf (-a) q hq)
  apply hp.unique
  exact (hasProd_qPochhammerInf (a ^ 2) (q ^ 2) (norm_pow_lt_one hq two_ne_zero)).congr_fun
    fun n => by rw [← pow_mul, mul_comm 2 n, pow_mul]; ring

private lemma diagonal_ne_zero {q : ℂ} (hq : ‖q‖ < 1) : P q q ≠ 0 := by
  simp only [qPochhammerInfRaw, sub_eq_add_neg, ← neg_mul]
  apply tprod_one_add_ne_zero_of_summable
  · intro n
    rw [neg_mul, ← sub_eq_add_neg, ← pow_succ']
    exact sub_ne_zero.mpr (fun he => by
      have hn := norm_pow_lt_one (n := n + 1) hq (Nat.succ_ne_zero n)
      simp only [← he, norm_one, lt_self_iff_false] at hn)
  · simpa only [norm_mul, norm_neg, norm_pow] using
      (summable_geometric_of_lt_one (norm_nonneg q) hq).mul_left ‖q‖

end ramanujanTheta_one_two

open ramanujanTheta_one_two in
/-- **Ramanujan's theta function at $(q, q^2)$.** Let
$f(a,b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's theta function and
$(a;q)_\infty = \prod_{n \ge 0} (1 - a q^n)$. For every complex number $q$ with $|q| < 1$,
$f(q,q^2) \, (q;q^2)_\infty = f(-q^3,-q^3)$, that is, $f(q,q^2) = \varphi(-q^3)/\chi(-q)$ with
the denominator cleared, where $\varphi(q) = f(q,q)$ and $\chi(-q) = (q;q^2)_\infty$.

Source: A. Vanitha, M. P. Chaudhary, and Madiha Khanum, *Modular Relations for the
Rogers-Ramanujan-Slater Type Functions of Order Eighteen with Applications to Partitions*,
INTEGERS 24 (2024), Article A103, Lemma 5, Equation (11) (`integers-2024-A103-lem-5`). -/
public theorem ramanujanTheta_one_two {q : ℂ} (hq : ‖q‖ < 1) :
    ramanujanThetaRaw q (q ^ 2) * qPochhammerInfRaw q (q ^ 2) =
      ramanujanThetaRaw (-q ^ 3) (-q ^ 3) := by
  have h₂ := norm_pow_lt_one hq two_ne_zero
  have h₃ := norm_pow_lt_one (n := 3) hq (by decide)
  have h₆ : (q ^ 3) ^ 2 = q ^ 6 := by rw [← pow_mul]
  have h₄ : (q ^ 2) ^ 2 = q ^ 4 := by rw [← pow_mul]
  have hdiag : ramanujanThetaRaw (-q ^ 3) (-q ^ 3) =
      P (q ^ 6) (q ^ 6) * P (q ^ 3) (q ^ 6) * P (q ^ 3) (q ^ 6) := by
    have h := theta_product 1 (-q ^ 3) one_ne_zero (by simpa only [norm_neg] using h₃)
    simp only [one_mul, inv_one, neg_neg, neg_sq] at h
    rwa [h₆] at h
  have hsplit₂ : P q q = P q (q ^ 2) * P (q ^ 2) (q ^ 2) := by
    simpa [Fin.prod_univ_two] using diagonal_split q hq 2
  have hsplit₃ : P q q = P q (q ^ 3) * P (q ^ 2) (q ^ 3) * P (q ^ 3) (q ^ 3) := by
    simpa [Fin.prod_univ_three, mul_assoc] using diagonal_split q hq 3
  have hsplit₂₃ : P (q ^ 2) (q ^ 2) =
      P (q ^ 2) (q ^ 6) * P (q ^ 4) (q ^ 6) * P (q ^ 6) (q ^ 6) := by
    simpa [Fin.prod_univ_three, ← pow_mul, mul_assoc] using diagonal_split (q ^ 2) h₂ 3
  have hsplit₃₂ : P (q ^ 3) (q ^ 3) = P (q ^ 3) (q ^ 6) * P (q ^ 6) (q ^ 6) := by
    simpa [Fin.prod_univ_two, h₆] using diagonal_split (q ^ 3) h₃ 2
  have hpair₁ : P q (q ^ 3) * P (-q) (q ^ 3) = P (q ^ 2) (q ^ 6) := by
    simpa only [h₆] using pair_product q (q ^ 3) h₃
  have hpair₂ : P (q ^ 2) (q ^ 3) * P (-q ^ 2) (q ^ 3) = P (q ^ 4) (q ^ 6) := by
    have h := pair_product (q ^ 2) (q ^ 3) h₃
    rwa [h₆, h₄] at h
  -- Clear the common Euler product so that the remaining factors can be paired.
  rw [one_two_product hq, hdiag]
  apply mul_right_cancel₀ (diagonal_ne_zero hq)
  calc
    _ = P (q ^ 3) (q ^ 3) ^ 2 * P q (q ^ 2) *
        ((P q (q ^ 3) * P (-q) (q ^ 3)) * (P (q ^ 2) (q ^ 3) * P (-q ^ 2) (q ^ 3))) := by
      rw [hsplit₃]
      ring
    _ = (P (q ^ 3) (q ^ 6) ^ 2 * P (q ^ 6) (q ^ 6)) * (P q (q ^ 2) * P (q ^ 2) (q ^ 2)) := by
      rw [hpair₁, hpair₂, hsplit₃₂, hsplit₂₃]
      ring
    _ = _ := by rw [hsplit₂]; ring

end MetaMathlibExt
