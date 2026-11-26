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
# Eta-quotients of Ramanujan's theta functions

This file proves the seven eta-product identities of `ramanujanTheta_eta_quotients`,
with denominators cleared on the open unit disk.

Source: A. Vanitha, M. P. Chaudhary, and Madiha Khanum, *Modular Relations for the
Rogers-Ramanujan-Slater Type Functions of Order Eighteen with Applications to Partitions*,
INTEGERS 24 (2024), Article A103, Lemma 1 (quoted from Berndt).
-/

namespace MetaMathlibExt

@[expose] public section

open QPochhammer

local notation "P" => qPochhammerInfRaw

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
    have he : -n * (-n + 1) = n * (n - 1) := by ring
    simpa only [he] using twice_triangle (-n)
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

private lemma theta_product_of_ne_zero {a b : ℂ} (ha : a ≠ 0) (hb : b ≠ 0)
    (hab : ‖a * b‖ < 1) :
    ramanujanThetaRaw a b = P (a * b) (a * b) * P (-a) (a * b) * P (-b) (a * b) := by
  obtain ⟨r, hr⟩ := IsAlgClosed.exists_pow_nat_eq (a * b) zero_lt_two
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact (mul_ne_zero ha hb) (by simpa using hr.symm)
  have hr1 : ‖r‖ < 1 := (sq_lt_one_iff₀ (norm_nonneg _)).mp (by
    rw [← norm_pow, hr]
    exact hab)
  have hza : a / r * r = a := div_mul_cancel₀ _ hr0
  have hzb : (a / r)⁻¹ * r = b := by
    rw [inv_div, div_mul_eq_mul_div, ← sq, hr, mul_div_cancel_left₀ _ ha]
  simpa only [hza, hzb, hr] using theta_product (a / r) r (div_ne_zero ha hr0) hr1

private lemma pochhammer_split (a q : ℂ) (hq : ‖q‖ < 1) (d : ℕ) [NeZero d] :
    P a q = ∏ i : Fin d, P (a * q ^ i.val) (q ^ d) := by
  let e := (Equiv.prodComm (Fin d) ℕ).trans (Nat.divModEquiv d).symm
  have hp := e.hasProd_iff.mpr (hasProd_qPochhammerInf a q hq)
  have hf := hp.prod_fiberwise (g := fun i : Fin d => P (a * q ^ i.val) (q ^ d)) (by
    intro i
    apply (hasProd_qPochhammerInf _ _ (norm_pow_lt_one hq (NeZero.ne d))).congr_fun
    intro n
    simp [e, pow_add, pow_mul, mul_comm n d]
    ring)
  exact hf.unique (hasProd_fintype _)

private lemma pochhammer_pair (a q : ℂ) (hq : ‖q‖ < 1) :
    P a q * P (-a) q = P (a ^ 2) (q ^ 2) := by
  have hp := (hasProd_qPochhammerInf a q hq).mul (hasProd_qPochhammerInf (-a) q hq)
  apply hp.unique
  exact (hasProd_qPochhammerInf (a ^ 2) (q ^ 2) (norm_pow_lt_one hq two_ne_zero)).congr_fun
    fun n => by rw [← pow_mul, mul_comm 2 n, pow_mul]; ring

/-- **Eta-quotients of Ramanujan's theta functions.** Let $q$ be a complex number with
$|q| < 1$. Write $(a;q)_\infty = \prod_{n \ge 0} (1 - a q^n)$ and $f_k = (q^k;q^k)_\infty$, and
let $f(a,b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's theta function.
Then $f(q,q) f_1^2 f_4^2 = f_2^5$, $f(q,q^3) f_1 = f_2^2$, $f(-q,-q) f_2 = f_1^2$,
$f(-q,-q^3) f_2 = f_1 f_4$, $f(q,-q^2) f_1 f_4 = f_2^3$, $(-q;q^2)_\infty f_1 f_4 = f_2^2$ and
$(q;q^2)_\infty f_2 = f_1$.

These are the classical eta-quotients $\varphi(q) = f_2^5/(f_1^2 f_4^2)$, $\psi(q) = f_2^2/f_1$,
$\varphi(-q) = f_1^2/f_2$, $\psi(-q) = f_1 f_4/f_2$, $f(q) = f_2^3/(f_1 f_4)$,
$\chi(q) = f_2^2/(f_1 f_4)$ and $\chi(-q) = f_1/f_2$ with the denominators cleared, where
$\varphi(q) = f(q,q)$, $\psi(q) = f(q,q^3)$, $f(q) = f(q,-q^2)$ and $\chi(q) = (-q;q^2)_\infty$.

Source: A. Vanitha, M. P. Chaudhary, and Madiha Khanum, *Modular Relations for the
Rogers-Ramanujan-Slater Type Functions of Order Eighteen with Applications to Partitions*,
INTEGERS 24 (2024), Article A103, Lemma 1 (quoted from Berndt) (`integers-2024-A103-lem-1`). -/
public theorem ramanujanTheta_eta_quotients {q : ℂ} (hq : ‖q‖ < 1) :
    let f₁ := qPochhammerInfRaw q q
    let f₂ := qPochhammerInfRaw (q ^ 2) (q ^ 2)
    let f₄ := qPochhammerInfRaw (q ^ 4) (q ^ 4)
    ramanujanThetaRaw q q * (f₁ ^ 2 * f₄ ^ 2) = f₂ ^ 5 ∧
      ramanujanThetaRaw q (q ^ 3) * f₁ = f₂ ^ 2 ∧
      ramanujanThetaRaw (-q) (-q) * f₂ = f₁ ^ 2 ∧
      ramanujanThetaRaw (-q) (-q ^ 3) * f₂ = f₁ * f₄ ∧
      ramanujanThetaRaw q (-q ^ 2) * (f₁ * f₄) = f₂ ^ 3 ∧
      qPochhammerInfRaw (-q) (q ^ 2) * (f₁ * f₄) = f₂ ^ 2 ∧
      qPochhammerInfRaw q (q ^ 2) * f₂ = f₁
    := by
  dsimp only
  by_cases hq0 : q = 0
  · subst q
    have ht : ramanujanThetaRaw 0 0 = 1 := by
      simpa [qPochhammerInfRaw] using theta_product 1 0 one_ne_zero (by simp)
    simp [qPochhammerInfRaw, ht]
  have h₂ := norm_pow_lt_one hq two_ne_zero
  have h₄ := norm_pow_lt_one (n := 4) hq (by decide)
  have hneg : ‖-q‖ < 1 := by simpa only [norm_neg] using hq
  have hsq : q * q = q ^ 2 := (sq q).symm
  have hcube : (-q) ^ 3 = -q ^ 3 := by ring
  have hfour : (q ^ 2) ^ 2 = q ^ 4 := by rw [← pow_mul]
  have hmul_four : q ^ 2 * q ^ 2 = q ^ 4 := by ring
  have hsplit₁ : P q (q ^ 2) * P (q ^ 2) (q ^ 2) = P q q := by
    simpa [Fin.prod_univ_two, ← sq] using (pochhammer_split q q hq 2).symm
  have hsplit₂ : P (q ^ 2) (q ^ 4) * P (q ^ 4) (q ^ 4) = P (q ^ 2) (q ^ 2) := by
    have hs := (pochhammer_split (q ^ 2) (q ^ 2) h₂ 2).symm
    rw [Fin.prod_univ_two] at hs
    simpa only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, mul_one,
      hmul_four, hfour] using hs
  have hpair : P (-q) (q ^ 2) * P q (q ^ 2) = P (q ^ 2) (q ^ 4) := by
    simpa only [neg_neg, neg_sq, hfour] using pochhammer_pair (-q) (q ^ 2) h₂
  have hchi : P (-q) (q ^ 2) * (P q q * P (q ^ 4) (q ^ 4)) =
      P (q ^ 2) (q ^ 2) ^ 2 := by
    calc
      _ = (P (-q) (q ^ 2) * P q (q ^ 2)) *
          (P (q ^ 2) (q ^ 4) * P (q ^ 4) (q ^ 4)) * P (q ^ 4) (q ^ 4) := by
        rw [← hsplit₁, ← hsplit₂]
        ring
      _ = (P (q ^ 2) (q ^ 4) * P (q ^ 4) (q ^ 4)) ^ 2 := by rw [hpair]; ring
      _ = _ := by rw [hsplit₂]
  have ht₁ : ramanujanThetaRaw q q = P (q ^ 2) (q ^ 2) * P (-q) (q ^ 2) ^ 2 := by
    rw [theta_product_of_ne_zero hq0 hq0 (hsq ▸ h₂), hsq]
    ring
  have ht₂ : ramanujanThetaRaw q (q ^ 3) = P (q ^ 4) (q ^ 4) * P (-q) (q ^ 2) := by
    have hprod : q * q ^ 3 = q ^ 4 := by ring
    have hs : P (-q) (q ^ 2) = P (-q) (q ^ 4) * P (-q ^ 3) (q ^ 4) := by
      simpa [Fin.prod_univ_two, hfour, ← pow_succ', mul_assoc] using
        pochhammer_split (-q) (q ^ 2) h₂ 2
    rw [theta_product_of_ne_zero hq0 (pow_ne_zero 3 hq0) (hprod ▸ h₄), hprod,
      mul_assoc, ← hs]
  have ht₃ : ramanujanThetaRaw (-q) (-q) =
      P (q ^ 2) (q ^ 2) * P q (q ^ 2) ^ 2 := by
    calc
      _ = P (q ^ 2) (q ^ 2) * P q (q ^ 2) * P q (q ^ 2) := by
        simpa only [one_mul, inv_one, neg_neg, neg_sq] using
          theta_product 1 (-q) one_ne_zero hneg
      _ = _ := by ring
  have ht₄ : ramanujanThetaRaw (-q) (-q ^ 3) = P (q ^ 4) (q ^ 4) * P q (q ^ 2) := by
    have hprod : (-q) * (-q ^ 3) = q ^ 4 := by ring
    have hs : P q (q ^ 2) = P q (q ^ 4) * P (q ^ 3) (q ^ 4) := by
      simpa [Fin.prod_univ_two, hfour, ← pow_succ', mul_assoc] using
        pochhammer_split q (q ^ 2) h₂ 2
    rw [theta_product_of_ne_zero (neg_ne_zero.mpr hq0)
      (neg_ne_zero.mpr (pow_ne_zero 3 hq0)) (hprod ▸ h₄), hprod,
      neg_neg, neg_neg, mul_assoc, ← hs]
  have ht₅ : ramanujanThetaRaw q (-q ^ 2) = P (-q) (-q) := by
    have hprod : q * (-q ^ 2) = -q ^ 3 := by ring
    have hn : ‖q * (-q ^ 2)‖ < 1 := by
      rw [hprod, norm_neg]
      exact norm_pow_lt_one hq (by decide)
    have hs : P (-q) (-q) =
        P (-q) (-q ^ 3) * P (q ^ 2) (-q ^ 3) * P (-q ^ 3) (-q ^ 3) := by
      simpa [Fin.prod_univ_three, ← pow_succ', hcube, mul_assoc] using
        pochhammer_split (-q) (-q) hneg 3
    rw [theta_product_of_ne_zero hq0 (neg_ne_zero.mpr (pow_ne_zero 2 hq0)) hn,
      hprod, neg_neg, hs]
    ring
  have hsplit_neg : P (-q) (-q) = P (-q) (q ^ 2) * P (q ^ 2) (q ^ 2) := by
    simpa [Fin.prod_univ_two, ← sq] using pochhammer_split (-q) (-q) hneg 2
  refine ⟨?_, ?_, ?_, ?_, ?_, hchi, hsplit₁⟩
  · rw [ht₁]
    calc
      _ = P (q ^ 2) (q ^ 2) *
          (P (-q) (q ^ 2) * (P q q * P (q ^ 4) (q ^ 4))) ^ 2 := by ring
      _ = _ := by rw [hchi]; ring
  · rw [ht₂]
    calc
      _ = P (-q) (q ^ 2) * (P q q * P (q ^ 4) (q ^ 4)) := by ring
      _ = _ := hchi
  · rw [ht₃]
    calc
      _ = (P q (q ^ 2) * P (q ^ 2) (q ^ 2)) ^ 2 := by ring
      _ = _ := by rw [hsplit₁]
  · rw [ht₄]
    calc
      _ = (P q (q ^ 2) * P (q ^ 2) (q ^ 2)) * P (q ^ 4) (q ^ 4) := by ring
      _ = _ := by rw [hsplit₁]
  · rw [ht₅, hsplit_neg]
    calc
      _ = P (q ^ 2) (q ^ 2) *
          (P (-q) (q ^ 2) * (P q q * P (q ^ 4) (q ^ 4))) := by ring
      _ = _ := by rw [hchi]; ring

end

end MetaMathlibExt
