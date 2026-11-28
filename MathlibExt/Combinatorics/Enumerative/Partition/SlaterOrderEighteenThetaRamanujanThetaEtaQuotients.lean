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
import Mathlib.Tactic.Ring

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
  have h₂ := norm_pow_lt_one hq two_ne_zero
  have h₄ := norm_pow_lt_one (n := 4) hq (by decide)
  have hneg : ‖-q‖ < 1 := by simpa only [norm_neg] using hq
  have hsq : q * q = q ^ 2 := (sq q).symm
  have hcube : (-q) ^ 3 = -q ^ 3 := by ring
  have hfour : (q ^ 2) ^ 2 = q ^ 4 := by rw [← pow_mul]
  have hmul_four : q ^ 2 * q ^ 2 = q ^ 4 := by ring
  have hsplit₁ : P q (q ^ 2) * P (q ^ 2) (q ^ 2) = P q q := by
    simpa [Fin.prod_univ_two, ← sq] using (qPochhammerInfRaw_split q q hq 2).symm
  have hsplit₂ : P (q ^ 2) (q ^ 4) * P (q ^ 4) (q ^ 4) = P (q ^ 2) (q ^ 2) := by
    have hs := (qPochhammerInfRaw_split (q ^ 2) (q ^ 2) h₂ 2).symm
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
    rw [ramanujanThetaRaw_eq_qPochhammerInfRaw (hsq ▸ h₂), hsq]
    ring
  have ht₂ : ramanujanThetaRaw q (q ^ 3) = P (q ^ 4) (q ^ 4) * P (-q) (q ^ 2) := by
    have hprod : q * q ^ 3 = q ^ 4 := by ring
    have hs : P (-q) (q ^ 2) = P (-q) (q ^ 4) * P (-q ^ 3) (q ^ 4) := by
      simpa [Fin.prod_univ_two, hfour, ← pow_succ', mul_assoc] using
        qPochhammerInfRaw_split (-q) (q ^ 2) h₂ 2
    rw [ramanujanThetaRaw_eq_qPochhammerInfRaw (hprod ▸ h₄), hprod,
      mul_assoc, ← hs]
  have ht₃ : ramanujanThetaRaw (-q) (-q) =
      P (q ^ 2) (q ^ 2) * P q (q ^ 2) ^ 2 := by
    have he : (-q) * (-q) = q ^ 2 := by rw [neg_mul_neg, ← sq]
    rw [ramanujanThetaRaw_eq_qPochhammerInfRaw (he ▸ h₂), he, neg_neg]
    ring
  have ht₄ : ramanujanThetaRaw (-q) (-q ^ 3) = P (q ^ 4) (q ^ 4) * P q (q ^ 2) := by
    have hprod : (-q) * (-q ^ 3) = q ^ 4 := by ring
    have hs : P q (q ^ 2) = P q (q ^ 4) * P (q ^ 3) (q ^ 4) := by
      simpa [Fin.prod_univ_two, hfour, ← pow_succ', mul_assoc] using
        qPochhammerInfRaw_split q (q ^ 2) h₂ 2
    rw [ramanujanThetaRaw_eq_qPochhammerInfRaw (hprod ▸ h₄), hprod,
      neg_neg, neg_neg, mul_assoc, ← hs]
  have ht₅ : ramanujanThetaRaw q (-q ^ 2) = P (-q) (-q) := by
    have hprod : q * (-q ^ 2) = -q ^ 3 := by ring
    have hn : ‖q * (-q ^ 2)‖ < 1 := by
      rw [hprod, norm_neg]
      exact norm_pow_lt_one hq (by decide)
    have hs : P (-q) (-q) =
        P (-q) (-q ^ 3) * P (q ^ 2) (-q ^ 3) * P (-q ^ 3) (-q ^ 3) := by
      simpa [Fin.prod_univ_three, ← pow_succ', hcube, mul_assoc] using
        qPochhammerInfRaw_split (-q) (-q) hneg 3
    rw [ramanujanThetaRaw_eq_qPochhammerInfRaw hn,
      hprod, neg_neg, hs]
    ring
  have hsplit_neg : P (-q) (-q) = P (-q) (q ^ 2) * P (q ^ 2) (q ^ 2) := by
    simpa [Fin.prod_univ_two, ← sq] using qPochhammerInfRaw_split (-q) (-q) hneg 2
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
