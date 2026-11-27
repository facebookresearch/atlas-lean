/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.JacobiTheta.Ramanujan
import MathlibExt.Analysis.SpecialFunctions.AndrewsJacobiTripleProduct
import MathlibExt.Analysis.SpecialFunctions.QPochhammer
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Product of the nonic theta functions

`ramanujanTheta_order_nine_product` expresses the product of three nonic theta functions
in terms of Euler products. The Jacobi triple product gives the factors in each residue
class modulo nine.
-/

namespace MetaMathlibExt
namespace NonicProduct

private noncomputable def progression (q : ℂ) (d r : ℕ) : ℂ :=
  ∏' n : ℕ, (1 - q ^ (d * n + r))

private lemma hasProd_progression {q : ℂ} (hq : ‖q‖ < 1) (d r : ℕ) (hd : d ≠ 0) :
    HasProd (fun n : ℕ => 1 - q ^ (d * n + r)) (progression q d r) := by
  have h := QPochhammer.hasProd_qPochhammerInf (q ^ r) (q ^ d)
    (by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq hd)
  simpa only [progression, QPochhammer.qPochhammerInf, QPochhammer.qPochhammerInfRaw,
    pow_add, pow_mul, mul_comm (q ^ r)] using h

-- Split the positive exponents into the residue classes 1, ..., d modulo d.
private lemma euler_split {q : ℂ} (hq : ‖q‖ < 1) (d : ℕ) [NeZero d] :
    progression q 1 1 = ∏ j : Fin d, progression q d (j.val + 1) := by
  have h := hasProd_progression hq 1 1 one_ne_zero
  let e := (Equiv.prodComm (Fin d) ℕ).trans (Nat.divModEquiv d).symm
  have hp := e.hasProd_iff.mpr h
  have hs := hp.prod_fiberwise (g := fun j : Fin d => progression q d (j.val + 1)) (by
    intro j
    simpa [e, mul_comm d, Nat.add_assoc] using hasProd_progression hq d (j.val + 1) (NeZero.ne d))
  exact hs.unique (hasProd_fintype _)

private lemma progression_pow (q : ℂ) (s d r : ℕ) :
    progression (q ^ s) d r = progression q (s * d) (s * r) := by
  unfold progression
  simp_rw [← pow_mul, Nat.mul_add, Nat.mul_assoc]

-- Twice the rising triangular exponent, including for negative indices.
private lemma twice_triangle (n : ℤ) :
    2 * (((n * (n + 1) / 2).toNat : ℕ) : ℤ) = n * (n + 1) := by
  have hn : 0 ≤ n * (n + 1) := by
    rcases le_or_gt 0 n with h | h
    · exact mul_nonneg h (by omega)
    · exact mul_nonneg_of_nonpos_of_nonpos (by omega) (by omega)
  rw [Int.toNat_of_nonneg (Int.ediv_nonneg hn (by decide)), mul_comm]
  exact Int.ediv_mul_cancel (Int.even_mul_succ_self n).two_dvd

private lemma theta_term (q : ℂ) (a b k : ℕ) (hab : a + b = 2 * k + 1) (n : ℤ) :
    ramanujanThetaTerm (-q ^ b) (-q ^ a) n =
      (-1 : ℂ) ^ n * q ^ ((2 * (k : ℤ) + 1) * n * (n + 1) / 2 - (a : ℤ) * n) := by
  let u := (n * (n + 1) / 2).toNat
  let v := (n * (n - 1) / 2).toNat
  have hu : 2 * (u : ℤ) = n * (n + 1) := twice_triangle n
  have hv : 2 * (v : ℤ) = n * (n - 1) := by
    simpa only [show -n * (-n + 1) = n * (n - 1) by ring] using twice_triangle (-n)
  have huv : (u : ℤ) = n + v := by linarith only [hu, hv]
  have hsign : (-1 : ℂ) ^ ((u + v : ℕ) : ℤ) = (-1 : ℂ) ^ n := by
    rw [Nat.cast_add, huv, add_assoc, ← two_mul, zpow_add₀ (by norm_num : (-1 : ℂ) ≠ 0),
      zpow_mul]
    norm_num
  have hexp : (2 * (k : ℤ) + 1) * n * (n + 1) / 2 = (2 * (k : ℤ) + 1) * u := by
    rw [mul_assoc, ← hu, mul_left_comm, Int.mul_ediv_cancel_left _ two_ne_zero]
  have hab' : (a : ℤ) + b = 2 * k + 1 := by exact_mod_cast hab
  have hp : ((b * u + a * v : ℕ) : ℤ) = (2 * (k : ℤ) + 1) * u - a * n := by
    push_cast
    rw [← hab', huv]
    ring
  calc
    _ = (-1 : ℂ) ^ (u + v) * q ^ (b * u + a * v) := by
      change (-q ^ b) ^ u * (-q ^ a) ^ v = _
      rw [← neg_one_mul (q ^ a), ← neg_one_mul (q ^ b)]
      simp only [mul_pow, pow_add, pow_mul]
      ac_rfl
    _ = _ := by rw [← zpow_natCast (n := u + v), hsign, ← zpow_natCast (n := b * u + a * v),
      hp, hexp]

private lemma theta_product {q : ℂ} (hq : ‖q‖ < 1) (a b k : ℕ) (ha : 0 < a)
    (hak : a ≤ k) (hab : a + b = 2 * k + 1) :
    ramanujanThetaRaw (-q ^ a) (-q ^ b) =
      progression q (a + b) (a + b) * progression q (a + b) a * progression q (a + b) b := by
  rw [ramanujanThetaRaw_symm, ramanujanThetaRaw]
  simp_rw [theta_term q a b k hab]
  rw [andrews_jacobi_triple_product q k a ha hak hq]
  have hd : a + b ≠ 0 := by omega
  have hp := ((hasProd_progression hq (a + b) (a + b) hd).mul
    (hasProd_progression hq (a + b) a hd)).mul (hasProd_progression hq (a + b) b hd)
  refine (hp.congr_fun (fun n => ?_)).tprod_eq
  have h : (a : ℤ) + b = 2 * k + 1 := by exact_mod_cast hab
  simp only [← h, ← zpow_natCast q]
  push_cast
  ring_nf

private lemma theta_euler {q : ℂ} (hq : ‖q‖ < 1) :
    ramanujanThetaRaw (-q) (-q ^ 2) = progression q 1 1 := by
  rw [euler_split hq 3, Fin.prod_univ_three]
  have h := theta_product hq 1 2 1 (by decide) (by decide) (by decide)
  rw [pow_one] at h
  exact h.trans (mul_rotate _ _ _)

end NonicProduct

open NonicProduct in
/-- **Product of the nonic theta functions.** Let
$f(a,b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's theta function and
write $f(-x) = f(-x,-x^2)$. For every complex number $q$ with $|q| < 1$,
$f(-q,-q^8) f(-q^2,-q^7) f(-q^4,-q^5) f(-q^3) = f(-q) f(-q^9)^3$, that is,
$f(-q,-q^8) f(-q^2,-q^7) f(-q^4,-q^5) = f(-q) f^3(-q^9)/f(-q^3)$ with the denominator cleared.

Source: A. Vanitha, M. P. Chaudhary, and Madiha Khanum, *Modular Relations for the
Rogers-Ramanujan-Slater Type Functions of Order Eighteen with Applications to Partitions*,
INTEGERS 24 (2024), Article A103, Lemma 4, Equation (10) (`integers-2024-A103-lem-4`). -/
public theorem ramanujanTheta_order_nine_product {q : ℂ} (hq : ‖q‖ < 1) :
    ramanujanThetaRaw (-q) (-q ^ 8) * ramanujanThetaRaw (-q ^ 2) (-q ^ 7) *
        ramanujanThetaRaw (-q ^ 4) (-q ^ 5) * ramanujanThetaRaw (-q ^ 3) (-(q ^ 3) ^ 2) =
      ramanujanThetaRaw (-q) (-q ^ 2) * ramanujanThetaRaw (-q ^ 9) (-(q ^ 9) ^ 2) ^ 3 := by
  have hd3 : ‖q ^ 3‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by decide)
  have hd9 : ‖q ^ 9‖ < 1 := by rw [norm_pow]; exact pow_lt_one₀ (norm_nonneg _) hq (by decide)
  have h18 := theta_product hq 1 8 4 (by decide) (by decide) (by decide)
  rw [pow_one] at h18
  rw [h18, theta_product hq 2 7 4 (by decide) (by decide) (by decide),
    theta_product hq 4 5 4 (by decide) (by decide) (by decide),
    theta_euler hd3, theta_euler hq, theta_euler hd9,
    euler_split hd3 3, euler_split hq 9]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Fin.val_succ, Fin.val_zero, mul_one,
    progression_pow]
  ring

end MetaMathlibExt
