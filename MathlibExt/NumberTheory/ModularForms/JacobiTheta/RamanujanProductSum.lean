/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanProduct
import Mathlib.Tactic.Ring

/-!
# Sum of products of Ramanujan theta functions

Adding the product formulas before and after simultaneous negation cancels the odd-index
contribution. The case where both parameters of the first theta function are zero follows
from the two-term formula for a theta function with one zero parameter.
-/

namespace MetaMathlibExt

open QPochhammer

private theorem ramanujanThetaRaw_zero_left (b : ℂ) : ramanujanThetaRaw 0 b = 1 + b := by
  rw [ramanujanThetaRaw_eq_qPochhammerInfRaw (a := 0) (b := b) (by simp)]
  simp only [zero_mul, neg_zero, qPochhammerInfRaw_eq_tprod, tprod_one, sub_zero, one_mul]
  rw [tprod_eq_prod (s := {0})]
  · simp
  · intro n hn
    simp [zero_pow (by simpa using hn : n ≠ 0)]

private theorem ramanujanTheta_mul_add_mul_neg_of_ne_zero {a b c d : ℂ} (ha : a ≠ 0)
    (habcd : a * b = c * d) (hab : ‖a * b‖ < 1) :
    ramanujanThetaRaw a b * ramanujanThetaRaw c d +
        ramanujanThetaRaw (-a) (-b) * ramanujanThetaRaw (-c) (-d) =
      2 * ramanujanThetaRaw (a * c) (b * d) * ramanujanThetaRaw (a * d) (b * c) := by
  have hneg := ramanujanTheta_mul_of_mul_eq (a := -a) (b := -b) (c := -c) (d := -d)
    (neg_ne_zero.mpr ha) (by simpa only [neg_mul_neg] using hab)
    (by simpa only [neg_mul_neg] using habcd)
  simp only [neg_div_neg_eq, neg_sq, mul_neg, neg_mul, neg_neg] at hneg
  rw [ramanujanTheta_mul_of_mul_eq ha hab habcd, hneg]
  ring

/-- **Ramanujan's theta function: sum of products when $ab = cd$.** Let
$f(a,b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's theta function. For
complex numbers $a, b, c, d$ with $ab = cd$ and $|ab| < 1$,
$f(a,b) f(c,d) + f(-a,-b) f(-c,-d) = 2 f(ac,bd) f(ad,bc)$.

This is Entry 29(i) of Berndt's *Ramanujan's Notebooks*; the hypothesis $|ab| < 1$ makes all
the theta series converge.

Source: A. Vanitha, M. P. Chaudhary, and Madiha Khanum, *Modular Relations for the
Rogers-Ramanujan-Slater Type Functions of Order Eighteen with Applications to Partitions*,
INTEGERS 24 (2024), Article A103, Lemma 2, Equation (6) (`integers-2024-A103-lem-2`). -/
public theorem ramanujanTheta_mul_add_mul_neg {a b c d : ℂ} (habcd : a * b = c * d)
    (hab : ‖a * b‖ < 1) :
    ramanujanThetaRaw a b * ramanujanThetaRaw c d +
        ramanujanThetaRaw (-a) (-b) * ramanujanThetaRaw (-c) (-d) =
      2 * ramanujanThetaRaw (a * c) (b * d) * ramanujanThetaRaw (a * d) (b * c) := by
  by_cases ha : a = 0
  · by_cases hb : b = 0
    · subst a b
      have hcd : c * d = 0 := by simpa using habcd.symm
      rcases mul_eq_zero.mp hcd with rfl | rfl
      · simp [ramanujanThetaRaw_zero_left]
        ring
      · simp [ramanujanThetaRaw_symm c 0, ramanujanThetaRaw_symm (-c) 0,
          ramanujanThetaRaw_zero_left]
        ring
    · rw [ramanujanThetaRaw_symm a b, ramanujanThetaRaw_symm c d,
        ramanujanThetaRaw_symm (-a) (-b), ramanujanThetaRaw_symm (-c) (-d),
        ramanujanThetaRaw_symm (a * c) (b * d), ramanujanThetaRaw_symm (a * d) (b * c)]
      exact ramanujanTheta_mul_add_mul_neg_of_ne_zero hb
        (by simpa only [mul_comm b a, mul_comm d c] using habcd)
        (by simpa only [mul_comm b a] using hab)
  · exact ramanujanTheta_mul_add_mul_neg_of_ne_zero ha habcd hab

end MetaMathlibExt
