/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ModularForms.JacobiTheta.RamanujanProduct
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Difference of products of Ramanujan theta functions

For parameters with a common product, `ramanujanTheta_mul_sub_mul_neg` factors the difference
of two theta products. Applying the product identity before and after negating the parameters
cancels the even-index contribution and doubles the odd-index contribution.
-/

namespace MetaMathlibExt

/-- **Ramanujan's theta function: difference of products when $ab = cd$.** Let
$f(a,b) = \sum_{n \in \mathbb{Z}} a^{n(n+1)/2} b^{n(n-1)/2}$ be Ramanujan's theta function. For
complex numbers $a, b, c, d$ with $ab = cd$, $|ab| < 1$, $c \ne 0$ and $d \ne 0$,
$f(a,b) f(c,d) - f(-a,-b) f(-c,-d) = 2a \, f(b/c, ac^2 d) \, f(b/d, acd^2)$.

This is Entry 29(ii) of Berndt's *Ramanujan's Notebooks*, where the second arguments are written
$(c/b)abcd = ac^2 d$ and $(d/b)abcd = acd^2$.

Source: A. Vanitha, M. P. Chaudhary, and Madiha Khanum, *Modular Relations for the
Rogers-Ramanujan-Slater Type Functions of Order Eighteen with Applications to Partitions*,
INTEGERS 24 (2024), Article A103, Lemma 2, Equation (7) (`integers-2024-A103-lem-2`). -/
public theorem ramanujanTheta_mul_sub_mul_neg {a b c d : ℂ} (habcd : a * b = c * d)
    (hab : ‖a * b‖ < 1) (hc : c ≠ 0) (hd : d ≠ 0) :
    ramanujanThetaRaw a b * ramanujanThetaRaw c d -
        ramanujanThetaRaw (-a) (-b) * ramanujanThetaRaw (-c) (-d) =
      2 * a * ramanujanThetaRaw (b / c) (a * c ^ 2 * d) *
        ramanujanThetaRaw (b / d) (a * c * d ^ 2) := by
  have hab_ne : a * b ≠ 0 := habcd ▸ mul_ne_zero hc hd
  have ha := (mul_ne_zero_iff.mp hab_ne).1
  have hneg := ramanujanTheta_mul_of_mul_eq (a := -a) (b := -b) (c := -c) (d := -d)
    (neg_ne_zero.mpr ha) (by simpa only [neg_mul_neg] using hab)
    (by simpa only [neg_mul_neg] using habcd)
  simp only [neg_div_neg_eq, neg_sq, mul_neg, neg_mul, neg_neg] at hneg
  have hca : c / a = b / d := (div_eq_div_iff ha hd).2 (by linear_combination -habcd)
  have hda : d / a = b / c := (div_eq_div_iff ha hc).2 (by linear_combination -habcd)
  have hbd : a ^ 2 * b * d = a * c * d ^ 2 := by linear_combination a * d * habcd
  have hbc : a ^ 2 * b * c = a * c ^ 2 * d := by linear_combination a * c * habcd
  rw [ramanujanTheta_mul_of_mul_eq ha hab habcd, hneg, hca, hda, hbd, hbc]
  ring

end MetaMathlibExt
