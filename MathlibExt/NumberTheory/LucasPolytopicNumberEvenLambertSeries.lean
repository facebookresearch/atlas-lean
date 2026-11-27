/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Topology.Algebra.InfiniteSum.Defs
public import MathlibExt.NumberTheory.LucasPolytopicNumber
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import all MathlibExt.NumberTheory.LucasPolytopicNumberHasSumInvLucasBracketMulSucc

/-!
# Even-index Lucas-bracket series

For nondegenerate real Lucas parameters with $s > 0$ and $s^2 + 4t > 0$, let
$\varphi' = (s - \sqrt{s^2 + 4t})/2$ and $q = \varphi'^2/t$. The series
$\sum_{n \ge 1} t^n/\{2n\}_{s,t}$ converges absolutely and sums to
$\sqrt{s^2 + 4t}\,(L(q) - L(q^2))$, where $L(x) = \sum_{n \ge 1} x^n/(1 - x^n)$.
The inequalities make explicit the real convergence conditions for the two Lambert arguments.

## References

* Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
  Journal of Integer Sequences 28 (2025), Article 25.5.6, pp. 1–19, §2 and Theorem 11 (p. 15).
* The proof uses `bracket_closed` from
  `MathlibExt.NumberTheory.LucasPolytopicNumberHasSumInvLucasBracketMulSucc` and
  `summable_norm_pow_mul_geometric_div_one_sub` from
  `Mathlib.NumberTheory.TsumDivisorsAntidiagonal`.
-/

namespace MetaMathlibExt

/-- **Even-index Lucas-bracket series as Lambert series.** Let $(s, t)$ be nondegenerate Lucas
parameters with $s > 0$ and $s^2 + 4t > 0$, write $\{n\}_{s,t}$ for the Lucas brackets, let
$\varphi' = (s - \sqrt{s^2 + 4t})/2$ and let $L(x) = \sum_{n \ge 1} x^n/(1 - x^n)$ be the Lambert
series. Then the series $\sum_{n \ge 1} t^n/\{2n\}_{s,t}$ converges absolutely, and its sum is
$\sqrt{s^2 + 4t}\,\bigl(L(\varphi'^2/t) - L(\varphi'^4/t^2)\bigr)$.

The hypotheses make $\varphi'$ real with $|\varphi'| < (s + \sqrt{s^2 + 4t})/2$, so both Lambert
arguments lie in $(-1, 1)$.

Source: Ronald Orozco López, *Simplicial d-Polytopic Numbers Defined on Lucas Sequences*,
Journal of Integer Sequences 28 (2025), Article 25.5.6, Theorem 11
(`jis-2025-25.5.6-thm-11`). -/
public theorem hasSum_pow_div_lucasBracket_two_mul (P : LucasParameters) (hs : 0 < P.s)
    (hdisc : 0 < P.s ^ 2 + 4 * P.t) :
    HasSum (fun n : ℕ => P.t ^ (n + 1) / lucasBracket P (2 * (n + 1)))
      (Real.sqrt (P.s ^ 2 + 4 * P.t) *
        ((∑' n : ℕ, (((P.s - Real.sqrt (P.s ^ 2 + 4 * P.t)) / 2) ^ 2 / P.t) ^ (n + 1) /
            (1 - (((P.s - Real.sqrt (P.s ^ 2 + 4 * P.t)) / 2) ^ 2 / P.t) ^ (n + 1))) -
          ∑' n : ℕ, (((P.s - Real.sqrt (P.s ^ 2 + 4 * P.t)) / 2) ^ 4 / P.t ^ 2) ^ (n + 1) /
            (1 - (((P.s - Real.sqrt (P.s ^ 2 + 4 * P.t)) / 2) ^ 4 / P.t ^ 2) ^ (n + 1)))) := by
  let d := Real.sqrt (P.s ^ 2 + 4 * P.t)
  let a := (P.s + d) / 2
  let b := (P.s - d) / 2
  let q := b ^ 2 / P.t
  have hd : 0 < d := Real.sqrt_pos.2 hdisc
  have hd2 : d ^ 2 = P.s ^ 2 + 4 * P.t := Real.sq_sqrt hdisc.le
  have hsum : a + b = P.s := by dsimp [a, b]; ring
  have hdiff : a - b = d := by dsimp [a, b]; ring
  have hprod : a * b = -P.t := by
    dsimp [a, b]
    linear_combination -hd2 / 4
  have ha : 0 < a := by dsimp [a]; linarith
  have hqa : a * q = -b := by
    dsimp [q]
    rw [← mul_div_assoc, div_eq_iff P.t_ne_zero]
    linear_combination b * hprod
  have hq : |q| < 1 := by
    have hab : |b| < a := abs_lt.2 ⟨by linarith, by linarith⟩
    rw [← abs_neg b, ← hqa, abs_mul, abs_of_pos ha] at hab
    exact (mul_lt_iff_lt_one_right ha).mp hab
  have hq2 : |q ^ 2| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg _) hq (by decide)
  have hsquare : q ^ 2 = b ^ 4 / P.t ^ 2 := by
    dsimp [q]
    rw [div_pow, ← pow_mul]
  have hlambert {r : ℝ} (hr : |r| < 1) :
      Summable (fun n : ℕ => r ^ (n + 1) / (1 - r ^ (n + 1))) := by
    have h := summable_norm_pow_mul_geometric_div_one_sub 0 (r := r)
      (by simpa only [Real.norm_eq_abs] using hr)
    simpa only [pow_zero, one_mul] using (summable_nat_add_iff 1).2 h
  change HasSum _ (d * ((∑' n : ℕ, q ^ (n + 1) / (1 - q ^ (n + 1))) -
    ∑' n : ℕ, (b ^ 4 / P.t ^ 2) ^ (n + 1) / (1 - (b ^ 4 / P.t ^ 2) ^ (n + 1))))
  rw [← hsquare]
  refine (((hlambert hq).hasSum.sub (hlambert hq2).hasSum).mul_left d).congr_fun fun n => ?_
  symm
  let m := n + 1
  have hden (r : ℝ) (hr : |r| < 1) : 1 - r ^ m ≠ 0 := by
    apply sub_ne_zero.mpr
    apply ne_of_gt
    refine (le_abs_self _).trans_lt ?_
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg _) hr (Nat.succ_ne_zero n)
  have hbr : lucasBracket P (2 * m) ≠ 0 :=
    lucasBracket_ne_zero P (Nat.mul_ne_zero (by decide) (Nat.succ_ne_zero n))
  have hbq : b = a * -q := by rw [mul_neg, hqa, neg_neg]
  have hta : P.t = a ^ 2 * q := by rw [pow_two, mul_assoc, hqa, mul_neg, hprod, neg_neg]
  have htpow : P.t ^ m = a ^ (2 * m) * q ^ m := by rw [hta, mul_pow, pow_mul a 2 m]
  have hbc : d * lucasBracket P (2 * m) = a ^ (2 * m) * (1 - (q ^ 2) ^ m) := by
    rw [← hdiff, bracket_closed P a b hsum hprod, hbq, mul_pow, pow_mul (-q) 2 m, neg_sq]
    ring
  calc
    d * (q ^ m / (1 - q ^ m) - (q ^ 2) ^ m / (1 - (q ^ 2) ^ m)) =
        d * (q ^ m / (1 - (q ^ 2) ^ m)) := by
      field_simp [hden q hq, hden (q ^ 2) hq2]
      rw [pow_right_comm q 2 m]
      ring
    _ = P.t ^ m / lucasBracket P (2 * m) := by
      rw [← mul_div_assoc, div_eq_div_iff (hden (q ^ 2) hq2) hbr, htpow]
      linear_combination q ^ m * hbc

end MetaMathlibExt
