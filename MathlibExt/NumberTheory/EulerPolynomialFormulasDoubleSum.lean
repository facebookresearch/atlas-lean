/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.EulerPolynomialGeneralizedStirling
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Polynomial.Eval.SMul
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Double-sum formula for Euler polynomials

For each natural number `n`, the scaled Euler polynomial `2^n E_n(x)` is a double sum
of generalized Stirling polynomials evaluated at `2x - 1`. We extract coefficients from
the formal derivative of `log(1 + z + z²/2)`, then regroup the Stirling expansion by
total index.

## References

* Nouara Mokhtari, Rachid Boumahdi, and Farid Bencherif,
  *Generalizations of Several Explicit Formulas for Euler Polynomials*, INTEGERS 25 (2025),
  Article A65, pp. 1–15, Theorem 4.3 (equation (30)) and Lemma 2.2 (equation (9)).
* Chun-Fu Wei and Feng Qi, *Several closed expressions for the Euler numbers*, Journal of
  Inequalities and Applications 2015 (2015), Article 219, Theorem 1.3, equation (1.6),
  the Euler-number formula that Theorem 4.3 generalizes.
-/

namespace MathlibExt.NumberTheory.EulerPolynomialFormulasWanted

section Coefficients

open PowerSeries

/-- The argument substituted into the power series for `log(1 + z)`. -/
private noncomputable def logArg : PowerSeries ℚ := X * (1 + C (1 / 2) * X)

private theorem logArg_hasSubst : HasSubst logArg :=
  HasSubst.of_constantCoeff_zero' (by simp [logArg])

private theorem logArg_eq : logArg = (X + C (1 / 2) * X ^ 2 : PowerSeries ℚ) := by
  unfold logArg
  ring

private theorem mk_eulerAlpha_mul :
    mk eulerAlpha * (1 + logArg) = (1 + X : PowerSeries ℚ) := by
  rw [logArg_eq, ← add_assoc, mul_add, mul_add, mul_one, mul_comm (C (1 / 2 : ℚ)), ← mul_assoc]
  apply PowerSeries.ext
  intro n
  cases n with
  | zero => simp [eulerAlpha]
  | succ n =>
    cases n with
    | zero => norm_num [eulerAlpha, coeff_mul_X_pow']
    | succ n =>
      have hcoeff : coeff (n + 2) (mk eulerAlpha * X ^ 2) = eulerAlpha n := by
        rw [coeff_mul_X_pow, coeff_mk]
      simp only [map_add, coeff_succ_mul_X, coeff_mul_C, hcoeff, coeff_mk,
        coeff_one, coeff_X, Nat.succ_ne_zero, Nat.succ.injEq, ite_false, add_zero]
      rw [eulerAlpha]
      ring

private theorem derivative_log_subst :
    derivative ((log ℚ).subst logArg) = mk eulerAlpha := by
  have hd : derivative logArg = (1 + X : PowerSeries ℚ) := by
    rw [logArg_eq, map_add, derivative_X, derivative_C_mul_X_sq]
    norm_num
  have h := congrArg (substAlgHom (R := ℚ) logArg_hasSubst)
    (derivative_log_mul_one_add_X (A := ℚ))
  simp only [map_mul, map_add, map_one, substAlgHom_X, coe_substAlgHom] at h
  have hn : (1 + logArg : PowerSeries ℚ) ≠ 0 := by
    intro heq
    simpa [logArg] using congrArg (constantCoeff (R := ℚ)) heq
  apply mul_right_cancel₀ hn
  rw [mk_eulerAlpha_mul, derivative_subst logArg_hasSubst, hd,
    mul_right_comm, h, one_mul]

private theorem coeff_logArg_pow (d m : ℕ) :
    coeff d (logArg ^ m) =
      if m ≤ d then (1 / 2 : ℚ) ^ (d - m) * (m.choose (d - m) : ℚ) else 0 := by
  have h (k : ℕ) : coeff k ((1 + C (1 / 2) * X : PowerSeries ℚ) ^ m) =
      (1 / 2 : ℚ) ^ k * (m.choose k : ℚ) := by
    have heq : (1 + C (1 / 2) * X : PowerSeries ℚ) ^ m =
        rescale (1 / 2) (↑((1 + Polynomial.X : Polynomial ℚ) ^ m) : PowerSeries ℚ) := by
      rw [Polynomial.coe_pow, Polynomial.coe_add, Polynomial.coe_one, Polynomial.coe_X,
        map_pow, map_add, map_one, rescale_X]
    rw [heq, coeff_rescale, Polynomial.coeff_coe, Polynomial.coeff_one_add_X_pow]
  simp only [logArg, mul_pow, coeff_X_pow_mul']
  split_ifs with hle
  · exact h _
  · rfl

private theorem eulerAlpha_eq_sum (j : ℕ) :
    eulerAlpha j = (j + 1 : ℚ) * ∑ l ∈ Finset.range (j + 1),
      ((-1 : ℚ) ^ l / (l + 1)) * ((l + 1).choose (j - l) : ℚ) / 2 ^ (j - l) := by
  rw [← coeff_mk j eulerAlpha, ← derivative_log_subst, coeff_derivative,
    mul_comm _ (j + 1 : ℚ), coeff_subst' logArg_hasSubst]
  congr 1
  rw [finsum_eq_sum_of_support_subset (s := Finset.range (j + 2))]
  · rw [Finset.sum_range_succ']
    simp only [show coeff 0 (log ℚ) = 0 by simp, zero_smul, add_zero]
    apply Finset.sum_congr rfl
    intro l hl
    have hle : l + 1 ≤ j + 1 := Nat.succ_le_succ (Nat.le_of_lt_succ (Finset.mem_range.mp hl))
    rw [coeff_log, ite_eq_right (Nat.succ_ne_zero l), coeff_logArg_pow, ite_eq_left hle]
    simp only [Nat.add_sub_add_right, Nat.cast_add, Nat.cast_one,
      Algebra.algebraMap_self_apply, smul_eq_mul, pow_succ' (-1 : ℚ) (l + 1),
      pow_succ' (-1 : ℚ) l, neg_one_mul, neg_neg, one_div, inv_pow]
    ring
  · intro m hm
    by_contra hmem
    change ¬ m ∈ Finset.range (j + 2) at hmem
    have hlt : ¬ m ≤ j + 1 := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hmem
    exact hm (by simp [coeff_logArg_pow, hlt])

end Coefficients

open Polynomial

@[expose] public section

/-- **Double-sum formula for Euler polynomials.** Let $E_n(x)$ denote the Euler polynomial and
$S(n, k, x) = \frac{1}{k!} \sum_{j=0}^{k} \binom{k}{j} (-1)^{k-j} (x + j)^n$ the generalized
Stirling polynomial. For every $n \ge 0$, as polynomials in $x$ with rational coefficients,
$2^n E_n(x) = \sum_{\ell=0}^{n} \frac{(-1)^\ell}{\ell + 1}
\sum_{k=0}^{n-\ell} \frac{(k + \ell + 1)!}{2^k} \binom{\ell + 1}{k} S(n, k + \ell, 2x - 1)$.

Source: Nouara Mokhtari, Rachid Boumahdi, and Farid
Bencherif, "Generalizations of Several Explicit Formulas
for Euler Polynomials", Theorem 4.3. -/
theorem eulerPoly_eq_double_sum (n : ℕ) :
    (2 : ℚ) ^ n • eulerPoly n =
      ∑ l ∈ Finset.range (n + 1),
        ((-1) ^ l / (l + 1 : ℚ)) •
          ∑ k ∈ Finset.range (n - l + 1),
            ((Nat.factorial (k + l + 1) : ℚ) / (2 : ℚ) ^ k *
                (Nat.choose (l + 1) k : ℚ)) •
              (genStirlingPoly n (k + l)).comp (C 2 * X - 1) := by
  rcases n with _ | n
  · apply Polynomial.funext
    intro x
    norm_num [eulerPoly, genStirlingPoly, eval_smul, smul_eq_mul]
    ring
  rw [eulerPoly_eq_sum_genStirling (n + 1) (by omega)]
  let f (j : ℕ) := (genStirlingPoly (n + 1) j).comp (C 2 * X - 1)
  let g (l j : ℕ) := ((-1) ^ l / (l + 1 : ℚ)) •
    (((j + 1).factorial : ℚ) / (2 : ℚ) ^ (j - l) * ((l + 1).choose (j - l) : ℚ)) • f j
  calc
    _ = ∑ j ∈ Finset.range (n + 1 + 1), ∑ l ∈ Finset.range (j + 1), g l j := by
      apply Finset.sum_congr rfl
      intro j _
      change _ • f j = _
      rw [eulerAlpha_eq_sum, ← mul_assoc, Finset.mul_sum, Finset.sum_smul]
      apply Finset.sum_congr rfl
      intro l _
      simp only [g, smul_smul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      congr 1
      ring
    _ = ∑ l ∈ Finset.range (n + 1 + 1), ∑ j ∈ Finset.Ico l (n + 1 + 1), g l j := by
      simpa only [Nat.Ico_zero_eq_range] using
        (Finset.sum_Ico_Ico_comm 0 (n + 1 + 1) g).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro l hl
      have hlen : n + 1 + 1 - l = n + 1 - l + 1 := by
        have := Finset.mem_range.mp hl
        omega
      rw [Finset.sum_Ico_eq_sum_range, hlen, Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro k _
      simp [g, f, Nat.add_comm l k]
end

end MathlibExt.NumberTheory.EulerPolynomialFormulasWanted
