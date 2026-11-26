/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.CarlitzTypeQPolynomials

/-!
# Sums of `q`-powers times `q`-falling factorials

For real `q > 0` with `q ≠ 1`, write `[x] = (q^x - 1)/(q - 1)` (`MetaMathlibExt.qBracket`) and
`[x]_m = [x][x-1]⋯[x-m+1]` for the `q`-falling factorial. The main result,
`MetaMathlibExt.sum_qpow_mul_qFalling`, is Farhi's closed form
`∑_{i<N} q^{ir} [i]_k = (∑_{ℓ<r} q^{(r-ℓ-1)N + (ℓ+1)k} [r-1]_ℓ / [k+r]_{ℓ+1}) [N]_{k+1}`
for natural numbers `r ≥ 1`, `k` and `N`.

## Proof

Write `F(N)` for the right-hand side. Then `F(0) = 0` because `[0]_{k+1}` has the factor
`[0] = 0`, and the sum telescopes once `F(i+1) - F(i) = q^{ir} [i]_k` is known. Splitting
`[i+1]` off `[i+1]_{k+1}` and `[i-k]` off `[i]_{k+1}` reduces this to an identity between the
inner sums, which telescopes in `ℓ`: with `x = q^i` and
`D_ℓ = q^{ℓk} [r-1]_ℓ / [k+r]_ℓ · x^{r-ℓ}`, the `ℓ`-th term equals `D_ℓ - D_{ℓ+1}`, while
`D_0 = x^r` and `D_r = 0` because `[r-1]_r` has the factor `[0] = 0`.

## References

* Bakir Farhi, *q-analogues of sums of consecutive powers of natural numbers and extended Carlitz
  q-Bernoulli numbers and polynomials*, arXiv:2501.02499v1 (2025), Proposition 2.24.
-/

namespace MetaMathlibExt

open Finset

namespace sum_qpow_mul_qFalling

variable {q : ℝ}

/-- For real `q > 0` with `q ≠ 1`, the `q`-analogue `[n]` of a positive natural number `n` is
nonzero. -/
private theorem qBracket_natCast_ne_zero (hq0 : 0 < q) (hq1 : q ≠ 1) {n : ℕ} (hn : n ≠ 0) :
    qBracket q n ≠ 0 := by
  have hpow : q ^ n ≠ 1 := fun h => hq1 ((pow_eq_one_iff_of_nonneg hq0.le hn).mp h)
  rw [qBracket, Real.rpow_natCast]
  exact div_ne_zero (sub_ne_zero.mpr hpow) (sub_ne_zero.mpr hq1)

/-- The `ℓ`-th term of the closed form, evaluated at `i + 1` against `[i+1]` minus its value at
`i` against `[i-k]`, is `D_ℓ - D_{ℓ+1}`, where `D_ℓ = q^{ℓk} [r-1]_ℓ / [k+r]_ℓ · (q^i)^{r-ℓ}`. -/
private theorem term_eq (hq0 : 0 < q) (hq1 : q ≠ 1) {r k l : ℕ} (hl : l < r) (i : ℕ) :
    q ^ ((r - l - 1) * (i + 1) + (l + 1) * k) *
          (∏ j ∈ range l, qBracket q ((r : ℝ) - 1 - j)) /
          (∏ j ∈ range (l + 1), qBracket q (((k + r : ℕ) : ℝ) - j)) *
          qBracket q ((i : ℝ) + 1) -
        q ^ ((r - l - 1) * i + (l + 1) * k) * (∏ j ∈ range l, qBracket q ((r : ℝ) - 1 - j)) /
          (∏ j ∈ range (l + 1), qBracket q (((k + r : ℕ) : ℝ) - j)) *
          qBracket q ((i : ℝ) - k) =
      q ^ (l * k) * (∏ j ∈ range l, qBracket q ((r : ℝ) - 1 - j)) /
          (∏ j ∈ range l, qBracket q (((k + r : ℕ) : ℝ) - j)) * (q ^ i) ^ (r - l) -
        q ^ ((l + 1) * k) * (∏ j ∈ range (l + 1), qBracket q ((r : ℝ) - 1 - j)) /
          (∏ j ∈ range (l + 1), qBracket q (((k + r : ℕ) : ℝ) - j)) *
          (q ^ i) ^ (r - (l + 1)) := by
  obtain ⟨m, rfl⟩ : ∃ m, r = l + 1 + m := ⟨r - (l + 1), by omega⟩
  have hB : ∏ j ∈ range l, qBracket q (((k + (l + 1 + m) : ℕ) : ℝ) - j) ≠ 0 := by
    refine prod_ne_zero_iff.mpr fun j hj => ?_
    have hjl : j < l := mem_range.mp hj
    rw [← Nat.cast_sub (by omega)]
    exact qBracket_natCast_ne_zero hq0 hq1 (by omega)
  have hlast := qBracket_natCast_ne_zero hq0 hq1 (n := k + m + 1) (by omega)
  -- Split off the last factors of `[r-1]_{ℓ+1}` and `[k+r]_{ℓ+1}` and write every bracket with
  -- a natural argument as a quotient of natural powers of `q`.
  rw [prod_range_succ, prod_range_succ]
  have e1 : l + 1 + m - l - 1 = m := by omega
  have e2 : l + 1 + m - l = m + 1 := by omega
  have e3 : l + 1 + m - (l + 1) = m := by omega
  have e4 : ((l + 1 + m : ℕ) : ℝ) - 1 - (l : ℝ) = (m : ℕ) := by push_cast; ring
  have e5 : ((k + (l + 1 + m) : ℕ) : ℝ) - (l : ℝ) = (k + m + 1 : ℕ) := by push_cast; ring
  have e6 : (i : ℝ) + 1 = (i + 1 : ℕ) := by push_cast; ring
  rw [e1, e2, e3, e4, e5, e6]
  generalize (∏ j ∈ range l, qBracket q (((l + 1 + m : ℕ) : ℝ) - 1 - j)) = A
  generalize (∏ j ∈ range l, qBracket q (((k + (l + 1 + m) : ℕ) : ℝ) - j)) = B at hB ⊢
  simp only [qBracket, Real.rpow_sub hq0, Real.rpow_natCast] at hlast ⊢
  have hpow : q ^ (k + m + 1) - 1 ≠ 0 := (div_ne_zero_iff.mp hlast).1
  field_simp
  ring

end sum_qpow_mul_qFalling

open sum_qpow_mul_qFalling in
/-- **Sums of $q^{ir}$ times $q$-falling factorials.** Let $q > 0$ with $q \ne 1$, let
$[x] = (q^x - 1)/(q - 1)$, and write $[x]_m = [x][x-1]\cdots[x-m+1]$ for the $q$-falling factorial
(with $[x]_0 = 1$). Then for all natural numbers $r \ge 1$, $k$ and $N$,
$$\sum_{i=0}^{N-1} q^{ir} [i]_k = \left(\sum_{\ell=0}^{r-1}
\frac{q^{(r-\ell-1)N + (\ell+1)k} \, [r-1]_\ell}{[k+r]_{\ell+1}}\right) [N]_{k+1}.$$

Source: Bakir Farhi, *q-Analogues of Sums of Consecutive Powers of Natural Numbers and Extended
Carlitz q-Bernoulli Numbers and Polynomials*, INTEGERS 26 (2026), Article A85, Proposition 2.14
(`integers-2026-A85-prop-2-14`). -/
public theorem sum_qpow_mul_qFalling (q : ℝ) (hq0 : 0 < q) (hq1 : q ≠ 1) (r k N : ℕ)
    (hr : 0 < r) :
    ∑ i ∈ range N, q ^ (i * r) * ∏ j ∈ range k, qBracket q ((i : ℝ) - j) =
      (∑ l ∈ range r, q ^ ((r - l - 1) * N + (l + 1) * k) *
          (∏ j ∈ range l, qBracket q ((r : ℝ) - 1 - j)) /
            ∏ j ∈ range (l + 1), qBracket q (((k + r : ℕ) : ℝ) - j)) *
        ∏ j ∈ range (k + 1), qBracket q ((N : ℝ) - j) := by
  -- `F n` is the right-hand side at `N = n`; the sum telescopes against it.
  let F : ℕ → ℝ := fun n => (∑ l ∈ range r, q ^ ((r - l - 1) * n + (l + 1) * k) *
      (∏ j ∈ range l, qBracket q ((r : ℝ) - 1 - j)) /
        ∏ j ∈ range (l + 1), qBracket q (((k + r : ℕ) : ℝ) - j)) *
    ∏ j ∈ range (k + 1), qBracket q ((n : ℝ) - j)
  have hF0 : F 0 = 0 := by
    have h0 : ∏ j ∈ range (k + 1), qBracket q (((0 : ℕ) : ℝ) - j) = 0 :=
      prod_eq_zero (mem_range.mpr k.succ_pos) (by simp [qBracket_zero])
    simp only [F, h0, mul_zero]
  have hstep (i : ℕ) :
      F (i + 1) - F i = q ^ (i * r) * ∏ j ∈ range k, qBracket q ((i : ℝ) - j) := by
    have hsucc : ∏ j ∈ range (k + 1), qBracket q (((i + 1 : ℕ) : ℝ) - j) =
        (∏ j ∈ range k, qBracket q ((i : ℝ) - j)) * qBracket q ((i : ℝ) + 1) := by
      rw [prod_range_succ']
      push_cast
      simp only [add_sub_add_right_eq_sub, sub_zero]
    have hAr : ∏ j ∈ range r, qBracket q ((r : ℝ) - 1 - j) = 0 :=
      prod_eq_zero (mem_range.mpr (Nat.sub_lt hr one_pos))
        (by rw [Nat.cast_pred hr, sub_self, qBracket_zero])
    -- The inner sums telescope in `ℓ` (`term_eq`), from `D_0 = (q^i)^r` down to `D_r = 0`.
    have htel := sum_range_sub' (fun l => q ^ (l * k) *
      (∏ j ∈ range l, qBracket q ((r : ℝ) - 1 - j)) /
        (∏ j ∈ range l, qBracket q (((k + r : ℕ) : ℝ) - j)) * (q ^ i) ^ (r - l)) r
    beta_reduce at htel
    rw [← sum_congr rfl fun l hl => term_eq hq0 hq1 (mem_range.mp hl) i, sum_sub_distrib,
      ← sum_mul, ← sum_mul] at htel
    simp only [hAr, prod_range_zero, Nat.sub_zero, mul_zero, zero_div, zero_mul, sub_zero,
      div_one, mul_one, pow_zero, one_mul] at htel
    simp only [F]
    rw [hsucc, prod_range_succ (fun j : ℕ => qBracket q ((i : ℝ) - j)) k, pow_mul]
    linear_combination (∏ j ∈ range k, qBracket q ((i : ℝ) - j)) * htel
  change _ = F N
  rw [← sub_zero (F N), ← hF0, ← sum_range_sub F N]
  exact sum_congr rfl fun i _ => (hstep i).symm

end MetaMathlibExt
