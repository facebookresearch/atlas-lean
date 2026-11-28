/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Polynomial.OfFn
import MathlibExt.Combinatorics.Sequences.LogConcaveProducts

/-!
# Log-concavity of ordinary convolutions

The ordinary convolution of two positive real sequences that are log-concave at every index
`j ≥ 1` is also log-concave at every `j ≥ 1`. For a fixed `j`, truncate both sequences through
`j + 1`. The three relevant convolution sums are coefficients of the product of these two
polynomials, to which the finite log-concavity theorem applies.

## References

* Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino,
  *A Note on Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, pp. 1–18, Lemma 3.
* Moussa Ahmia and Hacène Belbachir, *The Log-concavity Property Associated to Hyperjacobsthal
  and Hyperjacobsthal-Lucas Sequences*, Turkish Journal of Analysis and Number Theory 6 (2018),
  no. 3, pp. 107–110, Lemma 3.1, as cited by Spreafico and Catarino.
* D. W. Walkup, *Pólya sequences, binomial convolution and the union of random sets*,
  Journal of Applied Probability 13 (1976), no. 1, pp. 76–85, for the convolution background
  cited by Ahmia and Belbachir.
* `MathlibExt.Combinatorics.Sequences.LogConcaveProducts`, `logConcave_mul`, for the formalized
  finite polynomial result used here.
-/

open Polynomial MathlibExt.Combinatorics.Sequences.Unimodal
open MathlibExt.Combinatorics.Sequences.UnimodalProductsWanted (logConcave_mul)

namespace MetaMathlibExt

/-- **The convolution of log-concave sequences is log-concave.** Let $(x_n)_{n \ge 0}$ and
$(y_n)_{n \ge 0}$ be sequences of positive real numbers that are log-concave, that is,
$x_{j-1} x_{j+1} \le x_j^2$ and $y_{j-1} y_{j+1} \le y_j^2$ for every $j \ge 1$. Let
$z_n = \sum_{k=0}^{n} x_k y_{n-k}$ be their convolution. Then $z_{j-1} z_{j+1} \le z_j^2$ for
every $j \ge 1$.

Positivity is the paper's standing assumption on log-concave sequences.

Source: Elen Viviani Pereira Spreafico and Paula Maria Machado Cruz Catarino, *A Note on
Hyper-Leonardo Numbers*, INTEGERS 26 (2026), Article A48, Lemma 3, quoting [1]
(`integers-2026-A48-lem-3`). -/
public theorem logConcave_convolution (x y : ℕ → ℝ) (hx : ∀ n, 0 < x n)
    (hy : ∀ n, 0 < y n) (hxlc : ∀ j, 1 ≤ j → x (j - 1) * x (j + 1) ≤ x j ^ 2)
    (hylc : ∀ j, 1 ≤ j → y (j - 1) * y (j + 1) ≤ y j ^ 2) (j : ℕ) (hj : 1 ≤ j) :
    (∑ k ∈ Finset.range j, x k * y (j - 1 - k)) *
        (∑ k ∈ Finset.range (j + 2), x k * y (j + 1 - k)) ≤
      (∑ k ∈ Finset.range (j + 1), x k * y (j - k)) ^ 2 := by
  classical
  let P (a : ℕ → ℝ) : ℝ[X] := ofFn (j + 2) (fun i => a i)
  have hcoeff (a : ℕ → ℝ) (k : ℕ) (hk : k < j + 2) : (P a).coeff k = a k :=
    ofFn_coeff_eq_val_of_lt _ hk
  have hproperties (a : ℕ → ℝ) (ha : ∀ n, 0 < a n)
      (hlc : ∀ k, 1 ≤ k → a (k - 1) * a (k + 1) ≤ a k ^ 2) :
      (∀ k, 0 ≤ (P a).coeff k) ∧ IsLogConcave (P a).coeff (P a).natDegree ∧
        NoInternalZeros (P a).coeff (P a).natDegree := by
    have hd : (P a).natDegree < j + 2 := ofFn_natDegree_lt (by omega) _
    refine ⟨fun k => ?_, isLogConcave_iff_mul_le_sq.mpr ?_, NoInternalZeros.of_pos ?_⟩
    · by_cases hk : k < j + 2
      · rw [hcoeff a k hk]
        exact (ha k).le
      · rw [ofFn_coeff_eq_zero_of_ge _ (Nat.le_of_not_gt hk)]
    · intro k hk hkd
      simpa only [hcoeff a (k - 1) (by omega), hcoeff a (k + 1) (by omega),
        hcoeff a k (by omega)] using hlc k hk
    · intro k hk
      rw [hcoeff a k (hk.trans_lt hd)]
      exact ha k
  obtain ⟨hxnn, hxlc', hxnz⟩ := hproperties x hx hxlc
  obtain ⟨hynn, hylc', hynz⟩ := hproperties y hy hylc
  have hconv (n : ℕ) (hn : n < j + 2) :
      (P x * P y).coeff n = ∑ k ∈ Finset.range (n + 1), x k * y (n - k) := by
    rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun i k => (P x).coeff i * (P y).coeff k) n]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
    rw [hcoeff x k (hkn.trans_lt hn), hcoeff y (n - k) ((Nat.sub_le n k).trans_lt hn)]
  have hdeg : j < (P x * P y).natDegree := by
    have hpos : 0 < (P x * P y).coeff (j + 1) := by
      rw [hconv (j + 1) (Nat.lt_succ_self _)]
      exact Finset.sum_pos (fun k _ => mul_pos (hx k) (hy _)) Finset.nonempty_range_add_one
    exact le_natDegree_of_ne_zero hpos.ne'
  have h := isLogConcave_iff_mul_le_sq.mp (logConcave_mul hxnn hynn hxlc' hylc' hxnz hynz).2.1
    j hj hdeg
  simpa only [hconv (j - 1) (by omega), hconv j (by omega), hconv (j + 1) (Nat.lt_succ_self _),
    Nat.sub_add_cancel hj] using h

end MetaMathlibExt
