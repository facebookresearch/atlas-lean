/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.LinearAlgebra.Matrix.TrudiBrioschiDeterminant
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.Inverse
import Mathlib.Tactic.LinearCombination
import MathlibExt.Combinatorics.Enumerative.GeneralizedCatalanSchroeder
import MathlibExt.Combinatorics.Enumerative.ToeplitzHessenbergDetGenFun
import MathlibExt.Combinatorics.Enumerative.TrudiFussCatalan

/-!
# Toeplitz–Hessenberg determinants with Catalan entries

For superdiagonal `-1`, we evaluate the generating series for the positive sizes with odd-indexed
Catalan entries or with consecutive differences starting at `C₂ - C₁`, and the generating series
including the empty determinant with consecutive entries starting at `C₂`. For superdiagonal `1`
and size `n ≥ 1`, Trudi's formula gives two signed Catalan partial sums, corresponding to
consecutive differences starting at `C₁ - C₀` and at `C₂ - C₁`.

## References

* Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with Fuss-Catalan
  Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, pp. 1–23, Theorem 6,
  equations (12)–(16). We use Lemmas 1 and 2 and the partition sums of Corollary 9.
* Taras Goy and Mark Shattuck, *Determinants of Toeplitz–Hessenberg matrices with generalized
  Leonardo number entries*, Annales Mathematicae Silesianae 38 (2024), pp. 284–313, Lemma 2.2
  (the determinant generating function cited in the paper's Lemma 2).
* Mircea Merca, *A note on the determinant of a Toeplitz-Hessenberg matrix*, Special Matrices
  1 (2013), pp. 10–16, Theorem 1 (Trudi's formula).
* N. J. A. Sloane et al., *The On-Line Encyclopedia of Integer Sequences*, entries A066357 and
  A026674 (the generating functions used in the paper's equations (12) and (16)).
* The reduction to positive composition blocks follows `toeplitzHessenbergDet_fussCatalan` in
  `MathlibExt/Combinatorics/Enumerative/ToeplitzHessenbergDetFussCatalan.lean`.
* The Catalan equation uses `generalizedCatalanSchroeder_catalan_equation` from
  `MathlibExt/Combinatorics/Enumerative/GeneralizedCatalanSchroeder.lean`.
  The coefficient shift uses `coeff_catalanSeries_rat_sq` from
  `MathlibExt/Combinatorics/Enumerative/TrudiFussCatalan.lean`.
-/

namespace MetaMathlibExt

open PowerSeries

namespace toeplitzHessenbergDet_catalan

-- Keep only the terms of positive degree in the series of a sequence.
private noncomputable def positiveSeries (a : ℕ → ℚ) : PowerSeries ℚ :=
  mk fun n => if n = 0 then 0 else a n

private lemma positive_det_mul (a : ℕ → ℚ) (ha : a 0 = -1) :
    positiveSeries (toeplitzHessenbergDet a) * (1 - positiveSeries a) = positiveSeries a := by
  have h : positiveSeries (toeplitzHessenbergDet a) =
      positiveSeries a + positiveSeries a * positiveSeries (toeplitzHessenbergDet a) := by
    simpa [positiveSeries, ha] using toeplitzHessenbergDet_genFun a
  linear_combination h

private noncomputable abbrev cat : PowerSeries ℚ := mk fun n => (catalan n : ℚ)

-- Only positive block sizes enter the Trudi sum. The minus sign in the known sum
-- removes one power of `-1` from the determinant formula.
private lemma det_of_trudi_neg (a : ℕ → ℚ) (n : ℕ) (hn : 1 ≤ n) (s : ℚ)
    (hs : -trudiPartitionSum (-1) a n = s) :
    toeplitzHessenbergDet (fun i => if i = 0 then 1 else a i) n = (-1) ^ (n - 1) * s := by
  rw [toeplitzHessenbergDet_eq_neg_one_pow_mul_trudiPartitionSum _ (by simp)]
  have hsum : trudiPartitionSum (-1 : ℚ) (fun i => if i = 0 then 1 else a i) n =
      trudiPartitionSum (-1) a n := by
    simp only [trudiPartitionSum_eq_sum_compositions]
    refine Finset.sum_congr rfl fun c _ => congrArg (fun p => (-1 : ℚ) ^ c.length * p) ?_
    exact Finset.prod_congr rfl fun i _ => ite_eq_right (Nat.ne_of_gt (c.one_le_blocksFun i))
  have hsign : (-1 : ℚ) ^ n = (-1) ^ (n - 1) * (-1) := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  rw [hsum, hsign, mul_assoc, neg_one_mul, hs]

private lemma odd_entries :
    mk (fun m => if m % 2 = 0 ∧ 2 ≤ m then
        toeplitzHessenbergDet (fun i => if i = 0 then -1 else (catalan (2 * i - 1) : ℚ)) (m / 2)
      else 0) = X ^ 2 * cat ^ 2 * (rescale (-1 : ℚ) cat) ^ 2 := by
  let a : ℕ → ℚ := fun i => if i = 0 then -1 else (catalan (2 * i - 1) : ℚ)
  let E : PowerSeries ℚ →ₐ[ℚ] PowerSeries ℚ := expand 2 (by decide)
  have hcoeff (b : ℕ → ℚ) (m : ℕ) :
      coeff m (E (positiveSeries b)) = if m % 2 = 0 ∧ 2 ≤ m then b (m / 2) else 0 := by
    simp only [E, coeff_expand, positiveSeries, coeff_mk, Nat.dvd_iff_mod_eq_zero]
    split_ifs <;> first | rfl | omega
  let d := rescale (-1 : ℚ) cat
  let half : PowerSeries ℚ := C (1 / 2 : ℚ)
  let A : PowerSeries ℚ := half * (X * (cat - d))
  have hA : E (positiveSeries a) = A := by
    ext m
    rw [hcoeff, show A = C (1 / 2 : ℚ) * (X * (cat - d)) by rfl, coeff_C_mul]
    cases m with
    | zero => simp
    | succ m =>
      rw [coeff_succ_X_mul, map_sub, show d = rescale (-1 : ℚ) cat by rfl, coeff_rescale]
      by_cases hm : m % 2 = 0
      · have he : Even m := Nat.even_iff.mpr hm
        rw [he.neg_one_pow, ite_eq_right (by omega)]
        ring
      · have ho : Odd m := Nat.odd_iff.mpr (by omega)
        rw [ho.neg_one_pow, ite_eq_left (by omega)]
        simp only [a, ite_eq_right (show (m + 1) / 2 ≠ 0 by omega), cat, coeff_mk,
          show 2 * ((m + 1) / 2) - 1 = m by omega]
        ring
  have hdet : mk (fun m => if m % 2 = 0 ∧ 2 ≤ m then toeplitzHessenbergDet a (m / 2) else 0) =
      E (positiveSeries (toeplitzHessenbergDet a)) := by
    ext m
    rw [coeff_mk, hcoeff]
  change _ = X ^ 2 * cat ^ 2 * d ^ 2
  rw [hdet]
  have hF : E (positiveSeries (toeplitzHessenbergDet a)) * (1 - A) = A := by
    simpa only [map_mul, map_sub, map_one, hA] using
      congrArg E (positive_det_mul a (by simp [a]))
  have cat_eq : cat = 1 + X * cat ^ 2 := generalizedCatalanSchroeder_catalan_equation ℚ
  have hd : d = 1 - X * d ^ 2 := by
    simpa [d, rescale_neg_one_X, sub_eq_add_neg] using congrArg (rescale (-1 : ℚ)) cat_eq
  have hcInv : cat * (1 - X * cat) = 1 := by linear_combination cat_eq
  have hdInv : d * (1 + X * d) = 1 := by linear_combination hd
  have hhalf : 2 * half = 1 := by
    simpa only [map_mul, map_ofNat, map_one, half] using
      congrArg (C (R := ℚ)) (show (2 : ℚ) * (1 / 2) = 1 by norm_num)
  have hA' : A = half * (X ^ 2 * (cat ^ 2 + d ^ 2)) := by
    dsimp only [A]
    linear_combination half * X * (cat_eq - hd)
  -- The sum of the squares of the two Catalan inverses is `2(1 - A)`.
  have hinvSq : 2 * (1 - A) = (1 - X * cat) ^ 2 + (1 + X * d) ^ 2 := by
    dsimp only [A]
    linear_combination X * (cat_eq - hd) - X * (cat - d) * hhalf
  have hG : X ^ 2 * cat ^ 2 * d ^ 2 * (1 - A) = A := calc
    _ = half * (X ^ 2 * (cat ^ 2 * d ^ 2 * ((1 - X * cat) ^ 2 + (1 + X * d) ^ 2))) := by
      rw [← hinvSq]
      linear_combination -(X ^ 2 * cat ^ 2 * d ^ 2 * (1 - A)) * hhalf
    _ = half * (X ^ 2 * ((cat * (1 - X * cat)) ^ 2 * d ^ 2 +
        (d * (1 + X * d)) ^ 2 * cat ^ 2)) := by ring
    _ = A := by rw [hcInv, hdInv, hA']; simp [add_comm]
  have hunit : IsUnit (1 - A) := by
    rw [isUnit_iff_constantCoeff]
    simp [A]
  exact hunit.mul_right_cancel (hF.trans hG.symm)

private lemma consecutive_entries :
    mk (fun n =>
        toeplitzHessenbergDet (fun i => if i = 0 then -1 else (catalan (i + 1) : ℚ)) n) *
      (2 - cat ^ 2) = 1 := by
  let a : ℕ → ℚ := fun i => if i = 0 then -1 else (catalan (i + 1) : ℚ)
  have hA : positiveSeries a = cat ^ 2 - 1 := by
    ext n
    rw [map_sub, coeff_catalanSeries_rat_sq]
    cases n <;> simp [positiveSeries, a, coeff_one, catalan_one]
  have hFull : mk (toeplitzHessenbergDet a) = 1 + positiveSeries (toeplitzHessenbergDet a) := by
    ext n
    cases n with
    | zero =>
      simp only [coeff_mk, map_add, coeff_one, ite_true, positiveSeries, add_zero]
      rw [toeplitzHessenbergDet_eq_sum_compositions]
      have hlen (c : Composition 0) : c.length = 0 := c.length_eq_zero.mpr rfl
      simp [hlen, composition_card]
    | succ n => simp [positiveSeries, coeff_one]
  change mk (toeplitzHessenbergDet a) * (2 - cat ^ 2) = 1
  rw [hFull]
  have h := positive_det_mul a (by simp [a])
  rw [hA] at h
  linear_combination h

private lemma difference_entries :
    positiveSeries (toeplitzHessenbergDet
          (fun i => if i = 0 then -1 else (catalan (i + 1) : ℚ) - catalan i)) *
      (1 - X * cat ^ 3) = X * cat ^ 3 := by
  let a : ℕ → ℚ := fun i => if i = 0 then -1 else (catalan (i + 1) : ℚ) - catalan i
  have hA : positiveSeries a = cat ^ 2 - cat := by
    ext n
    rw [map_sub, coeff_catalanSeries_rat_sq]
    cases n <;> simp [positiveSeries, cat, a, catalan_zero, catalan_one]
  have cat_eq : cat = 1 + X * cat ^ 2 := generalizedCatalanSchroeder_catalan_equation ℚ
  have hcube : cat ^ 2 - cat = X * cat ^ 3 := by linear_combination cat * cat_eq
  rw [hcube] at hA
  simpa only [hA] using positive_det_mul a (by simp [a])

end toeplitzHessenbergDet_catalan

open toeplitzHessenbergDet_catalan

/-- **Toeplitz–Hessenberg determinants with Catalan entries.** Write $\det(a_0; a_1, \dots, a_n)$
for the determinant of the $n \times n$ Toeplitz–Hessenberg matrix whose entry in row $i$ and
column $j$ is $a_{i+1-j}$ for $j \le i + 1$ and $0$ above the superdiagonal (so $a_0$ fills the
superdiagonal and $a_1, \dots, a_n$ the first column); for $n = 0$ it is $1$. Let $C_n$ be the
$n$-th Catalan number, $C(x) = \sum_{n \ge 0} C_n x^n \in \mathbb{Q}[[x]]$, and
$K_m = C_{m+2} - C_{m+1}$ for $m \ge -1$, so that $K_{-1} = 0$. Then the following hold.
(1) $\sum_{n \ge 1} \det(-1; C_1, C_3, \dots, C_{2n-1})\, x^{2n} = x^2 C(x)^2 C(-x)^2$.
(2) $\bigl(\sum_{n \ge 0} \det(-1; C_2, \dots, C_{n+1})\, x^n\bigr) \bigl(2 - C(x)^2\bigr) = 1$.
(3) For every $n \ge 1$,
$\det(1; K_{-1}, K_0, \dots, K_{n-2}) = (-1)^{n-1} \sum_{i=1}^{n-1} C_i$.
(4) For every $n \ge 1$, $\det(1; K_0, K_1, \dots, K_{n-1}) = (-1)^{n-1} \sum_{i=0}^{n-1} C_i$.
(5) $\bigl(\sum_{n \ge 1} \det(-1; K_0, K_1, \dots, K_{n-1})\, x^n\bigr) \bigl(1 - x C(x)^3\bigr) =
x C(x)^3$.

Thus the determinants in (2) have generating function $1/(2 - C(x)^2)$ and those in (5) have
generating function $x C(x)^3/(1 - x C(x)^3)$, the generating function of OEIS A026674; the
determinants in (1) form OEIS A066357.

Source: Taras Goy and Mark Shattuck, *Determinants of Toeplitz-Hessenberg Matrices with
Fuss-Catalan Entries*, Journal of Integer Sequences 29 (2026), Article 26.1.2, Theorem 6
(`jis-2026-26.1.2-thm-6`). -/
public theorem toeplitzHessenbergDet_catalan :
    let C : PowerSeries ℚ := PowerSeries.mk fun n => (catalan n : ℚ)
    (PowerSeries.mk (fun m => if m % 2 = 0 ∧ 2 ≤ m then
        toeplitzHessenbergDet (fun i => if i = 0 then -1 else (catalan (2 * i - 1) : ℚ)) (m / 2)
      else 0) =
      PowerSeries.X ^ 2 * C ^ 2 * (PowerSeries.rescale (-1 : ℚ) C) ^ 2) ∧
    (PowerSeries.mk (fun n =>
        toeplitzHessenbergDet (fun i => if i = 0 then -1 else (catalan (i + 1) : ℚ)) n) *
      (2 - C ^ 2) = 1) ∧
    (∀ n : ℕ, 1 ≤ n →
      toeplitzHessenbergDet
          (fun i => if i = 0 then 1 else (catalan i : ℚ) - catalan (i - 1)) n =
        (-1) ^ (n - 1) * ∑ i ∈ Finset.Icc 1 (n - 1), (catalan i : ℚ)) ∧
    (∀ n : ℕ, 1 ≤ n →
      toeplitzHessenbergDet
          (fun i => if i = 0 then 1 else (catalan (i + 1) : ℚ) - catalan i) n =
        (-1) ^ (n - 1) * ∑ i ∈ Finset.range n, (catalan i : ℚ)) ∧
    PowerSeries.mk (fun n => if n = 0 then 0 else
        toeplitzHessenbergDet
          (fun i => if i = 0 then -1 else (catalan (i + 1) : ℚ) - catalan i) n) *
      (1 - PowerSeries.X * C ^ 3) = PowerSeries.X * C ^ 3 :=
  ⟨odd_entries, consecutive_entries,
    fun n hn => det_of_trudi_neg _ n hn _ (trudiPartitionSum_fussCatalan.2.1 n hn),
    fun n hn => det_of_trudi_neg _ n hn _ (trudiPartitionSum_fussCatalan.2.2.1 n hn),
    difference_entries⟩

end MetaMathlibExt
