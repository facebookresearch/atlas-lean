/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Set.Inclusion

/-!
# Rankin's bound for smooth reciprocal tails

For a positive exponent, the series of negative powers of smooth numbers converges: adjoining
one prime to the cutoff adds a geometric factor. Comparing the reciprocal terms beyond `x`
with `x ^ (-s)` times the negative powers at exponent `1 - s` then gives Rankin's bound.
-/

namespace MetaMathlibExt

private theorem summable_rpow_neg_smoothNumbers (N : ℕ) {a : ℝ} (ha : 0 < a) :
    Summable (fun n : Nat.smoothNumbers N ↦ (n : ℝ) ^ (-a)) := by
  induction N with
  | zero =>
      rw [Nat.smoothNumbers_zero]
      exact Summable.of_finite
  | succ p ih =>
      by_cases hp : p.Prime
      · have hp₁ : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
        have hratio : 0 ≤ (p : ℝ) ^ (-a) := Real.rpow_nonneg (Nat.cast_nonneg _) _
        have hgeom : Summable (fun e : ℕ ↦ ((p : ℝ) ^ (-a)) ^ e) :=
          summable_geometric_of_lt_one hratio
            (Real.rpow_lt_one_of_one_lt_of_neg hp₁ (neg_lt_zero.mpr ha))
        have hprod := hgeom.mul_of_nonneg ih (fun e ↦ pow_nonneg hratio e)
          (fun n ↦ Real.rpow_nonneg (Nat.cast_nonneg (n : ℕ)) _)
        refine (Nat.equivProdNatSmoothNumbers hp).summable_iff.mp (hprod.congr fun z ↦ ?_)
        simp only [Function.comp_apply, Nat.equivProdNatSmoothNumbers_apply', Nat.cast_mul,
          Nat.cast_pow, Real.mul_rpow (pow_nonneg (Nat.cast_nonneg p) _) (Nat.cast_nonneg _)]
        rw [← Real.rpow_natCast_mul (Nat.cast_nonneg p), mul_comm (z.1 : ℝ) (-a),
          Real.rpow_mul_natCast (Nat.cast_nonneg p)]
      · rwa [Nat.smoothNumbers_succ hp]

/-- **Rankin's bound for reciprocal sums of smooth numbers.** Let $x, y, s$ be real numbers with
$2 \le y < x$ and $0 < s < 1$. Call a positive integer $y$-smooth if all its prime factors are
at most $y$ (so $1$ is $y$-smooth). Let $S(x, y)$ be the sum of $1/n$ over the $y$-smooth
integers $n > x$, and let $\zeta(\sigma, y)$ be the sum of $n^{-\sigma}$ over all $y$-smooth
integers $n$. Then $S(x, y) \le x^{-s} \zeta(1 - s, y)$.

Both sums are unconditional sums of real numbers, which take the value $0$ for a family that is
not summable; the statement asserts only the inequality between these values, not that the
series converge.

Source: Nguyen and Pomerance, *The Reciprocal Sum of the Amicable Numbers*, Mathematics of
Computation 88 (2019), no. 317, 1503–1526, Lemma 2.9 (first inequality)
(<https://doi.org/10.1090/mcom/3362>). Also stated in Cheng, Kinlaw and Nguyen, *The Reciprocal
Sum of Even Pseudoprimes*, Journal of Integer Sequences 29 (2026), Article 26.1.3, Lemma 8,
display (smooth1) (`jis-2026-26.1.3-lem-8`). -/
public theorem smoothReciprocalTail_le_rpow_mul_smoothZeta {x y s : ℝ} (hy : 2 ≤ y)
    (hyx : y < x) (hs0 : 0 < s) (hs1 : s < 1) :
    ∑' n : {n : ℕ // n ∈ Nat.smoothNumbers (⌊y⌋₊ + 1) ∧ x < n}, (1 : ℝ) / n ≤
      x ^ (-s) * ∑' n : Nat.smoothNumbers (⌊y⌋₊ + 1), (n : ℝ) ^ (-(1 - s)) := by
  have hx : 0 < x := (zero_lt_two.trans_le hy).trans hyx
  let tail : Set ℕ := {n | n ∈ Nat.smoothNumbers (⌊y⌋₊ + 1) ∧ x < n}
  let hsub : tail ⊆ Nat.smoothNumbers (⌊y⌋₊ + 1) := fun _ hn ↦ hn.1
  let includeTail := Set.inclusion hsub
  have hinj := Set.inclusion_injective hsub
  have hzeta := summable_rpow_neg_smoothNumbers (⌊y⌋₊ + 1) (sub_pos.mpr hs1)
  have hscaled := hzeta.mul_left (x ^ (-s))
  have hterm (n : tail) : (1 : ℝ) / n ≤ x ^ (-s) * (includeTail n : ℝ) ^ (-(1 - s)) := by
    have hn : x < (n : ℝ) := n.property.2
    calc
      (1 : ℝ) / n = (n : ℝ) ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, one_div]
      _ = (n : ℝ) ^ (-s) * (n : ℝ) ^ (-(1 - s)) := by
        rw [← Real.rpow_add (hx.trans hn), ← neg_add, add_comm s, sub_add_cancel]
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow_of_nonpos hx hn.le (neg_nonpos.mpr hs0.le))
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have htail := (hscaled.comp_injective hinj).of_nonneg_of_le
    (fun n : tail ↦ one_div_nonneg.mpr (Nat.cast_nonneg (n : ℕ))) hterm
  rw [← hzeta.tsum_mul_left]
  exact Summable.tsum_le_tsum_of_inj includeTail hinj
    (fun n _ ↦ mul_nonneg (Real.rpow_nonneg hx.le _) (Real.rpow_nonneg (Nat.cast_nonneg (n : ℕ)) _))
    hterm htail hscaled

end MetaMathlibExt
