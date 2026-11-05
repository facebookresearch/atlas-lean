/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Combinatorics.Enumerative.Stirling
import MathlibExt.Combinatorics.Enumerative.StirlingSecondExplicit
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Tactic.Ring

/-!
# Symmetric exponential generating function for negative-index poly-Bernoulli numbers

This file proves the symmetric bivariate exponential generating function from the closed
Stirling-number formula, using the Stirling exponential generating function and absolute
convergence to rearrange the resulting triple series.
-/

@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators


private theorem pbs_pair_hasSum_abs (j : ℕ) (x y : ℝ) :
    HasSum
      (fun p : ℕ × ℕ =>
        (j.factorial : ℝ) ^ 2 *
          (Nat.stirlingSecond (p.1 + 1) (j + 1) : ℝ) *
          (Nat.stirlingSecond (p.2 + 1) (j + 1) : ℝ) *
          (|x| ^ p.1 / p.1.factorial) * (|y| ^ p.2 / p.2.factorial))
      (Real.exp |x| * Real.exp |y| *
        ((Real.exp |x| - 1) * (Real.exp |y| - 1)) ^ j) := by
  let u : ℕ → ℝ := fun n =>
    (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) * (|x| ^ n / n.factorial)
  let v : ℕ → ℝ := fun k =>
    (Nat.stirlingSecond (k + 1) (j + 1) : ℝ) * (|y| ^ k / k.factorial)
  have hx := hasSum_stirlingSecond_succ_egf j |x|
  have hy := hasSum_stirlingSecond_succ_egf j |y|
  have huv : Summable (fun p : ℕ × ℕ => u p.1 * v p.2) :=
    hx.summable.mul_of_nonneg hy.summable (fun _ => by positivity) (fun _ => by positivity)
  have hprod := hx.mul hy huv
  have hscaled := hprod.mul_left ((j.factorial : ℝ) ^ 2)
  have hlimit :
      (j.factorial : ℝ) ^ 2 *
        ((Real.exp |x| * (Real.exp |x| - 1) ^ j / j.factorial) *
          (Real.exp |y| * (Real.exp |y| - 1) ^ j / j.factorial)) =
        Real.exp |x| * Real.exp |y| *
          ((Real.exp |x| - 1) * (Real.exp |y| - 1)) ^ j := by
    rw [mul_pow]
    field_simp
  rw [← hlimit]
  exact hscaled.congr_fun fun p => by
    ring

private theorem pbs_pair_hasSum (j : ℕ) (x y : ℝ) :
    HasSum
      (fun p : ℕ × ℕ =>
        (j.factorial : ℝ) ^ 2 *
          (Nat.stirlingSecond (p.1 + 1) (j + 1) : ℝ) *
          (Nat.stirlingSecond (p.2 + 1) (j + 1) : ℝ) *
          (x ^ p.1 / p.1.factorial) * (y ^ p.2 / p.2.factorial))
      (Real.exp x * Real.exp y *
        ((Real.exp x - 1) * (Real.exp y - 1)) ^ j) := by
  let u : ℕ → ℝ := fun n =>
    (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) * (x ^ n / n.factorial)
  let v : ℕ → ℝ := fun k =>
    (Nat.stirlingSecond (k + 1) (j + 1) : ℝ) * (y ^ k / k.factorial)
  have hux : Summable fun n => ‖u n‖ := by
    apply (hasSum_stirlingSecond_succ_egf j |x|).summable.congr
    intro n
    dsimp [u]
    simp only [abs_mul, abs_div, abs_pow]
    have hs : 0 ≤ (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) := by positivity
    have hf : 0 ≤ (n.factorial : ℝ) := by positivity
    rw [abs_of_nonneg hs, abs_of_nonneg hf]
  have hvy : Summable fun k => ‖v k‖ := by
    apply (hasSum_stirlingSecond_succ_egf j |y|).summable.congr
    intro k
    dsimp [v]
    simp only [abs_mul, abs_div, abs_pow]
    have hs : 0 ≤ (Nat.stirlingSecond (k + 1) (j + 1) : ℝ) := by positivity
    have hf : 0 ≤ (k.factorial : ℝ) := by positivity
    rw [abs_of_nonneg hs, abs_of_nonneg hf]
  have hx := hasSum_stirlingSecond_succ_egf j x
  have hy := hasSum_stirlingSecond_succ_egf j y
  have huv : Summable (fun p : ℕ × ℕ => u p.1 * v p.2) :=
    summable_mul_of_summable_norm hux hvy
  have hscaled := (hx.mul hy huv).mul_left ((j.factorial : ℝ) ^ 2)
  have hlimit :
      (j.factorial : ℝ) ^ 2 *
        ((Real.exp x * (Real.exp x - 1) ^ j / j.factorial) *
          (Real.exp y * (Real.exp y - 1) ^ j / j.factorial)) =
        Real.exp x * Real.exp y *
          ((Real.exp x - 1) * (Real.exp y - 1)) ^ j := by
    rw [mul_pow]
    field_simp
  rw [← hlimit]
  exact hscaled.congr_fun fun p => by
    ring

private theorem pbs_triple_summable_abs (x y : ℝ)
    (hxy : (Real.exp |x| - 1) * (Real.exp |y| - 1) < 1) :
    Summable fun p : ℕ × (ℕ × ℕ) =>
      (p.1.factorial : ℝ) ^ 2 *
        (Nat.stirlingSecond (p.2.1 + 1) (p.1 + 1) : ℝ) *
        (Nat.stirlingSecond (p.2.2 + 1) (p.1 + 1) : ℝ) *
        (|x| ^ p.2.1 / p.2.1.factorial) *
        (|y| ^ p.2.2 / p.2.2.factorial) := by
  let r := (Real.exp |x| - 1) * (Real.exp |y| - 1)
  have hr : 0 ≤ r := by
    dsimp [r]
    exact mul_nonneg (sub_nonneg.mpr (Real.one_le_exp (abs_nonneg x)))
      (sub_nonneg.mpr (Real.one_le_exp (abs_nonneg y)))
  have habs : |r| < 1 := by simpa only [abs_of_nonneg hr] using hxy
  apply (summable_prod_of_nonneg (fun _ => by positivity)).2
  constructor
  · intro j
    exact (pbs_pair_hasSum_abs j x y).summable
  · have hgeom :=
      (summable_geometric_of_abs_lt_one habs).mul_left (Real.exp |x| * Real.exp |y|)
    apply hgeom.congr
    intro j
    exact (pbs_pair_hasSum_abs j x y).tsum_eq.symm

private theorem pbs_triple_summable (x y : ℝ)
    (hxy : (Real.exp |x| - 1) * (Real.exp |y| - 1) < 1) :
    Summable fun p : ℕ × (ℕ × ℕ) =>
      (p.1.factorial : ℝ) ^ 2 *
        (Nat.stirlingSecond (p.2.1 + 1) (p.1 + 1) : ℝ) *
        (Nat.stirlingSecond (p.2.2 + 1) (p.1 + 1) : ℝ) *
        (x ^ p.2.1 / p.2.1.factorial) *
        (y ^ p.2.2 / p.2.2.factorial) := by
  apply (pbs_triple_summable_abs x y hxy).of_norm_bounded
  intro p
  rw [Real.norm_eq_abs]
  simp only [abs_mul, abs_pow, abs_div]
  have hj : 0 ≤ (p.1.factorial : ℝ) := by positivity
  have hn : 0 ≤ (p.2.1.factorial : ℝ) := by positivity
  have hk : 0 ≤ (p.2.2.factorial : ℝ) := by positivity
  have hsn : 0 ≤ (Nat.stirlingSecond (p.2.1 + 1) (p.1 + 1) : ℝ) := by positivity
  have hsk : 0 ≤ (Nat.stirlingSecond (p.2.2 + 1) (p.1 + 1) : ℝ) := by positivity
  rw [abs_of_nonneg hj, abs_of_nonneg hn, abs_of_nonneg hk,
    abs_of_nonneg hsn, abs_of_nonneg hsk]

private theorem pbs_tsum_stirling_product (n k : ℕ) :
    (∑' j : ℕ, (j.factorial : ℝ) ^ 2 *
      (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) *
      (Nat.stirlingSecond (k + 1) (j + 1) : ℝ)) =
      ∑ j ∈ Finset.range (min n k + 1), (j.factorial : ℝ) ^ 2 *
        (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) *
        (Nat.stirlingSecond (k + 1) (j + 1) : ℝ) := by
  apply tsum_eq_sum
  intro j hj
  have hmin : min n k < j := by
    simp only [Finset.mem_range, not_lt] at hj
    omega
  rcases le_total n k with hnk | hkn
  · rw [Nat.min_eq_left hnk] at hmin
    rw [Nat.stirlingSecond_eq_zero_of_lt (by omega : n + 1 < j + 1)]
    simp
  · rw [Nat.min_eq_right hkn] at hmin
    rw [Nat.stirlingSecond_eq_zero_of_lt (by omega : k + 1 < j + 1)]
    simp

private theorem pbs_stirling_product_summable (n k : ℕ) :
    Summable fun j : ℕ => (j.factorial : ℝ) ^ 2 *
      (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) *
      (Nat.stirlingSecond (k + 1) (j + 1) : ℝ) := by
  apply summable_of_ne_finset_zero (s := Finset.range (min n k + 1))
  intro j hj
  have hmin : min n k < j := by
    simp only [Finset.mem_range, not_lt] at hj
    omega
  rcases le_total n k with hnk | hkn
  · rw [Nat.min_eq_left hnk] at hmin
    rw [Nat.stirlingSecond_eq_zero_of_lt (by omega : n + 1 < j + 1)]
    simp
  · rw [Nat.min_eq_right hkn] at hmin
    rw [Nat.stirlingSecond_eq_zero_of_lt (by omega : k + 1 < j + 1)]
    simp

private theorem pbs_ratio_abs_lt_one (x y : ℝ)
    (hxy : (Real.exp |x| - 1) * (Real.exp |y| - 1) < 1) :
    |(Real.exp x - 1) * (Real.exp y - 1)| < 1 := by
  let q := (Real.exp x - 1) * (Real.exp y - 1)
  let c := Real.exp x * Real.exp y
  have houter : Summable fun j : ℕ => c * q ^ j := by
    apply (pbs_triple_summable x y hxy).prod.congr
    intro j
    exact (pbs_pair_hasSum j x y).tsum_eq
  have hc : c ≠ 0 := by
    dsimp [c]
    positivity
  have hq : Summable fun j : ℕ => q ^ j := by
    apply (houter.mul_left c⁻¹).congr
    intro j
    simp [hc]
  exact summable_geometric_iff_norm_lt_one.mp hq

private theorem pbs_rearrange (x y : ℝ)
    (hxy : (Real.exp |x| - 1) * (Real.exp |y| - 1) < 1) :
    (∑' n : ℕ, ∑' k : ℕ,
      (∑ j ∈ Finset.range (min n k + 1),
        (j.factorial : ℝ) ^ 2 * (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) *
          (Nat.stirlingSecond (k + 1) (j + 1) : ℝ)) *
        (x ^ n / n.factorial) * (y ^ k / k.factorial)) =
      Real.exp (x + y) *
        (1 - (Real.exp x - 1) * (Real.exp y - 1))⁻¹ := by
  let F : ℕ → ℕ × ℕ → ℝ := fun j p =>
    (j.factorial : ℝ) ^ 2 *
      (Nat.stirlingSecond (p.1 + 1) (j + 1) : ℝ) *
      (Nat.stirlingSecond (p.2 + 1) (j + 1) : ℝ) *
      (x ^ p.1 / p.1.factorial) * (y ^ p.2 / p.2.factorial)
  have hF : Summable (Function.uncurry F) := pbs_triple_summable x y hxy
  have hfiber : ∀ n k : ℕ,
      (∑ j ∈ Finset.range (min n k + 1),
        (j.factorial : ℝ) ^ 2 * (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) *
          (Nat.stirlingSecond (k + 1) (j + 1) : ℝ)) *
        (x ^ n / n.factorial) * (y ^ k / k.factorial) =
        ∑' j : ℕ, F j (n, k) := by
    intro n k
    let C : ℕ → ℝ := fun j =>
      (j.factorial : ℝ) ^ 2 * (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) *
        (Nat.stirlingSecond (k + 1) (j + 1) : ℝ)
    have hC : Summable C := pbs_stirling_product_summable n k
    calc
      (∑ j ∈ Finset.range (min n k + 1),
          (j.factorial : ℝ) ^ 2 * (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) *
            (Nat.stirlingSecond (k + 1) (j + 1) : ℝ)) *
          (x ^ n / n.factorial) * (y ^ k / k.factorial) =
        (∑' j : ℕ, C j) *
          ((x ^ n / n.factorial) * (y ^ k / k.factorial)) := by
            rw [pbs_tsum_stirling_product]
            ring
      _ = ∑' j : ℕ, C j *
          ((x ^ n / n.factorial) * (y ^ k / k.factorial)) :=
        (hC.tsum_mul_right _).symm
      _ = ∑' j : ℕ, F j (n, k) := by
        apply tsum_congr
        intro j
        dsimp [C, F]
        ring
  have hleft : Summable fun p : ℕ × ℕ => ∑' j : ℕ, F j p :=
    hF.prod_symm.prod
  have hratio := pbs_ratio_abs_lt_one x y hxy
  calc
    (∑' n : ℕ, ∑' k : ℕ,
        (∑ j ∈ Finset.range (min n k + 1),
          (j.factorial : ℝ) ^ 2 * (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) *
            (Nat.stirlingSecond (k + 1) (j + 1) : ℝ)) *
          (x ^ n / n.factorial) * (y ^ k / k.factorial)) =
      ∑' n : ℕ, ∑' k : ℕ, ∑' j : ℕ, F j (n, k) := by
        apply tsum_congr
        intro n
        apply tsum_congr
        intro k
        exact hfiber n k
    _ = ∑' p : ℕ × ℕ, ∑' j : ℕ, F j p := hleft.tsum_prod.symm
    _ = ∑' j : ℕ, ∑' p : ℕ × ℕ, F j p := hF.tsum_comm
    _ = ∑' j : ℕ,
        Real.exp x * Real.exp y *
          ((Real.exp x - 1) * (Real.exp y - 1)) ^ j := by
      apply tsum_congr
      intro j
      exact (pbs_pair_hasSum j x y).tsum_eq
    _ = Real.exp x * Real.exp y *
        (1 - (Real.exp x - 1) * (Real.exp y - 1))⁻¹ :=
      ((hasSum_geometric_of_abs_lt_one hratio).mul_left
        (Real.exp x * Real.exp y)).tsum_eq
    _ = Real.exp (x + y) *
        (1 - (Real.exp x - 1) * (Real.exp y - 1))⁻¹ := by
      rw [Real.exp_add]

private theorem pbs_denominator (x y : ℝ) :
    1 - (Real.exp x - 1) * (Real.exp y - 1) =
      Real.exp x + Real.exp y - Real.exp (x + y) := by
  rw [Real.exp_add]
  ring

/--
**Generating function of negative-index poly-Bernoulli numbers.** For natural numbers $n, k$
let $B_{n,k} = \sum_{j=0}^{\min(n,k)} (j!)^2 \, S(n+1, j+1) \, S(k+1, j+1)$, where $S$ denotes
the Stirling numbers of the second kind. Then for all real numbers $x, y$ with
$(e^{|x|} - 1)(e^{|y|} - 1) < 1$,

$$\sum_{n=0}^{\infty} \left( \sum_{k=0}^{\infty} B_{n,k} \frac{x^n}{n!} \frac{y^k}{k!} \right) =
\frac{e^{x+y}}{e^x + e^y - e^{x+y}}.$$

By Kaneko's closed formula, $B_{n,k}$ is the poly-Bernoulli number $B_n^{(-k)}$ of negative
index. The condition $(e^{|x|} - 1)(e^{|y|} - 1) < 1$ is the domain of absolute convergence of
the double series (all $B_{n,k} \ge 0$). The weaker condition $|(e^x - 1)(e^y - 1)| < 1$ does
not suffice: at $x = -3$, $y = \log 1.9$ the outer series diverges.

Proves `Wanted` entry `polyBernoulli_negative_symmetric_exponential_generating_function`.

Proof: The Stirling EGF is derived from the finite-difference formula, then absolute convergence
permits a Fubini rearrangement and a geometric-series sum, following Hamahata–Masubuchi,
Theorems 2 and 4, and Kaneko's original formula.

Source: Y. Hamahata and H. Masubuchi, "Special Multi-Poly-Bernoulli Numbers,"
Journal of Integer Sequences 10 (2007), Article 07.4.1,
Theorem 4 (symmetric formula), lines 180–186,
<https://cs.uwaterloo.ca/journals/JIS/VOL10/Hamahata/hamahata3.tex>;
the closed formula identifying `B` is Theorem 2 there, lines 156–166.
Both are attributed there to M. Kaneko, "Poly-Bernoulli numbers,"
Journal de Théorie des Nombres de Bordeaux 9 (1997), 221–228.
-/
public theorem polyBernoulli_negative_symmetric_exponential_generating_function
    (B : ℕ → ℕ → ℝ)
    (hB : ∀ n k : ℕ,
      B n k = ∑ j ∈ Finset.range (min n k + 1),
        (j.factorial : ℝ) ^ 2 * Nat.stirlingSecond (n + 1) (j + 1) *
          Nat.stirlingSecond (k + 1) (j + 1))
    (x y : ℝ)
    (hxy : (Real.exp |x| - 1) * (Real.exp |y| - 1) < 1) :
    (∑' n : ℕ, ∑' k : ℕ,
      B n k * (x ^ n / n.factorial) * (y ^ k / k.factorial)) =
      Real.exp (x + y) /
        (Real.exp x + Real.exp y - Real.exp (x + y)) := by
  calc
    (∑' n : ℕ, ∑' k : ℕ,
        B n k * (x ^ n / n.factorial) * (y ^ k / k.factorial)) =
      ∑' n : ℕ, ∑' k : ℕ,
        (∑ j ∈ Finset.range (min n k + 1),
          (j.factorial : ℝ) ^ 2 * (Nat.stirlingSecond (n + 1) (j + 1) : ℝ) *
            (Nat.stirlingSecond (k + 1) (j + 1) : ℝ)) *
          (x ^ n / n.factorial) * (y ^ k / k.factorial) := by
            apply tsum_congr
            intro n
            apply tsum_congr
            intro k
            rw [hB n k]
    _ = Real.exp (x + y) *
        (1 - (Real.exp x - 1) * (Real.exp y - 1))⁻¹ :=
      pbs_rearrange x y hxy
    _ = Real.exp (x + y) /
        (Real.exp x + Real.exp y - Real.exp (x + y)) := by
      rw [div_eq_mul_inv, ← pbs_denominator]

end MetaMathlibExt
