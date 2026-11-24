/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-!
# Asymptotic expansion of a perturbed tail product

The tail product of small geometric perturbations of one equals its linear approximation
up to the error estimated by `tprod_one_sub_inv_add_eq_one_sub_tsum_add_isBigO`.
-/

open Filter Asymptotics
open scoped Topology

namespace MetaMathlibExt

-- After adding a factor, the new error is the old error plus the increment times
-- the deviation of the old product from one.
private lemma abs_prod_sub_one_sub_sum_le_sq (u : ℕ → ℝ) (s : Finset ℕ)
    (hs : ∑ i ∈ s, |u i| ≤ 1) :
    |∏ i ∈ s, (1 + u i) - 1 - ∑ i ∈ s, u i| ≤ (∑ i ∈ s, |u i|) ^ 2 := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi] at hs
    rw [Finset.prod_insert hi, Finset.sum_insert hi, Finset.sum_insert hi]
    let S := ∑ j ∈ s, |u j|
    let L := ∑ j ∈ s, u j
    let P := ∏ j ∈ s, (1 + u j)
    have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ ↦ abs_nonneg _
    have hS₁ : S ≤ 1 := by change |u i| + S ≤ 1 at hs; linarith [abs_nonneg (u i)]
    have hR : |P - 1 - L| ≤ S ^ 2 := ih hS₁
    have hL : |L| ≤ S := Finset.abs_sum_le_sum_abs _ _
    have hP : |P - 1| ≤ 2 * S := calc
      |P - 1| = |(P - 1 - L) + L| := by ring_nf
      _ ≤ |P - 1 - L| + |L| := abs_add_le _ _
      _ ≤ 2 * S := by nlinarith [mul_nonneg hS (sub_nonneg.mpr hS₁)]
    change |(1 + u i) * P - 1 - (u i + L)| ≤ (|u i| + S) ^ 2
    calc
      _ = |(P - 1 - L) + u i * (P - 1)| := by ring_nf
      _ ≤ |P - 1 - L| + |u i| * |P - 1| := by rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ S ^ 2 + |u i| * (2 * S) :=
        add_le_add hR (mul_le_mul_of_nonneg_left hP (abs_nonneg _))
      _ ≤ _ := by nlinarith [sq_nonneg |u i|]

private lemma abs_tprod_sub_one_sub_tsum_le_sq {u : ℕ → ℝ} (hu : Summable u)
    (hsmall : ∑' i, |u i| ≤ 1) :
    |∏' i, (1 + u i) - 1 - ∑' i, u i| ≤ (∑' i, |u i|) ^ 2 := by
  have hp := (Real.multipliable_one_add_of_summable hu).hasProd.tendsto_prod_nat
  apply le_of_tendsto' ((hp.sub_const 1).sub hu.hasSum.tendsto_sum_nat).abs
  intro m
  have hs := hu.abs.sum_le_tsum (Finset.range m) (fun i _ ↦ abs_nonneg (u i))
  exact (abs_prod_sub_one_sub_sum_le_sq u _ (hs.trans hsmall)).trans
    (pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _) hs 2)

-- Sum the geometric majorant from the start of the tail.
private lemma geometric_tail_bound {f : ℕ → ℝ} {C r : ℝ} {n : ℕ} (hr : 0 ≤ r)
    (hr₁ : r < 1) (hf : ∀ k : ℕ, |f k| ≤ C * r ^ (n + k)) :
    Summable f ∧ ∑' k, |f k| ≤ C / (1 - r) * r ^ n := by
  have hgeom := (hasSum_geometric_of_lt_one hr hr₁).mul_left (C * r ^ n)
  have hb (k : ℕ) : |f k| ≤ C * r ^ n * r ^ k := by simpa [pow_add, mul_assoc] using hf k
  have hsum := hgeom.summable.of_nonneg_of_le (fun k ↦ abs_nonneg (f k)) hb
  refine ⟨hsum.of_abs, (hsum.tsum_le_tsum hb hgeom.summable).trans_eq ?_⟩
  rw [hgeom.tsum_eq]
  ring

private lemma perturbed_geometric_product (a : ℝ) {p q : ℝ} (hp : 0 ≤ p) (hp₁ : p < 1)
    (hpq : p ^ 2 ≤ q) (hqp : q ≤ p) {e : ℕ → ℝ} (he : e =O[atTop] fun k : ℕ ↦ q ^ k) :
    (fun n : ℕ ↦ (∏' k : ℕ, (1 - a * p ^ (n + k) + e (n + k))) -
      (1 - ∑' k : ℕ, a * p ^ (n + k))) =O[atTop] fun n : ℕ ↦ q ^ n := by
  have hq := (sq_nonneg p).trans hpq
  obtain ⟨C, hC, hbound⟩ := isBigO_iff'.mp he
  obtain ⟨N, hN⟩ := eventually_atTop.1 hbound
  have he' (k : ℕ) (hk : N ≤ k) : |e k| ≤ C * q ^ k := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq k)] using hN k hk
  let u k := e k - a * p ^ k
  have hu' (k : ℕ) (hk : N ≤ k) : |u k| ≤ (C + |a|) * p ^ k := calc
    |u k| ≤ |e k| + |a * p ^ k| := abs_sub _ _
    _ ≤ C * p ^ k + |a| * p ^ k := by
      rw [abs_mul, abs_of_nonneg (pow_nonneg hp _)]
      exact add_le_add_left ((he' k hk).trans
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq hqp k) hC.le)) _
    _ = _ := (add_mul ..).symm
  let B := (C + |a|) / (1 - p)
  have hlim : Tendsto (fun n : ℕ ↦ B * p ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hp hp₁).const_mul B
  apply IsBigO.of_bound (B ^ 2 + C / (1 - q))
  filter_upwards [eventually_ge_atTop N, hlim.eventually_le_const zero_lt_one] with n hn hsmall
  obtain ⟨heu, hEtail⟩ := geometric_tail_bound hq (hqp.trans_lt hp₁)
    (fun k ↦ he' (n + k) (hn.trans (Nat.le_add_right ..)))
  obtain ⟨hu, hUtail⟩ := geometric_tail_bound hp hp₁
    (fun k ↦ hu' (n + k) (hn.trans (Nat.le_add_right ..)))
  change ∑' k, |u (n + k)| ≤ B * p ^ n at hUtail
  have hquad := abs_tprod_sub_one_sub_tsum_le_sq hu (hUtail.trans hsmall)
  have hpow : (B * p ^ n) ^ 2 ≤ B ^ 2 * q ^ n := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm, pow_mul]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg p) hpq n) (sq_nonneg _)
  have hR : |(∏' k, (1 + u (n + k))) - 1 - ∑' k, u (n + k)| ≤ B ^ 2 * q ^ n :=
    hquad.trans ((pow_le_pow_left₀ (tsum_nonneg fun _ ↦ abs_nonneg _) hUtail 2).trans hpow)
  have hE : |∑' k, e (n + k)| ≤ C / (1 - q) * q ^ n :=
    (norm_tsum_le_tsum_norm heu.norm).trans hEtail
  have hprod (k : ℕ) : 1 - a * p ^ (n + k) + e (n + k) = 1 + u (n + k) := by
    dsimp [u]
    ring
  have hsum : (∑' k, a * p ^ (n + k)) = (∑' k, e (n + k)) - ∑' k, u (n + k) := by
    rw [← heu.tsum_sub hu]
    simp [u]
  simp only [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq n), hprod, hsum]
  calc
    _ = |((∏' k, (1 + u (n + k))) - 1 - ∑' k, u (n + k)) + ∑' k, e (n + k)| := by ring_nf
    _ ≤ B ^ 2 * q ^ n + C / (1 - q) * q ^ n := (abs_add_le _ _).trans (add_le_add hR hE)
    _ = _ := (add_mul ..).symm

/-- **Asymptotic expansion of a perturbed tail product.** Let $\mu$ and $\lambda$ be real numbers
with $1 < \mu < \lambda$, let $c \ne 0$ be a real number, and let $(e_k)_{k \ge 0}$ be a real
sequence with $e_k = O\bigl((\mu/\lambda^3)^{k/2}\bigr)$ as $k \to \infty$. Then, as
$n \to \infty$,
$\prod_{k \ge n} \bigl(1 - 1/(c\lambda^k) + e_k\bigr) = 1 - \sum_{k \ge n} 1/(c\lambda^k) +
O\bigl((\mu/\lambda^3)^{n/2}\bigr)$.

Source: Tingting Du, *On the Reciprocal Sums and Products of m th-order Linear Recursive
Sequences*, Journal of Integer Sequences 27 (2024), Article 24.2.3, Lemma 7
(`jis-2024-24.2.3-lem-7`). -/
public theorem tprod_one_sub_inv_add_eq_one_sub_tsum_add_isBigO
    (c α μ : ℝ) (hc : c ≠ 0) (hμ : 1 < μ) (hμα : μ < α) (e : ℕ → ℝ)
    (he : e =O[atTop] fun k : ℕ => (μ / α ^ 3) ^ ((k : ℝ) / 2)) :
    (fun n : ℕ => (∏' k : ℕ, (1 - 1 / (c * α ^ (n + k)) + e (n + k))) -
        (1 - ∑' k : ℕ, 1 / (c * α ^ (n + k)))) =O[atTop]
      fun n : ℕ => (μ / α ^ 3) ^ ((n : ℝ) / 2) := by
  have hα₁ := hμ.trans hμα
  have hα := zero_lt_one.trans hα₁
  have hbase : 0 ≤ μ / α ^ 3 := by positivity
  let q := Real.sqrt (μ / α ^ 3)
  have hrate (k : ℕ) : (μ / α ^ 3) ^ ((k : ℝ) / 2) = q ^ k := by
    rw [show (k : ℝ) / 2 = (1 / 2 : ℝ) * k by ring, Real.rpow_mul_natCast hbase,
      ← Real.sqrt_eq_rpow]
  have hrecip (k : ℕ) : 1 / (c * α ^ k) = c⁻¹ * (α⁻¹) ^ k := by
    rw [inv_pow]
    field_simp
  have hqp : q ≤ α⁻¹ := by
    apply (Real.sqrt_le_left (inv_nonneg.mpr hα.le)).2
    field_simp
    exact hμα.le
  have hpq : (α⁻¹) ^ 2 ≤ q := by
    apply (Real.le_sqrt (sq_nonneg _) hbase).2
    field_simp
    exact one_le_mul_of_one_le_of_one_le hα₁.le hμ.le
  simp_rw [hrate] at he ⊢
  simp_rw [hrecip]
  exact perturbed_geometric_product _ (inv_nonneg.mpr hα.le) (inv_lt_one_of_one_lt₀ hα₁)
    hpq hqp he

end MetaMathlibExt
