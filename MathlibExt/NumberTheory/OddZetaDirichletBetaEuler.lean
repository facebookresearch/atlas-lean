/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.PSeriesComplex
public import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Zeta series over odd denominators

The main result is `MetaMathlibExt.hasSum_one_div_odd_pow`: for every natural
number `k ≥ 2`, the series over odd denominators `∑ n, 1 / (2 * n + 1) ^ k`
equals `(1 - 1 / 2 ^ k) * riemannZeta k`.
-/

namespace MetaMathlibExt

open scoped Topology

/-- **Zeta series over odd denominators.** Let $\zeta$ be the Riemann zeta function. For every
natural number $k \ge 2$, the series $\sum_{n \ge 0} 1/(2n+1)^k$ converges in $\mathbb{C}$ and
$$\sum_{n=0}^{\infty} \frac{1}{(2n+1)^k} = \Bigl(1 - \frac{1}{2^k}\Bigr) \zeta(k).$$

The source writes this as $\sum_{n \ge 1} 1/(2n-1)^k = (1 - 2^{-k}) \zeta(k)$ for integers
$k > 1$.

Source: Jan W. H. Swanepoel, *A Short Simple Probabilistic Proof of a Well Known Identity
and the Derivation of Related New Identities Involving the Bernoulli Numbers and the Euler
Numbers*, INTEGERS 25 (2025), Article A50, Proposition 2, Equation (11)
(`integers-2025-A50-prop-2`), citing its reference [20]. -/
public theorem hasSum_one_div_odd_pow (k : ℕ) (hk : 2 ≤ k) :
    HasSum (fun n : ℕ => 1 / (2 * (n : ℂ) + 1) ^ k) ((1 - 1 / 2 ^ k) * riemannZeta k) := by
  have hk1 : 1 < k := by omega
  have hk0 : k ≠ 0 := by omega
  have hre : (1 : ℝ) < ((k : ℂ)).re := by
    simp only [Complex.natCast_re]
    exact_mod_cast hk1
  have hsumm : Summable (fun n : ℕ => 1 / (n : ℂ) ^ k) := by
    have h : Summable (fun n : ℕ => 1 / (n : ℂ) ^ (k : ℂ)) :=
      (Complex.summable_one_div_nat_cpow (p := (k : ℂ))).mpr hre
    simpa only [Complex.cpow_natCast] using h
  have htotal0 : HasSum (fun n : ℕ => 1 / (n : ℂ) ^ k) (riemannZeta k) := by
    rw [zeta_nat_eq_tsum_of_gt_one hk1]
    exact hsumm.hasSum
  have hshift_sum : Summable (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ k) := by
    have h := hsumm.comp_injective (i := fun n : ℕ => n + 1)
      (by intro a b h; dsimp only at h; omega)
    have h2 : (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ k) =
        (fun n : ℕ => 1 / (n : ℂ) ^ k) ∘ (fun n : ℕ => n + 1) := by
      funext n
      simp [Nat.cast_add, Nat.cast_one]
    rw [h2]
    exact h
  have htotal : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ k) (riemannZeta k) := by
    have htsum : ∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ k = riemannZeta k := by
      have h0 : (1 : ℂ) / (0 : ℂ) ^ k = 0 := by simp [hk0]
      have h := hsumm.tsum_eq_zero_add
      simp only [Nat.cast_zero, h0, zero_add] at h
      have h' : (∑' n : ℕ, 1 / ((n : ℂ) + 1) ^ k) = ∑' n : ℕ, 1 / (↑(n + 1) : ℂ) ^ k := by
        apply tsum_congr
        intro n
        simp [Nat.cast_add, Nat.cast_one]
      rw [h', ← h, htotal0.tsum_eq]
    have h := hshift_sum.hasSum
    rw [htsum] at h
    exact h
  have h_even_summable : Summable (fun n : ℕ =>
      (fun m : ℕ => 1 / ((m : ℂ) + 1) ^ k) (2 * n)) := by
    have h := htotal.summable.comp_injective (i := fun n : ℕ => 2 * n)
      (by intro a b h; dsimp only at h; omega)
    exact h
  have h_odd_fun : (fun n : ℕ =>
      (fun m : ℕ => 1 / ((m : ℂ) + 1) ^ k) (2 * n + 1)) =
      fun n : ℕ => (1 / (2 : ℂ) ^ k) * (1 / ((n : ℂ) + 1) ^ k) := by
    funext n
    have hcast : ((2 * n + 1 : ℕ) : ℂ) + 1 = 2 * ((n : ℂ) + 1) := by
      push_cast
      ring
    change 1 / (((2 * n + 1 : ℕ) : ℂ) + 1) ^ k = _
    rw [hcast, mul_pow, ← one_div_mul_one_div]
  have h_odd : HasSum (fun n : ℕ =>
      (fun m : ℕ => 1 / ((m : ℂ) + 1) ^ k) (2 * n + 1))
      ((1 / (2 : ℂ) ^ k) * riemannZeta k) := by
    rw [h_odd_fun]
    exact htotal.mul_left _
  have h_even : HasSum (fun n : ℕ =>
      (fun m : ℕ => 1 / ((m : ℂ) + 1) ^ k) (2 * n))
      (∑' n : ℕ, (fun m : ℕ => 1 / ((m : ℂ) + 1) ^ k) (2 * n)) :=
    h_even_summable.hasSum
  have h_combined : HasSum (fun n : ℕ => 1 / ((n : ℂ) + 1) ^ k)
      ((∑' n : ℕ, (fun m : ℕ => 1 / ((m : ℂ) + 1) ^ k) (2 * n)) +
        (1 / (2 : ℂ) ^ k) * riemannZeta k) :=
    HasSum.even_add_odd h_even h_odd
  have huniq : riemannZeta k =
      (∑' n : ℕ, (fun m : ℕ => 1 / ((m : ℂ) + 1) ^ k) (2 * n)) +
        (1 / (2 : ℂ) ^ k) * riemannZeta k :=
    htotal.unique h_combined
  have h_even_val : (∑' n : ℕ, (fun m : ℕ => 1 / ((m : ℂ) + 1) ^ k) (2 * n)) =
      (1 - 1 / (2 : ℂ) ^ k) * riemannZeta k := by
    rw [sub_mul, one_mul]
    exact eq_sub_of_add_eq huniq.symm
  have h_target_fun : (fun n : ℕ => 1 / (2 * (n : ℂ) + 1) ^ k) =
      (fun n : ℕ => (fun m : ℕ => 1 / ((m : ℂ) + 1) ^ k) (2 * n)) := by
    funext n
    change 1 / (2 * (n : ℂ) + 1) ^ k = 1 / (((2 * n : ℕ) : ℂ) + 1) ^ k
    congr 2
    push_cast
    ring
  rw [h_even_val, ← h_target_fun] at h_even
  exact h_even

end MetaMathlibExt
