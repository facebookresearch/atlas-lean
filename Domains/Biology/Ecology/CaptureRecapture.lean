/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.Hypergeometric

import Mathlib.Data.Nat.Choose.Vandermonde

/-!
# Chapman's capture–recapture estimator

The exact expectation is obtained by shifting the binomial convolution for the
hypergeometric mass function and subtracting the term at index zero.
-/

@[expose] public section

namespace WantedExt.Biology.Ecology.CaptureRecaptureWanted

open Finset ProbabilityTheory

/-- **Chapman's estimate.** The population-size estimate `(n₁ + 1)(n₂ + 1)/(m + 1) - 1`. -/
noncomputable def chapman (n₁ n₂ m : ℕ) : ℝ :=
  ((n₁ : ℝ) + 1) * ((n₂ : ℝ) + 1) / ((m : ℝ) + 1) - 1

/-- **Expectation of Chapman's estimate.** For `n₁ ≤ N` and `n₂ ≤ N`,
with `m` hypergeometric,
`E[(n₁ + 1)(n₂ + 1)/(m + 1) - 1] = N - (N + 1) C(N - n₁, n₂ + 1) / C(N + 1, n₂ + 1)`.

Sources: D. G. Chapman, "Some properties of the hypergeometric distribution with applications to
zoological sample censuses", Univ. California Publ. Statist. 1 (1951) 131–160; the closed form is
derived. -/
public theorem expectation_chapman {N n₁ n₂ : ℕ} (hn₁ : n₁ ≤ N) (hn₂ : n₂ ≤ N) :
    ∑ k ∈ Finset.range (n₂ + 1), hypergeometricReal N n₁ n₂ k * chapman n₁ n₂ k =
      N - (N + 1) * ((N - n₁).choose (n₂ + 1) : ℝ) / ((N + 1).choose (n₂ + 1) : ℝ) := by
  have hden : (N.choose n₂ : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos hn₂).ne'
  have hden' : ((N + 1).choose (n₂ + 1) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.succ_le_succ hn₂)).ne'
  have hscale : ((n₂ : ℝ) + 1) / N.choose n₂ = ((N : ℝ) + 1) / (N + 1).choose (n₂ + 1) := by
    rw [div_eq_div_iff hden hden', mul_comm ((n₂ : ℝ) + 1)]
    exact_mod_cast (Nat.add_one_mul_choose_eq N n₂).symm
  -- Vandermonde includes the index zero, which is absent from the shifted sum.
  have hshift :
      (∑ k ∈ range (n₂ + 1), ((n₁ + 1).choose (k + 1) : ℝ) * (N - n₁).choose (n₂ - k)) =
        ((N + 1).choose (n₂ + 1) : ℝ) - (N - n₁).choose (n₂ + 1) := by
    have h := Nat.add_choose_eq (n₁ + 1) (N - n₁) (n₂ + 1)
    rw [show n₁ + 1 + (N - n₁) = N + 1 by omega,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => (n₁ + 1).choose i * (N - n₁).choose j),
      Finset.sum_range_succ'] at h
    simp only [Nat.add_sub_add_right, Nat.choose_zero_right, one_mul, Nat.sub_zero] at h
    apply eq_sub_iff_add_eq.mpr
    exact_mod_cast h.symm
  calc
    _ = (∑ k ∈ range (n₂ + 1), hypergeometricReal N n₁ n₂ k *
        (((n₁ : ℝ) + 1) * ((n₂ : ℝ) + 1) / ((k : ℝ) + 1))) - 1 := by
          simp only [chapman, mul_sub, mul_one, Finset.sum_sub_distrib,
            sum_hypergeometricReal hn₁ hn₂]
    _ = (((n₂ : ℝ) + 1) / N.choose n₂) *
        (∑ k ∈ range (n₂ + 1), ((n₁ + 1).choose (k + 1) : ℝ) * (N - n₁).choose (n₂ - k)) - 1 := by
          rw [Finset.mul_sum]
          refine congrArg (· - 1) (Finset.sum_congr rfl fun k hk => ?_)
          have hk' : k ≤ n₂ := Nat.lt_succ_iff.mp (mem_range.mp hk)
          have hk0 : (k : ℝ) + 1 ≠ 0 := by positivity
          have hchoose : ((n₁ : ℝ) + 1) * n₁.choose k / ((k : ℝ) + 1) =
              ((n₁ + 1).choose (k + 1) : ℝ) := by
            apply (div_eq_iff hk0).2
            exact_mod_cast Nat.add_one_mul_choose_eq n₁ k
          rw [hypergeometricReal, ite_eq_left hk']
          calc
            _ = (((n₂ : ℝ) + 1) / N.choose n₂) *
                ((((n₁ : ℝ) + 1) * n₁.choose k / ((k : ℝ) + 1)) *
                  (N - n₁).choose (n₂ - k)) := by ring
            _ = _ := by rw [hchoose]
    _ = _ := by
      rw [hscale, hshift]
      field_simp [hden']
      ring

end WantedExt.Biology.Ecology.CaptureRecaptureWanted
