/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fintype.Powerset
public import MathlibExt.Probability.Distributions.Hypergeometric

import Mathlib.Data.Nat.Choose.Vandermonde
import MathlibExt.Data.Finset.PowersetCardOverlap

/-!
# Chapman's capture–recapture estimator

Fix a marked set $A \subseteq \operatorname{Fin}(N)$ with $|A|=n_1$ and choose a second sample
uniformly among all subsets of size $n_2 \le N$. The number of marked individuals in that sample
has the hypergeometric mass at every $k \in \mathbb{N}$. For $k \le n_2$, count the subsets by
choosing their marked and unmarked parts independently. For $k>n_2$ the event is empty;
the unguarded binomial quotient with truncated natural subtraction can be nonzero in this range.
The count includes empty populations and samples under the same conventions.

For $n_1 \le N$ and $n_2 \le N$, the exact expectation of Chapman's estimator is obtained by
shifting the binomial convolution for the hypergeometric mass function and subtracting the term at
index zero.

## References

* D. G. Chapman, *Some properties of the hypergeometric distribution with applications to zoological
  sample censuses*, University of California Publications in Statistics 1, no. 7 (1951), 131–160,
  for the capture–recapture setting and estimator.
* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. I, 3rd ed.,
  John Wiley & Sons (1968), §II.6, pp. 43–45, equation (6.1) and example (c), for the recapture law
  and its counting argument. Feller's convention that binomial coefficients with negative lower
  indices vanish corresponds here to explicitly assigning mass zero for $k>n_2$.
-/

@[expose] public section

namespace WantedExt.Biology.Ecology.CaptureRecaptureWanted

open Finset ProbabilityTheory

/-- **The recapture count is hypergeometric.** Let a population `Fin N` contain a
marked set `A` of size `n₁`, and let the second sample be a uniformly random subset of size
`n₂ ≤ N`. For every `k : ℕ`, the proportion of `n₂`-subsets `S` with `#(S ∩ A) = k` equals
`hypergeometricReal N n₁ n₂ k`, which is `C(n₁, k) C(N - n₁, n₂ - k) / C(N, n₂)` for `k ≤ n₂` and
`0` for `k > n₂` (note that for `k > n₂`, natural-number subtraction would make the unguarded
binomial quotient nonzero, whereas `hypergeometricReal` is zero outside `k ≤ n₂`).

Sources: D. G. Chapman, "Some properties of the hypergeometric distribution with applications to
zoological sample censuses", Univ. California Publ. Statist. 1 (1951) 131–160. -/
public theorem card_filter_inter_eq {N n₁ n₂ : ℕ} (A : Finset (Fin N)) (hA : A.card = n₁)
    (hn₂ : n₂ ≤ N) (k : ℕ) :
    (((Finset.univ : Finset (Fin N)).powersetCard n₂).filter fun S => (S ∩ A).card = k).card /
        (N.choose n₂ : ℝ) = hypergeometricReal N n₁ n₂ k := by
  by_cases hk : k ≤ n₂
  · have hden : (N.choose n₂ : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hn₂).ne'
    rw [hypergeometricReal_of_le hk, div_left_inj₀ hden]
    exact_mod_cast (by
      simpa only [card_univ, Fintype.card_fin, hA] using
        card_filter_powersetCard_inter_eq_choose (subset_univ A) hk)
  · have hlt := Nat.lt_of_not_ge hk
    have hEmpty : ((univ : Finset (Fin N)).powersetCard n₂).filter
        (fun S => (S ∩ A).card = k) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro S hS
      rw [mem_filter, mem_powersetCard] at hS
      have hle : (S ∩ A).card ≤ S.card := card_le_card inter_subset_left
      rw [hS.2, hS.1.2] at hle
      exact hk hle
    simp only [hEmpty, card_empty, Nat.cast_zero, zero_div, hypergeometricReal_of_lt hlt]

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
          rw [hypergeometricReal_of_le hk']
          calc
            _ = (((n₂ : ℝ) + 1) / N.choose n₂) *
                ((((n₁ : ℝ) + 1) * n₁.choose k / ((k : ℝ) + 1)) *
                  (N - n₁).choose (n₂ - k)) := by ring
            _ = _ := by rw [hchoose]
    _ = _ := by
      rw [hscale, hshift]
      field_simp [hden']
      ring

/-- **Exact unbiasedness and strict bias of Chapman's estimate.** For
`n₁ ≤ N` and `n₂ ≤ N`, with `m` hypergeometric: if `n₁ + n₂ ≥ N` then
`E[(n₁ + 1)(n₂ + 1)/(m + 1) - 1] = N`, and if `n₁ + n₂ < N` then this expectation is strictly less
than `N`.

Sources: D. G. Chapman, "Some properties of the hypergeometric distribution with applications to
zoological sample censuses", Univ. California Publ. Statist. 1 (1951) 131–160; the closed form is
derived. -/
public theorem chapman_unbiased_iff {N n₁ n₂ : ℕ} (hn₁ : n₁ ≤ N) (hn₂ : n₂ ≤ N) :
    (N ≤ n₁ + n₂ →
        ∑ k ∈ Finset.range (n₂ + 1), hypergeometricReal N n₁ n₂ k * chapman n₁ n₂ k = N) ∧
      (n₁ + n₂ < N →
        ∑ k ∈ Finset.range (n₂ + 1), hypergeometricReal N n₁ n₂ k * chapman n₁ n₂ k < N) := by
  rw [expectation_chapman hn₁ hn₂]
  constructor
  · intro h
    rw [Nat.choose_eq_zero_of_lt (show N - n₁ < n₂ + 1 by omega)]
    simp
  · intro h
    have hnum : (0 : ℝ) < (N - n₁).choose (n₂ + 1) := by
      exact_mod_cast Nat.choose_pos (show n₂ + 1 ≤ N - n₁ by omega)
    have hden : (0 : ℝ) < (N + 1).choose (n₂ + 1) := by
      exact_mod_cast Nat.choose_pos (Nat.succ_le_succ hn₂)
    have hscale : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    exact sub_lt_self _ (div_pos (mul_pos hscale hnum) hden)

end WantedExt.Biology.Ecology.CaptureRecaptureWanted
