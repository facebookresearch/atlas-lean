/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Domains.Biology.PopulationGenetics.Diffusion.PoissonRandomField
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

/-!
# Neutral site-frequency-spectrum totals

The expected total number of segregating sites (`sum_expectedSFS_neutral`)
and the expected total pairwise diversity
(`sum_pairwiseDiversity_expectedSFS_neutral`) in the neutral infinite-sites
model, as finite sums over the segregating classes `1 ≤ i < n`.

Both statements are sums of the analytic expected spectrum
`MathlibExt.Biology.PopulationGenetics.Diffusion.expectedSFS` under the
neutral infinite-sites assumptions. They are not statements about a
constructed Poisson random field, about random site counts, or about
unbiasedness of an estimator.

These are derived totals building on the existing module's results: the
Sawyer–Hartl (1992) Poisson-random-field spectrum and its neutral case
`expectedSFS_neutral` (Fu 1995), proved in
`Domains.Biology.PopulationGenetics.Diffusion.PoissonRandomField`.

## References

* G. A. Watterson, *On the number of segregating sites in genetical models without recombination*,
  Theor. Popul. Biol. 7 (1975) 256–276.
* S. A. Sawyer and D. L. Hartl, *Population genetics of polymorphism and divergence*,
  Genetics 132 (1992) 1161–1176.
* Y.-X. Fu, *Statistical properties of segregating sites*, Theor. Popul. Biol. 48 (1995)
  172–197.
-/

@[expose] public section

namespace MathlibExt.Biology.PopulationGenetics.Diffusion

private theorem sum_range_cast (n : ℕ) :
    ∑ i ∈ Finset.range n, (i : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ _ k, ih]
    push_cast
    ring

private theorem sum_Ico_cast (n : ℕ) :
    ∑ i ∈ Finset.Ico 1 n, (i : ℝ) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rw [Finset.Ico_eq_empty_of_le (by norm_num : (0 : ℕ) ≤ 1)]
    simp
  · have h1n : 1 ≤ n := hn
    rw [Finset.sum_Ico_eq_sub _ h1n, Finset.sum_range_one, Nat.cast_zero, sub_zero,
      sum_range_cast]

private theorem sum_two_mul_sub_Ico (n : ℕ) (hn : 2 ≤ n) :
    ∑ i ∈ Finset.Ico 1 n, (2 * ((n : ℝ) - (i : ℝ))) = (n : ℝ) * ((n : ℝ) - 1) := by
  rw [← Finset.mul_sum, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
    Nat.card_Ico, Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one, sum_Ico_cast]
  ring

/-- Expected total number of segregating sites (Watterson's formula, with the
sum explicit; an expected count for `θ ≥ 0`): in the neutral infinite-sites model, the sum of
`expectedSFS θ 0 n i` over the segregating classes `1 ≤ i < n` equals `θ`
times the harmonic sum over those classes. The monomorphic class `i = n` is
excluded, matching `expectedSFS_neutral`. The class `i = 0` is also excluded: for
`θ ≠ 0` its integrand has a `θ / x` singularity and is not integrable (for `θ > 0` the model has an
infinite expected number of ancestral-monomorphic sites), while for `θ = 0` it is identically zero;
Lean assigns the value `0` to a non-integrable real integral, which is not an expectation result. -/
theorem sum_expectedSFS_neutral (θ : ℝ) (n : ℕ) :
    ∑ i ∈ Finset.Ico 1 n,
        MathlibExt.Biology.PopulationGenetics.Diffusion.expectedSFS θ 0 n i
      = θ * ∑ i ∈ Finset.Ico 1 n, (i : ℝ)⁻¹ := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mem_Ico] at hi
  have hi0 : 0 < i := by omega
  rw [MathlibExt.Biology.PopulationGenetics.Diffusion.expectedSFS_neutral θ hi0 hi.2,
    div_eq_mul_inv]

/-- Expected pairwise diversity from the neutral spectrum: each segregating
class `i` contributes its expected site count weighted by the probability
that two distinct sampled gene copies differ at a site of that class; the
total, for `n ≥ 2`, is the neutral expected pairwise diversity `θ` (an expectation for
`θ ≥ 0`). -/
theorem sum_pairwiseDiversity_expectedSFS_neutral (θ : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    ∑ i ∈ Finset.Ico 1 n,
        (2 * (i : ℝ) * ((n : ℝ) - (i : ℝ)) / ((n : ℝ) * ((n : ℝ) - 1)))
          * MathlibExt.Biology.PopulationGenetics.Diffusion.expectedSFS θ 0 n i
      = θ := by
  have hnR : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := by
    have hpos : (0 : ℝ) < (n : ℝ) := by linarith
    exact ne_of_gt hpos
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have hpos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    exact ne_of_gt hpos
  have hD : (n : ℝ) * ((n : ℝ) - 1) ≠ 0 := mul_ne_zero hn0 hn1
  have hterm : ∀ i ∈ Finset.Ico 1 n,
      (2 * (i : ℝ) * ((n : ℝ) - (i : ℝ)) / ((n : ℝ) * ((n : ℝ) - 1)))
          * MathlibExt.Biology.PopulationGenetics.Diffusion.expectedSFS θ 0 n i
        = θ * (2 * ((n : ℝ) - (i : ℝ)) / ((n : ℝ) * ((n : ℝ) - 1))) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hi0 : 0 < i := by omega
    have hiR : (i : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hi0)
    rw [MathlibExt.Biology.PopulationGenetics.Diffusion.expectedSFS_neutral θ hi0 hi.2]
    field_simp
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, ← Finset.sum_div,
    sum_two_mul_sub_Ico n hn, div_self hD, mul_one]

end MathlibExt.Biology.PopulationGenetics.Diffusion
