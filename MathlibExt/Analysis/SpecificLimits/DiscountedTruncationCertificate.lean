/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Algebra.InfiniteSum.NatInt
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Basic.Real.Basic
public import MathlibExt.Analysis.SpecificLimits.DiscountedSum

/-!
# Certified discounted-truncation examples

Two concrete, exact-rational error certificates for discounted finite
truncations (Atlas roadmap M15.T03, certified numerical examples only).
Both are stated with the canonical `MathlibExt.DiscountedSum.discountedValue`
and `MathlibExt.DiscountedSum.truncatedValue`, unfolded only in the proofs.
They are instances of the general discounted-truncation bound (M11.T03 /
`MathlibExt.DiscountedSum.abs_discountedValue_sub_truncatedValue_le`), not a
restatement of it: each certificate is an equality giving the exact tail value.

## Main results

* `discounted_truncation_certificate_half_five`
* `discounted_truncation_certificate_third_three`
(names in the `MathlibExt.Analysis.SpecificLimits.DiscountedTruncationCertificate`
namespace)
-/

@[expose] public section

namespace MathlibExt.Analysis.SpecificLimits.DiscountedTruncationCertificate

open MathlibExt.DiscountedSum

/-- Certified numerical example (Atlas roadmap M15.T03): for discount factor
`β = 1/2`, constant reward `1`, and truncation `T = 5`, the truncation error is
exactly `(1/2)^5 / (1 - 1/2) = 1/16`. This is a concrete instance of the general
discounted-truncation bound (M11.T03 / `MathlibExt.DiscountedSum`), not a
restatement of it. -/
theorem discounted_truncation_certificate_half_five :
    |discountedValue (1 / 2) (fun _ => 1) - truncatedValue (1 / 2) (fun _ => 1) 5| = 1 / 16 := by
  unfold discountedValue truncatedValue
  have h0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have h1 : (1 / 2 : ℝ) < 1 := by norm_num
  have hgeo : ∑' n : ℕ, (1 / 2 : ℝ) ^ n = (1 - 1 / 2)⁻¹ :=
    tsum_geometric_of_lt_one h0 h1
  have hfin : ∑ t ∈ Finset.range 5, (1 / 2 : ℝ) ^ t = 31 / 16 := by
    norm_num [Finset.sum_range_succ]
  simp only [mul_one]
  rw [hgeo, hfin]
  norm_num

/-- Certified numerical example (Atlas roadmap M15.T03): for discount factor
`β = 1/3`, constant reward `2`, and truncation `T = 3`, the truncation error is
exactly `2 * (1/3)^3 / (1 - 1/3) = 1/9`. -/
theorem discounted_truncation_certificate_third_three :
    |discountedValue (1 / 3) (fun _ => 2) - truncatedValue (1 / 3) (fun _ => 2) 3| = 1 / 9 := by
  unfold discountedValue truncatedValue
  have h0 : (0 : ℝ) ≤ 1 / 3 := by norm_num
  have h1 : (1 / 3 : ℝ) < 1 := by norm_num
  have hgeo : ∑' n : ℕ, (1 / 3 : ℝ) ^ n = (1 - 1 / 3)⁻¹ :=
    tsum_geometric_of_lt_one h0 h1
  have htsum : ∑' t, (1 / 3 : ℝ) ^ t * 2 = (1 - 1 / 3)⁻¹ * 2 := by
    rw [tsum_mul_right, hgeo]
  have hfin : ∑ t ∈ Finset.range 3, (1 / 3 : ℝ) ^ t * 2 = 26 / 9 := by
    norm_num [Finset.sum_range_succ]
  rw [htsum, hfin]
  norm_num

end MathlibExt.Analysis.SpecificLimits.DiscountedTruncationCertificate
