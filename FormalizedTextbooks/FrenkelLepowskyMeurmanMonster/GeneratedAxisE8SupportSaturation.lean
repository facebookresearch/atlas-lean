/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8Saturation

/-! Restricting an extremal short convolution to its actual nonzero support. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- A maximal convolution of unit signs determines each supported product separately.
The cardinality hypothesis counts genuine ordered supported edges. -/
theorem generatedAxisE8_supported_convolution_saturated {ι : Type*} [Fintype ι]
    (support : ι → Prop) (edge : ι → ι → Prop)
    [DecidablePred support] [DecidableRel edge] (e : ι → ι → ℝ)
    (x : ι → ℝ) (t : ℝ) (n : ℕ)
    (he : ∀ r s, e r s ^ 2 = 1)
    (hx : ∀ r, support r → x r ^ 2 = 1)
    (hz : ∀ r, ¬ support r → x r = 0) (ht : t ^ 2 = 1)
    (hc : (Finset.univ.filter fun rs : ι × ι =>
      support rs.1 ∧ support rs.2 ∧ edge rs.1 rs.2).card = n)
    (hs : (∑ r, ∑ s, if edge r s then e r s * x r * x s else 0) = (n : ℝ) * t)
    (r s : ι) (hr : support r) (hsupport : support s) (hedge : edge r s) :
    e r s * x r * x s = t := by
  classical
  let pairs := Finset.univ.filter fun rs : ι × ι =>
    support rs.1 ∧ support rs.2 ∧ edge rs.1 rs.2
  have hmem : (r, s) ∈ pairs := by simp [pairs, hr, hsupport, hedge]
  have hrestrict : (∑ rs ∈ pairs, e rs.1 rs.2 * x rs.1 * x rs.2) =
      ∑ r, ∑ s, if edge r s then e r s * x r * x s else 0 := by
    simp only [pairs, Finset.sum_filter, ← Finset.univ_product_univ,
      Finset.sum_product]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    by_cases ha : support a <;> by_cases hb : support b <;>
      simp [ha, hb, hz a, hz b]
  have hbound (rs : ι × ι) (h : rs ∈ pairs) :
      t * (e rs.1 rs.2 * x rs.1 * x rs.2) ≤ 1 := by
    have hp := (Finset.mem_filter.mp h).2
    have hv : (t * (e rs.1 rs.2 * x rs.1 * x rs.2)) ^ 2 = 1 := by
      simp only [mul_pow, ht, he, hx rs.1 hp.1, hx rs.2 hp.2.1, one_mul]
    nlinarith
  have hsum : (∑ rs ∈ pairs, t * (e rs.1 rs.2 * x rs.1 * x rs.2)) =
      (pairs.card : ℝ) := by
    rw [← Finset.mul_sum, hrestrict, hs]
    change t * ((n : ℝ) * t) = _
    have hcard : pairs.card = n := hc
    rw [hcard]
    nlinarith [ht]
  have hzero : (∑ rs ∈ pairs, (1 - t * (e rs.1 rs.2 * x rs.1 * x rs.2))) = 0 := by
    rw [Finset.sum_sub_distrib, hsum]
    simp
  have hle := Finset.single_le_sum
    (fun rs h => sub_nonneg.mpr (hbound rs h)) hmem
  rw [hzero] at hle
  have hunit : t * (e r s * x r * x s) = 1 := by
    linarith [hbound (r, s) hmem]
  calc
    e r s * x r * x s = (t * t) * (e r s * x r * x s) := by
      rw [← pow_two, ht, one_mul]
    _ = t * (t * (e r s * x r * x s)) := by ring
    _ = t := by rw [hunit, mul_one]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
