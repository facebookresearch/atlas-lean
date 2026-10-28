/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadPhaseExact

/-! Extremal finite sums and the actual zero-tensor short-product equation. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- If a finite sum reaches the sum of its upper bounds, every term reaches its bound. -/
theorem generatedAxisE8_sum_saturated {ι : Type*} [Fintype ι] (a : ι → ℝ)
    (ha : ∀ i, a i ≤ 1) (hs : (∑ i, a i) = (Fintype.card ι : ℝ)) :
    ∀ i, a i = 1 := by
  classical
  have hsum : (∑ i, (1 - a i)) = 0 := by
    rw [Finset.sum_sub_distrib, hs]
    simp
  intro i
  have hbound : 1 - a i ≤ ∑ j, (1 - a j) :=
    Finset.single_le_sum (fun j _ => sub_nonneg.mpr (ha j)) (Finset.mem_univ i)
  rw [hsum] at hbound
  linarith [ha i]

/-- A maximal sum of signed terms forces every summand to equal the target sign. -/
theorem generatedAxisE8_signed_sum_saturated {ι : Type*} [Fintype ι]
    (e a : ι → ℝ) (t : ℝ) (he : ∀ i, e i ^ 2 = 1) (ha : ∀ i, a i ^ 2 = 1)
    (ht : t ^ 2 = 1) (hs : (∑ i, e i * a i) = (Fintype.card ι : ℝ) * t) :
    ∀ i, e i * a i = t := by
  have hb (i : ι) : t * e i * a i ≤ 1 := by
    have hv : (t * e i * a i) ^ 2 = 1 := by
      rw [mul_pow, mul_pow, ht, he i, ha i]
      norm_num
    nlinarith
  have hsum : (∑ i, t * e i * a i) = (Fintype.card ι : ℝ) := by
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, hs]
    nlinarith [ht]
  have h := generatedAxisE8_sum_saturated (fun i => t * e i * a i) hb hsum
  intro i
  calc
    e i * a i = (t * t) * (e i * a i) := by rw [← pow_two, ht, one_mul]
    _ = t * (t * e i * a i) := by ring
    _ = t := by rw [h i, mul_one]

/-- Comparing two coherent signed triples removes their common cocycle phase. -/
theorem generatedAxisE8_triple_ratio (e xr xs xu yr ys yu : ℝ)
    (he : e ^ 2 = 1) (hx : e * xr * xs = xu) (hy : e * yr * ys = yu) :
    (yr * xr) * (ys * xs) = yu * xu := by
  calc
    (yr * xr) * (ys * xs) = (e * e) * ((yr * xr) * (ys * xs)) := by
      rw [← pow_two, he, one_mul]
    _ = (e * yr * ys) * (e * xr * xs) := by ring
    _ = yu * xu := by rw [hx, hy]

/-- In the actual product, zero tensor coordinates and pairing four leave a
short convolution of 56 times the short coordinate for a 64-idempotent. -/
theorem generatedAxisE8_short_convolution (x : ConwayRawSpace) (u : GriessShortIndex)
    (ht : x.2.2 = 0) (hp : conwayShortPairing x.1 u = 4)
    (hs : (conwayRawProduct x x).2.1 u = 64 * x.2.1 u) :
    (∑ r, ∑ s, if (griessShortQ r * griessShortQ s).base = (griessShortQ u).base then
      qSign (Multiplicative.toAdd (griessShortQ r * griessShortQ s).coeff) *
        x.2.1 r * x.2.1 s else 0) = 56 * x.2.1 u := by
  change conwayShortPairing x.1 u * x.2.1 u + conwayShortPairing x.1 u * x.2.1 u +
    (∑ r, ∑ s, if (griessShortQ r * griessShortQ s).base = (griessShortQ u).base then
      qSign (Multiplicative.toAdd (griessShortQ r * griessShortQ s).coeff) *
        x.2.1 r * x.2.1 s else 0) +
    (∑ t, ∑ i, ∑ j,
      spinOperator (griessShortQ u) (fun v => x.2.2 v i) t * x.2.2 t j *
        conwayTensorCoefficient u i j) / 8 = 64 * x.2.1 u at hs
  simp only [ht, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero,
    zero_div, add_zero, hp] at hs
  linarith

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
