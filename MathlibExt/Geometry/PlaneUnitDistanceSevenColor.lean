/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
The statement of `exists_seven_coloring` is adapted from OpenAI Math,
`lean/ComparatorChallenges/PlaneColoring.lean`, at commit
`3344da59991ed94f9ba711217b29c1d760badfa6`:
https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PlaneColoring.lean#L9-L15
The source is distributed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). Its file and license notices do
not specify a copyright holder or author for this statement.
Authors: OpenAI (project attribution in lean/formalization.yaml).
-/

module

public import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Uniform
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.MetricSpace.HausdorffDistance

/-!
# Seven colors suffice for the Euclidean plane

Assign every point to a nearest center of a triangular lattice with spacing `4/5`, breaking
boundary ties arbitrarily. A center indexed by `(a, b)` has color `a + 3b` modulo seven. Each
point is at distance less than `1/2` from its chosen center, and distinct centers of the same
color are at distance greater than `2`. Thus points at distance exactly one have different
colors, with no regularity assumption on the coloring.

## References

* Aubrey D.N.J. de Grey, *The chromatic number of the plane is at least 5*, Geombinatorics
  28 (2018), no. 1, pp. 18–31, §1 (Introduction), credits the hexagonal tiling upper bound
  to John Isbell (1950).
* Alexander Soifer, *The Mathematical Coloring Book: Mathematics of Coloring and the Colorful
  Life of Its Creators*, Springer (2008), Chapter 3, pp. 24 and 29, gives Isbell's account
  and credits Hugo Hadwiger's earlier use of the tiling for a different problem.
* H. Hadwiger, *Überdeckung des euklidischen Raumes durch kongruente Mengen*, Portugaliae
  Mathematica 4 (1945), pp. 238–242.
-/

namespace EuclideanGeometry

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private noncomputable def center (i : ℤ × ℤ) : Plane :=
  WithLp.toLp 2 ![4 / 5 * ((i.1 : ℝ) + (i.2 : ℝ) / 2), 2 / 5 * Real.sqrt 3 * (i.2 : ℝ)]

private lemma center_zero (i : ℤ × ℤ) :
    center i 0 = 4 / 5 * ((i.1 : ℝ) + (i.2 : ℝ) / 2) := by
  simp [center]

private lemma center_one (i : ℤ × ℤ) : center i 1 = 2 / 5 * Real.sqrt 3 * (i.2 : ℝ) := by
  simp [center]

private lemma sqrt_three_sq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

private lemma isClosed_range_center : IsClosed (Set.range center) := by
  let a (p : Plane) := 5 / 4 * p 0 - (5 / (2 * Real.sqrt 3) * p 1) / 2
  let b (p : Plane) := 5 / (2 * Real.sqrt 3) * p 1
  have hs : Real.sqrt 3 ≠ 0 := by positivity
  have hcast := Real.isClosed_range_intCast
  have ha : Continuous a := by
    unfold a
    fun_prop
  have hb : Continuous b := by
    unfold b
    fun_prop
  convert (hcast.preimage ha).inter (hcast.preimage hb) using 1
  ext p
  constructor
  · rintro ⟨i, rfl⟩
    have hb' : b (center i) = (i.2 : ℝ) := by
      dsimp [b]
      rw [center_one]
      field_simp [hs]
    refine ⟨⟨i.1, ?_⟩, ⟨i.2, hb'.symm⟩⟩
    change (i.1 : ℝ) = 5 / 4 * center i 0 - b (center i) / 2
    rw [center_zero, hb']
    ring
  · rintro ⟨⟨m, hm⟩, ⟨n, hn⟩⟩
    refine ⟨(m, n), ?_⟩
    change (m : ℝ) = a p at hm
    change (n : ℝ) = b p at hn
    apply PiLp.ext
    intro k
    fin_cases k
    · change center (m, n) 0 = p 0
      simp only [center_zero, hm, hn]
      dsimp [a, b]
      ring
    · change center (m, n) 1 = p 1
      simp only [center_one, hn]
      dsimp [b]
      field_simp [hs]

private lemma exists_nearest (p : Plane) :
    ∃ i : ℤ × ℤ, ∀ j : ℤ × ℤ, dist p (center i) ≤ dist p (center j) := by
  obtain ⟨q, ⟨i, rfl⟩, hq⟩ := isClosed_range_center.exists_infDist_eq_dist
    (Set.range_nonempty center) p
  exact ⟨i, fun j ↦ hq.symm.le.trans (Metric.infDist_le_dist_of_mem ⟨j, rfl⟩)⟩

private lemma dist_center_sq (i j : ℤ × ℤ) :
    dist (center i) (center j) ^ 2 = 16 / 25 *
      (((i.1 - j.1 : ℤ) : ℝ) ^ 2 + (i.1 - j.1 : ℤ) * (i.2 - j.2 : ℤ) +
        ((i.2 - j.2 : ℤ) : ℝ) ^ 2) := by
  simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs,
    center_zero, center_one, Int.cast_sub]
  linear_combination (4 / 25 : ℝ) * ((i.2 : ℝ) - j.2) ^ 2 * sqrt_three_sq

private lemma dist_lt_half_of_nearest (p : Plane) (i : ℤ × ℤ)
    (hi : ∀ j : ℤ × ℤ, dist p (center i) ≤ dist p (center j)) :
    dist p (center i) < 1 / 2 := by
  let u := p 0 - center i 0
  let v := p 1 - center i 1
  -- Compare the squared distance to the six adjacent centers.
  have hshift (j : ℤ × ℤ) :
      u ^ 2 + v ^ 2 ≤ (u - center j 0) ^ 2 + (v - center j 1) ^ 2 := by
    have h := pow_le_pow_left₀ dist_nonneg (hi (i + j)) 2
    simp only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs] at h
    convert h using 1
    simp only [u, v, center_zero, center_one, Prod.fst_add, Prod.snd_add, Int.cast_add]
    ring
  have hu : |u| ≤ 2 / 5 := by
    have hp := hshift (1, 0)
    have hn := hshift (-1, 0)
    norm_num [center_zero, center_one] at hp hn
    exact abs_le.mpr ⟨by nlinarith only [hn], by nlinarith only [hp]⟩
  have hp := hshift (0, 1)
  have hn := hshift (0, -1)
  have hq := hshift (1, -1)
  have hr := hshift (-1, 1)
  norm_num [center_zero, center_one] at hp hn hq hr
  have h₁ : |u + Real.sqrt 3 * v| ≤ 4 / 5 :=
    abs_le.mpr ⟨by nlinarith only [hn, sqrt_three_sq], by nlinarith only [hp, sqrt_three_sq]⟩
  have h₂ : |u - Real.sqrt 3 * v| ≤ 4 / 5 :=
    abs_le.mpr ⟨by nlinarith only [hr, sqrt_three_sq], by nlinarith only [hq, sqrt_three_sq]⟩
  have huv : |u| + |Real.sqrt 3 * v| ≤ 4 / 5 := by
    obtain ⟨h₁l, h₁r⟩ := abs_le.mp h₁
    obtain ⟨h₂l, h₂r⟩ := abs_le.mp h₂
    rcases le_total 0 u with ha | ha <;> rcases le_total 0 (Real.sqrt 3 * v) with hb | hb
    · simpa only [abs_of_nonneg ha, abs_of_nonneg hb] using h₁r
    · rw [abs_of_nonneg ha, abs_of_nonpos hb]
      linarith
    · rw [abs_of_nonpos ha, abs_of_nonneg hb]
      linarith
    · rw [abs_of_nonpos ha, abs_of_nonpos hb]
      linarith
  have hsq := pow_le_pow_left₀ (abs_nonneg (Real.sqrt 3 * v))
    (show |Real.sqrt 3 * v| ≤ 4 / 5 - |u| by linarith) 2
  rw [sq_abs, mul_pow, sqrt_three_sq] at hsq
  have hbound : u ^ 2 + v ^ 2 ≤ 16 / 75 := by
    nlinarith only [hsq, mul_nonneg (abs_nonneg u) (sub_nonneg.mpr hu), sq_abs u]
  have hdist : dist p (center i) ^ 2 ≤ 16 / 75 := by
    simpa only [EuclideanSpace.dist_sq_eq, Fin.sum_univ_two, Real.dist_eq, sq_abs] using hbound
  nlinarith only [hdist, dist_nonneg (x := p) (y := center i)]

private def residue (i : ℤ × ℤ) : Fin 7 :=
  ⟨((i.1 + 3 * i.2) % 7).toNat, by omega⟩

private lemma seven_le_of_dvd_form {a b : ℤ} (hne : a ≠ 0 ∨ b ≠ 0) (h : 7 ∣ a + 3 * b) :
    7 ≤ a ^ 2 + a * b + b ^ 2 := by
  obtain ⟨k, hk⟩ := h
  have hform : a ^ 2 + a * b + b ^ 2 = 7 * (k * (a - 2 * b) + b ^ 2) := calc
    _ = (a + 3 * b) * (a - 2 * b) + 7 * b ^ 2 := by ring
    _ = _ := by rw [hk]; ring
  have hpos : 0 < a ^ 2 + a * b + b ^ 2 := by
    by_cases hb : b = 0
    · subst b
      simpa using sq_pos_of_ne_zero (hne.resolve_right (fun h ↦ h rfl))
    · nlinarith only [sq_nonneg (2 * a + b), sq_pos_of_ne_zero hb]
  omega

private lemma two_lt_dist_center_of_same_residue {i j : ℤ × ℤ} (hij : i ≠ j)
    (hc : residue i = residue j) : 2 < dist (center i) (center j) := by
  have he := congrArg Fin.val hc
  change ((i.1 + 3 * i.2) % 7).toNat = ((j.1 + 3 * j.2) % 7).toNat at he
  have hd : 7 ∣ (i.1 - j.1) + 3 * (i.2 - j.2) := by omega
  have hn : i.1 - j.1 ≠ 0 ∨ i.2 - j.2 ≠ 0 := by
    by_contra! h
    exact hij (Prod.ext (sub_eq_zero.mp h.1) (sub_eq_zero.mp h.2))
  have hform := seven_le_of_dvd_form hn hd
  have hreal : (7 : ℝ) ≤ ((i.1 - j.1 : ℤ) : ℝ) ^ 2 +
      (i.1 - j.1 : ℤ) * (i.2 - j.2 : ℤ) + ((i.2 - j.2 : ℤ) : ℝ) ^ 2 := by
    exact_mod_cast hform
  have hsq := dist_center_sq i j
  by_contra! h
  have hle := pow_le_pow_left₀ dist_nonneg h 2
  nlinarith only [hsq, hle, hreal]

/-- There is a coloring of the entire Euclidean plane with seven colors in which any
pair of points at distance exactly one has different colors. No measurability or other
regularity is imposed, and the condition holds at every point, including boundaries.

Source: [OpenAI Math, `properColoring_seven`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/PlaneColoring.lean#L10-L15).

Source: Classical upper bound by Isbell's hexagonal tiling (1950), as credited in
Aubrey D.N.J. de Grey, *The chromatic number of the plane is at least 5*,
Geombinatorics 28 (2018), no. 1, pp. 18–31, §1. -/
public theorem exists_seven_coloring :
    ∃ c : EuclideanSpace ℝ (Fin 2) → Fin 7,
      ∀ x y : EuclideanSpace ℝ (Fin 2), dist x y = 1 → c x ≠ c y := by
  choose i hi using exists_nearest
  refine ⟨fun p ↦ residue (i p), ?_⟩
  intro x y hxy hcolor
  have hx := dist_lt_half_of_nearest x (i x) (hi x)
  have hy := dist_lt_half_of_nearest y (i y) (hi y)
  by_cases h : i x = i y
  · have ht := dist_triangle_right x y (center (i x))
    rw [h] at hx ht
    linarith
  · have hc := two_lt_dist_center_of_same_residue h hcolor
    have h₁ := dist_triangle x y (center (i y))
    have h₂ := dist_triangle_left (center (i x)) (center (i y)) x
    linarith

end EuclideanGeometry
