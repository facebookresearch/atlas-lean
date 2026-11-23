/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 2, Entry 7, Example 4

Sum of arctan(2/(k+1)²) over all k equals 3π/4.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch2

namespace Entry7Example4

private lemma arctan_two_div_sq (n : ℕ) (hn : 1 ≤ n) :
    Real.arctan (2 / ((n : ℝ)) ^ 2) =
      Real.arctan ((n : ℝ) + 1) - Real.arctan ((n : ℝ) - 1) := by
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos hnR)
  have ha_nonneg : (0 : ℝ) ≤ (n : ℝ) + 1 := by linarith
  have hb_nonneg : (0 : ℝ) ≤ (n : ℝ) - 1 := by linarith
  have hA_nn : 0 ≤ Real.arctan ((n : ℝ) + 1) := Real.arctan_nonneg.mpr ha_nonneg
  have hB_nn : 0 ≤ Real.arctan ((n : ℝ) - 1) := Real.arctan_nonneg.mpr hb_nonneg
  have hA_lt : Real.arctan ((n : ℝ) + 1) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have hB_lt : Real.arctan ((n : ℝ) - 1) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have hmem : Real.arctan ((n : ℝ) + 1) - Real.arctan ((n : ℝ) - 1) ∈
      Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
    constructor <;> linarith
  have hcosA : Real.cos (Real.arctan ((n : ℝ) + 1)) ≠ 0 := by
    rw [Real.cos_arctan]
    positivity
  have hcosB : Real.cos (Real.arctan ((n : ℝ) - 1)) ≠ 0 := by
    rw [Real.cos_arctan]
    positivity
  have hcond : ((∀ k : ℤ, Real.arctan ((n : ℝ) + 1) ≠ (2 * (k : ℝ) + 1) * Real.pi / 2) ∧
      ∀ l : ℤ, Real.arctan ((n : ℝ) - 1) ≠ (2 * (l : ℝ) + 1) * Real.pi / 2) := by
    constructor
    · intro k hk
      apply hcosA
      rw [hk]
      exact Real.cos_eq_zero_iff.mpr ⟨k, rfl⟩
    · intro l hl
      apply hcosB
      rw [hl]
      exact Real.cos_eq_zero_iff.mpr ⟨l, rfl⟩
  have htan : Real.tan (Real.arctan ((n : ℝ) + 1) - Real.arctan ((n : ℝ) - 1)) =
      2 / ((n : ℝ)) ^ 2 := by
    have h := Real.tan_sub (Or.inl hcond)
    rw [Real.tan_arctan, Real.tan_arctan] at h
    rw [h]
    field_simp
    ring
  exact Real.arctan_eq_of_tan_eq htan hmem

private lemma partial_sum (N : ℕ) :
    ∑ k ∈ Finset.range N, Real.arctan (2 / (((k : ℝ) + 1) ^ 2)) =
      Real.arctan ((N : ℝ) + 1) + Real.arctan (N : ℝ) - Real.pi / 4 := by
  induction N with
  | zero =>
    simp [Real.arctan_zero, Real.arctan_one]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have h := arctan_two_div_sq (N + 1) (by omega)
    push_cast at h
    have e1 : ((N : ℝ) + 1 + 1) = (N : ℝ) + 2 := by ring
    have e2 : ((N : ℝ) + 1 - 1) = (N : ℝ) := by ring
    rw [e1, e2] at h
    have ecast : (((N + 1 : ℕ)) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [h, ecast, e1]
    abel

private lemma summable_arctan :
    Summable (fun k : ℕ => Real.arctan (2 / (((k : ℝ) + 1) ^ 2))) := by
  have hnn : ∀ k : ℕ, 0 ≤ Real.arctan (2 / (((k : ℝ) + 1) ^ 2)) := by
    intro k
    apply Real.arctan_nonneg.mpr
    positivity
  have hle : ∀ k : ℕ, Real.arctan (2 / (((k : ℝ) + 1) ^ 2)) ≤ 2 / (((k : ℝ) + 1) ^ 2) := by
    intro k
    apply Real.arctan_le_self
    positivity
  have hmaj : Summable (fun k : ℕ => 2 / (((k : ℝ) + 1) ^ 2)) := by
    have hbase : Summable (fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ 2) :=
      (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    have hshift : Summable (fun k : ℕ => (1 : ℝ) / ((((k + 1 : ℕ)) : ℝ)) ^ 2) := by
      have := (summable_nat_add_iff (f := fun n : ℕ => (1 : ℝ) / ((n : ℝ)) ^ 2) 1).mpr hbase
      simpa using this
    have h2 : Summable (fun k : ℕ => (2 : ℝ) * ((1 : ℝ) / ((((k + 1 : ℕ)) : ℝ)) ^ 2)) :=
      hshift.mul_left 2
    have heq : (fun k : ℕ => 2 / (((k : ℝ) + 1) ^ 2)) =
        (fun k : ℕ => (2 : ℝ) * ((1 : ℝ) / ((((k + 1 : ℕ)) : ℝ)) ^ 2)) := by
      funext k
      push_cast
      ring
    rw [heq]
    exact h2
  exact Summable.of_nonneg_of_le hnn hle hmaj

private lemma tendsto_partial :
    Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.range N, Real.arctan (2 / (((k : ℝ) + 1) ^ 2)))
      Filter.atTop (nhds (3 * Real.pi / 4)) := by
  have heq : (fun N : ℕ => ∑ k ∈ Finset.range N, Real.arctan (2 / (((k : ℝ) + 1) ^ 2))) =
      (fun N : ℕ => Real.arctan ((N : ℝ) + 1) + Real.arctan (N : ℝ) - Real.pi / 4) :=
    funext partial_sum
  rw [heq]
  have h1 : Filter.Tendsto (fun N : ℕ => Real.arctan (N : ℝ)) Filter.atTop (nhds (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp tendsto_natCast_atTop_atTop
  have hcast : Filter.Tendsto (fun N : ℕ => ((N : ℝ) + 1)) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop 1 tendsto_natCast_atTop_atTop
  have h2 : Filter.Tendsto (fun N : ℕ => Real.arctan ((N : ℝ) + 1)) Filter.atTop (nhds (Real.pi / 2)) :=
    (Real.tendsto_arctan_atTop.mono_right nhdsWithin_le_nhds).comp hcast
  have h3 : Filter.Tendsto (fun N : ℕ => Real.arctan ((N : ℝ) + 1) + Real.arctan (N : ℝ))
      Filter.atTop (nhds (Real.pi / 2 + Real.pi / 2)) := h2.add h1
  have h4 : Filter.Tendsto (fun N : ℕ => Real.arctan ((N : ℝ) + 1) + Real.arctan (N : ℝ) - Real.pi / 4)
      Filter.atTop (nhds (Real.pi / 2 + Real.pi / 2 - Real.pi / 4)) := h3.sub_const (Real.pi / 4)
  have heq2 : Real.pi / 2 + Real.pi / 2 - Real.pi / 4 = 3 * Real.pi / 4 := by ring
  rw [heq2] at h4
  exact h4

/-- **Series of arctangents of 2/k² (Entry 7, Example 4).** The series
$$\sum_{k=0}^{\infty} \arctan \frac{2}{(k + 1)^2}$$
converges absolutely and its sum is $3\pi/4$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I (Springer, 1985), Chapter 2, Entry
    7, Example 4, printed p. 37 / PDF p. 47.
Proves `Wanted` entry `ramanujan_part1_ch2_entry7_example4`.
-/
theorem ramanujan_part1_ch2_entry7_example4 :
    HasSum (fun k : ℕ => Real.arctan (2 / (((k : ℝ) + 1) ^ 2))) (3 * Real.pi / 4) := by
  exact (Summable.hasSum_iff_tendsto_nat summable_arctan).mpr tendsto_partial

end Entry7Example4

end MathlibExt.NumberTheory.Ramanujan.Part1Ch2
