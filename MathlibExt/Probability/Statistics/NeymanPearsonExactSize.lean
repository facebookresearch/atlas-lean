/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.NeymanPearson
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Exact-size Neyman–Pearson test on a finite space

For normalized null and alternative weights on a finite nonempty space and a level
`α ∈ (0,1)`, a threshold test with a single tie-randomization constant attains null size
exactly `α` and is most powerful among tests of size at most `α`.

Main result: `exists_exact_size_most_powerful_finite`
(namespace `MathlibExt.Probability.Statistics.NeymanPearson`).
Optimality reuses `neyman_pearson_dominated_two_simple` with counting measure.

Sources: J. Neyman and E. S. Pearson (1933), DOI `10.1098/rsta.1933.0009`; E. L. Lehmann and
J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Theorem 3.2.1.
-/

namespace MathlibExt.Probability.Statistics.NeymanPearson

@[expose] public section

open MeasureTheory

/-- On a finite space there is a threshold `k ≥ 0` at which the null mass of `{k * p < q}`
is at most `α` and the null mass of `{k * p ≤ q}` is at least `α`. The threshold is the
least element, among `0` and the ratios `q x / p x` with `0 < p x`, whose strict rejection
region has null mass at most `α`. -/
private lemma exists_threshold_finite {Ω : Type*} [Fintype Ω]
    (p q : Ω → ℝ) (hp_nonneg : ∀ x, 0 ≤ p x) (hq_nonneg : ∀ x, 0 ≤ q x)
    (hp_sum : ∑ x, p x = 1) (α : ℝ) (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ k : ℝ, 0 ≤ k ∧ (∑ x, if k * p x < q x then p x else 0) ≤ α ∧
      α ≤ ∑ x, if k * p x ≤ q x then p x else 0 := by
  let S : Finset ℝ :=
    insert 0 ((Finset.univ.filter fun x => 0 < p x).image fun x => q x / p x)
  have hS0 : (0 : ℝ) ∈ S := Finset.mem_insert_self _ _
  have hratio : ∀ x, 0 < p x → q x / p x ∈ S := fun x hx =>
    Finset.mem_insert_of_mem
      (Finset.mem_image.mpr ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩, rfl⟩)
  have hS_nonneg : ∀ c ∈ S, 0 ≤ c := by
    intro c hc
    rcases Finset.mem_insert.mp hc with rfl | hc
    · exact le_rfl
    · obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hc
      exact div_nonneg (hq_nonneg x) (hp_nonneg x)
  let T : Finset ℝ := S.filter fun c => (∑ x, if c * p x < q x then p x else 0) ≤ α
  have hSne : S.Nonempty := ⟨0, hS0⟩
  have hmaxT : S.max' hSne ∈ T := by
    refine Finset.mem_filter.mpr ⟨Finset.max'_mem S hSne, ?_⟩
    have h0 : (∑ x, if S.max' hSne * p x < q x then p x else 0) = 0 := by
      refine Finset.sum_eq_zero fun x _ => ?_
      by_cases h : S.max' hSne * p x < q x
      · rw [ite_eq_left h]
        by_contra hpx
        have hpos : 0 < p x := lt_of_le_of_ne (hp_nonneg x) (Ne.symm hpx)
        have hle := Finset.le_max' S _ (hratio x hpos)
        rw [div_le_iff₀ hpos] at hle
        exact absurd h (not_lt.mpr hle)
      · rw [ite_eq_right h]
    rw [h0]
    exact hα0
  have hTne : T.Nonempty := ⟨_, hmaxT⟩
  let k := T.min' hTne
  have hkT : k ∈ T := Finset.min'_mem T hTne
  have hk0 : 0 ≤ k := hS_nonneg k (Finset.mem_filter.mp hkT).1
  refine ⟨k, hk0, (Finset.mem_filter.mp hkT).2, ?_⟩
  rcases hk0.eq_or_lt with hk | hk
  · rw [← hk]
    calc α ≤ 1 := hα1
      _ = ∑ x, p x := hp_sum.symm
      _ = ∑ x, if 0 * p x ≤ q x then p x else 0 := by
        refine Finset.sum_congr rfl fun x _ => ?_
        have h0 : 0 * p x ≤ q x := by
          rw [zero_mul]
          exact hq_nonneg x
        rw [ite_eq_left h0]
  · let L : Finset ℝ := S.filter fun c => c < k
    have hLne : L.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨hS0, hk⟩⟩
    let c := L.max' hLne
    have hcL : c ∈ L := Finset.max'_mem L hLne
    have hck : c < k := (Finset.mem_filter.mp hcL).2
    have hcα : α < ∑ x, if c * p x < q x then p x else 0 := by
      by_contra hcon
      have hcT : c ∈ T := Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hcL).1, not_lt.mp hcon⟩
      exact absurd (Finset.min'_le T c hcT) (not_le.mpr hck)
    refine hcα.le.trans (le_of_eq (Finset.sum_congr rfl fun x _ => ?_))
    rcases (hp_nonneg x).eq_or_lt with hpx | hpx
    · rw [← hpx, ite_self, ite_self]
    · have hiff : c * p x < q x ↔ k * p x ≤ q x := by
        rw [← lt_div_iff₀ hpx, ← le_div_iff₀ hpx]
        constructor
        · intro h
          by_contra h'
          have hmem : q x / p x ∈ L := Finset.mem_filter.mpr ⟨hratio x hpx, not_le.mp h'⟩
          exact absurd (Finset.le_max' L _ hmem) (not_le.mpr h)
        · intro h
          exact hck.trans_le h
      by_cases h : k * p x ≤ q x
      · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
      · rw [ite_eq_right (mt hiff.mp h), ite_eq_right h]

/-- **Exact-size Neyman–Pearson test on a finite space.** For normalized nonnegative
null and alternative weights `p`, `q` on a finite nonempty space and a level `α ∈ (0,1)`,
there are a threshold `k ≥ 0`, a tie value `γ ∈ [0,1]` and a `[0,1]`-valued test `φstar`
that rejects where `k * p < q`, accepts where `q < k * p`, randomizes with the single
constant `γ` on the tie set `q = k * p`, has null size exactly `α`, and has alternative
power at least that of every test of null size at most `α`.

Source: J. Neyman and E. S. Pearson (1933), DOI `10.1098/rsta.1933.0009`; E. L. Lehmann and
J. P. Romano, *Testing Statistical Hypotheses*, 3rd ed., Theorem 3.2.1 (i)–(ii). -/
theorem exists_exact_size_most_powerful_finite
    {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (p q : Ω → ℝ) (hp_nonneg : ∀ x, 0 ≤ p x) (hq_nonneg : ∀ x, 0 ≤ q x)
    (hp_sum : ∑ x, p x = 1) (hq_sum : ∑ x, q x = 1)
    (α : ℝ) (hα0 : 0 < α) (hα1 : α < 1) :
    ∃ k : ℝ, 0 ≤ k ∧ ∃ γ : ℝ, γ ∈ Set.Icc (0 : ℝ) 1 ∧
      ∃ φstar : Ω → Set.Icc (0 : ℝ) 1,
        (∀ x, k * p x < q x → (φstar x).val = 1) ∧
        (∀ x, q x < k * p x → (φstar x).val = 0) ∧
        (∀ x, q x = k * p x → (φstar x).val = γ) ∧
        ∑ x, (φstar x).val * p x = α ∧
        ∀ φ : Ω → Set.Icc (0 : ℝ) 1,
          ∑ x, (φ x).val * p x ≤ α →
            ∑ x, (φ x).val * q x ≤ ∑ x, (φstar x).val * q x := by
  have _ := hq_sum
  obtain ⟨k, hk, hF, hG⟩ :=
    exists_threshold_finite p q hp_nonneg hq_nonneg hp_sum α hα0.le hα1.le
  have hFG : (∑ x, if k * p x < q x then p x else 0) ≤
      ∑ x, if k * p x ≤ q x then p x else 0 := by
    refine Finset.sum_le_sum fun x _ => ?_
    by_cases h : k * p x < q x
    · rw [ite_eq_left h, ite_eq_left h.le]
    · rw [ite_eq_right h]
      split_ifs
      · exact hp_nonneg x
      · exact le_rfl
  generalize hF_def : (∑ x, if k * p x < q x then p x else 0) = F at hF hFG
  generalize hG_def : (∑ x, if k * p x ≤ q x then p x else 0) = G at hG hFG
  generalize hγ_def : (α - F) / (G - F) = γ
  have hγ0 : 0 ≤ γ := hγ_def ▸ div_nonneg (sub_nonneg.mpr hF) (sub_nonneg.mpr hFG)
  have hγ1 : γ ≤ 1 :=
    hγ_def ▸ div_le_one_of_le₀ (sub_le_sub_right hG F) (sub_nonneg.mpr hFG)
  have hγsize : F + γ * (G - F) = α := by
    rcases hFG.eq_or_lt with h | h
    · rw [← h, sub_self, mul_zero, add_zero]
      exact le_antisymm hF (hG.trans_eq h.symm)
    · rw [← hγ_def, div_mul_cancel₀ _ (sub_ne_zero.mpr h.ne')]
      ring
  let φv : Ω → ℝ := fun x => if k * p x < q x then 1 else if q x < k * p x then 0 else γ
  have hφv : ∀ x, φv x ∈ Set.Icc (0 : ℝ) 1 := fun x => by
    change (if k * p x < q x then (1 : ℝ) else if q x < k * p x then 0 else γ) ∈ Set.Icc 0 1
    split_ifs
    · exact Set.mem_Icc.mpr ⟨zero_le_one, le_rfl⟩
    · exact Set.mem_Icc.mpr ⟨le_rfl, zero_le_one⟩
    · exact Set.mem_Icc.mpr ⟨hγ0, hγ1⟩
  let φstar : Ω → Set.Icc (0 : ℝ) 1 := fun x => ⟨φv x, hφv x⟩
  have hφstar : ∀ x, (φstar x).val =
      if k * p x < q x then 1 else if q x < k * p x then 0 else γ := fun _ => rfl
  have hgt : ∀ x, k * p x < q x → (φstar x).val = 1 := fun x h => by
    rw [hφstar, ite_eq_left h]
  have hlt : ∀ x, q x < k * p x → (φstar x).val = 0 := fun x h => by
    rw [hφstar, ite_eq_right (not_lt.mpr h.le), ite_eq_left h]
  have heq : ∀ x, q x = k * p x → (φstar x).val = γ := fun x h => by
    have h1 : ¬ k * p x < q x := by
      rw [h]
      exact lt_irrefl _
    have h2 : ¬ q x < k * p x := by
      rw [h]
      exact lt_irrefl _
    rw [hφstar, ite_eq_right h1, ite_eq_right h2]
  have hsize : ∑ x, (φstar x).val * p x = α := by
    rw [← hγsize, ← hF_def, ← hG_def, ← Finset.sum_sub_distrib, Finset.mul_sum,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hφstar]
    split_ifs <;> first | (exfalso; linarith) | ring1
  refine ⟨k, hk, γ, Set.mem_Icc.mpr ⟨hγ0, hγ1⟩, φstar, hgt, hlt, heq, hsize, ?_⟩
  intro φ hφ
  let _ : MeasurableSpace Ω := ⊤
  have hdisc : DiscreteMeasurableSpace Ω := ⟨fun _ => trivial⟩
  have hint : ∀ f : Ω → ℝ, ∫ x, f x ∂Measure.count = ∑ x, f x := fun f => by
    simp [integral_fintype]
  have key := neyman_pearson_dominated_two_simple (μ := Measure.count) (p := p) (q := q)
    (measurable_of_countable _) (measurable_of_countable _) hp_nonneg hq_nonneg
    Integrable.of_finite Integrable.of_finite k hk φstar (measurable_of_countable _) hgt hlt
    φ (measurable_of_countable _)
  have h := key (by simpa only [hint] using hφ.trans_eq hsize.symm)
  simpa only [hint] using h

end

end MathlibExt.Probability.Statistics.NeymanPearson
