/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Case analysis for strip crossings (pigeonhole and symmetry)

Measure-theoretic bookkeeping used in RSW-type arguments: if an event of probability `≥ s` is
covered by `N` events, one of them has probability `≥ s / N`; if the horizontal crossing of a
strip has probability `< 1/2`, its complement (in the intended application, a vertical crossing)
has probability `≥ 1/2` and is covered by `18 k` pieces; each piece splits into a "top" case and
two symmetric "side" cases. The geometric covering and duality facts are hypotheses.

## Main results

* `StatMech.RSW.StripCases.rsc_pigeonhole_cover`: pigeonhole bound `s / |t|` for a finite cover.
* `StatMech.RSW.StripCases.rsc_strip_dichotomy`: `ℙ(H) ≥ 1/2`, or some piece has probability
  `≥ 1 / (36 k)`.
* `StatMech.RSW.StripCases.rsc_dichotomy_cases`: if `ℙ(H) < 1/2`, some piece has a top or side
  case of probability `≥ 1 / (108 k)`.
-/

@[expose] public section

open Set MeasureTheory
open scoped BigOperators

namespace StatMech

namespace RSW

namespace StripCases

/-- Pigeonhole for measures: if `μ Ev ≥ s` and `Ev ⊆ ⋃ i ∈ t, A i` with `t` nonempty, then some
`A i` has `μ (A i) ≥ s / |t|`. -/
theorem rsc_pigeonhole_cover {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {ι : Type*} (t : Finset ι) (A : ι → Set E)
    {Ev : Set E} {s : ℝ} (hEv : s ≤ μ.real Ev) (hcover : Ev ⊆ ⋃ i ∈ t, A i)
    (htne : t.Nonempty) :
    ∃ i ∈ t, s / (t.card : ℝ) ≤ μ.real (A i) := by
  have hub : μ.real Ev ≤ ∑ i ∈ t, μ.real (A i) := by
    refine (measureReal_mono hcover (measure_ne_top μ _)).trans ?_
    exact measureReal_biUnion_finset_le t A
  have hs : s ≤ ∑ i ∈ t, μ.real (A i) := hEv.trans hub
  by_contra hcon
  push Not at hcon
  have hcardpos : (0 : ℝ) < (t.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr htne
  have hlt : ∑ i ∈ t, μ.real (A i) < ∑ _i ∈ t, s / (t.card : ℝ) := by
    apply Finset.sum_lt_sum_of_nonempty htne
    intro i hi
    exact hcon i hi
  rw [Finset.sum_const, nsmul_eq_mul] at hlt
  rw [mul_div_cancel₀ s hcardpos.ne'] at hlt
  linarith

/-- Either `μ H ≥ 1/2`, or (when `μ H < 1/2` forces `μ V ≥ 1/2` and `V` is covered by `18 k`
events) one of the covering events has probability `≥ 1 / (36 k)`. -/
theorem rsc_strip_dichotomy {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {k : ℕ} (hk : 1 ≤ k)
    (H V : Set E) (A : ℕ → Set E)
    (hcompl : μ.real H < 1 / 2 → 1 / 2 ≤ μ.real V)
    (hcover : V ⊆ ⋃ i ∈ Finset.range (18 * k), A i) :
    (1 / 2 ≤ μ.real H) ∨
      (∃ i ∈ Finset.range (18 * k), (1 : ℝ) / (36 * k) ≤ μ.real (A i)) := by
  rcases le_or_gt (1 / 2 : ℝ) (μ.real H) with hH | hH
  · exact Or.inl hH
  · refine Or.inr ?_
    have hV : (1 / 2 : ℝ) ≤ μ.real V := hcompl hH
    have htne : (Finset.range (18 * k)).Nonempty := by
      rw [Finset.nonempty_range_iff]
      omega
    obtain ⟨i, hi, hbound⟩ :=
      rsc_pigeonhole_cover μ (Finset.range (18 * k)) A hV hcover htne
    refine ⟨i, hi, le_trans ?_ hbound⟩
    rw [Finset.card_range]
    have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
    rw [show ((18 * k : ℕ) : ℝ) = 18 * (k : ℝ) by push_cast; ring]
    rw [div_div]
    apply le_of_eq
    field_simp
    ring

/-- If `c₁ ≤ a + b + c'` and `b = c'`, then `c₁ / 3 ≤ a` or `c₁ / 3 ≤ b`. -/
theorem rsc_three_way {a b c' c₁ : ℝ} (hub : c₁ ≤ a + b + c') (hsym : b = c') :
    c₁ / 3 ≤ a ∨ c₁ / 3 ≤ b := by
  subst hsym
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  linarith

/-- If `Arm ⊆ Top ∪ Left ∪ Right` and `μ Left = μ Right`, then `μ Top` or `μ Left` is at least
`μ Arm / 3`. -/
theorem rsc_strip_cases {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {c₁ : ℝ} (Arm Top Left Right : Set E)
    (hArm : c₁ ≤ μ.real Arm)
    (hcover : Arm ⊆ Top ∪ Left ∪ Right)
    (hsym : μ.real Left = μ.real Right) :
    (c₁ / 3 ≤ μ.real Top) ∨ (c₁ / 3 ≤ μ.real Left) := by
  have hub : c₁ ≤ μ.real Top + μ.real Left + μ.real Right := by
    refine hArm.trans (le_trans (measureReal_mono hcover (measure_ne_top μ _)) ?_)
    have h1 : μ.real (Top ∪ Left ∪ Right) ≤ μ.real (Top ∪ Left) + μ.real Right :=
      measureReal_union_le _ _
    have h2 : μ.real (Top ∪ Left) ≤ μ.real Top + μ.real Left :=
      measureReal_union_le _ _
    linarith
  exact rsc_three_way hub hsym

/-- Combination of `rsc_strip_dichotomy` and `rsc_strip_cases`: if `μ H < 1/2`, some covering
event has a top or side case of probability `≥ 1 / (108 k)`. -/
theorem rsc_dichotomy_cases {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] {k : ℕ} (hk : 1 ≤ k)
    (H V : Set E) (A Top Left Right : ℕ → Set E)
    (hH : μ.real H < 1 / 2)
    (hcompl : μ.real H < 1 / 2 → 1 / 2 ≤ μ.real V)
    (hcover : V ⊆ ⋃ i ∈ Finset.range (18 * k), A i)
    (hcase : ∀ i, A i ⊆ Top i ∪ Left i ∪ Right i)
    (hsym : ∀ i, μ.real (Left i) = μ.real (Right i)) :
    ∃ i ∈ Finset.range (18 * k),
      ((1 : ℝ) / (108 * k) ≤ μ.real (Top i)) ∨
        ((1 : ℝ) / (108 * k) ≤ μ.real (Left i)) := by
  rcases rsc_strip_dichotomy μ hk H V A hcompl hcover with hHge | ⟨i, hi, hAi⟩
  · linarith
  · refine ⟨i, hi, ?_⟩
    have hcases := rsc_strip_cases μ (A i) (Top i) (Left i) (Right i) hAi
      (hcase i) (hsym i)
    have heq : ((1 : ℝ) / (36 * k)) / 3 = (1 : ℝ) / (108 * k) := by
      rw [div_div]; norm_num; ring
    rwa [heq] at hcases

end StripCases

end RSW

end StatMech
