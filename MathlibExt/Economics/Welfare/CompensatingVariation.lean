/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Consumer.TwoGood
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.BigOperators.Fin
/-!
# Compensating variation

For a price change `p⁰ → p¹` at wealth `w`, the compensating variation with the sign convention
`CV = e(p⁰, u⁰) - e(p¹, u⁰)` at the fixed baseline utility `u⁰ = v(p⁰, w)`: the wealth that can
be taken from the consumer after the change while keeping the baseline utility (positive for a
welfare gain).

## Main definitions

* `indirectUtility u X p w`: `v(p, w) = sup {u x | x ∈ B(p, w)}`.
* `expenditure u X p ū`: `e(p, ū) = inf {p ⬝ᵥ x | x ∈ X, ū ≤ u x}`.
* `compensatingVariation u X p₀ p₁ w`: `e(p⁰, u⁰) - e(p¹, u⁰)`.

## Main results

* `compensatingVariation_eq_sub`: under expenditure–utility duality `e(p⁰, u⁰) = w`, the
  compensating variation is `w - e(p¹, u⁰)`.
* `compensatingVariation_nonneg_of_le`: a price fall (`0 ≤ p¹ ≤ p⁰`) on a nonnegative
  consumption set has `CV ≥ 0`.
* `expenditure_min`, `indirectUtility_min`, `compensatingVariation_min`: the exact worked
  example for the perfect-complements utility `min x₀ x₁`.

`indirectUtility` and `expenditure` have the shapes of the consumer-duality interface under
review in Atlas (`Economics.Consumer`, roadmap EC04.T02), whose
`expenditure_indirectUtility_eq` supplies the duality hypothesis under local nonsatiation and
attainment; unifying the definitions is future work.

Atlas roadmap target EC09.T01.

## References

* A. Mas-Colell, M. D. Whinston and J. R. Green, *Microeconomic Theory*, Oxford University
  Press (1995), §3.I.
* H. R. Varian, *Intermediate Microeconomics*, 9th ed., Norton (2014), ch. 14.
-/

@[expose] public section

namespace MathlibExt.Economics.Consumer

open Matrix

/-- The indirect utility `v(p, w) = sup {u x | x ∈ B(p, w)}`. As a real supremum it is
meaningful only when the supremum exists. -/
noncomputable def indirectUtility {ι : Type*} [Fintype ι] (u : (ι → ℝ) → ℝ)
    (X : Set (ι → ℝ)) (p : ι → ℝ) (w : ℝ) : ℝ :=
  sSup (u '' budgetSet X p w)

/-- The expenditure function `e(p, ū) = inf {p ⬝ᵥ x | x ∈ X, ū ≤ u x}`: the least cost of
reaching utility at least `ū`. As a real infimum it is meaningful only when the target is
feasible and costs are bounded below. -/
noncomputable def expenditure {ι : Type*} [Fintype ι] (u : (ι → ℝ) → ℝ)
    (X : Set (ι → ℝ)) (p : ι → ℝ) (ubar : ℝ) : ℝ :=
  sInf ((fun x => p ⬝ᵥ x) '' {x | x ∈ X ∧ ubar ≤ u x})

/-- The compensating variation of a price change `p⁰ → p¹` at wealth `w`, with the frozen
sign `CV = e(p⁰, u⁰) - e(p¹, u⁰)` at the fixed baseline utility `u⁰ = v(p⁰, w)`: the wealth
that can be taken from the consumer after the change while keeping baseline utility
(positive for a welfare gain). -/
noncomputable def compensatingVariation {ι : Type*} [Fintype ι] (u : (ι → ℝ) → ℝ)
    (X : Set (ι → ℝ)) (p₀ p₁ : ι → ℝ) (w : ℝ) : ℝ :=
  expenditure u X p₀ (indirectUtility u X p₀ w) - expenditure u X p₁ (indirectUtility u X p₀ w)

/-- **Compensating variation as an expenditure difference.** When baseline expenditure at the
baseline utility recovers wealth, `e(p⁰, v(p⁰, w)) = w` (expenditure–utility duality), the
compensating variation is `w - e(p¹, u⁰)`. -/
theorem compensatingVariation_eq_sub {ι : Type*} [Fintype ι] {u : (ι → ℝ) → ℝ}
    {X : Set (ι → ℝ)} {p₀ p₁ : ι → ℝ} {w : ℝ}
    (hdual : expenditure u X p₀ (indirectUtility u X p₀ w) = w) :
    compensatingVariation u X p₀ p₁ w = w - expenditure u X p₁ (indirectUtility u X p₀ w) := by
  unfold compensatingVariation
  rw [hdual]

/-- **A price fall has nonnegative compensating variation.** On a consumption set of
nonnegative bundles, if the new prices are nonnegative and nowhere above the old ones, then
`0 ≤ CV`. -/
theorem compensatingVariation_nonneg_of_le {ι : Type*} [Fintype ι] {u : (ι → ℝ) → ℝ}
    {X : Set (ι → ℝ)} {p₀ p₁ : ι → ℝ} {w : ℝ} (hX : ∀ x ∈ X, ∀ i, 0 ≤ x i)
    (hp₁ : ∀ i, 0 ≤ p₁ i) (hle : ∀ i, p₁ i ≤ p₀ i) :
    0 ≤ compensatingVariation u X p₀ p₁ w := by
  have hle_cost : ∀ x ∈ X, p₁ ⬝ᵥ x ≤ p₀ ⬝ᵥ x := by
    intro x hx
    unfold dotProduct
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (hle i) (hX x hx i)
  have hnn : ∀ x ∈ X, 0 ≤ p₁ ⬝ᵥ x := by
    intro x hx
    unfold dotProduct
    apply Finset.sum_nonneg
    intro i _
    exact mul_nonneg (hp₁ i) (hX x hx i)
  have key : expenditure u X p₁ (indirectUtility u X p₀ w)
      ≤ expenditure u X p₀ (indirectUtility u X p₀ w) := by
    unfold expenditure
    by_cases hS : {x | x ∈ X ∧ indirectUtility u X p₀ w ≤ u x}.Nonempty
    · have hbdd : BddBelow ((fun x => p₁ ⬝ᵥ x)
          '' {x | x ∈ X ∧ indirectUtility u X p₀ w ≤ u x}) := by
        refine ⟨0, ?_⟩
        intro b hb
        simp only [Set.mem_image] at hb
        obtain ⟨x, hxmem, rfl⟩ := hb
        obtain ⟨hxX, -⟩ := hxmem
        exact hnn x hxX
      have hB : ((fun x => p₀ ⬝ᵥ x)
          '' {x | x ∈ X ∧ indirectUtility u X p₀ w ≤ u x}).Nonempty := by
        obtain ⟨x, hx⟩ := hS
        exact ⟨p₀ ⬝ᵥ x, Set.mem_image_of_mem _ hx⟩
      apply le_csInf hB
      intro b hb
      simp only [Set.mem_image] at hb
      obtain ⟨x, hxmem, rfl⟩ := hb
      obtain ⟨hxX, hxu⟩ := hxmem
      calc sInf ((fun x => p₁ ⬝ᵥ x) '' {x | x ∈ X ∧ indirectUtility u X p₀ w ≤ u x})
          ≤ p₁ ⬝ᵥ x := csInf_le hbdd (Set.mem_image_of_mem _ ⟨hxX, hxu⟩)
        _ ≤ p₀ ⬝ᵥ x := hle_cost x hxX
    · rw [Set.not_nonempty_iff_eq_empty] at hS
      simp [hS, Set.image_empty, Real.sInf_empty]
  unfold compensatingVariation
  linarith

/-- Worked example: the expenditure function of the perfect-complements utility
`min x₀ x₁` at positive prices is `e(p, ū) = (p₀ + p₁) ū` for `ū ≥ 0`. -/
theorem expenditure_min {p : Fin 2 → ℝ} {ubar : ℝ} (hp : ∀ i, 0 < p i) (hu : 0 ≤ ubar) :
    expenditure (fun x => min (x 0) (x 1)) twoGoodSet p ubar = (p 0 + p 1) * ubar := by
  have hcost : ∀ x : Fin 2 → ℝ, p ⬝ᵥ x = p 0 * x 0 + p 1 * x 1 := by
    intro x
    simp [dotProduct, Fin.sum_univ_two]
  have hLeast : IsLeast ((fun x => p ⬝ᵥ x)
      '' {x | x ∈ twoGoodSet ∧ ubar ≤ min (x 0) (x 1)}) ((p 0 + p 1) * ubar) := by
    constructor
    · have hmem : (fun _ => ubar) ∈ {x | x ∈ twoGoodSet ∧ ubar ≤ min (x 0) (x 1)} := by
        constructor
        · intro i
          exact hu
        · change ubar ≤ min ubar ubar
          exact le_min le_rfl le_rfl
      have hval : (fun x => p ⬝ᵥ x) (fun _ => ubar) = (p 0 + p 1) * ubar := by
        change p ⬝ᵥ (fun _ => ubar) = _
        rw [hcost]
        show p 0 * ubar + p 1 * ubar = (p 0 + p 1) * ubar
        ring
      have himg : (fun x => p ⬝ᵥ x) (fun _ => ubar)
          ∈ (fun x => p ⬝ᵥ x) '' {x | x ∈ twoGoodSet ∧ ubar ≤ min (x 0) (x 1)} :=
        Set.mem_image_of_mem _ hmem
      rwa [hval] at himg
    · intro b hb
      simp only [Set.mem_image] at hb
      obtain ⟨x, hxmem, rfl⟩ := hb
      obtain ⟨_, hxu⟩ := hxmem
      have hx0 : ubar ≤ x 0 := le_trans hxu (min_le_left _ _)
      have hx1 : ubar ≤ x 1 := le_trans hxu (min_le_right _ _)
      have h0 : p 0 * ubar ≤ p 0 * x 0 :=
        mul_le_mul_of_nonneg_left hx0 (le_of_lt (hp 0))
      have h1 : p 1 * ubar ≤ p 1 * x 1 :=
        mul_le_mul_of_nonneg_left hx1 (le_of_lt (hp 1))
      change (p 0 + p 1) * ubar ≤ p ⬝ᵥ x
      rw [hcost]
      calc (p 0 + p 1) * ubar = p 0 * ubar + p 1 * ubar := by ring
        _ ≤ p 0 * x 0 + p 1 * x 1 := add_le_add h0 h1
  unfold expenditure
  exact IsLeast.csInf_eq hLeast

/-- Worked example: the indirect utility of `min x₀ x₁` at positive prices and nonnegative
wealth is `v(p, w) = w / (p₀ + p₁)`. -/
theorem indirectUtility_min {p : Fin 2 → ℝ} {w : ℝ} (hp : ∀ i, 0 < p i) (hw : 0 ≤ w) :
    indirectUtility (fun x => min (x 0) (x 1)) twoGoodSet p w = w / (p 0 + p 1) := by
  have hs : (0:ℝ) < p 0 + p 1 := by
    have h0 := hp 0
    have h1 := hp 1
    positivity
  have hcost : ∀ x : Fin 2 → ℝ, p ⬝ᵥ x = p 0 * x 0 + p 1 * x 1 := by
    intro x
    simp [dotProduct, Fin.sum_univ_two]
  have hcostT : p ⬝ᵥ (fun _ => w / (p 0 + p 1)) = w := by
    have h := hcost (fun _ => w / (p 0 + p 1))
    rw [h]
    change p 0 * (w / (p 0 + p 1)) + p 1 * (w / (p 0 + p 1)) = w
    have hs' : p 0 + p 1 ≠ 0 := ne_of_gt hs
    have hrw : p 0 * (w / (p 0 + p 1)) + p 1 * (w / (p 0 + p 1))
        = (p 0 + p 1) * (w / (p 0 + p 1)) := by ring
    rw [hrw, mul_comm, div_mul_cancel₀ _ hs']
  have hGreat : IsGreatest ((fun x => min (x 0) (x 1)) '' budgetSet twoGoodSet p w)
      (w / (p 0 + p 1)) := by
    constructor
    · have hmem : (fun _ => w / (p 0 + p 1)) ∈ budgetSet twoGoodSet p w := by
        constructor
        · intro i
          exact div_nonneg hw (le_of_lt hs)
        · exact hcostT.le
      have hval : (fun x => min (x 0) (x 1)) (fun _ => w / (p 0 + p 1))
          = w / (p 0 + p 1) := by
        change min (w / (p 0 + p 1)) (w / (p 0 + p 1)) = _
        simp
      have himg : (fun x => min (x 0) (x 1)) (fun _ => w / (p 0 + p 1))
          ∈ (fun x => min (x 0) (x 1)) '' budgetSet twoGoodSet p w :=
        Set.mem_image_of_mem _ hmem
      rwa [hval] at himg
    · intro b hb
      simp only [Set.mem_image] at hb
      obtain ⟨x, hx, rfl⟩ := hb
      obtain ⟨_, hbud⟩ := hx
      show min (x 0) (x 1) ≤ w / (p 0 + p 1)
      rw [hcost] at hbud
      have hx0 : min (x 0) (x 1) ≤ x 0 := min_le_left _ _
      have hx1 : min (x 0) (x 1) ≤ x 1 := min_le_right _ _
      have h0 : p 0 * min (x 0) (x 1) ≤ p 0 * x 0 :=
        mul_le_mul_of_nonneg_left hx0 (le_of_lt (hp 0))
      have h1 : p 1 * min (x 0) (x 1) ≤ p 1 * x 1 :=
        mul_le_mul_of_nonneg_left hx1 (le_of_lt (hp 1))
      have hsum : (p 0 + p 1) * min (x 0) (x 1) ≤ w := by
        calc (p 0 + p 1) * min (x 0) (x 1)
            = p 0 * min (x 0) (x 1) + p 1 * min (x 0) (x 1) := by ring
          _ ≤ p 0 * x 0 + p 1 * x 1 := add_le_add h0 h1
          _ ≤ w := hbud
      rw [le_div_iff₀ hs]
      calc min (x 0) (x 1) * (p 0 + p 1)
          = (p 0 + p 1) * min (x 0) (x 1) := by ring
        _ ≤ w := hsum
  unfold indirectUtility
  exact IsGreatest.csSup_eq hGreat

/-- Worked example: for `min x₀ x₁`, a price change `p⁰ → p¹` (both positive) at nonnegative
wealth has compensating variation `w - (p¹₀ + p¹₁) w / (p⁰₀ + p⁰₁)`. -/
theorem compensatingVariation_min {p₀ p₁ : Fin 2 → ℝ} {w : ℝ} (hp₀ : ∀ i, 0 < p₀ i)
    (hp₁ : ∀ i, 0 < p₁ i) (hw : 0 ≤ w) :
    compensatingVariation (fun x => min (x 0) (x 1)) twoGoodSet p₀ p₁ w =
      w - (p₁ 0 + p₁ 1) * (w / (p₀ 0 + p₀ 1)) := by
  have hv : indirectUtility (fun x => min (x 0) (x 1)) twoGoodSet p₀ w
      = w / (p₀ 0 + p₀ 1) := indirectUtility_min hp₀ hw
  have hs0 : (0:ℝ) < p₀ 0 + p₀ 1 := by
    have h0 := hp₀ 0
    have h1 := hp₀ 1
    positivity
  have hu0 : 0 ≤ indirectUtility (fun x => min (x 0) (x 1)) twoGoodSet p₀ w := by
    rw [hv]
    exact div_nonneg hw (le_of_lt hs0)
  have he0 : expenditure (fun x => min (x 0) (x 1)) twoGoodSet p₀
      (indirectUtility (fun x => min (x 0) (x 1)) twoGoodSet p₀ w) = w := by
    rw [expenditure_min hp₀ hu0, hv]
    have hs0' : p₀ 0 + p₀ 1 ≠ 0 := ne_of_gt hs0
    calc (p₀ 0 + p₀ 1) * (w / (p₀ 0 + p₀ 1))
        = w / (p₀ 0 + p₀ 1) * (p₀ 0 + p₀ 1) := mul_comm _ _
      _ = w := div_mul_cancel₀ _ hs0'
  have he1 : expenditure (fun x => min (x 0) (x 1)) twoGoodSet p₁
      (indirectUtility (fun x => min (x 0) (x 1)) twoGoodSet p₀ w)
      = (p₁ 0 + p₁ 1) * (w / (p₀ 0 + p₀ 1)) := by
    rw [expenditure_min hp₁ hu0, hv]
  unfold compensatingVariation
  rw [he0, he1]

end MathlibExt.Economics.Consumer
