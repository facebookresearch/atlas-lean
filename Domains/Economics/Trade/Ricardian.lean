/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Order.Basic
public import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Field.Basic

/-!
# Ricardian gains from trade (Atlas AP01.T01)

Two goods, one factor (labor). A country needs `a₁` units of labor per unit of
good 1 and `a₂` per unit of good 2, and has `L` units of labor. Its autarky
consumption set is its production possibility set. At a world relative price
`p` (units of good 2 per unit of good 1), a country that specializes completely
in good 1 earns `p * (L / a₁)` in units of good 2; one that specializes in good 2
earns `L / a₂`.

"Gains from trade" here means the textbook statement about consumption
possibilities: trade strictly enlarges the set of bundles a country can consume.
Specializing in good 1 does so exactly when `p` exceeds the autarky opportunity
cost `a₁ / a₂`; specializing in good 2 exactly when `p` is below it. Hence any `p`
strictly between the two autarky prices enlarges both countries' consumption sets
(potential mutual gains). No preferences are modelled, so no claim is made that a
particular consumer's chosen bundle, or utility, strictly improves (a consumer
whose optimum is the specialization corner can be indifferent), and no
market-clearing allocation is constructed.

## References

* D. Ricardo, *On the Principles of Political Economy and Taxation* (1817),
  chapter 7 (comparative advantage).
* P. R. Krugman, M. Obstfeld and M. J. Melitz, *International Economics: Theory
  and Policy*, Pearson, chapter 3 (the one-factor Ricardian model: the world
  relative price lies between the autarky relative prices, and trade enlarges
  each country's consumption possibilities).
-/
@[expose] public section

namespace MathlibExt.Economics.Ricardian

/-- One country of a two-good Ricardian model. -/
structure Country where
  /-- Unit labor requirement of good 1. -/
  a₁ : ℝ
  /-- Unit labor requirement of good 2. -/
  a₂ : ℝ
  /-- Labor endowment. -/
  L : ℝ
  a₁_pos : 0 < a₁
  a₂_pos : 0 < a₂
  L_pos : 0 < L

/-- Autarky relative price of good 1 (its opportunity cost in units of good 2). -/
noncomputable def autarkyPrice (c : Country) : ℝ := c.a₁ / c.a₂

/-- Autarky consumption set = production possibility set:
`{x ≥ 0 | a₁ x₁ + a₂ x₂ ≤ L}`. -/
def autarkySet (c : Country) : Set (ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ c.a₁ * x.1 + c.a₂ * x.2 ≤ c.L}

/-- Consumption set when the country specializes completely in good 1 and trades
at relative price `p`: `{x ≥ 0 | p x₁ + x₂ ≤ p (L / a₁)}`. -/
noncomputable def specializeGood1Set (c : Country) (p : ℝ) : Set (ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ p * x.1 + x.2 ≤ p * (c.L / c.a₁)}

/-- Consumption set when the country specializes completely in good 2 and trades
at relative price `p`: `{x ≥ 0 | p x₁ + x₂ ≤ L / a₂}`. -/
noncomputable def specializeGood2Set (c : Country) (p : ℝ) : Set (ℝ × ℝ) :=
  {x | 0 ≤ x.1 ∧ 0 ≤ x.2 ∧ p * x.1 + x.2 ≤ c.L / c.a₂}

/-- Specializing in good 1 strictly enlarges the consumption set iff the world
price exceeds the autarky price. -/
theorem autarkySet_ssubset_specializeGood1Set_iff (c : Country) {p : ℝ} (hp : 0 < p) :
    autarkySet c ⊂ specializeGood1Set c p ↔ autarkyPrice c < p := by
  have ha₁ : 0 < c.a₁ := c.a₁_pos
  have ha₂ : 0 < c.a₂ := c.a₂_pos
  have hL : 0 < c.L := c.L_pos
  have ha₁ne : c.a₁ ≠ 0 := ne_of_gt ha₁
  constructor
  · intro h
    rw [Set.ssubset_iff_subset_ne] at h
    by_contra hcon
    push Not at hcon
    have hpa : p * c.a₂ ≤ c.a₁ := by
      have hcon' : p ≤ c.a₁ / c.a₂ := hcon
      exact (le_div_iff₀ ha₂).mp hcon'
    have hsub : specializeGood1Set c p ⊆ autarkySet c := by
      intro x hx
      obtain ⟨hx1, hx2, hle⟩ := hx
      refine ⟨hx1, hx2, ?_⟩
      have hA : (p * x.1 + x.2) * c.a₁ ≤ p * c.L := by
        have h := mul_le_mul_of_nonneg_right hle ha₁.le
        have hrw : p * (c.L / c.a₁) * c.a₁ = p * c.L := by
          calc p * (c.L / c.a₁) * c.a₁
              = p * (c.L / c.a₁ * c.a₁) := by ring
            _ = p * c.L := by rw [div_mul_cancel₀ _ ha₁ne]
        rwa [hrw] at h
      have hB : 0 ≤ (c.a₁ - p * c.a₂) * x.2 := mul_nonneg (sub_nonneg.mpr hpa) hx2
      have hC : (c.a₁ * x.1 + c.a₂ * x.2) * p ≤ c.L * p := by linarith [hA, hB]
      exact le_of_mul_le_mul_right hC hp
    exact h.2 (Set.Subset.antisymm h.1 hsub)
  · intro hprice
    have hpa : c.a₁ < p * c.a₂ := by
      have hprice' : c.a₁ / c.a₂ < p := hprice
      exact (div_lt_iff₀ ha₂).mp hprice'
    have hsubset : autarkySet c ⊆ specializeGood1Set c p := by
      intro x hx
      obtain ⟨hx1, hx2, hle⟩ := hx
      refine ⟨hx1, hx2, ?_⟩
      rw [← mul_div_assoc, le_div_iff₀ ha₁]
      have hAp := mul_le_mul_of_nonneg_right hle hp.le
      have hB : 0 ≤ (p * c.a₂ - c.a₁) * x.2 :=
        mul_nonneg (le_of_lt (sub_pos.mpr hpa)) hx2
      linarith [hAp, hB]
    refine (Set.ssubset_iff_of_subset hsubset).mpr ⟨(0, p * (c.L / c.a₁)), ?_, ?_⟩
    · change (0:ℝ) ≤ 0 ∧ 0 ≤ p * (c.L / c.a₁) ∧
        p * 0 + p * (c.L / c.a₁) ≤ p * (c.L / c.a₁)
      refine ⟨le_rfl, le_of_lt (mul_pos hp (div_pos hL ha₁)), ?_⟩
      simp
    · intro hmem
      obtain ⟨-, -, hle⟩ := hmem
      have hle' : c.a₁ * 0 + c.a₂ * (p * (c.L / c.a₁)) ≤ c.L := hle
      rw [mul_zero, zero_add] at hle'
      have h2 := mul_le_mul_of_nonneg_right hle' ha₁.le
      have hrw : c.a₂ * (p * (c.L / c.a₁)) * c.a₁ = (p * c.a₂) * c.L := by
        calc c.a₂ * (p * (c.L / c.a₁)) * c.a₁
            = (c.a₂ * p) * (c.L / c.a₁ * c.a₁) := by ring
          _ = (c.a₂ * p) * c.L := by rw [div_mul_cancel₀ _ ha₁ne]
          _ = (p * c.a₂) * c.L := by ring
      rw [hrw] at h2
      have h4 := mul_lt_mul_of_pos_right hpa hL
      linarith [h2, h4]

/-- Specializing in good 2 strictly enlarges the consumption set iff the world
price is below the autarky price. -/
theorem autarkySet_ssubset_specializeGood2Set_iff (c : Country) {p : ℝ} (hp : 0 < p) :
    autarkySet c ⊂ specializeGood2Set c p ↔ p < autarkyPrice c := by
  have ha₁ : 0 < c.a₁ := c.a₁_pos
  have ha₂ : 0 < c.a₂ := c.a₂_pos
  have hL : 0 < c.L := c.L_pos
  have ha₂ne : c.a₂ ≠ 0 := ne_of_gt ha₂
  constructor
  · intro h
    rw [Set.ssubset_iff_subset_ne] at h
    by_contra hcon
    push Not at hcon
    have hpa : c.a₁ ≤ p * c.a₂ := by
      have hcon' : c.a₁ / c.a₂ ≤ p := hcon
      exact (div_le_iff₀ ha₂).mp hcon'
    have hsub : specializeGood2Set c p ⊆ autarkySet c := by
      intro x hx
      obtain ⟨hx1, hx2, hle⟩ := hx
      refine ⟨hx1, hx2, ?_⟩
      have hA : (p * x.1 + x.2) * c.a₂ ≤ c.L := by
        have h := mul_le_mul_of_nonneg_right hle ha₂.le
        have hrw : c.L / c.a₂ * c.a₂ = c.L := div_mul_cancel₀ _ ha₂ne
        rwa [hrw] at h
      have hB : 0 ≤ (p * c.a₂ - c.a₁) * x.1 := mul_nonneg (sub_nonneg.mpr hpa) hx1
      linarith [hA, hB]
    exact h.2 (Set.Subset.antisymm h.1 hsub)
  · intro hprice
    have hpa : p * c.a₂ < c.a₁ := by
      have hprice' : p < c.a₁ / c.a₂ := hprice
      exact (lt_div_iff₀ ha₂).mp hprice'
    have hsubset : autarkySet c ⊆ specializeGood2Set c p := by
      intro x hx
      obtain ⟨hx1, hx2, hle⟩ := hx
      refine ⟨hx1, hx2, ?_⟩
      rw [le_div_iff₀ ha₂]
      have hB : 0 ≤ (c.a₁ - p * c.a₂) * x.1 :=
        mul_nonneg (le_of_lt (sub_pos.mpr hpa)) hx1
      linarith [hle, hB]
    refine (Set.ssubset_iff_of_subset hsubset).mpr ⟨((c.L / c.a₂) / p, 0), ?_, ?_⟩
    · change 0 ≤ (c.L / c.a₂) / p ∧ (0:ℝ) ≤ 0 ∧
        p * ((c.L / c.a₂) / p) + 0 ≤ c.L / c.a₂
      refine ⟨le_of_lt (div_pos (div_pos hL ha₂) hp), le_rfl, ?_⟩
      have hw1 : p * ((c.L / c.a₂) / p) = c.L / c.a₂ := mul_div_cancel₀ _ hp.ne'
      rw [hw1, add_zero]
    · intro hmem
      obtain ⟨-, -, hle⟩ := hmem
      have hle' : c.a₁ * ((c.L / c.a₂) / p) + c.a₂ * 0 ≤ c.L := hle
      rw [mul_zero, add_zero] at hle'
      have h2 := mul_le_mul_of_nonneg_right hle' hp.le
      have hrw : c.a₁ * ((c.L / c.a₂) / p) * p = c.a₁ * (c.L / c.a₂) := by
        calc c.a₁ * ((c.L / c.a₂) / p) * p
            = c.a₁ * (((c.L / c.a₂) / p) * p) := by ring
          _ = c.a₁ * (c.L / c.a₂) := by rw [div_mul_cancel₀ _ hp.ne']
      rw [hrw] at h2
      have h3 := mul_le_mul_of_nonneg_right h2 ha₂.le
      have hrw2 : c.a₁ * (c.L / c.a₂) * c.a₂ = c.a₁ * c.L := by
        calc c.a₁ * (c.L / c.a₂) * c.a₂
            = c.a₁ * ((c.L / c.a₂) * c.a₂) := by ring
          _ = c.a₁ * c.L := by rw [div_mul_cancel₀ _ ha₂ne]
      rw [hrw2] at h3
      have h5 := mul_lt_mul_of_pos_right hpa hL
      linarith [h3, h5]

/-- **Potential mutual gains from Ricardian trade.** If the world price lies
strictly between Home's and Foreign's autarky prices, Home (specializing in good 1)
and Foreign (specializing in good 2) both strictly enlarge their consumption sets.
This is an opportunity-set statement, not a utility comparison. -/
theorem ssubset_specializeSets_of_mem_Ioo (H F : Country) {p : ℝ}
    (hp : p ∈ Set.Ioo (autarkyPrice H) (autarkyPrice F)) :
    autarkySet H ⊂ specializeGood1Set H p ∧ autarkySet F ⊂ specializeGood2Set F p := by
  rw [Set.mem_Ioo] at hp
  have hHpos : 0 < autarkyPrice H := div_pos H.a₁_pos H.a₂_pos
  have hp0 : 0 < p := lt_trans hHpos hp.1
  exact ⟨(autarkySet_ssubset_specializeGood1Set_iff H hp0).mpr hp.1,
    (autarkySet_ssubset_specializeGood2Set_iff F hp0).mpr hp.2⟩

/-- A world price at which both countries' consumption sets strictly enlarge (Home
specializing in good 1, Foreign in good 2) exists iff Home has a comparative
advantage in good 1. -/
theorem exists_ssubset_specializeSets_iff (H F : Country) :
    (∃ p, autarkySet H ⊂ specializeGood1Set H p ∧ autarkySet F ⊂ specializeGood2Set F p) ↔
      autarkyPrice H < autarkyPrice F := by
  constructor
  · rintro ⟨p, hH, hF⟩
    have h00 : ((0:ℝ), 0) ∈ autarkySet H := by
      change (0:ℝ) ≤ 0 ∧ (0:ℝ) ≤ 0 ∧ H.a₁ * 0 + H.a₂ * 0 ≤ H.L
      refine ⟨le_rfl, le_rfl, ?_⟩
      simp only [mul_zero, add_zero]
      exact le_of_lt H.L_pos
    have h00' := hH.1 h00
    have h0le' : p * (0:ℝ) + 0 ≤ p * (H.L / H.a₁) := h00'.2.2
    rw [mul_zero, add_zero] at h0le'
    have hp0 : 0 ≤ p := nonneg_of_mul_nonneg_left h0le' (div_pos H.L_pos H.a₁_pos)
    have hp : 0 < p := by
      rcases eq_or_lt_of_le hp0 with h | hpos
      · exfalso
        subst h
        have hmem : ((0:ℝ), H.L / H.a₂) ∈ autarkySet H := by
          change (0:ℝ) ≤ 0 ∧ 0 ≤ H.L / H.a₂ ∧ H.a₁ * 0 + H.a₂ * (H.L / H.a₂) ≤ H.L
          refine ⟨le_rfl, le_of_lt (div_pos H.L_pos H.a₂_pos), ?_⟩
          rw [mul_zero, zero_add, mul_div_cancel₀ _ (ne_of_gt H.a₂_pos)]
        have hcon := hH.1 hmem
        have hle0 : (0:ℝ) * 0 + H.L / H.a₂ ≤ 0 * (H.L / H.a₁) := hcon.2.2
        rw [mul_zero, zero_add, zero_mul] at hle0
        exact absurd hle0 (not_le_of_gt (div_pos H.L_pos H.a₂_pos))
      · exact hpos
    have h1 := (autarkySet_ssubset_specializeGood1Set_iff H hp).mp hH
    have h2 := (autarkySet_ssubset_specializeGood2Set_iff F hp).mp hF
    exact lt_trans h1 h2
  · intro hlt
    obtain ⟨p, hp⟩ := exists_between hlt
    exact ⟨p, ssubset_specializeSets_of_mem_Ioo H F (Set.mem_Ioo.mpr hp)⟩

end MathlibExt.Economics.Ricardian
