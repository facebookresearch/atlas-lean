/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Steven Warner, Nam Trang
-/
module

public import Mathlib.Analysis.Real.Cardinality
public import Mathlib.SetTheory.Cardinal.Regular

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Logic 3, Logic 483

open Cardinal Ordinal Set Order

namespace MetaMathlibExt

-- Logic 3: Continuum Hypothesis (CH)

/-- CH: 2^{ℵ₀}=ℵ₁ -/
def ContinuumHypothesis.{u} : Prop := (2 : Cardinal.{u}) ^ ℵ₀ = ℵ₁

-- Logic 483: Theorems concerning the Continuum Hypothesis

/-! ### Informal statement of `continuumHypothesis_iff_continuum_eq_aleph_one`

1. The continuum hypothesis holds if and only if the continuum equals ℵ₁.
  2. The continuum hypothesis holds if and only if the continuum is at most ℵ₁.
  3. The continuum hypothesis holds if and only if the reals have cardinality ℵ₁, i.e. |ℝ| =
     ℵ₁.
  4. The continuum hypothesis holds if and only if there is no cardinal strictly between ℵ₀ and the
     continuum.
  5. The continuum hypothesis holds if and only if ℶ₁ = ℵ₁.
  6. Under the continuum hypothesis, x^{ℵ₀} = ℵ₁ for every cardinal x with 2 ≤ x ≤ 𝔠.
  7. Under the continuum hypothesis, the power set of the natural numbers has cardinality ℵ₁, i.e.
     |𝒫(ℕ)| = ℵ₁.
  8. The continuum hypothesis is universe-independent: it holds in one universe if and only if it
     holds in another.
  9. Under the continuum hypothesis, the continuum is regular: it equals its own cofinality.
  10. Under the continuum hypothesis, 2^{ℵ₀} < 2^{ℵ₁}.
  11. Under the continuum hypothesis, ℵ₁^{ℵ₀} = ℵ₁.
  12. The continuum hypothesis holds if and only if every set of reals is countable or has
      cardinality continuum.
-/

/-- 1. The continuum hypothesis holds if and only if the continuum equals ℵ₁.   2. The continuum
   hypothesis holds if and only if the continuum is at most ℵ₁.   3. The continuum hypothesis holds
   if and only if the reals have cardinality ℵ₁, i.e. |ℝ| =      ℵ₁.   4. The continuum hypothesis
   holds if and only if there is no cardinal strictly between ℵ₀ and the continuum.   5.

The full informal statement is in the module documentation directly above.
-/
theorem continuumHypothesis_iff_continuum_eq_aleph_one.{u} :
    ContinuumHypothesis.{u} ↔ (𝔠 : Cardinal.{u}) = ℵ₁ :=
  Iff.rfl

theorem continuumHypothesis_iff_continuum_le_aleph_one.{u} :
    ContinuumHypothesis.{u} ↔ (𝔠 : Cardinal.{u}) ≤ ℵ₁ := by
  rw [continuumHypothesis_iff_continuum_eq_aleph_one]
  exact ⟨le_of_eq, fun h => le_antisymm h aleph_one_le_continuum⟩

theorem continuumHypothesis_iff_mk_real :
    ContinuumHypothesis.{0} ↔ #ℝ = ℵ₁ := by
  rw [continuumHypothesis_iff_continuum_eq_aleph_one, mk_real]

theorem continuumHypothesis_iff_no_intermediate_cardinal.{u} :
    ContinuumHypothesis.{u} ↔ ¬ ∃ κ : Cardinal.{u}, ℵ₀ < κ ∧ κ < 𝔠 := by
  rw [continuumHypothesis_iff_continuum_eq_aleph_one]
  constructor
  · intro hCH ⟨κ, h1, h2⟩
    rw [hCH, lt_aleph_one_iff] at h2
    exact not_lt_of_ge h2 h1
  · intro h
    apply le_antisymm _ aleph_one_le_continuum
    by_contra hle
    exact h ⟨ℵ₁, aleph0_lt_aleph_one, lt_of_not_ge hle⟩

theorem continuumHypothesis_iff_beth_one_eq_aleph_one.{u} :
    ContinuumHypothesis.{u} ↔ (ℶ_ 1 : Cardinal.{u}) = ℵ₁ := by
  rw [continuumHypothesis_iff_continuum_eq_aleph_one, beth_one]

theorem power_aleph0_eq_aleph_one_of_continuumHypothesis.{u} {x : Cardinal.{u}}
    (hCH : ContinuumHypothesis.{u}) (h1 : 2 ≤ x) (h2 : x ≤ 𝔠) :
    x ^ ℵ₀ = ℵ₁ := by
  have hc : (𝔠 : Cardinal.{u}) = ℵ₁ :=
    continuumHypothesis_iff_continuum_eq_aleph_one.mp hCH
  rw [power_aleph0_of_le_continuum h1 h2, hc]

theorem mk_set_nat_eq_aleph_one_of_continuumHypothesis
    (hCH : ContinuumHypothesis.{0}) : #(Set ℕ) = ℵ₁ := by
  rw [mk_set_nat, continuumHypothesis_iff_continuum_eq_aleph_one.mp hCH]

theorem continuumHypothesis_universe_iff.{v, w} :
    ContinuumHypothesis.{v} ↔ ContinuumHypothesis.{w} := by
  simp only [continuumHypothesis_iff_continuum_eq_aleph_one]
  have h1 : Cardinal.lift (𝔠 : Cardinal.{v}) = (𝔠 : Cardinal.{max v w}) := lift_continuum
  have h2 : Cardinal.lift (ℵ₁ : Cardinal.{v}) = (ℵ₁ : Cardinal.{max v w}) := by
    rw [lift_aleph, Ordinal.lift_one]
  have h3 : Cardinal.lift (𝔠 : Cardinal.{w}) = (𝔠 : Cardinal.{max v w}) := lift_continuum
  have h4 : Cardinal.lift (ℵ₁ : Cardinal.{w}) = (ℵ₁ : Cardinal.{max v w}) := by
    rw [lift_aleph, Ordinal.lift_one]
  have e1 : ((𝔠 : Cardinal.{v}) = ℵ₁) ↔ ((𝔠 : Cardinal.{max v w}) = ℵ₁) := by
    rw [← h1, ← h2, Cardinal.lift_inj]
  have e2 : ((𝔠 : Cardinal.{w}) = ℵ₁) ↔ ((𝔠 : Cardinal.{max v w}) = ℵ₁) := by
    rw [← h3, ← h4, Cardinal.lift_inj]
  exact e1.trans e2.symm

theorem continuum_ord_cof_of_continuumHypothesis.{u} (hCH : ContinuumHypothesis.{u}) :
    (𝔠 : Cardinal.{u}).ord.cof = 𝔠 := by
  have hc : (𝔠 : Cardinal.{u}) = ℵ₁ :=
    continuumHypothesis_iff_continuum_eq_aleph_one.mp hCH
  rw [hc]
  exact isRegular_aleph_one.cof_ord

theorem two_power_aleph0_lt_two_power_aleph_one_of_continuumHypothesis.{u}
    (hCH : ContinuumHypothesis.{u}) : (2 : Cardinal.{u}) ^ ℵ₀ < 2 ^ ℵ₁ := by
  rw [hCH]
  exact cantor ℵ₁

theorem aleph_one_power_aleph0_of_continuumHypothesis.{u} (hCH : ContinuumHypothesis.{u}) :
    (ℵ₁ : Cardinal.{u}) ^ ℵ₀ = ℵ₁ :=
  power_aleph0_eq_aleph_one_of_continuumHypothesis hCH
    (ofNat_le_aleph0.trans aleph0_lt_aleph_one.le) aleph_one_le_continuum

theorem continuumHypothesis_iff_forall_set_real :
    ContinuumHypothesis.{0} ↔ ∀ s : Set ℝ, #s ≤ ℵ₀ ∨ #s = 𝔠 := by
  rw [continuumHypothesis_iff_no_intermediate_cardinal]
  constructor
  · intro hno s
    have hs : #s ≤ (𝔠 : Cardinal.{0}) :=
      calc #s ≤ #(Set.univ : Set ℝ) := mk_le_mk_of_subset (Set.subset_univ s)
        _ = #ℝ := mk_univ
        _ = 𝔠 := mk_real
    by_cases h0 : #s ≤ ℵ₀
    · exact Or.inl h0
    · refine Or.inr (le_antisymm hs (le_of_not_gt ?_))
      exact fun hlt => hno ⟨#s, lt_of_not_ge h0, hlt⟩
  · intro h
    rintro ⟨κ, hκ1, hκ2⟩
    have hκ : κ ≤ (#ℝ : Cardinal.{0}) := by
      rw [mk_real]
      exact hκ2.le
    obtain ⟨s, hs⟩ := le_mk_iff_exists_set.mp hκ
    rcases h s with h0 | h0
    · rw [hs] at h0
      exact not_lt_of_ge h0 hκ1
    · rw [hs] at h0
      exact absurd h0 hκ2.ne

end MetaMathlibExt

end
