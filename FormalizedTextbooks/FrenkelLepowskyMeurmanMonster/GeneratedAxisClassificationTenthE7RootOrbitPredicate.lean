/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationTenthE7RootOrbitProjection

/-! The entire actual preferred short-line set of the standard E7 space is preserved. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

/-- Actual integral short lines supported in the standard octad and perpendicular to the normal. -/
def generatedTenthE7RootShortPredicate (r : GriessShortIndex) : Prop :=
  griessShortLatticeVector r ∈ generatedTenthE7StandardE8Section ∧
    (griessShortLatticeVector r).val 4 + (griessShortLatticeVector r).val 5 = 0

/-- The entire actual preferred E7 short-line set, rather than a hypothetical orbit. -/
def generatedTenthE7RootShortSet : Set GriessShortIndex :=
  {r | generatedTenthE7RootShortPredicate r}

/-- The already proved complete actual perpendicular catalogue is exactly this short-line set. -/
def generatedTenthE7RootShortCatalogueEquiv :
    generatedTenthE7StandardRootLines ≃ generatedTenthE7RootShortSet where
  toFun r := ⟨r.val.val, r.val.property, r.property⟩
  invFun r := ⟨⟨r.val, r.property.1⟩, r.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The entire actual E7 short-line set has exactly sixty-three members. -/
theorem generatedTenth_e7_root_short_set_card : Nat.card generatedTenthE7RootShortSet = 63 := by
  rw [← Nat.card_congr generatedTenthE7RootShortCatalogueEquiv]
  exact generatedTenth_e7_standard_root_lines_card

private theorem integral_eigen_iff (u : leechIntegral) :
    generatedTenthE7XiProjection.map (Int.castRingHom ℝ) *ᵥ leechCoordinateEmbedding u.val =
      (2 : ℝ) • leechCoordinateEmbedding u.val ↔
        (∀ i : Fin 24, 8 ≤ i.val → u.val i = 0) ∧ u.val 4 + u.val 5 = 0 := by
  rw [generatedTenth_e7_root_orbit_eigenspace]
  have hsqrt : Real.sqrt 8 ≠ 0 := by positivity
  constructor
  · rintro ⟨hs, hn⟩
    constructor
    · intro i hi
      have h := hs i hi
      change (u.val i : ℝ) / Real.sqrt 8 = 0 at h
      have hc : (u.val i : ℝ) = 0 := by simpa only [div_eq_zero_iff, hsqrt, or_false] using h
      exact_mod_cast hc
    · change (u.val 4 : ℝ) / Real.sqrt 8 + (u.val 5 : ℝ) / Real.sqrt 8 = 0 at hn
      rw [← add_div] at hn
      have hc : (u.val 4 : ℝ) + (u.val 5 : ℝ) = 0 := by
        simpa only [div_eq_zero_iff, hsqrt, or_false] using hn
      exact_mod_cast hc
  · rintro ⟨hs, hn⟩
    constructor
    · intro i hi
      change (u.val i : ℝ) / Real.sqrt 8 = 0
      rw [hs i hi, Int.cast_zero, zero_div]
    · change (u.val 4 : ℝ) / Real.sqrt 8 + (u.val 5 : ℝ) / Real.sqrt 8 = 0
      rw [← add_div, ← Int.cast_add, hn, Int.cast_zero, zero_div]

/-- Actual preferred E7 incidence is precisely membership in the genuine E7 eigenspace. -/
theorem generatedTenth_e7_root_short_predicate_eigen (r : GriessShortIndex) :
    generatedTenthE7RootShortPredicate r ↔
      generatedTenthE7XiProjection.map (Int.castRingHom ℝ) *ᵥ
        leechCoordinateEmbedding (griessShortLatticeVector r).val =
          (2 : ℝ) • leechCoordinateEmbedding (griessShortLatticeVector r).val := by
  rw [integral_eigen_iff]
  unfold generatedTenthE7RootShortPredicate
  rw [generatedTenth_e7_standard_e8_section_mem]

/-- Every actual full matrix fixer preserves the entire genuine E7
short-line predicate. -/
theorem generatedTenth_e7_root_short_preserved (g : generatedTenthE7StandardMatrixGroup)
    (r : GriessShortIndex) (hr : generatedTenthE7RootShortPredicate r) :
    generatedTenthE7RootShortPredicate (griessShortPermutation g.val r) := by
  have he := (generatedTenth_e7_root_short_predicate_eigen r).mp hr
  have hv : generatedTenthE7XiProjection.map (Int.castRingHom ℝ) *ᵥ
      leechCoordinateEmbedding (leechIntegralAction g.val (griessShortLatticeVector r)).val =
        (2 : ℝ) •
          leechCoordinateEmbedding
            (leechIntegralAction g.val (griessShortLatticeVector r)).val := by
    rw [leechIntegralAction_embedding, ← generatedTenth_e7_root_orbit_standard_commute,
      he, map_smul]
  apply (generatedTenth_e7_root_short_predicate_eigen _).mpr
  rcases generatedE8Short_integral_sign g.val r with h | h
  · rw [h] at hv
    exact hv
  · rw [h] at hv
    change generatedTenthE7XiProjection.map (Int.castRingHom ℝ) *ᵥ
      leechCoordinateEmbedding (-(griessShortLatticeVector _).val) =
        (2 : ℝ) • leechCoordinateEmbedding (-(griessShortLatticeVector _).val) at hv
    rw [map_neg, Matrix.mulVec_neg, smul_neg] at hv
    exact neg_injective hv

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
