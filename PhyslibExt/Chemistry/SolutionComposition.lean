/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Basic.Real.Basic
public import PhyslibExt.Chemistry.Amounts.MolarMassComposition
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!

# Solution composition and concentration

Molarity, molality, mole fractions, mass fractions, and parts-per-million, with the
molarity–molality conversion bijection, dilution from amount conservation, mixture mole
fractions, and concentration behavior under a temperature change at fixed composition.

## i. Overview

All quantities are real numerical coordinates after a consistent SI unit choice: amount `n` in
mol, volume `V` in litres (or m³, used consistently within each lemma — no lemma mixes unit
conventions), mass in kg (or g, consistently), solution density `ρ` as mass per solution
volume, and solute molar mass `M` as mass per amount. `c` (molarity) is amount per solution
volume; `b` (molality) is amount per solvent mass; `xᵢ` (mole fraction) is `nᵢ / ∑ⱼ nⱼ`.
Dimensions are not tracked.

For a single-solute solution with solution density `ρ > 0` and solute molar mass `M > 0`, the
maps `b = c / (ρ - c * M)` and `c = b * ρ / (1 + b * M)` send the physical molarity domain
`0 ≤ c ∧ c < ρ / M` and the molalities `b ≥ 0` into each other (`mapsTo_molarityToMolality`,
`mapsTo_molalityToMolarity`) and are mutually inverse there, so each is a bijection between
these two sets (`bijOn_molarityToMolality`, `bijOn_molalityToMolarity`); at the boundary
`c = ρ / M` the conversion denominator vanishes and no finite molality satisfies the
conversion identity. With solute mass `n * M` and solution mass `ρ * V`, the mass fraction is
`c * M / ρ`.

Dilution follows from amount conservation: if `n₁ = n₂` with `c₁ = n₁ / V₁` and `c₂ = n₂ / V₂`
then `c₁ * V₁ = c₂ * V₂`. For a positive target `c₂` and a positive initial amount `c₁ * V₁`,
the final volume `V₂ = c₁ * V₁ / c₂` is positive and achieves the target. Without these
hypotheses the formula degenerates: with no solute it gives `V₂ = 0`, and with target `c₂ = 0`
the molarity identity survives only through Lean's `x / 0 = 0`.
In `dilution_conserved` the final volume is a separately given measured quantity, and no
volume additivity is used anywhere.

For amounts `n i ≥ 0` with `∑ i, n i > 0`, mole fractions are nonnegative and sum to `1`.
When two solutions combine with no reaction, each mixture mole fraction is the average of the
two mole fractions weighted by the total amounts `N₁` and `N₂`: an algebraic identity whenever
both totals are nonzero (`moleFraction_mix`), and a convex combination, with weight
`N₁ / (N₁ + N₂)` in `(0, 1)`, when both totals are positive (`moleFraction_mix_convex`).
Mixture molarity is not determined by the single-solution data: two scenarios agreeing on
`(c₁, c₂, n₁, n₂)` with different measured final volumes have different mixture molarities.

A temperature change in a closed, nonreacting sample leaves solute amount and solvent mass
unchanged while the solution volume may change, so molality is unchanged, while for a positive
amount molarity changes whenever the volume does (`molarity_temp_ne`), by the inverse volume
ratio (`molarity_temp_ratio`).

Parts-per-million by mass is `10^6` times the mass fraction. With solute density `ρs` and
solution density `ρ` it is `ρs / ρ` times parts-per-million by volume
(`ppmByMass_eq_mul_ppmByVolume`), so the relation depends on the density ratio, not on the
numerical value of `ρ`; for a nonzero volume fraction the two agree exactly when `ρs = ρ`
(`ppmByMass_eq_ppmByVolume_iff`).

The results are algebraic. They provide no reaction stoichiometry, activity coefficients,
colligative properties, titration, temperature dependence of density (density is a parameter at
the given temperature), or any volume-additivity model.

## ii. Key results

- `molarity`, `molality` : amount per solution volume and amount per solvent mass. Mole
  fractions are reused from `Chemistry.Amounts.moleFraction` (`n i / ∑ j, n j`); this module
  defines no mole fraction of its own.
- `molarityToMolality`, `molalityToMolarity` : the conversion maps `c / (ρ - c * M)` and
  `b * ρ / (1 + b * M)`.
- `conversion_denom_pos_iff` : for `M > 0`, the denominator is positive exactly on `c < ρ / M`.
- `molalityToMolarity_molarityToMolality`, `molarityToMolality_molalityToMolarity` : both
  round trips.
- `injOn_molarityToMolality`, `injOn_molalityToMolarity` : injectivity on each domain.
- `mapsTo_molarityToMolality`, `mapsTo_molalityToMolarity`, `bijOn_molarityToMolality`,
  `bijOn_molalityToMolarity` : each conversion maps its domain into the other's, and each is a
  bijection between `0 ≤ c ∧ c < ρ / M` and `b ≥ 0`.
- `boundary_denom_eq_zero`, `no_molality_at_boundary` : the boundary `c = ρ / M` is outside
  the conversion domain.
- `massFraction`, `massFraction_eq_molarity_mul` : `w = mSolute / mSoln = c * M / ρ`.
- `amounts_massFraction_eq_massFraction` : the family mass fraction
  `Chemistry.Amounts.massFraction M n i` is the scalar ratio of `n i * M i` over
  `∑ j, n j * M j`.
- `dilutionVolume`, `dilution_conserved`, `dilutionVolume_cross_mul`,
  `molarity_dilutionVolume_algebraic`, `dilutionVolume_achieves_target` : `c₁ * V₁ = c₂ * V₂`,
  two algebraic identities for the computed final volume, and that for a positive target and a
  positive initial amount this volume is positive and achieves the target molarity.
- `Chemistry.Amounts.moleFraction_nonneg`, `Chemistry.Amounts.sum_moleFraction` : reused
  mole-fraction facts; mole fractions are nonnegative and sum to `1`.
- `moleFraction_mix` : the algebraic mixing identity for mole fractions over
  `Chemistry.Amounts.moleFraction`, for nonzero totals.
- `moleFraction_mix_convex` : for positive totals, mixture mole fractions are convex
  combinations with weight `N₁ / (N₁ + N₂)` in `(0, 1)`.
- `mixtureMolarity_notDeterminedByComponents` : mixture molarity needs the final volume.
- `molality_temp_invariant`, `molarity_temp_ne`, `molarity_temp_ratio` : molality is
  temperature-invariant at fixed composition; molarity tracks the volume.
- `ppmByMass`, `ppmByVolume`, `ppmByMass_eq`, `massFraction_of_volumes`,
  `ppmByMass_eq_mul_ppmByVolume`, `ppmByMass_eq_ppmByVolume_iff` : parts-per-million by mass
  and by volume, related by the density ratio `ρs / ρ`.

## iii. Table of contents

- A. Molarity, molality, and the conversion bijection
- B. Dilution from amount conservation
- C. Mixture mole fractions
- D. Temperature change and parts-per-million

## iv. References

- OpenStax, *Chemistry 2e* (planning anchor CHEM-S1), for molarity, molality, dilution, and
  the mass and mole composition of solutions.
- IUPAC, *Quantities, Units and Symbols in Physical Chemistry* (the Green Book), for the
  symbols `n` (amount of substance), `c` (molarity), `b` (molality), `x` (mole fraction),
  and `w` (mass fraction).

-/

@[expose] public section

namespace Chemistry.SolutionComposition

/-!

## A. Molarity, molality, and the conversion bijection

-/

/-- Molarity `c = n / V`: amount of solute per volume of solution, with the volume in litres
(or m³, fixed per lemma). Molarity is a different function from `molality`: the denominator
here is a solution volume, not a solvent mass. No Mathlib definition provides this chemistry
convention (Loogle finds no `molarity`), so it is defined here. -/
noncomputable def molarity (n V : ℝ) : ℝ := n / V

/-- Molality `b = n / mSolvent`: amount of solute per mass of solvent, with the mass in kg
(or g, fixed per lemma). Molality is a different function from `molarity`: the denominator
here is a solvent mass, not a solution volume. No Mathlib definition provides this chemistry
convention (Loogle finds no `molality`), so it is defined here. -/
noncomputable def molality (n mSolvent : ℝ) : ℝ := n / mSolvent

/-- Molarity-to-molality conversion `b = c / (ρ - c * M)` for solution density `ρ` and solute
molar mass `M`, meant for the physical domain `0 ≤ c ∧ c < ρ / M`, which it maps bijectively
onto `b ≥ 0` for positive `ρ` and `M` (`bijOn_molarityToMolality`). No Mathlib definition
provides this conversion, so it is defined here. -/
noncomputable def molarityToMolality (ρ M c : ℝ) : ℝ := c / (ρ - c * M)

/-- Molality-to-molarity conversion `c = b * ρ / (1 + b * M)` for solution density `ρ` and
solute molar mass `M`, meant for `b ≥ 0`, which it maps bijectively onto the physical molarity
domain for positive `ρ` and `M` (`bijOn_molalityToMolarity`). No Mathlib definition provides
this conversion, so it is defined here. -/
noncomputable def molalityToMolarity (ρ M b : ℝ) : ℝ := b * ρ / (1 + b * M)

/-- The conversion denominator `ρ - c * M` (solvent mass per solution volume) is positive
exactly on the physical domain `c < ρ / M`, for `M > 0`. -/
lemma conversion_denom_pos_iff {ρ M c : ℝ} (hM : 0 < M) :
    0 < ρ - c * M ↔ c < ρ / M := by
  rw [sub_pos, lt_div_iff₀ hM]

/-- Molarity-to-molality maps the physical molarity domain `0 ≤ c ∧ c < ρ / M` into the
molalities `b ≥ 0`, for `M > 0`. -/
lemma mapsTo_molarityToMolality {ρ M : ℝ} (hM : 0 < M) :
    Set.MapsTo (molarityToMolality ρ M) {c | 0 ≤ c ∧ c < ρ / M} {b | 0 ≤ b} := by
  intro c hc
  simp only [Set.mem_ofPred_eq] at hc ⊢
  exact div_nonneg hc.1 ((conversion_denom_pos_iff hM).mpr hc.2).le

/-- Molality-to-molarity maps the molalities `b ≥ 0` into the physical molarity domain
`0 ≤ c ∧ c < ρ / M`, for positive `ρ` and `M`. -/
lemma mapsTo_molalityToMolarity {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 < M) :
    Set.MapsTo (molalityToMolarity ρ M) {b | 0 ≤ b} {c | 0 ≤ c ∧ c < ρ / M} := by
  intro b hb
  simp only [Set.mem_ofPred_eq] at hb ⊢
  have h1pos : (0 : ℝ) < 1 + b * M :=
    lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (mul_nonneg hb hM.le))
  refine ⟨div_nonneg (mul_nonneg hb hρ.le) h1pos.le, ?_⟩
  unfold molalityToMolarity
  rw [lt_div_iff₀ hM, div_mul_eq_mul_div, div_lt_iff₀ h1pos]
  have h := add_lt_add_right hρ (b * ρ * M)
  rwa [add_zero, show b * ρ * M + ρ = ρ * (1 + b * M) from by ring] at h

/-- Round trip: converting molarity to molality and back returns the molarity, on the
physical domain `0 ≤ c ∧ c < ρ / M`. Only `M > 0` and the domain are needed. -/
lemma molalityToMolarity_molarityToMolality {ρ M c : ℝ} (hM : 0 < M)
    (hc₀ : 0 ≤ c) (hc : c < ρ / M) :
    molalityToMolarity ρ M (molarityToMolality ρ M c) = c := by
  have hdenom : 0 < ρ - c * M := (conversion_denom_pos_iff hM).mpr hc
  have hdenom' : ρ - c * M ≠ 0 := hdenom.ne'
  have hb : 0 ≤ c / (ρ - c * M) := mapsTo_molarityToMolality hM ⟨hc₀, hc⟩
  have h1 : (1 : ℝ) + c / (ρ - c * M) * M ≠ 0 :=
    (lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (mul_nonneg hb hM.le))).ne'
  simp only [molalityToMolarity, molarityToMolality]
  field_simp
  ring

/-- Round trip: converting molality to molarity and back returns the molality, for `b ≥ 0`
and positive `ρ` and `M`. The converted molarity lies in the physical domain
(`mapsTo_molalityToMolarity`), so `molarityToMolality` maps that domain onto all of `b ≥ 0`
(`bijOn_molarityToMolality`). -/
lemma molarityToMolality_molalityToMolarity {ρ M b : ℝ} (hρ : 0 < ρ) (hM : 0 < M)
    (hb : 0 ≤ b) :
    molarityToMolality ρ M (molalityToMolarity ρ M b) = b := by
  have h1pos : (0 : ℝ) < 1 + b * M :=
    lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (mul_nonneg hb hM.le))
  have h1 : (1 : ℝ) + b * M ≠ 0 := h1pos.ne'
  have hc : b * ρ / (1 + b * M) < ρ / M := (mapsTo_molalityToMolarity hρ hM hb).2
  have hdenom : 0 < ρ - b * ρ / (1 + b * M) * M :=
    (conversion_denom_pos_iff hM).mpr hc
  have hdenom' : ρ - b * ρ / (1 + b * M) * M ≠ 0 := hdenom.ne'
  simp only [molarityToMolality, molalityToMolarity]
  field_simp
  ring

/-- Molarity-to-molality is injective on the physical domain `0 ≤ c ∧ c < ρ / M`, for
`M > 0`. -/
lemma injOn_molarityToMolality {ρ M : ℝ} (hM : 0 < M) :
    Set.InjOn (molarityToMolality ρ M) {c | 0 ≤ c ∧ c < ρ / M} := by
  intro c₁ hc₁ c₂ hc₂ h
  simp only [Set.mem_ofPred_eq] at hc₁ hc₂
  have e₁ := molalityToMolarity_molarityToMolality hM hc₁.1 hc₁.2
  have e₂ := molalityToMolarity_molarityToMolality hM hc₂.1 hc₂.2
  rw [h] at e₁
  rw [e₂] at e₁
  exact e₁.symm

/-- Molality-to-molarity is injective on `b ≥ 0`. -/
lemma injOn_molalityToMolarity {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 < M) :
    Set.InjOn (molalityToMolarity ρ M) {b | 0 ≤ b} := by
  intro b₁ hb₁ b₂ hb₂ h
  simp only [Set.mem_ofPred_eq] at hb₁ hb₂
  have e₁ := molarityToMolality_molalityToMolarity hρ hM hb₁
  have e₂ := molarityToMolality_molalityToMolarity hρ hM hb₂
  rw [h] at e₁
  rw [e₂] at e₁
  exact e₁.symm

/-- **The conversion bijection**: for positive `ρ` and `M`, molarity-to-molality is a bijection
from the physical molarity domain `0 ≤ c ∧ c < ρ / M` onto the molalities `b ≥ 0`, with inverse
`molalityToMolarity`. -/
lemma bijOn_molarityToMolality {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 < M) :
    Set.BijOn (molarityToMolality ρ M) {c | 0 ≤ c ∧ c < ρ / M} {b | 0 ≤ b} := by
  refine Set.InvOn.bijOn ⟨?_, ?_⟩ (mapsTo_molarityToMolality hM)
    (mapsTo_molalityToMolarity hρ hM)
  · intro c hc
    simp only [Set.mem_ofPred_eq] at hc
    exact molalityToMolarity_molarityToMolality hM hc.1 hc.2
  · intro b hb
    simp only [Set.mem_ofPred_eq] at hb
    exact molarityToMolality_molalityToMolarity hρ hM hb

/-- The inverse direction of the conversion bijection: for positive `ρ` and `M`,
molality-to-molarity is a bijection from `b ≥ 0` onto the physical molarity domain
`0 ≤ c ∧ c < ρ / M`. -/
lemma bijOn_molalityToMolarity {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 < M) :
    Set.BijOn (molalityToMolarity ρ M) {b | 0 ≤ b} {c | 0 ≤ c ∧ c < ρ / M} := by
  refine Set.InvOn.bijOn ⟨?_, ?_⟩ (mapsTo_molalityToMolarity hρ hM)
    (mapsTo_molarityToMolality hM)
  · intro b hb
    simp only [Set.mem_ofPred_eq] at hb
    exact molarityToMolality_molalityToMolarity hρ hM hb
  · intro c hc
    simp only [Set.mem_ofPred_eq] at hc
    exact molalityToMolarity_molarityToMolality hM hc.1 hc.2

/-- At the boundary `c = ρ / M` the conversion denominator vanishes. -/
lemma boundary_denom_eq_zero {ρ M : ℝ} (hM : M ≠ 0) : ρ - ρ / M * M = 0 := by
  rw [div_mul_cancel₀ _ hM, sub_self]

/-- At the boundary `c = ρ / M` there is no finite molality satisfying the conversion
identity `c = b * (ρ - c * M)`, for positive `ρ` and `M`. The conversion is physically
undefined there; no value is claimed. -/
lemma no_molality_at_boundary {ρ M : ℝ} (hρ : 0 < ρ) (hM : 0 < M) :
    ¬ ∃ b : ℝ, ρ / M = b * (ρ - ρ / M * M) := by
  rw [boundary_denom_eq_zero hM.ne']
  intro h
  obtain ⟨b, hb⟩ := h
  simp only [mul_zero] at hb
  exact (div_pos hρ hM).ne' hb

/-- Mass fraction `w = mSolute / mSoln`: solute mass over total solution mass. This is the
single-solute ratio `mSolute / mSoln`; it is NOT `Chemistry.Amounts.massFraction`, which is
the family version `n i * M i / ∑ j, n j * M j` over per-species molar masses. No Mathlib
definition provides this single-solute convention. -/
noncomputable def massFraction (mSolute mSoln : ℝ) : ℝ := mSolute / mSoln

/-- With solute mass `n * M` and solution mass `ρ * V`, the mass fraction is `c * M / ρ`. -/
lemma massFraction_eq_molarity_mul {n M ρ V : ℝ} (hV : V ≠ 0) (hρ : ρ ≠ 0) :
    massFraction (n * M) (ρ * V) = molarity n V * M / ρ := by
  have hρV : ρ * V ≠ 0 := mul_ne_zero hρ hV
  simp only [massFraction, molarity]
  field_simp

/-- Bridge: the family mass fraction `Chemistry.Amounts.massFraction M n i` equals the scalar
`massFraction` of the component mass `n i * M i` over the total mass `∑ j, n j * M j`. -/
lemma amounts_massFraction_eq_massFraction {ι : Type*} [Fintype ι] (M n : ι → ℝ) (i : ι) :
    Chemistry.Amounts.massFraction M n i = massFraction (n i * M i) (∑ j, n j * M j) := by
  simp only [Chemistry.Amounts.massFraction, massFraction]

/-!

## B. Dilution from amount conservation

-/

/-- The computed final volume `V₂ = c₁ * V₁ / c₂` for diluting from `c₁, V₁` to the target
concentration `c₂`. It achieves the target when `c₂ > 0` and `c₁ * V₁ > 0`
(`dilutionVolume_achieves_target`). This pins the dilution-volume convention; no Mathlib
definition provides it (Loogle finds no `dilutionVolume`). -/
noncomputable def dilutionVolume (c₁ V₁ c₂ : ℝ) : ℝ := c₁ * V₁ / c₂

/-- Dilution from amount conservation: if `n₁ = n₂` with `c₁ = n₁ / V₁` and `c₂ = n₂ / V₂`
for positive volumes, then `c₁ * V₁ = c₂ * V₂`. `V₂` is a separately given measured final
volume; the proof never uses `V₂ = V₁ + V_added` or any volume additivity. -/
lemma dilution_conserved {n₁ n₂ V₁ V₂ c₁ c₂ : ℝ}
    (hc₁ : c₁ = molarity n₁ V₁) (hc₂ : c₂ = molarity n₂ V₂) (hn : n₁ = n₂)
    (hV₁ : 0 < V₁) (hV₂ : 0 < V₂) :
    c₁ * V₁ = c₂ * V₂ := by
  simp only [hc₁, hc₂, molarity]
  rw [hn, div_mul_cancel₀ _ hV₁.ne', div_mul_cancel₀ _ hV₂.ne']

/-- The cross-multiplied (algebraic) identity for the computed final volume: for `c₂ > 0` and
arbitrary `c₁, V₁`, `V₂ = c₁ * V₁ / c₂` satisfies `c₂ * V₂ = c₁ * V₁`. This alone does not show
that `V₂` achieves molarity `c₂`: with `c₁ * V₁ = 0` it gives `V₂ = 0`. For that, see
`dilutionVolume_achieves_target`. -/
lemma dilutionVolume_cross_mul {c₁ V₁ c₂ : ℝ} (hc₂ : 0 < c₂) :
    c₂ * dilutionVolume c₁ V₁ c₂ = c₁ * V₁ := by
  rw [dilutionVolume, mul_comm c₂ (c₁ * V₁ / c₂), div_mul_cancel₀ _ hc₂.ne']

/-- An algebraic identity, not a physical claim: for `c₁ * V₁ ≠ 0` and every `c₂`,
`(c₁ * V₁) / (c₁ * V₁ / c₂) = c₂`, i.e. `molarity (c₁ * V₁) (dilutionVolume c₁ V₁ c₂) = c₂`.
At `c₂ = 0` the computed volume is `0` and the identity holds only through Lean's `x / 0 = 0`.
For the physical statement see `dilutionVolume_achieves_target`. -/
lemma molarity_dilutionVolume_algebraic {c₁ V₁ c₂ : ℝ} (h : c₁ * V₁ ≠ 0) :
    molarity (c₁ * V₁) (dilutionVolume c₁ V₁ c₂) = c₂ := by
  rw [molarity, dilutionVolume]
  exact div_div_cancel₀ h

/-- **The computed final volume achieves the target concentration**: for a positive target
`c₂` and a positive initial amount `c₁ * V₁` (physically, positive initial concentration and
volume), the final volume `V₂ = c₁ * V₁ / c₂` is positive and the solution of amount `c₁ * V₁`
in it has molarity `c₂`. -/
lemma dilutionVolume_achieves_target {c₁ V₁ c₂ : ℝ} (hc₂ : 0 < c₂) (h : 0 < c₁ * V₁) :
    0 < dilutionVolume c₁ V₁ c₂ ∧ molarity (c₁ * V₁) (dilutionVolume c₁ V₁ c₂) = c₂ :=
  ⟨div_pos h hc₂, molarity_dilutionVolume_algebraic h.ne'⟩

/-!

## C. Mixture mole fractions

-/

/-- **Mixing identity** (algebraic): when two solutions with amount families `n₁, n₂` over the
same species are combined with no reaction (amounts add), each mixture mole fraction (over
`Chemistry.Amounts.moleFraction`) is the average of the two mole fractions weighted by the
totals `N₁ = ∑ j, n₁ j` and `N₂ = ∑ j, n₂ j`. Only `N₁ ≠ 0` and `N₂ ≠ 0` are assumed, so this
is not a convexity claim: totals `-1` and `2` give weights `-1` and `2`, and when
`N₁ + N₂ = 0` both sides are `0` by Lean's division convention. For positive totals see
`moleFraction_mix_convex`. -/
lemma moleFraction_mix {ι : Type*} [Fintype ι] (n₁ n₂ : ι → ℝ) (i : ι)
    (h₁ : ∑ j, n₁ j ≠ 0) (h₂ : ∑ j, n₂ j ≠ 0) :
    Chemistry.Amounts.moleFraction (n₁ + n₂) i =
      ((∑ j, n₁ j) * Chemistry.Amounts.moleFraction n₁ i +
        (∑ j, n₂ j) * Chemistry.Amounts.moleFraction n₂ i) /
        ((∑ j, n₁ j) + (∑ j, n₂ j)) := by
  have hmul₁ : (∑ j, n₁ j) * Chemistry.Amounts.moleFraction n₁ i = n₁ i := by
    rw [Chemistry.Amounts.moleFraction, mul_comm (∑ j, n₁ j) _, div_mul_cancel₀ _ h₁]
  have hmul₂ : (∑ j, n₂ j) * Chemistry.Amounts.moleFraction n₂ i = n₂ i := by
    rw [Chemistry.Amounts.moleFraction, mul_comm (∑ j, n₂ j) _, div_mul_cancel₀ _ h₂]
  rw [hmul₁, hmul₂]
  simp only [Chemistry.Amounts.moleFraction, Pi.add_apply, Finset.sum_add_distrib]

/-- **Mixing as a convex combination**: if both solutions have positive total amounts
`N₁ = ∑ j, n₁ j` and `N₂ = ∑ j, n₂ j`, the weight `w = N₁ / (N₁ + N₂)` lies in `(0, 1)` and each
mixture mole fraction is `w * x₁ + (1 - w) * x₂`. With nonnegative amounts each `xₖ` is also
nonnegative (`Chemistry.Amounts.moleFraction_nonneg`). -/
lemma moleFraction_mix_convex {ι : Type*} [Fintype ι] (n₁ n₂ : ι → ℝ) (i : ι)
    (h₁ : 0 < ∑ j, n₁ j) (h₂ : 0 < ∑ j, n₂ j) :
    0 < (∑ j, n₁ j) / ((∑ j, n₁ j) + ∑ j, n₂ j) ∧
      (∑ j, n₁ j) / ((∑ j, n₁ j) + ∑ j, n₂ j) < 1 ∧
      Chemistry.Amounts.moleFraction (n₁ + n₂) i =
        (∑ j, n₁ j) / ((∑ j, n₁ j) + ∑ j, n₂ j) * Chemistry.Amounts.moleFraction n₁ i +
          (1 - (∑ j, n₁ j) / ((∑ j, n₁ j) + ∑ j, n₂ j)) *
            Chemistry.Amounts.moleFraction n₂ i := by
  have hS : 0 < (∑ j, n₁ j) + ∑ j, n₂ j := add_pos h₁ h₂
  refine ⟨div_pos h₁ hS, (div_lt_one hS).2 (lt_add_of_pos_right _ h₂), ?_⟩
  rw [moleFraction_mix n₁ n₂ i h₁.ne' h₂.ne']
  field_simp
  ring

/-- Mixture molarity is not determined by the single-solution data: two scenarios agreeing on
`(c₁, c₂, n₁, n₂)` with different measured final volumes have different mixture molarities.
Concretely, `n₁ = n₂ = 1` with `V₁ = V₂ = 1` gives `c₁ = c₂ = 1`, while final volume `2`
gives mixture molarity `1` and final volume `3` gives `2 / 3`. This is an existence statement
about the two scenarios, not a claim about real mixture volumes. -/
lemma mixtureMolarity_notDeterminedByComponents :
    ∃ (c₁ c₂ n₁ n₂ Vₐ V₆ : ℝ),
      c₁ = molarity n₁ 1 ∧ c₂ = molarity n₂ 1 ∧ n₁ = 1 ∧ n₂ = 1 ∧ Vₐ = 2 ∧ V₆ = 3 ∧
        Vₐ ≠ V₆ ∧ molarity (n₁ + n₂) Vₐ = 1 ∧ molarity (n₁ + n₂) V₆ = 2 / 3 ∧
        molarity (n₁ + n₂) Vₐ ≠ molarity (n₁ + n₂) V₆ := by
  refine ⟨1, 1, 1, 1, 2, 3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    (try simp only [molarity]) <;> norm_num

/-!

## D. Temperature change and parts-per-million

-/

/-- Molality is unchanged by a temperature change in a closed, nonreacting sample: solute
amount and solvent mass are unchanged, while the solution volume may change arbitrarily. -/
lemma molality_temp_invariant {n n' mSolvent mSolvent' : ℝ}
    (hn : n' = n) (hm : mSolvent' = mSolvent) :
    molality n' mSolvent' = molality n mSolvent := by
  rw [hn, hm]

/-- Molarity changes when the volume changes: for `n > 0` and positive volumes, `V' ≠ V`
implies different molarities. -/
lemma molarity_temp_ne {n V V' : ℝ} (hn : 0 < n) (hV : 0 < V) (hV' : 0 < V')
    (hVV : V' ≠ V) : molarity n V' ≠ molarity n V := by
  simp only [molarity]
  intro h
  rw [div_eq_div_iff hV'.ne' hV.ne'] at h
  have hVV' : V = V' := mul_left_cancel₀ hn.ne' h
  exact hVV hVV'.symm

/-- Quantitative form: the molarity ratio under a volume change is the inverse volume ratio. -/
lemma molarity_temp_ratio {n V V' : ℝ} (hn : n ≠ 0) (hV : V ≠ 0) (hV' : V' ≠ 0) :
    molarity n V' / molarity n V = V / V' := by
  have hdiv : n / V ≠ 0 := div_ne_zero hn hV
  simp only [molarity]
  field_simp

/-- Parts-per-million by mass: `10^6` times the mass fraction. This pins the ppm convention;
no Mathlib definition provides it. -/
noncomputable def ppmByMass (w : ℝ) : ℝ := 10 ^ 6 * w

/-- Parts-per-million by volume: `10^6` times solute volume over solution volume. This pins
the ppm-by-volume convention; no Mathlib definition provides it. -/
noncomputable def ppmByVolume (vSolute vSoln : ℝ) : ℝ := 10 ^ 6 * (vSolute / vSoln)

/-- `ppmByMass` is `10^6` times the mass fraction. -/
lemma ppmByMass_eq (w : ℝ) : ppmByMass w = 10 ^ 6 * w := rfl

/-- Mass fraction from volumes: with solute density `ρs` (so `mSolute = ρs * vSolute`) and
solution density `ρ` (so `mSoln = ρ * vSoln`), the mass fraction is `(ρs / ρ)` times the
volume fraction. Hence ppm by mass is `ρs / ρ` times ppm by volume
(`ppmByMass_eq_mul_ppmByVolume`). -/
lemma massFraction_of_volumes {mSolute mSoln vSolute vSoln ρs ρ : ℝ}
    (hs : mSolute = ρs * vSolute) (h : mSoln = ρ * vSoln)
    (hρ : ρ ≠ 0) (hv : vSoln ≠ 0) :
    massFraction mSolute mSoln = (ρs / ρ) * (vSolute / vSoln) := by
  have hρV : ρ * vSoln ≠ 0 := mul_ne_zero hρ hv
  rw [hs, h]
  simp only [massFraction]
  field_simp

/-- **ppm by mass versus ppm by volume**: with solute density `ρs` (`mSolute = ρs * vSolute`)
and solution density `ρ` (`mSoln = ρ * vSoln`), ppm by mass is `ρs / ρ` times ppm by volume.
The factor is the density ratio, not the numerical value of `ρ`. -/
lemma ppmByMass_eq_mul_ppmByVolume {mSolute mSoln vSolute vSoln ρs ρ : ℝ}
    (hs : mSolute = ρs * vSolute) (h : mSoln = ρ * vSoln)
    (hρ : ρ ≠ 0) (hv : vSoln ≠ 0) :
    ppmByMass (massFraction mSolute mSoln) = (ρs / ρ) * ppmByVolume vSolute vSoln := by
  rw [ppmByMass_eq, massFraction_of_volumes hs h hρ hv, ppmByVolume]
  ring

/-- For a nonzero volume fraction, ppm by mass equals ppm by volume exactly when the solute
and solution densities agree. -/
lemma ppmByMass_eq_ppmByVolume_iff {mSolute mSoln vSolute vSoln ρs ρ : ℝ}
    (hs : mSolute = ρs * vSolute) (h : mSoln = ρ * vSoln)
    (hρ : ρ ≠ 0) (hv : vSoln ≠ 0) (hvs : vSolute ≠ 0) :
    ppmByMass (massFraction mSolute mSoln) = ppmByVolume vSolute vSoln ↔ ρs = ρ := by
  have hP : ppmByVolume vSolute vSoln ≠ 0 :=
    mul_ne_zero (by norm_num) (div_ne_zero hvs hv)
  rw [ppmByMass_eq_mul_ppmByVolume hs h hρ hv]
  constructor
  · intro heq
    have h0 : (ρs / ρ - 1) * ppmByVolume vSolute vSoln = 0 := by
      rw [sub_mul, heq, one_mul, sub_self]
    rcases mul_eq_zero.1 h0 with h1 | h1
    · rwa [sub_eq_zero, div_eq_one_iff_eq hρ] at h1
    · exact absurd h1 hP
  · intro heq
    rw [heq, div_self hρ, one_mul]

end Chemistry.SolutionComposition
