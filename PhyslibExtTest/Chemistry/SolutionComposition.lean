/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.SolutionComposition
public import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!

# Tests for solution composition and concentration

-/

@[expose] public section

open Chemistry.SolutionComposition

namespace PhyslibExtTest.Chemistry.SolutionComposition

/-!

## A. Molarity, molality, and the conversion bijection

-/

/-- Forward conversion at `ρ = 11/10`, `M = 58/1000`, `c = 1/2`: the molality is `500/1071`. -/
example : molarityToMolality (11/10) (58/1000) (1/2) = 500/1071 := by
  simp only [molarityToMolality]
  norm_num

/-- Backward conversion at the same parameters returns `c = 1/2`. -/
example : molalityToMolarity (11/10) (58/1000) (500/1071) = 1/2 := by
  simp only [molalityToMolarity]
  norm_num

/-- Round trip through the lemmas at the stated numbers. -/
example :
    molalityToMolarity (11/10) (58/1000)
      (molarityToMolality (11/10) (58/1000) (1/2)) = 1/2 :=
  molalityToMolarity_molarityToMolality (by norm_num) (by norm_num) (by norm_num)

/-- Round trip the other way at the stated numbers. -/
example :
    molarityToMolality (11/10) (58/1000)
      (molalityToMolarity (11/10) (58/1000) (500/1071)) = 500/1071 :=
  molarityToMolality_molalityToMolarity (by norm_num) (by norm_num) (by norm_num)

/-- The physical domain holds at the stated numbers. -/
example : (0:ℝ) < 11/10 - (1/2) * (58/1000) :=
  (conversion_denom_pos_iff (M := 58/1000) (by norm_num)).mpr (by norm_num)

/-- The conversion denominator vanishes at the boundary. -/
example : (11/10:ℝ) - (11/10)/(58/1000) * (58/1000) = 0 :=
  boundary_denom_eq_zero (by norm_num)

/-- No finite molality satisfies the conversion identity at the boundary. -/
example : ¬ ∃ b : ℝ, (11/10)/(58/1000) =
    b * ((11/10) - (11/10)/(58/1000) * (58/1000)) :=
  no_molality_at_boundary (by norm_num) (by norm_num)

/-- Injectivity of molarity-to-molality at the stated parameters. -/
example : Set.InjOn (molarityToMolality (11/10) (58/1000))
    {c | 0 ≤ c ∧ c < (11/10)/(58/1000)} :=
  injOn_molarityToMolality (by norm_num)

/-- Injectivity of molality-to-molarity at the stated parameters. -/
example : Set.InjOn (molalityToMolarity (11/10) (58/1000)) {b | 0 ≤ b} :=
  injOn_molalityToMolarity (by norm_num) (by norm_num)

/-- Mass fraction `(29/1000)/(11/10) = 29/1100`. -/
example : massFraction (29/1000) (11/10) = 29/1100 := by
  simp only [massFraction]
  norm_num

/-- The mass fraction is `c * M / ρ` at the stated numbers. -/
example : massFraction ((1/2) * (58/1000)) ((11/10) * 1) =
    molarity (1/2) 1 * (58/1000) / (11/10) :=
  massFraction_eq_molarity_mul (by norm_num) (by norm_num)

/-!

## B. Dilution from amount conservation

-/

/-- Diluting `c₁ = 6`, `V₁ = 1/2` to `c₂ = 1` needs final volume `3`. -/
example : dilutionVolume 6 (1/2) 1 = 3 := by
  simp only [dilutionVolume]
  norm_num

/-- The cross-multiplied identity for the computed final volume. -/
example : 1 * dilutionVolume 6 (1/2) 1 = 6 * (1/2) :=
  dilutionVolume_cross_mul (by norm_num)

/-- The computed final volume achieves the target concentration `1`. -/
example : molarity (6 * (1/2)) (dilutionVolume 6 (1/2) 1) = 1 :=
  molarity_dilutionVolume (by norm_num)

/-- Boundary case with no solute (`c₁ = 0`, `V₁ = 1`, target `c₂ = 1`): the cross-multiplied
identity still holds, but the final volume is `0` and the molarity is `0`, not the target `1`.
`molarity_dilutionVolume` excludes this case through `c₁ * V₁ ≠ 0`. -/
example : (1:ℝ) * dilutionVolume 0 1 1 = 0 * 1 ∧ dilutionVolume 0 1 1 = 0 ∧
    molarity (0 * 1) (dilutionVolume 0 1 1) ≠ 1 := by
  refine ⟨dilutionVolume_cross_mul (by norm_num), ?_, ?_⟩ <;>
    simp only [dilutionVolume, molarity] <;> norm_num

/-- Amount conservation gives `c₁ * V₁ = c₂ * V₂` at the stated numbers. -/
example : (6:ℝ) * (1/2) = 1 * 3 :=
  dilution_conserved (n₁ := 3) (n₂ := 3) (by simp only [molarity]; norm_num)
    (by simp only [molarity]; norm_num) rfl (by norm_num) (by norm_num)

/-!

## C. Mixture mole fractions

-/

/-- The amounts `1` and `2` of a first two-component solution. -/
def mixN1 : Fin 2 → ℝ := ![1, 2]

/-- The amounts `3` and `4` of a second two-component solution. -/
def mixN2 : Fin 2 → ℝ := ![3, 4]

/-- The total amount of the first solution is `3`. -/
lemma mixN1_sum : ∑ j, mixN1 j = 3 := by
  norm_num [mixN1, Fin.sum_univ_two]

/-- The total amount of the second solution is `7`. -/
lemma mixN2_sum : ∑ j, mixN2 j = 7 := by
  norm_num [mixN2, Fin.sum_univ_two]

/-- The amounts of the first solution are nonnegative. -/
lemma mixN1_nonneg : ∀ i, 0 ≤ mixN1 i := by
  intro i
  fin_cases i <;> norm_num [mixN1]

/-- The mole fractions of the first solution sum to `1`. -/
example : ∑ i, Chemistry.Amounts.moleFraction mixN1 i = 1 :=
  Chemistry.Amounts.sum_moleFraction (by rw [mixN1_sum]; norm_num)

/-- The mole fractions of the first solution are nonnegative. -/
example (i : Fin 2) : 0 ≤ Chemistry.Amounts.moleFraction mixN1 i :=
  Chemistry.Amounts.moleFraction_nonneg mixN1_nonneg i

/-- The algebraic mixing identity, for the stated amount families with totals `3` and `7`. -/
example (i : Fin 2) : Chemistry.Amounts.moleFraction (mixN1 + mixN2) i =
    ((∑ j, mixN1 j) * Chemistry.Amounts.moleFraction mixN1 i +
      (∑ j, mixN2 j) * Chemistry.Amounts.moleFraction mixN2 i) /
      ((∑ j, mixN1 j) + (∑ j, mixN2 j)) :=
  moleFraction_mix mixN1 mixN2 i (by rw [mixN1_sum]; norm_num)
    (by rw [mixN2_sum]; norm_num)

/-- With positive totals `3` and `7` the mixture is a convex combination with weight `3/10`. -/
example (i : Fin 2) : Chemistry.Amounts.moleFraction (mixN1 + mixN2) i =
    3/10 * Chemistry.Amounts.moleFraction mixN1 i +
      (1 - 3/10) * Chemistry.Amounts.moleFraction mixN2 i := by
  obtain ⟨-, -, h⟩ := moleFraction_mix_convex mixN1 mixN2 i
    (by rw [mixN1_sum]; norm_num) (by rw [mixN2_sum]; norm_num)
  rw [h, mixN1_sum, mixN2_sum]
  norm_num

/-- Concretely, the first mixture mole fraction is `(1 + 3) / (3 + 7) = 2/5`. -/
example : Chemistry.Amounts.moleFraction (mixN1 + mixN2) 0 = 2/5 := by
  norm_num [Chemistry.Amounts.moleFraction, Pi.add_apply, mixN1, mixN2, Fin.sum_univ_two]

/-- Counterexample, scenario A: final volume `2` gives mixture molarity `1`. -/
example : molarity (1 + 1) 2 = 1 := by
  simp only [molarity]
  norm_num

/-- Counterexample, scenario B: final volume `3` gives mixture molarity `2/3`. -/
example : molarity (1 + 1) 3 = 2/3 := by
  simp only [molarity]
  norm_num

/-- The two mixture molarities differ although all single-solution data agree. -/
example : molarity (1 + 1) 2 ≠ molarity (1 + 1) 3 := by
  simp only [molarity]
  norm_num

/-!

## D. Temperature change and parts-per-million

-/

/-- Molality is unchanged when amount and solvent mass are unchanged. -/
example : molality (1:ℝ) 5 = molality 1 5 :=
  molality_temp_invariant rfl rfl

/-- Molarity changes when the volume changes from `1` to `2`. -/
example : molarity (1:ℝ) 2 ≠ molarity 1 1 :=
  molarity_temp_ne (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The molarity ratio is the inverse volume ratio: `(1/2)/(1/1) = 1/2`. -/
example : molarity (1:ℝ) 2 / molarity 1 1 = 1/2 :=
  molarity_temp_ratio (by norm_num) (by norm_num) (by norm_num)

/-- The `M` vs `mol/kg` guard: molarity and molality differ already on small numbers. -/
example : molarity (1:ℝ) 2 ≠ molality 1 3 := by
  simp only [molarity, molality]
  norm_num

/-- `ppmByMass` is `10^6` times the mass fraction. -/
example (w : ℝ) : ppmByMass w = 10^6 * w := ppmByMass_eq w

/-- ppm by mass differs from ppm by volume when the solute and solution densities differ: with
solute mass `2` in solution mass `100` (solute density `1`, solution density `2`), ppm by mass
is `20000` while ppm by volume from solute volume `2` in solution volume `50` is `40000`. -/
example : ppmByMass (massFraction 2 100) = 20000 ∧ ppmByVolume 2 50 = 40000 ∧
    ppmByMass (massFraction 2 100) ≠ ppmByVolume 2 50 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [ppmByMass, ppmByVolume, massFraction] <;> norm_num

/-- The mass fraction is `(ρs / ρ)` times the volume fraction at the stated numbers. -/
example : massFraction 2 100 = ((1:ℝ)/2) * (2/50) :=
  massFraction_of_volumes (ρs := 1) (ρ := 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- ppm by mass is `ρs / ρ = 1/2` times ppm by volume at the same numbers. -/
example : ppmByMass (massFraction 2 100) = ((1:ℝ)/2) * ppmByVolume 2 50 :=
  ppmByMass_eq_mul_ppmByVolume (ρs := 1) (ρ := 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)

/-- Equal densities give equal ppm figures even though the density is `2`, not `1`: solute
volume `1` in solution volume `50`, both densities `2`. -/
example : ppmByMass (massFraction 2 100) = ppmByVolume 1 50 :=
  (ppmByMass_eq_ppmByVolume_iff (ρs := 2) (ρ := 2) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)).2 rfl

end PhyslibExtTest.Chemistry.SolutionComposition
