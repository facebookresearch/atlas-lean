/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Chemistry.Amounts.MolarMassComposition

/-!

# Tests for amount of substance, molar mass and composition

-/

@[expose] public section

open Chemistry.Amounts

namespace PhyslibExtTest.Chemistry.Amounts

/-!

## A. Amount of substance

-/

/-- `N = 3 N_A` entities are `3` units of amount of substance, for a symbolic `N_A > 0`. -/
example {N_A : ℝ} (hN_A : 0 < N_A) {N : ℕ} (hN : (N : ℝ) = 3 * N_A) :
    amountOfSubstance N N_A = 3 :=
  (amountOfSubstance_eq_iff N hN_A).mpr hN

example {N_A : ℝ} (hN_A : 0 < N_A) (N : ℕ) : amountOfSubstance N N_A * N_A = N :=
  amountOfSubstance_mul N hN_A

example (N_A : ℝ) :
    amountOfSubstance (2 + 3) N_A = amountOfSubstance 2 N_A + amountOfSubstance 3 N_A :=
  amountOfSubstance_add 2 3 N_A

example {N_A : ℝ} (hN_A : 0 < N_A) : 0 < amountOfSubstance 7 N_A :=
  amountOfSubstance_pos (by norm_num) hN_A

/-- A numeric instance with the illustrative value `N_A = 4`: `12` entities are `3` units. -/
example : amountOfSubstance 12 4 = 3 := by
  rw [amountOfSubstance_eq_iff 12 (by norm_num : (0 : ℝ) < 4)]
  norm_num

/-!

## B. Molar mass of a sample

-/

/-- `36` mass units in `2` units of amount of substance: molar mass `18`. -/
example : molarMass 36 2 two_ne_zero = 18 := by
  rw [molarMass_eq_iff]
  norm_num

example : molarMass 36 2 two_ne_zero * 2 = 36 :=
  molarMass_mul 36 two_ne_zero

example {m n : ℝ} (hm : 0 < m) (hn : 0 < n) : 0 < molarMass m n hn.ne' :=
  molarMass_pos hm hn

/-- Five entities of mass `m₀` each have molar mass `m₀ N_A`. -/
example {m₀ N_A : ℝ} (hN_A : 0 < N_A) :
    molarMass ((5 : ℕ) * m₀) (amountOfSubstance 5 N_A)
      (amountOfSubstance_pos (by norm_num) hN_A).ne' = m₀ * N_A :=
  molarMass_of_entities (by norm_num) hN_A

/-- (e) Boundary case: with zero amount of substance no molar mass reproduces a nonzero mass,
which is why `molarMass` requires `n ≠ 0`. -/
example : ¬ ∃ M : ℝ, (5 : ℝ) = M * 0 := by
  rintro ⟨M, h⟩
  rw [mul_zero] at h
  norm_num at h

/-- (e) Boundary case: Lean's total division answers `5 / 0 = 0`, and that value fails
`m = M n`. -/
example : (5 : ℝ) / 0 = 0 ∧ (5 : ℝ) / 0 * 0 ≠ 5 := by
  norm_num

/-!

## C. Molar mass of a formula

-/

/-- Water `H₂O` over the elements `Fin 2`, with `0 = H` and `1 = O`. -/
def water : Fin 2 → ℕ := ![2, 1]

/-- (a) The molar mass of `H₂O` with symbolic element molar masses `M_H` and `M_O`. -/
lemma formulaMolarMass_water (M_H M_O : ℝ) :
    formulaMolarMass ![M_H, M_O] water = 2 * M_H + M_O := by
  simp [formulaMolarMass, water, Fin.sum_univ_two]

/-- (a) A rational numeric instance, with the illustrative element values `1008/1000` and `16`
(not atomic-weight data). -/
example : formulaMolarMass ![1008 / 1000, 16] water = 18016 / 1000 := by
  rw [formulaMolarMass_water]
  norm_num

/-- Additivity: hydrogen peroxide `H₂O₂` is `H₂O` plus one `O`. -/
example (M_H M_O : ℝ) :
    formulaMolarMass ![M_H, M_O] (water + ![0, 1]) = 2 * M_H + 2 * M_O := by
  rw [formulaMolarMass_add, formulaMolarMass_water]
  simp [formulaMolarMass, Fin.sum_univ_two]
  ring

/-- Homogeneity: three formula units of `H₂O`. -/
example (M_H M_O : ℝ) :
    formulaMolarMass ![M_H, M_O] (3 • water) = 3 * (2 * M_H + M_O) := by
  rw [formulaMolarMass_nsmul, formulaMolarMass_water]
  norm_num

example (M : Fin 2 → ℝ) : formulaMolarMass M 0 = 0 :=
  formulaMolarMass_zero M

example {M_H M_O : ℝ} (hH : 0 < M_H) (hO : 0 < M_O) :
    0 < formulaMolarMass ![M_H, M_O] water :=
  formulaMolarMass_pos (fun e => by fin_cases e <;> simp [hH, hO])
    (Function.ne_iff.mpr ⟨0, by simp [water]⟩)

/-!

## D. Isotope-weighted means

-/

/-- Isotope molar masses `10` and `11` with abundances `1/5` and `4/5`: the mean lies between
`10` and `11`. -/
example : (10 : ℝ) ≤ ∑ i, (![1 / 5, 4 / 5] : Fin 2 → ℝ) i * (![10, 11] : Fin 2 → ℝ) i ∧
    ∑ i, (![1 / 5, 4 / 5] : Fin 2 → ℝ) i * (![10, 11] : Fin 2 → ℝ) i ≤ 11 := by
  have hw₀ : ∀ i, 0 ≤ (![1 / 5, 4 / 5] : Fin 2 → ℝ) i := by
    intro i
    fin_cases i <;> norm_num
  have hw₁ : ∑ i, (![1 / 5, 4 / 5] : Fin 2 → ℝ) i = 1 := by
    norm_num [Fin.sum_univ_two]
  constructor
  · refine le_trans (Finset.le_inf' _ _ fun i _ => ?_) (inf'_le_sum_mul _ hw₀ hw₁)
    fin_cases i <;> norm_num
  · refine le_trans (sum_mul_le_sup' _ hw₀ hw₁) (Finset.sup'_le _ _ fun i _ => ?_)
    fin_cases i <;> norm_num

/-- (e) Boundary case: without `0 ≤ w i` the upper bound fails. The weights `-1` and `2` sum to
`1` but give the mean `12`, above the largest mass `11`. -/
example : ∑ i, (![-1, 2] : Fin 2 → ℝ) i = 1 ∧
    (11 : ℝ) < ∑ i, (![-1, 2] : Fin 2 → ℝ) i * (![10, 11] : Fin 2 → ℝ) i := by
  norm_num [Fin.sum_univ_two]

/-!

## E. Two-isotope abundances

-/

/-- (b) Two isotopes of distinct molar masses `11` and `10` with mean `54/5`: the abundances
are recovered as `4/5` and `1/5`. -/
example {w₁ w₂ : ℝ} (hw : w₁ + w₂ = 1) (hμ : w₁ * 11 + w₂ * 10 = 54 / 5) :
    w₁ = 4 / 5 ∧ w₂ = 1 / 5 := by
  obtain ⟨h₁, h₂⟩ := twoIsotope_weights_eq hw (by norm_num) hμ.symm
  constructor
  · rw [h₁]
    norm_num
  · rw [h₂]
    norm_num

/-- (b) The recovered abundances sum to `1`, reproduce the mean `54/5` and are nonnegative. -/
example : ((54 / 5 : ℝ) - 10) / (11 - 10) + (11 - 54 / 5) / (11 - 10) = 1 ∧
    ((54 / 5 : ℝ) - 10) / (11 - 10) * 11 + (11 - 54 / 5) / (11 - 10) * 10 = 54 / 5 :=
  twoIsotope_mean_of_weights (54 / 5) (by norm_num)

example : 0 ≤ ((54 / 5 : ℝ) - 10) / (11 - 10) ∧ 0 ≤ (11 - (54 / 5 : ℝ)) / (11 - 10) :=
  twoIsotope_weights_nonneg (by norm_num) (by norm_num) (by norm_num)

/-- (b) Any abundances with the same mean as `4/5, 1/5` are `4/5, 1/5`. -/
example {w₁ w₂ : ℝ} (hw : w₁ + w₂ = 1) (hμ : w₁ * 11 + w₂ * 10 = 4 / 5 * 11 + 1 / 5 * 10) :
    w₁ = 4 / 5 ∧ w₂ = 1 / 5 :=
  twoIsotope_weights_unique hw (by norm_num) (by norm_num) hμ

/-- (e) Boundary case: with equal isotope masses the mean does not determine the
abundances. -/
example : ∃ w₁ w₂ v₁ v₂ : ℝ, w₁ + w₂ = 1 ∧ v₁ + v₂ = 1 ∧
    w₁ * 10 + w₂ * 10 = v₁ * 10 + v₂ * 10 ∧ w₁ ≠ v₁ :=
  ⟨1, 0, 0, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-!

## F. Empirical formulas

-/

/-- (c) The mole ratios `1/2 : 1/3` have the empirical formula `3 : 2`. -/
lemma empiricalFormula_half_third :
    empiricalFormula (![1 / 2, 1 / 3] : Fin 2 → ℚ) = ![3, 2] := by
  refine (eq_empiricalFormula (c := 6) (fun e => ?_) ?_ ?_ fun e => ?_).symm
  · fin_cases e <;> norm_num
  · exact Function.ne_iff.mpr ⟨0, by norm_num⟩
  · decide
  · fin_cases e <;> norm_num

/-- (c) The empirical formula `3 : 2` is primitive. -/
example : Finset.univ.gcd (empiricalFormula (![1 / 2, 1 / 3] : Fin 2 → ℚ)) = 1 :=
  gcd_empiricalFormula (fun e => by fin_cases e <;> norm_num)
    (Function.ne_iff.mpr ⟨0, by norm_num⟩)

/-- (c) The mole ratios `6 : 12 : 6` of glucose over `C, H, O` have the empirical formula
`CH₂O`. -/
lemma empiricalFormula_glucose :
    empiricalFormula (![6, 12, 6] : Fin 3 → ℚ) = ![1, 2, 1] := by
  refine (eq_empiricalFormula (c := 1 / 6) (fun e => ?_) ?_ ?_ fun e => ?_).symm
  · fin_cases e <;> norm_num
  · exact Function.ne_iff.mpr ⟨0, by norm_num⟩
  · decide
  · fin_cases e <;> norm_num

example : ∃! p : Fin 2 → ℕ, Finset.univ.gcd p = 1 ∧ p ≠ 0 ∧
    ∃ c > 0, ∀ e, (p e : ℚ) = c * (![1 / 2, 1 / 3] : Fin 2 → ℚ) e :=
  existsUnique_primitive_proportional _ (fun e => by fin_cases e <;> norm_num)
    (Function.ne_iff.mpr ⟨0, by norm_num⟩)

/-- Without the gcd normalization the proportional vector is not unique: `6 : 4` is also
proportional to `1/2 : 1/3`, but its entries have greatest common divisor `2`. -/
example : (∀ e, ((![6, 4] : Fin 2 → ℕ) e : ℚ) = 12 * (![1 / 2, 1 / 3] : Fin 2 → ℚ) e) ∧
    Finset.univ.gcd (![6, 4] : Fin 2 → ℕ) = 2 := by
  refine ⟨fun e => ?_, by decide⟩
  fin_cases e <;> norm_num

/-- (e) Boundary case: the zero vector of ratios, excluded by `r ≠ 0`, has no primitive
proportional formula vector. -/
example : ¬ ∃ p : Fin 2 → ℕ, Finset.univ.gcd p = 1 ∧
    ∃ c > 0, ∀ e, (p e : ℚ) = c * (0 : Fin 2 → ℚ) e := by
  rintro ⟨p, hp, c, -, hc⟩
  refine ne_zero_of_gcd_eq_one hp (funext fun e => ?_)
  have h := hc e
  simp only [Pi.zero_apply, mul_zero, Nat.cast_eq_zero] at h
  exact h

/-- (e) Boundary case: a negative ratio, excluded by `0 ≤ r e`, has no proportional formula
vector with a positive factor. -/
example : ¬ ∃ p : Fin 2 → ℕ, ∃ c > 0, ∀ e, (p e : ℚ) = c * (![-1, 1] : Fin 2 → ℚ) e := by
  rintro ⟨p, c, hc, h⟩
  have h0 := h 0
  simp only [Matrix.cons_val_zero, mul_neg, mul_one] at h0
  have hp0 : (0 : ℚ) ≤ p 0 := Nat.cast_nonneg _
  rw [h0, neg_nonneg] at hp0
  exact absurd hc (not_lt.mpr hp0)

/-!

## G. Molecular formulas

-/

/-- The empirical formula `CH₂O` over `Fin 3`, with `0 = C`, `1 = H` and `2 = O`. -/
def ch2o : Fin 3 → ℕ := ![1, 2, 1]

/-- `CH₂O` is primitive. -/
lemma gcd_ch2o : Finset.univ.gcd ch2o = 1 := by
  decide

/-- The molar mass of `CH₂O` with symbolic element molar masses `M_C`, `M_H` and `M_O`. -/
lemma formulaMolarMass_ch2o (M_C M_H M_O : ℝ) :
    formulaMolarMass ![M_C, M_H, M_O] ch2o = M_C + 2 * M_H + M_O := by
  simp [formulaMolarMass, ch2o, Fin.sum_univ_three]

/-- A formula vector proportional to `CH₂O` with six times its molar mass is `C₆H₁₂O₆`, for
symbolic element molar masses. -/
example {M_C M_H M_O : ℝ} (hpos : 0 < M_C + 2 * M_H + M_O) {ν : Fin 3 → ℕ} {c : ℚ}
    (hν : ∀ e, (ν e : ℚ) = c * ch2o e)
    (hM : formulaMolarMass ![M_C, M_H, M_O] ν = 6 * (M_C + 2 * M_H + M_O)) :
    ν = ![6, 12, 6] := by
  rw [eq_nsmul_of_formulaMolarMass_eq (k := 6) gcd_ch2o hν (formulaMolarMass_ch2o M_C M_H M_O)
    hpos hM (by norm_num)]
  decide

/-- With the illustrative element values `12`, `1` and `16`, `CH₂O` has molar mass `30`, and a
compound of molar mass `180` with empirical formula `CH₂O` is `C₆H₁₂O₆`. -/
example {ν : Fin 3 → ℕ} (hν : ν ≠ 0) (hp : empiricalFormula (fun e => (ν e : ℚ)) = ch2o)
    (hM : formulaMolarMass ![12, 1, 16] ν = 180) : ν = ![6, 12, 6] := by
  rw [eq_nsmul_of_empiricalFormula_eq (k := 6) hν hp (formulaMolarMass_ch2o 12 1 16)
    (by norm_num) hM (by norm_num)]
  decide

/-- Conversely, `6 • CH₂O` has molar mass `180`, and `6` is the consistency ratio
`180 / 30`. -/
example : formulaMolarMass ![12, 1, 16] (6 • ch2o) = 180 ∧
    ((6 : ℕ) : ℝ) = 180 / (12 + 2 * 1 + 16) := by
  have hM : formulaMolarMass ![12, 1, 16] (6 • ch2o) = 180 := by
    rw [formulaMolarMass_nsmul, formulaMolarMass_ch2o]
    norm_num
  exact ⟨hM, (formulaMolarMass_nsmul_consistency (formulaMolarMass_ch2o 12 1 16)
    (by norm_num) hM).2⟩

/-- The molecular formula `6 • CH₂O` is primitive-scaled: its gcd is `6`, and its empirical
formula is `CH₂O`. -/
example : Finset.univ.gcd (6 • ch2o) = 6 ∧
    empiricalFormula (fun e => ((6 • ch2o) e : ℚ)) = ch2o :=
  ⟨gcd_nsmul_of_gcd_eq_one gcd_ch2o 6, empiricalFormula_nsmul gcd_ch2o (by norm_num)⟩

/-- With the illustrative element values `12`, `1` and `16`, a compound of positive molar mass
`180 = 6 * 30` with empirical formula `CH₂O` has the positive integer ratio `6` and is
`6 • CH₂O`. -/
example {ν : Fin 3 → ℕ} (hν : ν ≠ 0) (hp : empiricalFormula (fun e => (ν e : ℚ)) = ch2o)
    (hM : formulaMolarMass ![12, 1, 16] ν = 180) : 0 < 6 ∧ ν = 6 • ch2o :=
  eq_nsmul_of_formulaMolarMass_eq_pos hν hp (formulaMolarMass_ch2o 12 1 16) (by norm_num)
    (by norm_num) hM (by norm_num)

/-- Conversely, with positive molar masses, `6 • CH₂O` of molar mass `180` has the positive
consistency ratio `6 = 180 / 30`. -/
example : 0 < 6 ∧ (180 : ℝ) = (6 : ℕ) * (12 + 2 * 1 + 16) ∧
    ((6 : ℕ) : ℝ) = 180 / (12 + 2 * 1 + 16) :=
  formulaMolarMass_nsmul_consistency_pos (formulaMolarMass_ch2o 12 1 16) (by norm_num)
    (by norm_num) (by rw [formulaMolarMass_nsmul, formulaMolarMass_ch2o]; norm_num)

/-- (e) Boundary case: the degenerate ratio `k = 0`. For one element of molar mass `1`,
`p = [1]` and `ν = [0]`, the molar mass `M = 0` satisfies `M = 0 * M_emp` but not the
hypothesis `0 < M` of `eq_nsmul_of_formulaMolarMass_eq_pos` and
`formulaMolarMass_nsmul_consistency_pos`. -/
example : formulaMolarMass ![1] (![0] : Fin 1 → ℕ) = (0 : ℕ) * formulaMolarMass ![1] ![1] ∧
    ¬ 0 < formulaMolarMass ![1] (![0] : Fin 1 → ℕ) := by
  simp [formulaMolarMass]

/-- (e) Boundary case: `M / M_emp` need not be an integer. For `M = 45` and `M_emp = 30` no
natural number `k` satisfies `M = k * M_emp`. -/
example : ¬ ∃ k : ℕ, (45 : ℝ) = k * 30 := by
  rintro ⟨k, hk⟩
  have h : (45 : ℕ) = k * 30 := by exact_mod_cast hk
  omega

/-!

## H. Mole fractions and mass fractions

-/

/-- The amounts `1` and `3` of a two-component mixture. -/
def mixAmounts : Fin 2 → ℝ := ![1, 3]

/-- Illustrative molar masses `2` and `32` of the two components. -/
def mixMolarMasses : Fin 2 → ℝ := ![2, 32]

/-- The amounts of the mixture are nonnegative. -/
lemma mixAmounts_nonneg : ∀ i, 0 ≤ mixAmounts i := by
  intro i
  fin_cases i <;> norm_num [mixAmounts]

/-- The total amount of the mixture is positive. -/
lemma mixAmounts_sum_pos : 0 < ∑ i, mixAmounts i := by
  norm_num [mixAmounts, Fin.sum_univ_two]

/-- The molar masses of the components are positive. -/
lemma mixMolarMasses_pos : ∀ i, 0 < mixMolarMasses i := by
  intro i
  fin_cases i <;> norm_num [mixMolarMasses]

/-- (d) The mole fractions are `1/4` and `3/4`. -/
example : moleFraction mixAmounts = ![1 / 4, 3 / 4] := by
  funext i
  fin_cases i <;> norm_num [moleFraction, mixAmounts, Fin.sum_univ_two]

/-- (d) The mass fractions are `2/98 = 1/49` and `96/98 = 48/49`. -/
example : massFraction mixMolarMasses mixAmounts = ![1 / 49, 48 / 49] := by
  funext i
  fin_cases i <;> norm_num [massFraction, mixAmounts, mixMolarMasses, Fin.sum_univ_two]

/-- (d) The mass fractions sum to `1`. -/
example : ∑ i, massFraction mixMolarMasses mixAmounts i = 1 :=
  sum_massFraction mixAmounts_nonneg mixAmounts_sum_pos mixMolarMasses_pos

/-- (d) The mole fractions sum to `1`. -/
example : ∑ i, moleFraction mixAmounts i = 1 :=
  sum_moleFraction mixAmounts_sum_pos

example (i : Fin 2) :
    0 ≤ moleFraction mixAmounts i ∧ 0 ≤ massFraction mixMolarMasses mixAmounts i :=
  ⟨moleFraction_nonneg mixAmounts_nonneg i,
    massFraction_nonneg mixAmounts_nonneg mixMolarMasses_pos i⟩

example : massFraction mixMolarMasses (moleFraction mixAmounts) =
    massFraction mixMolarMasses mixAmounts :=
  massFraction_moleFraction mixMolarMasses mixAmounts_sum_pos

example : moleFractionOfMassFraction mixMolarMasses (massFraction mixMolarMasses mixAmounts) =
    moleFraction mixAmounts :=
  moleFractionOfMassFraction_massFraction mixAmounts_nonneg mixAmounts_sum_pos mixMolarMasses_pos

/-- (d) Round trip from the mole fractions `1/4, 3/4` through mass fractions. -/
example : moleFractionOfMassFraction mixMolarMasses (massFraction mixMolarMasses ![1 / 4, 3 / 4]) =
    ![1 / 4, 3 / 4] :=
  moleFractionOfMassFraction_massFraction_of_sum_eq_one (fun i => by fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_two]) mixMolarMasses_pos

/-- (d) Round trip from the mass fractions `1/49, 48/49` through mole fractions. -/
example : massFraction mixMolarMasses
    (moleFractionOfMassFraction mixMolarMasses ![1 / 49, 48 / 49]) = ![1 / 49, 48 / 49] :=
  massFraction_moleFractionOfMassFraction_of_sum_eq_one (fun i => by fin_cases i <;> norm_num)
    (by norm_num [Fin.sum_univ_two]) mixMolarMasses_pos

/-- (d) Concretely, the mass fractions `1/49, 48/49` convert to the mole fractions
`1/4, 3/4`. -/
example : moleFractionOfMassFraction mixMolarMasses ![1 / 49, 48 / 49] = ![1 / 4, 3 / 4] := by
  funext i
  fin_cases i <;>
    norm_num [moleFractionOfMassFraction, moleFraction, mixMolarMasses, Fin.sum_univ_two]

/-- (e) Boundary case: with zero total amount the mole fractions sum to `0`, not `1`. -/
example : ∑ i, moleFraction (0 : Fin 2 → ℝ) i = 0 := by
  simp [moleFraction]

end PhyslibExtTest.Chemistry.Amounts

#print axioms Chemistry.Amounts.amountOfSubstance
#print axioms Chemistry.Amounts.amountOfSubstance_mul
#print axioms Chemistry.Amounts.amountOfSubstance_eq_iff
#print axioms Chemistry.Amounts.amountOfSubstance_add
#print axioms Chemistry.Amounts.amountOfSubstance_pos
#print axioms Chemistry.Amounts.molarMass
#print axioms Chemistry.Amounts.molarMass_mul
#print axioms Chemistry.Amounts.molarMass_eq_iff
#print axioms Chemistry.Amounts.molarMass_pos
#print axioms Chemistry.Amounts.molarMass_of_entities
#print axioms Chemistry.Amounts.formulaMolarMass
#print axioms Chemistry.Amounts.formulaMolarMass_zero
#print axioms Chemistry.Amounts.formulaMolarMass_add
#print axioms Chemistry.Amounts.formulaMolarMass_nsmul
#print axioms Chemistry.Amounts.formulaMolarMass_pos
#print axioms Chemistry.Amounts.inf'_le_sum_mul
#print axioms Chemistry.Amounts.sum_mul_le_sup'
#print axioms Chemistry.Amounts.twoIsotope_weights_eq
#print axioms Chemistry.Amounts.twoIsotope_weights_unique
#print axioms Chemistry.Amounts.twoIsotope_mean_of_weights
#print axioms Chemistry.Amounts.twoIsotope_weights_nonneg
#print axioms Chemistry.Amounts.commonDenominator
#print axioms Chemistry.Amounts.clearDenominators
#print axioms Chemistry.Amounts.empiricalFormula
#print axioms Chemistry.Amounts.commonDenominator_pos
#print axioms Chemistry.Amounts.den_dvd_commonDenominator
#print axioms Chemistry.Amounts.clearDenominators_cast
#print axioms Chemistry.Amounts.exists_clearDenominators_ne_zero
#print axioms Chemistry.Amounts.gcd_empiricalFormula
#print axioms Chemistry.Amounts.empiricalFormula_proportional
#print axioms Chemistry.Amounts.mul_eq_mul_of_proportional
#print axioms Chemistry.Amounts.gcd_mul_eq_mul_gcd
#print axioms Chemistry.Amounts.eq_of_proportional
#print axioms Chemistry.Amounts.eq_empiricalFormula
#print axioms Chemistry.Amounts.ne_zero_of_gcd_eq_one
#print axioms Chemistry.Amounts.existsUnique_primitive_proportional
#print axioms Chemistry.Amounts.gcd_nsmul_of_gcd_eq_one
#print axioms Chemistry.Amounts.empiricalFormula_nsmul
#print axioms Chemistry.Amounts.eq_nsmul_of_formulaMolarMass_eq
#print axioms Chemistry.Amounts.eq_nsmul_of_empiricalFormula_eq
#print axioms Chemistry.Amounts.formulaMolarMass_nsmul_consistency
#print axioms Chemistry.Amounts.eq_nsmul_of_formulaMolarMass_eq_pos
#print axioms Chemistry.Amounts.formulaMolarMass_nsmul_consistency_pos
#print axioms Chemistry.Amounts.moleFraction
#print axioms Chemistry.Amounts.massFraction
#print axioms Chemistry.Amounts.moleFractionOfMassFraction
#print axioms Chemistry.Amounts.sum_amount_mul_molarMass_pos
#print axioms Chemistry.Amounts.moleFraction_nonneg
#print axioms Chemistry.Amounts.sum_moleFraction
#print axioms Chemistry.Amounts.massFraction_nonneg
#print axioms Chemistry.Amounts.sum_massFraction
#print axioms Chemistry.Amounts.massFraction_moleFraction
#print axioms Chemistry.Amounts.moleFractionOfMassFraction_massFraction
#print axioms Chemistry.Amounts.moleFractionOfMassFraction_massFraction_of_sum_eq_one
#print axioms Chemistry.Amounts.massFraction_moleFractionOfMassFraction_of_sum_eq_one
#print axioms PhyslibExtTest.Chemistry.Amounts.formulaMolarMass_water
#print axioms PhyslibExtTest.Chemistry.Amounts.empiricalFormula_half_third
#print axioms PhyslibExtTest.Chemistry.Amounts.empiricalFormula_glucose
#print axioms PhyslibExtTest.Chemistry.Amounts.gcd_ch2o
#print axioms PhyslibExtTest.Chemistry.Amounts.formulaMolarMass_ch2o
#print axioms PhyslibExtTest.Chemistry.Amounts.mixAmounts_nonneg
#print axioms PhyslibExtTest.Chemistry.Amounts.mixAmounts_sum_pos
#print axioms PhyslibExtTest.Chemistry.Amounts.mixMolarMasses_pos
#print axioms PhyslibExtTest.Chemistry.Amounts.water
#print axioms PhyslibExtTest.Chemistry.Amounts.ch2o
#print axioms PhyslibExtTest.Chemistry.Amounts.mixAmounts
#print axioms PhyslibExtTest.Chemistry.Amounts.mixMolarMasses
