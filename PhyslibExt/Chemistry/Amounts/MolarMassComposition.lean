/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Cast.Field
/-!

# Amount of substance, molar mass and composition

Amounts of substance, molar masses of samples and formulas, isotope-weighted means, empirical and
molecular formulas, and the conversion between mole fractions and mass fractions.

## i. Overview

All quantities are numerical values after a consistent choice of units: real numbers, except
mole ratios, which are rational numbers. Dimensions are not tracked.

The amount of substance of a sample of `N` entities is `n = N / N_A`. The Avogadro constant `N_A`
is a parameter and the results assume only `0 < N_A`; no numerical value is fixed. The molar mass
of a sample of mass `m` and amount `n` is `M = m / n`. Its definition takes a proof of `n ≠ 0` as
an argument, so Lean's convention `m / 0 = 0` never supplies a molar mass for an empty sample.

A formula is a vector `ν : E → ℕ` of subscripts over a finite type `E` of elements. For element
molar masses `M : E → ℝ` its molar mass is `∑ e, ν e * M e`. This is additive in `ν` and
homogeneous under scaling by natural numbers. Formula vectors have no negative entries, and
nothing is claimed about negative scalings.

For isotope molar masses `m` and abundances `w i ≥ 0` with `∑ i, w i = 1`, the mean
`∑ i, w i * m i` lies between the smallest and the largest `m i`. For two isotopes of distinct
masses the mean determines both abundances, by explicit formulas.

Empirical formulas are computed from mole ratios `r : E → ℚ`. The ratios are assumed to be exact
rational numbers, nonnegative and not all zero. The zero vector is excluded by hypothesis: no
primitive vector is proportional to it. Measured ratios are approximate; turning them into exact
rational numbers needs a rounding rule, which is out of scope here. The normalization clears
denominators, multiplying by the least common multiple `D` of the denominators, and divides the
resulting natural numbers by their greatest common divisor. The result is the unique primitive
vector (entries with greatest common divisor `1`) proportional to `r` with a positive factor.

A molecular formula with primitive empirical formula `p` is `k • p`, where the natural number `k`
satisfies `M = k * M_emp` for the molar mass `M` of the compound and the molar mass `M_emp` of
`p`. The integer `k` is a hypothesis, a consistency check on the data: nothing here claims that
`M / M_emp` is an integer for a measured `M`.

The mole fractions of a mixture are `x i = n i / ∑ j, n j` and its mass fractions are
`w i = n i * M i / ∑ j, n j * M j`, for amounts `n i ≥ 0` with `∑ i, n i > 0` (absent components
are allowed) and molar masses `M i > 0`. Both sum to `1`, and on the simplex of fractions the
conversions between mole fractions and mass fractions are mutually inverse.

The results are algebraic. They do not provide dimensional quantities, atomic-weight data or
measured intervals, combustion analysis, reaction stoichiometry, or significant-figure rules.

## ii. Key results

- `amountOfSubstance` : the amount of substance `N / N_A`.
- `molarMass` : the molar mass `m / n` of a sample, for `n ≠ 0`.
- `formulaMolarMass` : the molar mass `∑ e, ν e * M e` of a formula.
- `formulaMolarMass_add`, `formulaMolarMass_nsmul` : the molar mass of a formula is additive and
  homogeneous over `ℕ`.
- `inf'_le_sum_mul`, `sum_mul_le_sup'` : an isotope-weighted mean lies between the smallest and
  the largest isotope molar mass.
- `twoIsotope_weights_eq`, `twoIsotope_weights_unique` : for two isotopes of distinct masses the
  mean determines the abundances.
- `empiricalFormula` : clearing denominators, then dividing by the greatest common divisor.
- `existsUnique_primitive_proportional` : nonzero nonnegative rational mole ratios have exactly
  one primitive proportional formula vector.
- `eq_nsmul_of_formulaMolarMass_eq_pos` : the source-facing statement. For positive molar masses
  with `M = k * M_emp`, the ratio `k` is a positive integer and the molecular formula is `k • p`.
- `eq_nsmul_of_formulaMolarMass_eq`, `eq_nsmul_of_empiricalFormula_eq` : the molecular formula
  is `k • p` when `M = k * M_emp`.
- `gcd_nsmul_of_gcd_eq_one`, `empiricalFormula_nsmul` : the molecular formula `k • p` has
  greatest common divisor `k` and empirical formula `p`.
- `formulaMolarMass_nsmul_consistency` : conversely, `k • p` has `M = k * M_emp`, so
  `k = M / M_emp`.
- `formulaMolarMass_nsmul_consistency_pos` : for positive molar masses, the ratio `k = M / M_emp`
  of `k • p` is moreover a positive integer.
- `sum_moleFraction`, `sum_massFraction` : mole fractions and mass fractions sum to `1`.
- `moleFractionOfMassFraction_massFraction_of_sum_eq_one`,
  `massFraction_moleFractionOfMassFraction_of_sum_eq_one` : on the simplex, the conversions
  between mole fractions and mass fractions are mutually inverse.

## iii. Table of contents

- A. Amount of substance
- B. Molar mass of a sample
- C. Molar mass of a formula
- D. Isotope-weighted means
- E. Two-isotope abundances
- F. Empirical formulas
- G. Molecular formulas
- H. Mole fractions and mass fractions

## iv. References

- OpenStax, *Chemistry 2e*, Chapter 3, "Composition of Substances and Solutions".
- OpenStax, *Chemistry 2e*, §3.1, "Formula Mass and the Mole Concept".
- OpenStax, *Chemistry 2e*, §3.2, "Determining Empirical and Molecular Formulas".
- IUPAC, *Quantities, Units and Symbols in Physical Chemistry* (the Green Book), for the
  symbols `n` (amount of substance), `M` (molar mass) and `N_A` (Avogadro constant).

-/

@[expose] public section

namespace Chemistry.Amounts

/-!

## A. Amount of substance

-/

/-- The amount of substance `n = N / N_A` of a sample of `N` specified entities, where `N_A` is
the Avogadro constant. `N_A` is a parameter: no numerical value is fixed, and the results below
assume only `0 < N_A`. -/
noncomputable def amountOfSubstance (N : ℕ) (N_A : ℝ) : ℝ :=
  N / N_A

/-- `N = n N_A`: the number of entities is the amount of substance times the Avogadro
constant. -/
lemma amountOfSubstance_mul (N : ℕ) {N_A : ℝ} (hN_A : 0 < N_A) :
    amountOfSubstance N N_A * N_A = N :=
  div_mul_cancel₀ _ hN_A.ne'

/-- The amount of substance of `N` entities is the unique `n` with `N = n N_A`. -/
lemma amountOfSubstance_eq_iff (N : ℕ) {N_A n : ℝ} (hN_A : 0 < N_A) :
    amountOfSubstance N N_A = n ↔ (N : ℝ) = n * N_A :=
  div_eq_iff hN_A.ne'

/-- Amounts of substance add when two samples of the same entity are combined. -/
lemma amountOfSubstance_add (N₁ N₂ : ℕ) (N_A : ℝ) :
    amountOfSubstance (N₁ + N₂) N_A = amountOfSubstance N₁ N_A + amountOfSubstance N₂ N_A := by
  rw [amountOfSubstance, amountOfSubstance, amountOfSubstance, Nat.cast_add, add_div]

/-- A sample of at least one entity has a positive amount of substance. -/
lemma amountOfSubstance_pos {N : ℕ} {N_A : ℝ} (hN : 0 < N) (hN_A : 0 < N_A) :
    0 < amountOfSubstance N N_A :=
  div_pos (Nat.cast_pos.mpr hN) hN_A

/-!

## B. Molar mass of a sample

-/

/-- The molar mass `M = m / n` of a sample of mass `m` and amount of substance `n`. The
hypothesis `n ≠ 0` is an argument, so no molar mass is formed for an empty sample and Lean's
convention `m / 0 = 0` cannot supply one. -/
noncomputable def molarMass (m n : ℝ) (_hn : n ≠ 0) : ℝ :=
  m / n

/-- `m = M n`: the mass is the molar mass times the amount of substance. -/
lemma molarMass_mul (m : ℝ) {n : ℝ} (hn : n ≠ 0) : molarMass m n hn * n = m :=
  div_mul_cancel₀ m hn

/-- The molar mass is the unique `M` with `m = M n`. -/
lemma molarMass_eq_iff {m n M : ℝ} (hn : n ≠ 0) : molarMass m n hn = M ↔ m = M * n :=
  div_eq_iff hn

/-- A sample of positive mass and positive amount of substance has a positive molar mass. -/
lemma molarMass_pos {m n : ℝ} (hm : 0 < m) (hn : 0 < n) : 0 < molarMass m n hn.ne' :=
  div_pos hm hn

/-- A sample of `N > 0` entities, each of mass `m₀`, has molar mass `M = m₀ N_A`. -/
lemma molarMass_of_entities {N : ℕ} {m₀ N_A : ℝ} (hN : 0 < N) (hN_A : 0 < N_A) :
    molarMass (N * m₀) (amountOfSubstance N N_A) (amountOfSubstance_pos hN hN_A).ne' =
      m₀ * N_A := by
  have hN_A' : N_A ≠ 0 := hN_A.ne'
  rw [molarMass_eq_iff, amountOfSubstance]
  field_simp

/-!

## C. Molar mass of a formula

-/

/-- The molar mass `M(ν) = ∑ e, ν e * M e` of the formula with subscripts `ν : E → ℕ`, where `E`
is a finite type of elements and `M e` is the molar mass of the element `e`. -/
def formulaMolarMass {E : Type*} [Fintype E] (M : E → ℝ) (ν : E → ℕ) : ℝ :=
  ∑ e, (ν e : ℝ) * M e

/-- The empty formula has molar mass `0`. -/
lemma formulaMolarMass_zero {E : Type*} [Fintype E] (M : E → ℝ) : formulaMolarMass M 0 = 0 := by
  simp [formulaMolarMass]

/-- The molar mass of a formula is additive in the formula vector. -/
lemma formulaMolarMass_add {E : Type*} [Fintype E] (M : E → ℝ) (ν₁ ν₂ : E → ℕ) :
    formulaMolarMass M (ν₁ + ν₂) = formulaMolarMass M ν₁ + formulaMolarMass M ν₂ := by
  simp only [formulaMolarMass, Pi.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib]

/-- The molar mass of a formula is homogeneous under scaling the formula vector by a natural
number. -/
lemma formulaMolarMass_nsmul {E : Type*} [Fintype E] (M : E → ℝ) (k : ℕ) (ν : E → ℕ) :
    formulaMolarMass M (k • ν) = k * formulaMolarMass M ν := by
  simp only [formulaMolarMass, Pi.smul_apply, smul_eq_mul, Nat.cast_mul, Finset.mul_sum,
    mul_assoc]

/-- A nonzero formula has a positive molar mass when every element has a positive molar
mass. -/
lemma formulaMolarMass_pos {E : Type*} [Fintype E] {M : E → ℝ} {ν : E → ℕ}
    (hM : ∀ e, 0 < M e) (hν : ν ≠ 0) : 0 < formulaMolarMass M ν := by
  obtain ⟨e, he⟩ := Function.ne_iff.mp hν
  exact Finset.sum_pos' (fun i _ => mul_nonneg (Nat.cast_nonneg _) (hM i).le)
    ⟨e, Finset.mem_univ e, mul_pos (Nat.cast_pos.mpr (Nat.pos_of_ne_zero he)) (hM e)⟩

/-!

## D. Isotope-weighted means

-/

/-- For abundances `w i ≥ 0` with `∑ i, w i = 1`, the isotope-weighted mean `∑ i, w i * m i` of
the isotope molar masses `m` is at least the smallest of them. This is
`Finset.inf_le_centerMass` for normalized weights. -/
lemma inf'_le_sum_mul {ι : Type*} [Fintype ι] [Nonempty ι] {w : ι → ℝ} (m : ι → ℝ)
    (hw₀ : ∀ i, 0 ≤ w i) (hw₁ : ∑ i, w i = 1) :
    Finset.univ.inf' Finset.univ_nonempty m ≤ ∑ i, w i * m i := by
  have h := Finset.inf_le_centerMass (s := Finset.univ) (f := m) (fun i _ => hw₀ i)
    (by rw [hw₁]; exact one_pos)
  rw [Finset.centerMass_eq_of_sum_1 _ _ hw₁] at h
  simpa only [smul_eq_mul] using h

/-- For abundances `w i ≥ 0` with `∑ i, w i = 1`, the isotope-weighted mean `∑ i, w i * m i` of
the isotope molar masses `m` is at most the largest of them. This is
`Finset.centerMass_le_sup` for normalized weights. -/
lemma sum_mul_le_sup' {ι : Type*} [Fintype ι] [Nonempty ι] {w : ι → ℝ} (m : ι → ℝ)
    (hw₀ : ∀ i, 0 ≤ w i) (hw₁ : ∑ i, w i = 1) :
    ∑ i, w i * m i ≤ Finset.univ.sup' Finset.univ_nonempty m := by
  have h := Finset.centerMass_le_sup (s := Finset.univ) (f := m) (fun i _ => hw₀ i)
    (by rw [hw₁]; exact one_pos)
  rw [Finset.centerMass_eq_of_sum_1 _ _ hw₁] at h
  simpa only [smul_eq_mul] using h

/-!

## E. Two-isotope abundances

-/

/-- For two isotopes of distinct molar masses `m₁ ≠ m₂` and abundances with `w₁ + w₂ = 1`, the
mean `μ = w₁ * m₁ + w₂ * m₂` determines `w₁ = (μ - m₂) / (m₁ - m₂)` and
`w₂ = (m₁ - μ) / (m₁ - m₂)`. Nonnegativity of the abundances is not needed. -/
lemma twoIsotope_weights_eq {w₁ w₂ m₁ m₂ μ : ℝ} (hw : w₁ + w₂ = 1) (hm : m₁ ≠ m₂)
    (hμ : μ = w₁ * m₁ + w₂ * m₂) :
    w₁ = (μ - m₂) / (m₁ - m₂) ∧ w₂ = (m₁ - μ) / (m₁ - m₂) := by
  have hd : m₁ - m₂ ≠ 0 := sub_ne_zero.mpr hm
  subst hμ
  constructor
  · rw [eq_div_iff hd]
    linear_combination (-m₂) * hw
  · rw [eq_div_iff hd]
    linear_combination m₁ * hw

/-- Two pairs of abundances, each summing to `1`, that give the same mean for two isotopes of
distinct molar masses are equal. -/
lemma twoIsotope_weights_unique {w₁ w₂ v₁ v₂ m₁ m₂ : ℝ} (hw : w₁ + w₂ = 1) (hv : v₁ + v₂ = 1)
    (hm : m₁ ≠ m₂) (hμ : w₁ * m₁ + w₂ * m₂ = v₁ * m₁ + v₂ * m₂) :
    w₁ = v₁ ∧ w₂ = v₂ := by
  obtain ⟨hw₁, hw₂⟩ := twoIsotope_weights_eq hw hm hμ.symm
  obtain ⟨hv₁, hv₂⟩ := twoIsotope_weights_eq hv hm rfl
  exact ⟨hw₁.trans hv₁.symm, hw₂.trans hv₂.symm⟩

/-- For two isotopes of distinct molar masses and any `μ`, the abundances
`(μ - m₂) / (m₁ - m₂)` and `(m₁ - μ) / (m₁ - m₂)` sum to `1` and have mean `μ`. -/
lemma twoIsotope_mean_of_weights {m₁ m₂ : ℝ} (μ : ℝ) (hm : m₁ ≠ m₂) :
    (μ - m₂) / (m₁ - m₂) + (m₁ - μ) / (m₁ - m₂) = 1 ∧
      (μ - m₂) / (m₁ - m₂) * m₁ + (m₁ - μ) / (m₁ - m₂) * m₂ = μ := by
  have hd : m₁ - m₂ ≠ 0 := sub_ne_zero.mpr hm
  constructor
  · rw [← add_div, div_eq_one_iff_eq hd]
    ring
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, div_eq_iff hd]
    ring

/-- The abundances recovered from a mean `μ` with `m₂ ≤ μ ≤ m₁` and `m₂ < m₁` are
nonnegative. -/
lemma twoIsotope_weights_nonneg {m₁ m₂ μ : ℝ} (hm : m₂ < m₁) (h₂ : m₂ ≤ μ) (h₁ : μ ≤ m₁) :
    0 ≤ (μ - m₂) / (m₁ - m₂) ∧ 0 ≤ (m₁ - μ) / (m₁ - m₂) :=
  ⟨div_nonneg (sub_nonneg.mpr h₂) (sub_nonneg.mpr hm.le),
    div_nonneg (sub_nonneg.mpr h₁) (sub_nonneg.mpr hm.le)⟩

/-!

## F. Empirical formulas

-/

/-- The least common denominator `D` of the mole ratios `r`: the least common multiple of the
denominators of the `r e` in lowest terms. -/
def commonDenominator {E : Type*} [Fintype E] (r : E → ℚ) : ℕ :=
  Finset.univ.lcm fun e => (r e).den

/-- Clearing denominators of nonnegative ratios: for `r e = a / b ≥ 0` in lowest terms, the
natural number `a * (D / b)`, where `D = commonDenominator r`; it equals `D * r e`
(`clearDenominators_cast`). A negative ratio, which the results below exclude by hypothesis, has
`a.toNat = 0` and is sent to `0`. -/
def clearDenominators {E : Type*} [Fintype E] (r : E → ℚ) (e : E) : ℕ :=
  (r e).num.toNat * (commonDenominator r / (r e).den)

/-- The empirical formula of the nonnegative mole ratios `r`: clear denominators, then divide
every entry by the greatest common divisor of all the entries. -/
def empiricalFormula {E : Type*} [Fintype E] (r : E → ℚ) (e : E) : ℕ :=
  clearDenominators r e / Finset.univ.gcd (clearDenominators r)

/-- The common denominator is positive. -/
lemma commonDenominator_pos {E : Type*} [Fintype E] (r : E → ℚ) : 0 < commonDenominator r := by
  refine Nat.pos_of_ne_zero fun h => ?_
  obtain ⟨e, -, he⟩ := Finset.lcm_eq_zero_iff.mp h
  exact (r e).den_ne_zero he

/-- Every denominator divides the common denominator. -/
lemma den_dvd_commonDenominator {E : Type*} [Fintype E] (r : E → ℚ) (e : E) :
    (r e).den ∣ commonDenominator r :=
  Finset.dvd_lcm (f := fun e => (r e).den) (Finset.mem_univ e)

/-- Clearing denominators multiplies a nonnegative ratio by the common denominator. -/
lemma clearDenominators_cast {E : Type*} [Fintype E] {r : E → ℚ} (hr₀ : ∀ e, 0 ≤ r e)
    (e : E) : (clearDenominators r e : ℚ) = commonDenominator r * r e := by
  have hnum : (((r e).num.toNat : ℕ) : ℚ) = (r e).num := by
    have h := Int.toNat_of_nonneg (Rat.num_nonneg.mpr (hr₀ e))
    exact_mod_cast h
  have hden : ((r e).den : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (r e).den_ne_zero
  rw [clearDenominators, Nat.cast_mul, hnum,
    Nat.cast_div (den_dvd_commonDenominator r e) hden]
  calc ((r e).num : ℚ) * ((commonDenominator r : ℚ) / (r e).den)
      = commonDenominator r * ((r e).num / (r e).den) := by ring
    _ = commonDenominator r * r e := by rw [Rat.num_div_den]

/-- Clearing denominators of a nonzero vector of nonnegative ratios leaves a nonzero entry. -/
lemma exists_clearDenominators_ne_zero {E : Type*} [Fintype E] {r : E → ℚ}
    (hr₀ : ∀ e, 0 ≤ r e) (hr : r ≠ 0) : ∃ e, clearDenominators r e ≠ 0 := by
  obtain ⟨e, he⟩ := Function.ne_iff.mp hr
  refine ⟨e, fun h => he ?_⟩
  have h' := clearDenominators_cast hr₀ e
  rw [h, Nat.cast_zero] at h'
  have hD : (commonDenominator r : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (commonDenominator_pos r).ne'
  exact (mul_eq_zero.mp h'.symm).resolve_left hD

/-- The empirical formula of a nonzero vector of nonnegative ratios is primitive: the greatest
common divisor of its entries is `1`. -/
lemma gcd_empiricalFormula {E : Type*} [Fintype E] {r : E → ℚ} (hr₀ : ∀ e, 0 ≤ r e)
    (hr : r ≠ 0) : Finset.univ.gcd (empiricalFormula r) = 1 := by
  obtain ⟨e, he⟩ := exists_clearDenominators_ne_zero hr₀ hr
  exact Finset.gcd_div_eq_one (Finset.mem_univ e) he

/-- The empirical formula of a nonzero vector of nonnegative ratios is proportional to it, with
the positive factor `D / g`, where `D` is the common denominator and `g` the greatest common
divisor of the cleared entries. -/
lemma empiricalFormula_proportional {E : Type*} [Fintype E] {r : E → ℚ} (hr₀ : ∀ e, 0 ≤ r e)
    (hr : r ≠ 0) : ∃ c > 0, ∀ e, (empiricalFormula r e : ℚ) = c * r e := by
  obtain ⟨e₀, he₀⟩ := exists_clearDenominators_ne_zero hr₀ hr
  have hg : Finset.univ.gcd (clearDenominators r) ≠ 0 := fun h =>
    he₀ (Finset.gcd_eq_zero_iff.mp h e₀ (Finset.mem_univ e₀))
  refine ⟨commonDenominator r / Finset.univ.gcd (clearDenominators r), ?_, fun e => ?_⟩
  · exact div_pos (Nat.cast_pos.mpr (commonDenominator_pos r))
      (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hg))
  · rw [empiricalFormula,
      Nat.cast_div (Finset.gcd_dvd (f := clearDenominators r) (Finset.mem_univ e))
        (Nat.cast_ne_zero.mpr hg),
      clearDenominators_cast hr₀ e]
    ring

/-- Formula vectors proportional to the same ratios satisfy `p e * q e' = p e' * q e`. -/
lemma mul_eq_mul_of_proportional {E : Type*} {p q : E → ℕ} {r : E → ℚ} {c d : ℚ}
    (hp : ∀ e, (p e : ℚ) = c * r e) (hq : ∀ e, (q e : ℚ) = d * r e) (e e' : E) :
    p e * q e' = p e' * q e := by
  have h : ((p e * q e' : ℕ) : ℚ) = ((p e' * q e : ℕ) : ℚ) := by
    push_cast
    rw [hp e, hq e', hp e', hq e]
    ring
  exact_mod_cast h

/-- If `p e * q e' = p e' * q e` for all `e` and `e'`, then
`gcd p * q e' = p e' * gcd q`. -/
lemma gcd_mul_eq_mul_gcd {E : Type*} [Fintype E] {p q : E → ℕ}
    (h : ∀ e e', p e * q e' = p e' * q e) (e' : E) :
    Finset.univ.gcd p * q e' = p e' * Finset.univ.gcd q := by
  calc Finset.univ.gcd p * q e' = Finset.univ.gcd fun e => p e * q e' := by
        rw [Finset.gcd_mul_right, normalize_eq]
    _ = Finset.univ.gcd fun e => p e' * q e := Finset.gcd_congr rfl fun e _ => h e e'
    _ = p e' * Finset.univ.gcd q := by rw [Finset.gcd_mul_left, normalize_eq]

/-- Two primitive formula vectors proportional to the same ratios are equal. -/
lemma eq_of_proportional {E : Type*} [Fintype E] {p q : E → ℕ} {r : E → ℚ} {c d : ℚ}
    (hp₁ : Finset.univ.gcd p = 1) (hq₁ : Finset.univ.gcd q = 1)
    (hp : ∀ e, (p e : ℚ) = c * r e) (hq : ∀ e, (q e : ℚ) = d * r e) : p = q := by
  funext e
  have h := gcd_mul_eq_mul_gcd (mul_eq_mul_of_proportional hp hq) e
  rw [hp₁, hq₁, one_mul, mul_one] at h
  exact h.symm

/-- A primitive formula vector proportional to a nonzero vector of nonnegative ratios is its
empirical formula. -/
lemma eq_empiricalFormula {E : Type*} [Fintype E] {p : E → ℕ} {r : E → ℚ} {c : ℚ}
    (hr₀ : ∀ e, 0 ≤ r e) (hr : r ≠ 0) (hp₁ : Finset.univ.gcd p = 1)
    (hp : ∀ e, (p e : ℚ) = c * r e) : p = empiricalFormula r := by
  obtain ⟨d, -, hd⟩ := empiricalFormula_proportional hr₀ hr
  exact eq_of_proportional hp₁ (gcd_empiricalFormula hr₀ hr) hp hd

/-- A primitive formula vector is nonzero. -/
lemma ne_zero_of_gcd_eq_one {E : Type*} [Fintype E] {p : E → ℕ}
    (hp : Finset.univ.gcd p = 1) : p ≠ 0 := by
  rintro rfl
  rw [(Finset.gcd_eq_zero_iff (f := (0 : E → ℕ))).mpr fun _ _ => rfl] at hp
  exact zero_ne_one hp

/-- **Empirical formula.** A nonzero vector `r` of nonnegative rational mole ratios has exactly
one primitive formula vector (greatest common divisor `1`, hence nonzero) proportional to it with
a positive factor, namely `empiricalFormula r`. The zero vector is excluded by the hypothesis
`r ≠ 0`. -/
theorem existsUnique_primitive_proportional {E : Type*} [Fintype E] (r : E → ℚ)
    (hr₀ : ∀ e, 0 ≤ r e) (hr : r ≠ 0) :
    ∃! p : E → ℕ, Finset.univ.gcd p = 1 ∧ p ≠ 0 ∧ ∃ c > 0, ∀ e, (p e : ℚ) = c * r e :=
  ⟨empiricalFormula r, ⟨gcd_empiricalFormula hr₀ hr,
      ne_zero_of_gcd_eq_one (gcd_empiricalFormula hr₀ hr), empiricalFormula_proportional hr₀ hr⟩,
    fun _ ⟨hp₁, _, _, _, hp⟩ => eq_empiricalFormula hr₀ hr hp₁ hp⟩

/-!

## G. Molecular formulas

-/

/-- The molecular formula `k • p` of a primitive formula `p` has greatest common divisor `k`. -/
lemma gcd_nsmul_of_gcd_eq_one {E : Type*} [Fintype E] {p : E → ℕ}
    (hp : Finset.univ.gcd p = 1) (k : ℕ) : Finset.univ.gcd (k • p) = k := by
  have h : k • p = fun e => k * p e := by
    funext e
    simp
  rw [h, Finset.gcd_mul_left, hp, normalize_eq, mul_one]

/-- The empirical formula of the molecular formula `k • p`, for a primitive `p` and `k > 0`, is
`p`. -/
lemma empiricalFormula_nsmul {E : Type*} [Fintype E] {p : E → ℕ}
    (hp : Finset.univ.gcd p = 1) {k : ℕ} (hk : 0 < k) :
    empiricalFormula (fun e => ((k • p) e : ℚ)) = p := by
  have hk' : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hk.ne'
  refine (eq_empiricalFormula (c := 1 / k) (fun e => Nat.cast_nonneg _) ?_ hp fun e => ?_).symm
  · obtain ⟨e, he⟩ := Function.ne_iff.mp (ne_zero_of_gcd_eq_one hp)
    refine Function.ne_iff.mpr ⟨e, ?_⟩
    simp only [Pi.smul_apply, smul_eq_mul, Nat.cast_mul, Pi.zero_apply]
    exact mul_ne_zero hk' (Nat.cast_ne_zero.mpr he)
  · rw [Pi.smul_apply, smul_eq_mul, Nat.cast_mul, ← mul_assoc, one_div_mul_cancel hk', one_mul]

/-- **Molecular formula.** Let `p` be a primitive formula with molar mass `M_emp > 0`, and let
`ν` be a formula vector proportional to `p` over `ℚ`, of molar mass `M`. If `M = k * M_emp` for a
natural number `k`, then `ν = k • p`. The integer `k` is a hypothesis; the hypotheses `0 < M` and
`0 < k` of the textbook procedure are not needed. -/
theorem eq_nsmul_of_formulaMolarMass_eq {E : Type*} [Fintype E] {Mₑ : E → ℝ} {p ν : E → ℕ}
    {c : ℚ} {M M_emp : ℝ} {k : ℕ} (hp : Finset.univ.gcd p = 1)
    (hν : ∀ e, (ν e : ℚ) = c * p e) (hemp : formulaMolarMass Mₑ p = M_emp)
    (hpos : 0 < M_emp) (hM : formulaMolarMass Mₑ ν = M) (hk : M = k * M_emp) : ν = k • p := by
  obtain ⟨g, rfl⟩ : ∃ g : ℕ, ν = g • p := by
    refine ⟨Finset.univ.gcd ν, funext fun e => ?_⟩
    have h := gcd_mul_eq_mul_gcd
      (mul_eq_mul_of_proportional hν fun e => (one_mul (p e : ℚ)).symm) e
    rw [hp, mul_one] at h
    rw [Pi.smul_apply, smul_eq_mul, h]
  rw [formulaMolarMass_nsmul, hemp] at hM
  have hg : (g : ℝ) = k := mul_right_cancel₀ hpos.ne' (hM.trans hk)
  rw [Nat.cast_inj.mp hg]

/-- The molecular formula of a compound with formula vector `ν ≠ 0`, empirical formula `p` and
molar mass `M = k * M_emp`, where `M_emp > 0` is the molar mass of `p` and `k` is a natural
number, is `k • p`. -/
theorem eq_nsmul_of_empiricalFormula_eq {E : Type*} [Fintype E] {Mₑ : E → ℝ} {p ν : E → ℕ}
    {M M_emp : ℝ} {k : ℕ} (hν : ν ≠ 0) (hp : empiricalFormula (fun e => (ν e : ℚ)) = p)
    (hemp : formulaMolarMass Mₑ p = M_emp) (hpos : 0 < M_emp)
    (hM : formulaMolarMass Mₑ ν = M) (hk : M = k * M_emp) : ν = k • p := by
  have hr₀ : ∀ e, 0 ≤ (ν e : ℚ) := fun e => Nat.cast_nonneg _
  have hr : (fun e => (ν e : ℚ)) ≠ 0 := by
    obtain ⟨e, he⟩ := Function.ne_iff.mp hν
    exact Function.ne_iff.mpr ⟨e, Nat.cast_ne_zero.mpr he⟩
  obtain ⟨c, hc, hpc⟩ := empiricalFormula_proportional hr₀ hr
  subst hp
  refine eq_nsmul_of_formulaMolarMass_eq (c := c⁻¹) (gcd_empiricalFormula hr₀ hr) (fun e => ?_)
    hemp hpos hM hk
  rw [hpc e, ← mul_assoc, inv_mul_cancel₀ hc.ne', one_mul]

/-- Conversely, the molecular formula `k • p` has molar mass `M = k * M_emp`, where `M_emp > 0`
is the molar mass of `p`, so `k` is the consistency ratio `M / M_emp`. -/
lemma formulaMolarMass_nsmul_consistency {E : Type*} [Fintype E] {Mₑ : E → ℝ} {p : E → ℕ}
    {M M_emp : ℝ} {k : ℕ} (hemp : formulaMolarMass Mₑ p = M_emp) (hpos : 0 < M_emp)
    (hM : formulaMolarMass Mₑ (k • p) = M) : M = k * M_emp ∧ (k : ℝ) = M / M_emp := by
  rw [formulaMolarMass_nsmul, hemp] at hM
  exact ⟨hM.symm, by rw [← hM, mul_div_cancel_right₀ _ hpos.ne']⟩

/-- **Molecular formula, positive ratio.** The source-facing C7 statement of the textbook
procedure, with positive molar masses and a positive integer ratio. Let a compound have formula
vector `ν ≠ 0`, empirical formula `p` and molar mass `M > 0`, and let `M_emp > 0` be the molar
mass of `p`. If `M = k * M_emp` for a natural number `k`, then `0 < k` and `ν = k • p`. The
algebraic lemmas `eq_nsmul_of_formulaMolarMass_eq` and `eq_nsmul_of_empiricalFormula_eq` are the
generalizations without positivity; they conclude only `ν = k • p`. -/
theorem eq_nsmul_of_formulaMolarMass_eq_pos {E : Type*} [Fintype E] {Mₑ : E → ℝ} {p ν : E → ℕ}
    {M M_emp : ℝ} {k : ℕ} (hν : ν ≠ 0) (hp : empiricalFormula (fun e => (ν e : ℚ)) = p)
    (hemp : formulaMolarMass Mₑ p = M_emp) (hpos : 0 < M_emp) (hM₀ : 0 < M)
    (hM : formulaMolarMass Mₑ ν = M) (hk : M = k * M_emp) : 0 < k ∧ ν = k • p := by
  refine ⟨Nat.pos_of_ne_zero fun h => ?_, eq_nsmul_of_empiricalFormula_eq hν hp hemp hpos hM hk⟩
  rw [h, Nat.cast_zero, zero_mul] at hk
  exact hM₀.ne' hk

/-- Conversely, with positive molar masses, the molecular formula `k • p` of molar mass `M > 0`
has `M = k * M_emp`, where `M_emp > 0` is the molar mass of `p`, and `k` is the positive
consistency ratio `M / M_emp`. -/
lemma formulaMolarMass_nsmul_consistency_pos {E : Type*} [Fintype E] {Mₑ : E → ℝ} {p : E → ℕ}
    {M M_emp : ℝ} {k : ℕ} (hemp : formulaMolarMass Mₑ p = M_emp) (hpos : 0 < M_emp)
    (hM₀ : 0 < M) (hM : formulaMolarMass Mₑ (k • p) = M) :
    0 < k ∧ M = k * M_emp ∧ (k : ℝ) = M / M_emp := by
  obtain ⟨hk, hk'⟩ := formulaMolarMass_nsmul_consistency hemp hpos hM
  refine ⟨Nat.pos_of_ne_zero fun h => ?_, hk, hk'⟩
  rw [h, Nat.cast_zero, zero_mul] at hk
  exact hM₀.ne' hk

/-!

## H. Mole fractions and mass fractions

-/

/-- The mole fraction `x i = n i / ∑ j, n j` of the component `i` of a mixture with amounts of
substance `n`. -/
noncomputable def moleFraction {ι : Type*} [Fintype ι] (n : ι → ℝ) (i : ι) : ℝ :=
  n i / ∑ j, n j

/-- The mass fraction `w i = n i * M i / ∑ j, n j * M j` of the component `i` of a mixture with
amounts `n` and molar masses `M`. Applied to mole fractions in place of amounts, it converts mole
fractions to mass fractions (`massFraction_moleFraction`). -/
noncomputable def massFraction {ι : Type*} [Fintype ι] (M n : ι → ℝ) (i : ι) : ℝ :=
  n i * M i / ∑ j, n j * M j

/-- The mole fractions `x i = (w i / M i) / ∑ j, w j / M j` of a mixture with mass fractions `w`
and molar masses `M`. -/
noncomputable def moleFractionOfMassFraction {ι : Type*} [Fintype ι] (M w : ι → ℝ) (i : ι) :
    ℝ :=
  moleFraction (fun j => w j / M j) i

/-- A mixture with nonnegative amounts, a positive total amount and positive molar masses has a
positive total mass `∑ i, n i * M i`. -/
lemma sum_amount_mul_molarMass_pos {ι : Type*} [Fintype ι] {M n : ι → ℝ} (hn₀ : ∀ i, 0 ≤ n i)
    (hn : 0 < ∑ i, n i) (hM : ∀ i, 0 < M i) : 0 < ∑ i, n i * M i := by
  obtain ⟨j, -, hj⟩ := Finset.exists_lt_of_sum_lt (s := Finset.univ) (f := fun _ => (0 : ℝ))
    (g := n) (by simpa using hn)
  exact Finset.sum_pos' (fun i _ => mul_nonneg (hn₀ i) (hM i).le)
    ⟨j, Finset.mem_univ j, mul_pos hj (hM j)⟩

/-- Mole fractions of nonnegative amounts are nonnegative. -/
lemma moleFraction_nonneg {ι : Type*} [Fintype ι] {n : ι → ℝ} (hn₀ : ∀ i, 0 ≤ n i) (i : ι) :
    0 ≤ moleFraction n i :=
  div_nonneg (hn₀ i) (Finset.sum_nonneg fun j _ => hn₀ j)

/-- Mole fractions sum to `1`. -/
lemma sum_moleFraction {ι : Type*} [Fintype ι] {n : ι → ℝ} (hn : 0 < ∑ i, n i) :
    ∑ i, moleFraction n i = 1 := by
  simp only [moleFraction]
  rw [← Finset.sum_div, div_self hn.ne']

/-- Mass fractions of nonnegative amounts with positive molar masses are nonnegative. -/
lemma massFraction_nonneg {ι : Type*} [Fintype ι] {M n : ι → ℝ} (hn₀ : ∀ i, 0 ≤ n i)
    (hM : ∀ i, 0 < M i) (i : ι) : 0 ≤ massFraction M n i :=
  div_nonneg (mul_nonneg (hn₀ i) (hM i).le)
    (Finset.sum_nonneg fun j _ => mul_nonneg (hn₀ j) (hM j).le)

/-- Mass fractions sum to `1`. -/
lemma sum_massFraction {ι : Type*} [Fintype ι] {M n : ι → ℝ} (hn₀ : ∀ i, 0 ≤ n i)
    (hn : 0 < ∑ i, n i) (hM : ∀ i, 0 < M i) : ∑ i, massFraction M n i = 1 := by
  simp only [massFraction]
  rw [← Finset.sum_div, div_self (sum_amount_mul_molarMass_pos hn₀ hn hM).ne']

/-- Mass fractions computed from the mole fractions equal the mass fractions computed from the
amounts. -/
lemma massFraction_moleFraction {ι : Type*} [Fintype ι] (M : ι → ℝ) {n : ι → ℝ}
    (hn : 0 < ∑ i, n i) : massFraction M (moleFraction n) = massFraction M n := by
  funext i
  simp only [massFraction, moleFraction, div_mul_eq_mul_div]
  rw [← Finset.sum_div, div_div_div_cancel_right₀ hn.ne']

/-- Converting the mass fractions of a mixture to mole fractions gives its mole fractions. -/
lemma moleFractionOfMassFraction_massFraction {ι : Type*} [Fintype ι] {M n : ι → ℝ}
    (hn₀ : ∀ i, 0 ≤ n i) (hn : 0 < ∑ i, n i) (hM : ∀ i, 0 < M i) :
    moleFractionOfMassFraction M (massFraction M n) = moleFraction n := by
  have hS : ∑ j, n j * M j ≠ 0 := (sum_amount_mul_molarMass_pos hn₀ hn hM).ne'
  have h : ∀ i, massFraction M n i / M i = n i / ∑ j, n j * M j := fun i => by
    rw [massFraction, div_div, mul_comm (∑ j, n j * M j) (M i), ← div_div,
      mul_div_cancel_right₀ _ (hM i).ne']
  funext i
  simp only [moleFractionOfMassFraction, moleFraction, h]
  rw [← Finset.sum_div, div_div_div_cancel_right₀ hS]

/-- **Mole fractions to mass fractions and back.** For mole fractions `x` on the simplex
(`0 ≤ x i`, `∑ i, x i = 1`) and positive molar masses `M`, converting `x` to mass fractions and
back returns `x`. -/
theorem moleFractionOfMassFraction_massFraction_of_sum_eq_one {ι : Type*} [Fintype ι]
    {M x : ι → ℝ} (hx₀ : ∀ i, 0 ≤ x i) (hx₁ : ∑ i, x i = 1) (hM : ∀ i, 0 < M i) :
    moleFractionOfMassFraction M (massFraction M x) = x := by
  rw [moleFractionOfMassFraction_massFraction hx₀ (by rw [hx₁]; exact one_pos) hM]
  funext i
  rw [moleFraction, hx₁, div_one]

/-- **Mass fractions to mole fractions and back.** For mass fractions `w` on the simplex
(`0 ≤ w i`, `∑ i, w i = 1`) and positive molar masses `M`, converting `w` to mole fractions and
back returns `w`. -/
theorem massFraction_moleFractionOfMassFraction_of_sum_eq_one {ι : Type*} [Fintype ι]
    {M w : ι → ℝ} (hw₀ : ∀ i, 0 ≤ w i) (hw₁ : ∑ i, w i = 1) (hM : ∀ i, 0 < M i) :
    massFraction M (moleFractionOfMassFraction M w) = w := by
  have ha : 0 < ∑ i, w i / M i := by
    have h := sum_amount_mul_molarMass_pos (M := fun i => (M i)⁻¹) hw₀
      (by rw [hw₁]; exact one_pos) fun i => inv_pos.mpr (hM i)
    simpa only [div_eq_mul_inv] using h
  have hmole : moleFractionOfMassFraction M w = moleFraction fun j => w j / M j := rfl
  rw [hmole, massFraction_moleFraction M ha]
  have h : ∀ j, w j / M j * M j = w j := fun j => div_mul_cancel₀ (w j) (hM j).ne'
  funext i
  simp only [massFraction, h, hw₁, div_one]

end Chemistry.Amounts
