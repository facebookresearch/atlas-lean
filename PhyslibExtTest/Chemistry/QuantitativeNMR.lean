/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import PhyslibExt.Chemistry.QuantitativeNMR

open Chemistry.QuantitativeNMR

/-!

# Tests for quantitative NMR

Exact numeric checks for `Chemistry.QuantitativeNMR`, including nonzero-coupling checks of the
AB energy levels and lines, plus `#print axioms` for every public declaration.

-/

/-!

## A. Zeeman checks

-/

/-- Energy difference at `γ = 1, hbar = 1, B0 = 2π` is `ΔE = 2π`. -/
example : zeemanEnergy 1 1 (2 * Real.pi) (-1 / 2) -
    zeemanEnergy 1 1 (2 * Real.pi) (1 / 2) = 2 * Real.pi := by
  have hpos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h := zeeman_energy_split 1 1 (2 * Real.pi) (by norm_num) (by norm_num)
    (by linarith)
  simpa using h

/-- Transition frequency at `γ = 1, hbar = 1, B0 = 2π` is `ν = 1`. -/
example (ΔE h ν : ℝ) (hΔE : ΔE = 1 * 1 * (2 * Real.pi)) (hh : h = 2 * Real.pi * 1)
    (hν : ν = ΔE / h) : ν = 1 := by
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  rw [zeeman_transition_freq 1 1 (2 * Real.pi) ΔE h ν (by norm_num) (by norm_num)
    (by positivity) hΔE hh hν, one_mul, div_self hpi]

/-!

## B. Chemical shift checks

-/

/-- `chemicalShift 400 400 = 0` in abstract units. -/
example : chemicalShift 400 400 = 0 := chemicalShift_self 400 (by norm_num)

/-- Field-independence instance: `σ = 0`, `σref = 1 / 1000000` gives
`δ = 1000000 * (1/1000000) / (1 - 1/1000000) = 1000000 / 999999`
(hand-verified; NOT exactly `1`). -/
example : chemicalShift (1 * (2 * Real.pi) * (1 - 0) / (2 * Real.pi))
    (1 * (2 * Real.pi) * (1 - 1 / 1000000) / (2 * Real.pi)) =
    1000000 / 999999 := by
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hpos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h := chemicalShift_field_indep 1 (2 * Real.pi) 0 (1 / 1000000) _ _ rfl
    rfl (by positivity) (by norm_num)
  rw [h]
  norm_num

/-!

## C. Multiplet, multiplicity and convolution checks

-/

/-- Triplet weights `(1, 2, 1)` for `n = 2`. -/
example : multipletWeights 2 ⟨0, by decide⟩ = 1 := by
  simp [multipletWeights]

example : multipletWeights 2 ⟨1, by decide⟩ = 2 := by
  simp [multipletWeights]

example : multipletWeights 2 ⟨2, by decide⟩ = 1 := by
  simp [multipletWeights]

/-- Triplet weights sum to `4 = 2 ^ 2`. -/
example : ∑ k, multipletWeights 2 k = 4 := by
  rw [multiplet_sum]
  norm_num

/-- Quartet weights `(1, 3, 3, 1)` for `n = 3`. -/
example : multipletWeights 3 ⟨0, by decide⟩ = 1 := by
  simp [multipletWeights]

example : multipletWeights 3 ⟨1, by decide⟩ = 3 := by
  simp [multipletWeights]

example : multipletWeights 3 ⟨2, by decide⟩ = 3 := by
  norm_num [multipletWeights, Nat.choose]

example : multipletWeights 3 ⟨3, by decide⟩ = 1 := by
  simp [multipletWeights]

/-- Quartet weights sum to `8 = 2 ^ 3`. -/
example : ∑ k, multipletWeights 3 k = 8 := by
  rw [multiplet_sum]
  norm_num

/-- Distinctness of positions for `J = 1 ≠ 0` at `n = 2`. -/
example (ν0 : ℝ) : Function.Injective (linePosition ν0 1 2) :=
  linePosition_injective ν0 1 2 (by norm_num)

/-- Two spin-1/2 groups with `n = (2, 1)` give `3 * 2 = 6`. -/
example : maxMultiplicity ![2, 1] ![1, 1] = 6 := by
  norm_num [maxMultiplicity, maxMultiplicityOn, Fin.prod_univ_two]

/-- One spin-1 group (`s = 2`) with `n = 1` gives `3`. -/
example : maxMultiplicity ![1] ![2] = 3 := by
  norm_num [maxMultiplicity, maxMultiplicityOn, Fin.prod_univ_one]

/-- Resolved-bound instance of the production lemma: cards `(3, 2)` give `≤ 6`. -/
example : (combinedLines ![{0, 1, 2}, {0, 1}]).card ≤ 6 := by
  have c3 : ({0, 1, 2} : Finset ℝ).card = 3 := by
    have n0 : (0 : ℝ) ∉ ({1, 2} : Finset ℝ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      norm_num
    have n1 : (1 : ℝ) ∉ ({2} : Finset ℝ) := by
      simp only [Finset.mem_singleton]
      norm_num
    rw [Finset.card_insert_of_notMem n0, Finset.card_insert_of_notMem n1,
      Finset.card_singleton]
  have c2 : ({0, 1} : Finset ℝ).card = 2 := by
    have n01 : (0 : ℝ) ∉ ({1} : Finset ℝ) := by
      simp only [Finset.mem_singleton]
      norm_num
    rw [Finset.card_insert_of_notMem n01, Finset.card_singleton]
  have hcard : ∀ i, ((![{0, 1, 2}, {0, 1}] : Fin 2 → Finset ℝ) i).card =
      ![2, 1] i * ![1, 1] i + 1 := by
    intro i
    fin_cases i
    · norm_num [c3, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
    · norm_num [c2, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.head_cons]
  have h := card_combined_le ![{0, 1, 2}, {0, 1}] ![2, 1] ![1, 1] hcard
  have hmax : maxMultiplicity ![2, 1] ![1, 1] = 6 := by
    norm_num [maxMultiplicity, maxMultiplicityOn, Fin.prod_univ_two]
  rw [hmax] at h
  exact h

/-- Coincidence instance: the two groups share shifts (`1 + 0 = 0 + 1` with
`1 ∈ lines 0`, `0 ∈ lines 1`, `0 ∈ lines 0`, `1 ∈ lines 1`), so the distinct
count is `< 6`. -/
example : (combinedLines ![{0, 1, 2}, {0, 1}]).card < 6 := by
  have hsub : combinedLines ![{0, 1, 2}, {0, 1}] ⊆ ({0, 1, 2, 3} : Finset ℝ) := by
    intro z hz
    simp only [combinedLines, Finset.mem_image, Finset.mem_univ,
      true_and] at hz
    obtain ⟨x, rfl⟩ := hz
    have hx0 : ((x 0 : ↥((![{0, 1, 2}, {0, 1}] : Fin 2 → Finset ℝ) 0)) : ℝ) ∈
        ({0, 1, 2} : Finset ℝ) := (x 0).2
    have hx1 : ((x 1 : ↥((![{0, 1, 2}, {0, 1}] : Fin 2 → Finset ℝ) 1)) : ℝ) ∈
        ({0, 1} : Finset ℝ) := (x 1).2
    simp only [combinedSum, Fin.sum_univ_two, Finset.mem_insert,
      Finset.mem_singleton]
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx0 hx1
    obtain h0 | h0 | h0 := hx0 <;> obtain h1 | h1 := hx1 <;>
      rw [h0, h1] <;> norm_num
  have n0 : (0 : ℝ) ∉ ({1, 2, 3} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    norm_num
  have n1 : (1 : ℝ) ∉ ({2, 3} : Finset ℝ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    norm_num
  have n2 : (2 : ℝ) ∉ ({3} : Finset ℝ) := by
    simp only [Finset.mem_singleton]
    norm_num
  have c4 : ({0, 1, 2, 3} : Finset ℝ).card = 4 := by
    rw [Finset.card_insert_of_notMem n0, Finset.card_insert_of_notMem n1,
      Finset.card_insert_of_notMem n2, Finset.card_singleton]
  have hle : (combinedLines ![{0, 1, 2}, {0, 1}]).card ≤
      ({0, 1, 2, 3} : Finset ℝ).card :=
    Finset.card_le_card hsub
  omega

/-- Vandermonde at `n = 2, m = 1, k = 1`: the antidiagonal sum is
`choose 2 0 * choose 1 1 + choose 2 1 * choose 1 0 = 3`. -/
example : ∑ ij ∈ Finset.antidiagonal 1,
    ((Nat.choose 2 ij.1 : ℝ) * (Nat.choose 1 ij.2 : ℝ)) = 3 := by
  have hanti : Finset.antidiagonal 1 = {(0, 1), (1, 0)} := by decide
  have c20 : Nat.choose 2 0 = 1 := by decide
  have c11 : Nat.choose 1 1 = 1 := by decide
  have c21 : Nat.choose 2 1 = 2 := by decide
  have c10 : Nat.choose 1 0 = 1 := by decide
  rw [hanti, Finset.sum_insert (by decide), Finset.sum_singleton]
  show ((Nat.choose 2 0 : ℝ) * (Nat.choose 1 1 : ℝ)) +
    ((Nat.choose 2 1 : ℝ) * (Nat.choose 1 0 : ℝ)) = 3
  norm_num [c20, c11, c21, c10]

/-- The production Vandermonde lemma at `n = 2, m = 1, k = 1`. -/
example : ∑ ij ∈ Finset.antidiagonal 1,
    ((Nat.choose 2 ij.1 : ℝ) * (Nat.choose 1 ij.2 : ℝ)) =
    ((Nat.choose (2 + 1) 1 : ℕ) : ℝ) :=
  binomial_vandermonde 2 1 1

/-- `choose 3 1 = 3` (the closed form above). -/
example : ((Nat.choose 3 1 : ℕ) : ℝ) = 3 := by
  simp

/-!

## D. Integral and population checks

-/

/-- Integral ratio `2` for `C = 1 / 2`, `N = (6, 3)`. -/
example (ii ij : ℝ) (hi : ii = 1 / 2 * 6) (hj : ij = 1 / 2 * 3) : ii / ij = 2 := by
  rw [integral_ratio (1 / 2) 6 3 ii ij (by norm_num) (by norm_num) hi hj]
  norm_num

/-- Population excess at `x = 0` is `0`. -/
example : excessFraction 0 = 0 := by
  simp [excessFraction, Real.exp_zero]

/-- Boltzmann populations `Nα = e^x * Nβ` have excess fraction `excessFraction x`. -/
example (x Nβ : ℝ) (hβ : 0 < Nβ) :
    (Real.exp x * Nβ - Nβ) / (Real.exp x * Nβ + Nβ) = excessFraction x :=
  excessFraction_eq_of_populations x _ Nβ hβ rfl

/-- Equal populations (`x = 0`) have zero excess. -/
example (N : ℝ) (hN : 0 < N) : (N - N) / (N + N) = excessFraction 0 :=
  excessFraction_eq_of_populations 0 N N hN (by simp)

/-- First-order bound instance at `x = 1 / 2`. -/
example : |excessFraction (1 / 2) - (1 / 2) / 2| ≤ (1 / 2) ^ 2 :=
  excessFraction_bound (1 / 2) (by norm_num)

/-!

## E. AB spin system checks

With `νA = 4`, `νB = -4`, `J = 6` one has `D = √(8 ^ 2 + 6 ^ 2) = 10`: the energies are
`αα, ββ = 3 / 2`, `+ = 7 / 2`, `− = -13 / 2`, and the four lines are `±8` and `±2`.

-/

private lemma sqrt_ab_example : Real.sqrt ((4 - -4) ^ 2 + (6 : ℝ) ^ 2) = 10 := by
  rw [show ((4 - -4) ^ 2 + (6 : ℝ) ^ 2) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- The four energy levels at `νA = 4`, `νB = -4`, `J = 6`. -/
example : abEnergyAlphaAlpha 4 (-4) 6 = 3 / 2 ∧ abEnergyBetaBeta 4 (-4) 6 = 3 / 2 ∧
    abEnergyPlus 4 (-4) 6 = 7 / 2 ∧ abEnergyMinus 4 (-4) 6 = -13 / 2 := by
  simp only [abEnergyAlphaAlpha, abEnergyBetaBeta, abEnergyPlus, abEnergyMinus,
    sqrt_ab_example]
  norm_num

/-- `7 / 2` is an eigenvalue of the AB Hamiltonian at `νA = 4`, `νB = -4`, `J = 6`. -/
example : Module.End.HasEigenvalue (Matrix.toLin' (abHamiltonian 4 (-4) 6)) (7 / 2) := by
  have h : abEnergyPlus 4 (-4) 6 = 7 / 2 := by
    rw [abEnergyPlus, sqrt_ab_example]; norm_num
  have := abHamiltonian_hasEigenvalue_plus 4 (-4) 6
  rw [h] at this
  simpa using this

/-- `0` is not an eigenvalue there: the spectrum is exactly the four levels. -/
example : ¬ Module.End.HasEigenvalue (Matrix.toLin' (abHamiltonian 4 (-4) 6)) 0 := by
  rw [abHamiltonian_hasEigenvalue_iff]
  simp only [abEnergyAlphaAlpha, abEnergyPlus, abEnergyMinus, abEnergyBetaBeta,
    sqrt_ab_example]
  norm_num

/-- The four lines at `νA = 4`, `νB = -4`, `J = 6` are `8, -2, 2, -8`. -/
example : abLineAlphaMinus 4 (-4) 6 = 8 ∧ abLineAlphaPlus 4 (-4) 6 = -2 ∧
    abLinePlusBeta 4 (-4) 6 = 2 ∧ abLineMinusBeta 4 (-4) 6 = -8 := by
  obtain ⟨h1, h2, h3, h4⟩ := abLines_eq 4 (-4) 6
  rw [sqrt_ab_example] at h1 h2 h3 h4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> [rw [h1]; rw [h2]; rw [h3]; rw [h4]] <;> norm_num

/-- At `J = 0` the lines are exactly the two resonance frequencies, each twice. -/
example : abLineAlphaMinus 10 0 0 = 10 ∧ abLineAlphaPlus 10 0 0 = 0 ∧
    abLinePlusBeta 10 0 0 = 10 ∧ abLineMinusBeta 10 0 0 = 0 := by
  have hD : Real.sqrt ((10 - 0) ^ 2 + (0 : ℝ) ^ 2) = 10 := by
    rw [show ((10 - 0) ^ 2 + (0 : ℝ) ^ 2) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  obtain ⟨h1, h2, h3, h4⟩ := abLines_eq 10 0 0
  rw [hD] at h1 h2 h3 h4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> [rw [h1]; rw [h2]; rw [h3]; rw [h4]] <;> norm_num

/-- Strong coupling moves the lines off first order: at `νA = 3`, `νB = -3`, `J = 4` the line
`αα ↔ −` is `2 + √13`, not the first-order position `3 + J / 2 = 5`. -/
example : abLineAlphaMinus 3 (-3) 4 ≠ 3 + 4 / 2 := by
  obtain ⟨h1, -, -, -⟩ := abLines_eq 3 (-3) 4
  rw [h1]
  intro h
  have hs : Real.sqrt ((3 - -3) ^ 2 + (4 : ℝ) ^ 2) = 6 := by norm_num at h ⊢; linarith
  have := Real.sq_sqrt (show (0 : ℝ) ≤ (3 - -3) ^ 2 + 4 ^ 2 by norm_num)
  rw [hs] at this
  norm_num at this

/-- Weak coupling at `νA = 100`, `νB = 0`, `J = 6`: the line `αα ↔ −` is within
`36 / 400` of the first-order position `100 + J / 2`. -/
example : |abLineAlphaMinus 100 0 6 - (100 + 6 / 2)| ≤ 6 ^ 2 / (4 * |(100 : ℝ) - 0|) := by
  have h := (abLines_weakCoupling 100 0 6 (by norm_num)).1
  rwa [show max (100 : ℝ) 0 = 100 by norm_num] at h

/-- The mixed-state energies are the eigenvalues of `abMixingMatrix` minus
`(νA + νB) / 2 + J / 4`. -/
example : abEnergyPlus 4 (-4) 6 = abMixingEigenPlus 4 (-4) 6 - ((4 + -4) / 2 + 6 / 4) :=
  (abEnergyPlus_eq_abMixingEigenPlus 4 (-4) 6).1

/-- `abMixingMatrix` at `νA = 10`, `νB = 0`, `J = 0` has eigenvalues `10` and `0`. -/
example : abMixingEigenPlus 10 0 0 = 10 ∧ abMixingEigenMinus 10 0 0 = 0 := by
  have hD : Real.sqrt ((10 - 0) ^ 2 + (0 : ℝ) ^ 2) = 10 := by
    rw [show ((10 - 0) ^ 2 + (0 : ℝ) ^ 2) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  simp only [abMixingEigenPlus, abMixingEigenMinus, hD]
  norm_num

/-- Characteristic-equation instances for `abMixingMatrix` at `νA = 4`, `νB = -4`, `J = 6`. -/
example : Matrix.det (abMixingMatrix 4 (-4) 6 - abMixingEigenPlus 4 (-4) 6 • 1) = 0 :=
  ab_det_plus 4 (-4) 6

example : Matrix.det (abMixingMatrix 4 (-4) 6 - abMixingEigenMinus 4 (-4) 6 • 1) = 0 :=
  ab_det_minus 4 (-4) 6

/-- Trace-matching instance at `νA = 4`, `νB = -4`, `J = 6`. -/
example : abMixingEigenPlus 4 (-4) 6 + abMixingEigenMinus 4 (-4) 6 = 4 + (-4) :=
  ab_eigen_sum 4 (-4) 6

/-!

## Boundary notes

-/

-- `chemicalShift` with `νref = 0` is not claimed: division by zero in Lean is
-- junk (`x / 0 = 0`), and no theorem above applies there (`chemicalShift_self`
-- and `chemicalShift_scale` both require `νref ≠ 0`).

/-!

## Axioms

-/

#print axioms zeemanEnergy
#print axioms zeeman_energy_split
#print axioms zeeman_transition_freq
#print axioms chemicalShift
#print axioms chemicalShift_field_indep
#print axioms chemicalShift_self
#print axioms chemicalShift_scale
#print axioms multipletWeights
#print axioms multiplet_sum
#print axioms multiplet_symm_nat
#print axioms multiplet_symm
#print axioms multiplet_card
#print axioms linePosition
#print axioms linePosition_injective
#print axioms maxMultiplicityOn
#print axioms maxMultiplicity
#print axioms maxMultiplicityOn_spinHalf
#print axioms maxMultiplicity_spinHalf
#print axioms maxMultiplicityOn_union
#print axioms combinedSum
#print axioms combinedLines
#print axioms card_univ_choices_eq_maxMult
#print axioms card_combined_le
#print axioms card_combined_eq_iff
#print axioms convIntensity
#print axioms conv_total
#print axioms binomial_vandermonde
#print axioms integral_ratio
#print axioms excessFraction
#print axioms excessFraction_eq_of_populations
#print axioms excessFraction_abs_lt_one
#print axioms excessFraction_lower
#print axioms excessFraction_upper
#print axioms excessFraction_bound_interior
#print axioms excessFraction_bound
#print axioms abHamiltonian
#print axioms abHamiltonian_mulVec_alphaAlpha
#print axioms abHamiltonian_mulVec_alphaBeta
#print axioms abHamiltonian_mulVec_betaAlpha
#print axioms abHamiltonian_mulVec_betaBeta
#print axioms abHamiltonian_mulVec_eq_smul_iff
#print axioms abHamiltonian_hasEigenvalue_iff_exists
#print axioms abEnergyAlphaAlpha
#print axioms abEnergyBetaBeta
#print axioms abEnergyPlus
#print axioms abEnergyMinus
#print axioms ab_half_sqrt_sq
#print axioms abHamiltonian_hasEigenvalue_alphaAlpha
#print axioms abHamiltonian_hasEigenvalue_betaBeta
#print axioms abHamiltonian_hasEigenvalue_plus
#print axioms abHamiltonian_hasEigenvalue_minus
#print axioms abHamiltonian_eigenvalue_cases
#print axioms abHamiltonian_hasEigenvalue_iff
#print axioms abMixedState
#print axioms abMixingMatrix
#print axioms abHamiltonian_submatrix_mixed
#print axioms abMixingEigenPlus
#print axioms abMixingEigenMinus
#print axioms ab_det_plus
#print axioms ab_det_minus
#print axioms ab_eigen_sum
#print axioms ab_eigen_prod
#print axioms abEnergyPlus_eq_abMixingEigenPlus
#print axioms abLineAlphaMinus
#print axioms abLineAlphaPlus
#print axioms abLinePlusBeta
#print axioms abLineMinusBeta
#print axioms abLines_eq
#print axioms ab_first_order_limit
#print axioms abLines_weakCoupling
