/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import PhyslibExt.Chemistry.QuantitativeNMR

open Classical
open Chemistry.QuantitativeNMR

/-!
# Quantitative NMR tests

Exact numeric checks for `Chemistry.QuantitativeNMR`, plus `#print axioms` for
every public declaration. Verification concatenation: production content
followed by these test examples with only the production import mechanically
removed.
-/

/-! ## Zeeman checks (CH43.1) -/

/-- Energy difference at `γ = 1, hbar = 1, B0 = 2π` is `ΔE = 2π`. -/
example : zeemanEnergy 1 1 (2 * Real.pi) (-1 / 2) -
    zeemanEnergy 1 1 (2 * Real.pi) (1 / 2) = 2 * Real.pi := by
  have hpos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h := zeeman_energy_split 1 1 (2 * Real.pi) (by norm_num) (by norm_num)
    (by linarith)
  simpa using h

/-- Transition frequency at `γ = 1, hbar = 1, B0 = 2π` is `ν = 1`. -/
example : (2 * Real.pi) / (2 * Real.pi * 1) = 1 := by
  have hpi : (2 : ℝ) * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hpos : (0 : ℝ) < Real.pi := Real.pi_pos
  have h := zeeman_transition_freq 1 1 (2 * Real.pi) (2 * Real.pi)
    (2 * Real.pi * 1) ((2 * Real.pi) / (2 * Real.pi * 1))
    (by norm_num) (by norm_num) (by linarith) (by ring) rfl rfl
  have h2 : (1 : ℝ) * (2 * Real.pi) / (2 * Real.pi) = 1 := by
    rw [div_eq_iff hpi]
  rw [h]
  exact h2

/-! ## Chemical shift checks (CH43.2) -/

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

/-! ## Multiplet checks (CH43.3, binomial part) -/

/-- Triplet weights `(1, 2, 1)` for `n = 2`. -/
example : multipletWeights 2 ⟨0, by decide⟩ = 1 := by
  have h0 : ((⟨0, by decide⟩ : Fin (2 + 1)) : ℕ) = 0 := rfl
  have h : Nat.choose 2 0 = 1 := by decide
  simp only [multipletWeights, h0, h, Nat.cast_one]

example : multipletWeights 2 ⟨1, by decide⟩ = 2 := by
  have h1 : ((⟨1, by decide⟩ : Fin (2 + 1)) : ℕ) = 1 := rfl
  have h : Nat.choose 2 1 = 2 := by decide
  simp only [multipletWeights, h1, h, Nat.cast_ofNat]

example : multipletWeights 2 ⟨2, by decide⟩ = 1 := by
  have h2 : ((⟨2, by decide⟩ : Fin (2 + 1)) : ℕ) = 2 := rfl
  have h : Nat.choose 2 2 = 1 := by decide
  simp only [multipletWeights, h2, h, Nat.cast_one]

/-- Triplet weights sum to `4 = 2 ^ 2`. -/
example : ∑ k, multipletWeights 2 k = 4 := by
  rw [multiplet_sum]
  norm_num

/-- Quartet weights `(1, 3, 3, 1)` for `n = 3`. -/
example : multipletWeights 3 ⟨0, by decide⟩ = 1 := by
  have h0 : ((⟨0, by decide⟩ : Fin (3 + 1)) : ℕ) = 0 := rfl
  have h : Nat.choose 3 0 = 1 := by decide
  simp only [multipletWeights, h0, h, Nat.cast_one]

example : multipletWeights 3 ⟨1, by decide⟩ = 3 := by
  have h1 : ((⟨1, by decide⟩ : Fin (3 + 1)) : ℕ) = 1 := rfl
  have h : Nat.choose 3 1 = 3 := by decide
  simp only [multipletWeights, h1, h, Nat.cast_ofNat]

example : multipletWeights 3 ⟨2, by decide⟩ = 3 := by
  have h2 : ((⟨2, by decide⟩ : Fin (3 + 1)) : ℕ) = 2 := rfl
  have h : Nat.choose 3 2 = 3 := by decide
  simp only [multipletWeights, h2, h, Nat.cast_ofNat]

example : multipletWeights 3 ⟨3, by decide⟩ = 1 := by
  have h3 : ((⟨3, by decide⟩ : Fin (3 + 1)) : ℕ) = 3 := rfl
  have h : Nat.choose 3 3 = 1 := by decide
  simp only [multipletWeights, h3, h, Nat.cast_one]

/-- Quartet weights sum to `8 = 2 ^ 3`. -/
example : ∑ k, multipletWeights 3 k = 8 := by
  rw [multiplet_sum]
  norm_num

/-- Distinctness of positions for `J = 1 ≠ 0` at `n = 2`. -/
example (ν0 : ℝ) : Function.Injective (linePosition ν0 1 2) :=
  linePosition_injective ν0 1 2 (by norm_num)

/-! ## General multiplicity checks (CH43.3, product part) -/

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

/-! ## Convolution checks (CH43.3, Vandermonde part) -/

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
  have h : Nat.choose 3 1 = 3 := by decide
  simpa [h]

/-! ## Integral and population checks (CH43.4) -/

/-- Integral ratio `2` for `C = 1 / 2`, `N = (6, 3)`. -/
example : ((1 / 2 : ℝ) * 6) / ((1 / 2 : ℝ) * 3) = 2 := by
  have h := integral_ratio (1 / 2) 6 3 _ _ (by norm_num) (by norm_num) rfl rfl
  rw [h]
  norm_num

/-- Population excess at `x = 0` is `0`. -/
example : excessFraction 0 = 0 := by
  simp [excessFraction, Real.exp_zero]

/-- First-order bound instance at `x = 1 / 2`. -/
example : |excessFraction (1 / 2) - (1 / 2) / 2| ≤ (1 / 2) ^ 2 :=
  excessFraction_bound (1 / 2) (by norm_num)

/-! ## AB checks (CH43.5) -/

/-- `νA = 10, νB = 0, J = 0` gives eigenvalues `10, 0` (first-order limit). -/
example : abEigenPlus 10 0 0 = 10 := by
  simp only [abEigenPlus]
  have hsq : Real.sqrt ((10 - 0) ^ 2 + (0 : ℝ) ^ 2) = 10 := by
    have h100 : ((10 - 0) ^ 2 + (0 : ℝ) ^ 2) = 10 ^ 2 := by norm_num
    rw [h100, Real.sqrt_sq_eq_abs]
    norm_num
  rw [hsq]
  norm_num

example : abEigenMinus 10 0 0 = 0 := by
  simp only [abEigenMinus]
  have hsq : Real.sqrt ((10 - 0) ^ 2 + (0 : ℝ) ^ 2) = 10 := by
    have h100 : ((10 - 0) ^ 2 + (0 : ℝ) ^ 2) = 10 ^ 2 := by norm_num
    rw [h100, Real.sqrt_sq_eq_abs]
    norm_num
  rw [hsq]
  norm_num

/-- `νA = 4, νB = -4, J = 6` gives eigenvalues `±5`
(hand-verified: `√(64 + 36) / 2 = 5`). -/
example : abEigenPlus 4 (-4) 6 = 5 := by
  simp only [abEigenPlus]
  have hsq : Real.sqrt ((4 - -4) ^ 2 + (6 : ℝ) ^ 2) = 10 := by
    have h100 : ((4 - -4) ^ 2 + (6 : ℝ) ^ 2) = 10 ^ 2 := by norm_num
    rw [h100, Real.sqrt_sq_eq_abs]
    norm_num
  rw [hsq]
  norm_num

example : abEigenMinus 4 (-4) 6 = -5 := by
  simp only [abEigenMinus]
  have hsq : Real.sqrt ((4 - -4) ^ 2 + (6 : ℝ) ^ 2) = 10 := by
    have h100 : ((4 - -4) ^ 2 + (6 : ℝ) ^ 2) = 10 ^ 2 := by norm_num
    rw [h100, Real.sqrt_sq_eq_abs]
    norm_num
  rw [hsq]
  norm_num

/-- Characteristic-equation instances at `νA = 10, νB = 0, J = 0`. -/
example : Matrix.det (abHamiltonian 10 0 0 - abEigenPlus 10 0 0 • 1) = 0 :=
  ab_det_plus 10 0 0

example : Matrix.det (abHamiltonian 10 0 0 - abEigenMinus 10 0 0 • 1) = 0 :=
  ab_det_minus 10 0 0

/-- Trace-matching instance at `νA = 4, νB = -4, J = 6`. -/
example : abEigenPlus 4 (-4) 6 + abEigenMinus 4 (-4) 6 = 4 + (-4) :=
  ab_eigen_sum 4 (-4) 6

/-! ## Countermodel / boundary notes (no theorems claimed) -/

-- `chemicalShift` with `νref = 0` is not claimed: division by zero in Lean is
-- junk (`x / 0 = 0`), and no theorem above applies there (`chemicalShift_self`
-- and `chemicalShift_scale` both require `νref ≠ 0`).
-- The first-order multiplet (`multipletWeights`, `linePosition`) is not claimed
-- when `Δν ~ J`; the AB section (§E) shows the deviation from first order
-- (e.g. `νA = 3, νB = -3, J = 4` gives `±√13`, hand-verified, not `±5`).

/-! ## Axioms -/

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
#print axioms excessFraction_abs_lt_one
#print axioms excessFraction_lower
#print axioms excessFraction_upper
#print axioms excessFraction_bound_interior
#print axioms excessFraction_bound
#print axioms abHamiltonian
#print axioms abEigenPlus
#print axioms abEigenMinus
#print axioms ab_det_plus
#print axioms ab_det_minus
#print axioms ab_eigen_sum
#print axioms ab_eigen_prod
#print axioms ab_first_order_limit
