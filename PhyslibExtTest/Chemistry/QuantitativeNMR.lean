/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import PhyslibExt.Chemistry.QuantitativeNMR
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Vandermonde

open Chemistry.QuantitativeNMR

/-!

# Tests for quantitative NMR

Exact numeric checks for `Chemistry.QuantitativeNMR`, including convolution weights and totals,
nonzero-coupling checks of the AB energy levels, signed transition offsets and line frequencies,
and the equivalent-shift boundary, plus `#print axioms` for every public declaration.

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

/-- Triplet line positions at `ν0 = 100`, `J = 6`: `94`, `100` and `106`. -/
example : linePosition 100 6 2 0 = 94 ∧ linePosition 100 6 2 1 = 100 ∧
    linePosition 100 6 2 2 = 106 := by
  norm_num [linePosition]

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

/-- Combined line index `i + j` of a triplet line `i` and a doublet line `j` with equal
couplings. -/
private def tripletDoubletPos (i : Fin 3) (j : Fin 2) : Fin 4 :=
  ⟨i.val + j.val, by have := i.isLt; have := j.isLt; omega⟩

/-- Convolving the triplet `(1, 2, 1)` with the doublet `(1, 1)` at equal couplings gives the
quartet `(1, 3, 3, 1)`: each outer position comes from one pair, each inner position from two
coincident pairs. -/
example :
    convIntensity (multipletWeights 2) (multipletWeights 1) tripletDoubletPos 0 = 1 ∧
      convIntensity (multipletWeights 2) (multipletWeights 1) tripletDoubletPos 1 = 3 ∧
      convIntensity (multipletWeights 2) (multipletWeights 1) tripletDoubletPos 2 = 3 ∧
      convIntensity (multipletWeights 2) (multipletWeights 1) tripletDoubletPos 3 = 1 := by
  simp only [convIntensity, Fin.sum_univ_succ, Fin.sum_univ_zero]
  simp +decide [multipletWeights]
  norm_num

/-- `conv_total` on that quartet: the total intensity is `(1 + 2 + 1) * (1 + 1) = 8`. -/
example :
    ∑ k, convIntensity (multipletWeights 2) (multipletWeights 1) tripletDoubletPos k = 8 := by
  rw [conv_total, multiplet_sum, multiplet_sum]
  norm_num

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

/-- Mathlib's Vandermonde identity `Nat.add_choose_eq`, cast to `ℝ`, at `n = 2, m = 1, k = 1`:
the inner quartet weight `3` above is `choose 3 1`. -/
example : ∑ ij ∈ Finset.antidiagonal 1,
    ((Nat.choose 2 ij.1 : ℝ) * (Nat.choose 1 ij.2 : ℝ)) =
    ((Nat.choose (2 + 1) 1 : ℕ) : ℝ) := by
  exact_mod_cast (Nat.add_choose_eq 2 1 1).symm

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

/-- Populations in the ratio `3 : 1` (`x = log 3`) have excess `(3 - 1) / (3 + 1) = 1 / 2`. -/
example : excessFraction (Real.log 3) = 1 / 2 := by
  rw [excessFraction, Real.exp_log (by norm_num)]
  norm_num

/-- The excess is signed: the ratio `1 : 3` (`x = -log 3`) gives `-1 / 2`. -/
example : excessFraction (-Real.log 3) = -1 / 2 := by
  rw [excessFraction, Real.exp_neg, Real.exp_log (by norm_num)]
  norm_num

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

With `νA = 4`, `νB = -4`, `J = 6` (signed frequencies measured from a carrier) one has
`D = √(8 ^ 2 + 6 ^ 2) = 10`: the energies are `αα, ββ = 3 / 2`, `+ = 7 / 2`, `− = -13 / 2`, the
four signed transition offsets are `±8` and `±2`, and the line frequencies are `8, 2, 2, 8`.
With `νA = 104`, `νB = 96`, `J = 6` (both above `|J|`) again `D = 10`, and the line frequencies
equal the offsets `92, 102, 98, 108`. With `νA = 10`, `νB = 0`, `J = 0` the levels show the
Zeeman sign of §A: `αα` lies below `ββ`.

-/

private lemma sqrt_ab_example : Real.sqrt ((4 - -4) ^ 2 + (6 : ℝ) ^ 2) = 10 := by
  rw [show ((4 - -4) ^ 2 + (6 : ℝ) ^ 2) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

private lemma sqrt_ab_lab : Real.sqrt ((104 - 96) ^ 2 + (6 : ℝ) ^ 2) = 10 := by
  rw [show ((104 - 96) ^ 2 + (6 : ℝ) ^ 2) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]

/-- With the Zeeman sign of `zeemanEnergy`, `αα` (both `m = +1/2`) is the lowest level and `ββ`
the highest at `νA = 10`, `νB = 0`, `J = 0`. -/
example : abEnergyAlphaAlpha 10 0 0 = -5 ∧ abEnergyBetaBeta 10 0 0 = 5 := by
  norm_num [abEnergyAlphaAlpha, abEnergyBetaBeta]

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

/-- The four signed transition offsets at `νA = 4`, `νB = -4`, `J = 6` are `-8, 2, -2, 8`. -/
example : abOffsetAlphaMinus 4 (-4) 6 = -8 ∧ abOffsetAlphaPlus 4 (-4) 6 = 2 ∧
    abOffsetPlusBeta 4 (-4) 6 = -2 ∧ abOffsetMinusBeta 4 (-4) 6 = 8 := by
  obtain ⟨h1, h2, h3, h4⟩ := abOffsets_eq 4 (-4) 6
  rw [sqrt_ab_example] at h1 h2 h3 h4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> [rw [h1]; rw [h2]; rw [h3]; rw [h4]] <;> norm_num

/-- The line frequencies there are the absolute energy gaps `8, 2, 2, 8`, although two offsets
are negative. -/
example : abGapAlphaMinus 4 (-4) 6 = 8 ∧ abGapAlphaPlus 4 (-4) 6 = 2 ∧
    abGapPlusBeta 4 (-4) 6 = 2 ∧ abGapMinusBeta 4 (-4) 6 = 8 := by
  simp only [abGapAlphaMinus, abGapAlphaPlus, abGapPlusBeta, abGapMinusBeta, abEnergyAlphaAlpha,
    abEnergyBetaBeta, abEnergyPlus, abEnergyMinus, sqrt_ab_example]
  norm_num

/-- With both resonance frequencies above `|J|` (`νA = 104`, `νB = 96`, `J = 6`) the offsets are
positive, and the line frequencies are `92, 102, 98, 108` (`abGaps_eq`). -/
example : 0 < abOffsetAlphaMinus 104 96 6 ∧ abGapAlphaMinus 104 96 6 = 92 ∧
    abGapAlphaPlus 104 96 6 = 102 ∧ abGapPlusBeta 104 96 6 = 98 ∧
    abGapMinusBeta 104 96 6 = 108 := by
  obtain ⟨h1, h2, h3, h4⟩ := abGaps_eq 104 96 6 (by norm_num) (by norm_num)
  rw [sqrt_ab_lab] at h1 h2 h3 h4
  refine ⟨(abOffsets_pos 104 96 6 (by norm_num) (by norm_num)).1, ?_, ?_, ?_, ?_⟩ <;>
    [rw [h1]; rw [h2]; rw [h3]; rw [h4]] <;> norm_num

/-- There each line frequency equals the offset of its candidate (`abGaps_eq_offsets`). -/
example : abGapPlusBeta 104 96 6 = abOffsetPlusBeta 104 96 6 :=
  (abGaps_eq_offsets 104 96 6 (by norm_num) (by norm_num)).2.2.1

/-- At `J = 0` the offsets are exactly the two resonance frequencies, each twice: the `A` flips
`αα → +` and `− → ββ` at `νA = 10`, the `B` flips at `νB = 0`. -/
example : abOffsetAlphaMinus 10 0 0 = 0 ∧ abOffsetAlphaPlus 10 0 0 = 10 ∧
    abOffsetPlusBeta 10 0 0 = 0 ∧ abOffsetMinusBeta 10 0 0 = 10 := by
  have hD : Real.sqrt ((10 - 0) ^ 2 + (0 : ℝ) ^ 2) = 10 := by
    rw [show ((10 - 0) ^ 2 + (0 : ℝ) ^ 2) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  obtain ⟨h1, h2, h3, h4⟩ := abOffsets_eq 10 0 0
  rw [hD] at h1 h2 h3 h4
  refine ⟨?_, ?_, ?_, ?_⟩ <;> [rw [h1]; rw [h2]; rw [h3]; rw [h4]] <;> norm_num

/-- Equivalent shifts at `ν0 = 100`, `J = 6`: the candidates are `94`, `100`, `100` and `106`;
the two at `100 ± 6` are the forbidden singlet transitions of the `A₂` spectrum. -/
example : abOffsetAlphaMinus 100 100 6 = 94 ∧ abOffsetAlphaPlus 100 100 6 = 100 ∧
    abOffsetPlusBeta 100 100 6 = 100 ∧ abOffsetMinusBeta 100 100 6 = 106 := by
  obtain ⟨h1, h2, h3, h4⟩ := abOffsets_self 100 6 (by norm_num)
  refine ⟨?_, h2, h3, ?_⟩
  · rw [h1]; norm_num
  · rw [h4]; norm_num

/-- Strong coupling moves the offsets off first order: at `νA = 3`, `νB = -3`, `J = 4` the offset
of `− → ββ` is `2 + √13`, not the first-order position `3 + J / 2 = 5`. -/
example : abOffsetMinusBeta 3 (-3) 4 ≠ 3 + 4 / 2 := by
  obtain ⟨-, -, -, h4⟩ := abOffsets_eq 3 (-3) 4
  rw [h4]
  intro h
  have hs : Real.sqrt ((3 - -3) ^ 2 + (4 : ℝ) ^ 2) = 6 := by norm_num at h ⊢; linarith
  have := Real.sq_sqrt (show (0 : ℝ) ≤ (3 - -3) ^ 2 + 4 ^ 2 by norm_num)
  rw [hs] at this
  norm_num at this

/-- Weak coupling at `νA = 100`, `νB = 0`, `J = 6`: the offset of `− → ββ` is within `36 / 400`
of the first-order position `100 + J / 2`. -/
example : |abOffsetMinusBeta 100 0 6 - (100 + 6 / 2)| ≤ 6 ^ 2 / (4 * |(100 : ℝ) - 0|) := by
  have h := (abOffsets_weakCoupling 100 0 6 (by norm_num)).1
  rwa [show max (100 : ℝ) 0 = 100 by norm_num] at h

/-- The same bound for line frequencies at `νA = 1100`, `νB = 1000`, `J = 6`: the line frequency
of `− ↔ ββ` is within `36 / 400` of the first-order position `1100 + J / 2`. -/
example : |abGapMinusBeta 1100 1000 6 - (1100 + 6 / 2)| ≤
    6 ^ 2 / (4 * |(1100 : ℝ) - 1000|) := by
  have h := (abGaps_weakCoupling 1100 1000 6 (by norm_num) (by norm_num) (by norm_num)).1
  rwa [show max (1100 : ℝ) 1000 = 1100 by norm_num] at h

/-- `abMixedState` lists `βα` before `αβ`. -/
example : abMixedState 0 = (1, 0) ∧ abMixedState 1 = (0, 1) := ⟨rfl, rfl⟩

/-- The mixed-state block at `νA = 4`, `νB = -4`, `J = 6`: the `βα` diagonal entry is
`(νA - νB) / 2 - J / 4 = 5 / 2` and the coupling entry is `J / 2 = 3`. -/
example : (abHamiltonian 4 (-4) 6).submatrix abMixedState abMixedState 0 0 = 5 / 2 ∧
    (abHamiltonian 4 (-4) 6).submatrix abMixedState abMixedState 0 1 = 3 := by
  rw [abHamiltonian_submatrix_mixed]
  constructor <;> simp [abMixingMatrix] <;> norm_num

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
#print axioms multiplet_symm
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
#print axioms abOffsetAlphaMinus
#print axioms abOffsetAlphaPlus
#print axioms abOffsetPlusBeta
#print axioms abOffsetMinusBeta
#print axioms abGapAlphaMinus
#print axioms abGapAlphaPlus
#print axioms abGapPlusBeta
#print axioms abGapMinusBeta
#print axioms abOffsets_eq
#print axioms abOffsets_self
#print axioms abOffsets_pos
#print axioms abGaps_eq_offsets
#print axioms abGaps_eq
#print axioms ab_first_order_limit
#print axioms abOffsets_weakCoupling
#print axioms abGaps_weakCoupling
