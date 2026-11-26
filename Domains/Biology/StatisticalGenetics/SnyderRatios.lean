/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Snyder's ratios for a recessive trait

One autosomal locus with a dominant allele `T` and a recessive allele `t` at frequencies
`p = 1 - q` and `q`. This file defines the Hardy–Weinberg genotype law `hwGenotype`, Mendelian
transmission probabilities `transmitRecessive`, the dominant phenotype `IsDominant` with its
frequency `dominantFreq`, the recessive frequency `recessiveFreq`, and Snyder's ratios
`ratioDominantRecessive` (`S`) and `ratioDominantDominant` (`R`), and proves `snyder_ratios`:
`S = q / (1 + q)`, `R = (q / (1 + q))² = S²`, and `q = √B`.

Sources: L. H. Snyder, "Studies in human inheritance IX. The inheritance of taste deficiency in
man", Ohio J. Sci. 32 (1932) 436–440, p. 438 and Table I.
-/

@[expose] public section

namespace WantedExt.Biology.StatisticalGenetics.SnyderRatiosWanted

/-- Hardy–Weinberg genotype law at a two-allele locus, indexed by the number `k ∈ {0, 1, 2}` of
recessive alleles `t`: `P(TT) = (1 - q)²`, `P(Tt) = 2q(1 - q)`, `P(tt) = q²`. -/
noncomputable def hwGenotype (q : ℝ) (k : Fin 3) : ℝ :=
  (Nat.choose 2 k : ℝ) * q ^ (k : ℕ) * (1 - q) ^ (2 - (k : ℕ))

/-- Probability that a parent with `k` copies of the recessive allele transmits a recessive
allele to a child (Mendelian segregation): `k / 2`. -/
noncomputable def transmitRecessive (k : Fin 3) : ℝ := (k : ℝ) / 2

/-- The dominant phenotype (taster): at least one dominant allele, i.e. `k < 2`. -/
def IsDominant (k : Fin 3) : Prop := (k : ℕ) < 2

instance (k : Fin 3) : Decidable (IsDominant k) := inferInstanceAs (Decidable ((k : ℕ) < 2))

/-- Frequency of the dominant phenotype under the Hardy–Weinberg genotype law. -/
noncomputable def dominantFreq (q : ℝ) : ℝ :=
  ∑ k : Fin 3, if IsDominant k then hwGenotype q k else 0

/-- Frequency `B` of the recessive phenotype (genotype `tt`) under Hardy–Weinberg. -/
noncomputable def recessiveFreq (q : ℝ) : ℝ := hwGenotype q 2

/-- **Snyder's `S`**: the probability that a child of a dominant × recessive mating is recessive,
for parents drawn independently from the Hardy–Weinberg law. The recessive parent always
transmits `t`, so the child is recessive exactly when the dominant parent transmits `t`. It is a
quotient by the dominant-phenotype frequency `dominantFreq q = 1 - q²`, which is positive exactly
for `q < 1` when `0 ≤ q ≤ 1`, the intended domain. At `q = 1` the denominator vanishes and the
value is `0`, since Lean's division is total (`x / 0 = 0`). -/
noncomputable def ratioDominantRecessive (q : ℝ) : ℝ :=
  (∑ k : Fin 3, if IsDominant k then hwGenotype q k * transmitRecessive k else 0) /
    dominantFreq q

/-- **Snyder's `R`**: the probability that a child of a dominant × dominant mating is recessive,
for parents drawn independently from the Hardy–Weinberg law: both parents must transmit `t`,
independently. It is a quotient by `(dominantFreq q)²` with `dominantFreq q = 1 - q²`, which is
positive exactly for `q < 1` when `0 ≤ q ≤ 1`, the intended domain. At `q = 1` the denominator
vanishes and the value is `0`, since Lean's division is total (`x / 0 = 0`). -/
noncomputable def ratioDominantDominant (q : ℝ) : ℝ :=
  (∑ k₁ : Fin 3, ∑ k₂ : Fin 3,
      if IsDominant k₁ ∧ IsDominant k₂ then
        hwGenotype q k₁ * hwGenotype q k₂ * (transmitRecessive k₁ * transmitRecessive k₂)
      else 0) /
    (dominantFreq q) ^ 2

private lemma dom_zero : IsDominant 0 := by decide

private lemma dom_one : IsDominant 1 := by decide

private lemma ndom_two : ¬IsDominant 2 := by decide

private lemma hw_zero (q : ℝ) : hwGenotype q 0 = (1 - q) ^ 2 := by
  have c0 : Nat.choose 2 0 = 1 := by decide
  simp [hwGenotype, c0]

private lemma hw_one (q : ℝ) : hwGenotype q 1 = 2 * q * (1 - q) := by
  simp [hwGenotype]

private lemma hw_two (q : ℝ) : hwGenotype q 2 = q ^ 2 := by simp [hwGenotype]

private lemma tr_zero : transmitRecessive 0 = 0 := by simp [transmitRecessive]

private lemma tr_one : transmitRecessive 1 = 1 / 2 := by simp [transmitRecessive]

private lemma domFreq_eq (q : ℝ) : dominantFreq q = 1 - q ^ 2 := by
  simp [dominantFreq, Fin.sum_univ_three, dom_zero, dom_one, ndom_two, hw_zero, hw_one]
  ring

private lemma numerS_eq (q : ℝ) :
    (∑ k : Fin 3, if IsDominant k then hwGenotype q k * transmitRecessive k else 0)
      = q * (1 - q) := by
  simp [Fin.sum_univ_three, dom_zero, dom_one, ndom_two, hw_zero, hw_one, tr_zero, tr_one]
  ring

private lemma numerR_eq (q : ℝ) :
    (∑ k₁ : Fin 3, ∑ k₂ : Fin 3,
      if IsDominant k₁ ∧ IsDominant k₂ then
        hwGenotype q k₁ * hwGenotype q k₂ * (transmitRecessive k₁ * transmitRecessive k₂)
      else 0) = (q * (1 - q)) ^ 2 := by
  have h : ∀ k₁ k₂ : Fin 3,
      (if IsDominant k₁ ∧ IsDominant k₂ then
        hwGenotype q k₁ * hwGenotype q k₂ * (transmitRecessive k₁ * transmitRecessive k₂)
      else (0 : ℝ)) =
      (if IsDominant k₁ then hwGenotype q k₁ * transmitRecessive k₁ else 0) *
      (if IsDominant k₂ then hwGenotype q k₂ * transmitRecessive k₂ else 0) := by
    intro k₁ k₂
    by_cases h₁ : IsDominant k₁ <;> by_cases h₂ : IsDominant k₂ <;> simp [h₁, h₂]
    ring
  simp_rw [h, ← Finset.sum_mul_sum, numerS_eq]
  ring

private lemma recFreq_eq (q : ℝ) : recessiveFreq q = q ^ 2 := by
  simp [recessiveFreq, hw_two]

/-- **Snyder's ratios** (Snyder 1932, p. 438): for a recessive allele frequency `0 < q < 1`,
with parents drawn independently from the Hardy–Weinberg genotype law and Mendelian
transmission, the recessive fraction among children of dominant × recessive matings is
`S = q / (1 + q)`, the recessive fraction among children of dominant × dominant matings is
`R = (q / (1 + q))² = S²`, and the recessive phenotype frequency `B` determines the allele
frequency by `q = √B`.

Source: Snyder (1932), p. 438. -/
public theorem snyder_ratios (q : ℝ) (hq₀ : 0 < q) (hq₁ : q < 1) :
    ratioDominantRecessive q = q / (1 + q) ∧
      ratioDominantDominant q = (q / (1 + q)) ^ 2 ∧
      ratioDominantDominant q = (ratioDominantRecessive q) ^ 2 ∧
      Real.sqrt (recessiveFreq q) = q
    := by
  have h1q : (0 : ℝ) < 1 - q := sub_pos.mpr hq₁
  have h1q' : (0 : ℝ) < 1 + q := add_pos zero_lt_one hq₀
  have n1q : (1 : ℝ) - q ≠ 0 := ne_of_gt h1q
  have n1q' : (1 : ℝ) + q ≠ 0 := ne_of_gt h1q'
  have nprod : (1 - q) * (1 + q) ≠ 0 := mul_ne_zero n1q n1q'
  have hsq : (1 : ℝ) - q ^ 2 = (1 - q) * (1 + q) := by ring
  have hS : ratioDominantRecessive q = q / (1 + q) := by
    rw [ratioDominantRecessive, numerS_eq, domFreq_eq, hsq]
    field_simp
  have hR : ratioDominantDominant q = (q / (1 + q)) ^ 2 := by
    rw [ratioDominantDominant, numerR_eq, domFreq_eq, hsq]
    field_simp
  have hRS : ratioDominantDominant q = (ratioDominantRecessive q) ^ 2 := by
    rw [hR, hS]
  have hsqrt : Real.sqrt (recessiveFreq q) = q := by
    rw [recFreq_eq]
    exact Real.sqrt_sq (le_of_lt hq₀)
  exact ⟨hS, hR, hRS, hsqrt⟩

end WantedExt.Biology.StatisticalGenetics.SnyderRatiosWanted
