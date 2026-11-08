/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.Ewens
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Tests for the Ewens sampling formula and Hoppe's urn

Samples of two genes: the two allelic partitions `{2}` and `{1, 1}` have probabilities
`1 / (θ + 1)` and `θ / (θ + 1)`, which sum to one; the expected number of alleles is
`1 + θ / (θ + 1)`; the empty sample (`n = 0`); the junk value at `θ = 0`, outside the
domain; the first steps of Hoppe's urn; and nonnegativity of both laws.
-/

@[expose] public section

open Finset

namespace MathlibExtTest.Biology.PopulationGenetics.Ewens

open MathlibExt.Biology.PopulationGenetics.Ewens

/-- The allelic partition `{1, 1}` of two genes (two distinct alleles). -/
def twoAlleles : Nat.Partition 2 where
  parts := {1, 1}
  parts_pos := by simp
  parts_sum := by simp

/-- The allelic partition `{2}` of two genes (one allele). -/
def oneAllele : Nat.Partition 2 := Nat.Partition.indiscrete 2

/-- Two genes carry the same allele with probability `1 / (θ + 1)`. -/
example (θ : ℝ) (hθ : 0 < θ) : ewensProb θ oneAllele = 1 / (θ + 1) := by
  have : θ * (θ + 1) ≠ 0 := by positivity
  simp [ewensProb, oneAllele, ascPochhammer_succ_eval]
  field_simp

/-- Two genes carry distinct alleles with probability `θ / (θ + 1)`. -/
example (θ : ℝ) (hθ : 0 < θ) : ewensProb θ twoAlleles = θ / (θ + 1) := by
  have : θ * (θ + 1) ≠ 0 := by positivity
  simp [ewensProb, twoAlleles, ascPochhammer_succ_eval, Multiset.count_cons]
  field_simp

/-- The empty sample has the empty partition with probability one. -/
example (θ : ℝ) (π : Nat.Partition 0) : ewensProb θ π = 1 := by
  simp [ewensProb]

/-- Outside the domain `θ > 0`: for `θ = 0` the rising factorial vanishes and `ewensProb`
returns Lean's junk value `0` (division by zero), so the formula no longer sums to one. -/
example : ewensProb 0 oneAllele = 0 := by
  simp [ewensProb, ascPochhammer_succ_eval]

/-- Normalization for two genes, from the general theorem. -/
example (θ : ℝ) (hθ : 0 < θ) : ∑ π : Nat.Partition 2, ewensProb θ π = 1 :=
  sum_ewensProb θ hθ 2

/-- Expected number of alleles in a sample of two: `1 + θ / (θ + 1)`. -/
example (θ : ℝ) (hθ : 0 < θ) :
    ∑ π : Nat.Partition 2, ewensProb θ π * (π.parts.card : ℝ) = 1 + θ / (θ + 1) := by
  rw [sum_ewensProb_mul_card_parts θ hθ 2]
  have : θ ≠ 0 := hθ.ne'
  simp [sum_range_succ, div_self this]

/-- The first draw of Hoppe's urn always produces a new allele. -/
example (θ : ℝ) (hθ : 0 < θ) (π : Nat.Partition 1) : hoppeLaw θ 1 π = 1 := by
  rw [hoppeLaw_eq_ewensProb hθ]
  have : θ ≠ 0 := hθ.ne'
  simp only [ewensProb, Subsingleton.elim π (Nat.Partition.indiscrete 1),
    Nat.Partition.indiscrete_parts one_ne_zero]
  simp [inv_mul_cancel₀ this]

/-- Second draw of Hoppe's urn from one gene: a new allele with probability `θ / (θ + 1)`. -/
example (θ : ℝ) :
    hoppeStep θ (Nat.Partition.indiscrete 1) twoAlleles = θ / (θ + 1) := by
  have h : (1 ::ₘ {1} : Multiset ℕ) ≠ {2} := by decide
  simp [hoppeStep, twoAlleles, h]

/-- Second draw of Hoppe's urn from one gene: a copy with probability `1 / (θ + 1)`. -/
example (θ : ℝ) :
    hoppeStep θ (Nat.Partition.indiscrete 1) oneAllele = 1 / (θ + 1) := by
  have h : ({2} : Multiset ℕ) ≠ 1 ::ₘ {1} := by decide
  simp [hoppeStep, oneAllele, h]

/-- The Hoppe-urn transition is stochastic (an instance of `sum_hoppeStep`). -/
example (θ : ℝ) (hθ : 0 < θ) :
    ∑ π' : Nat.Partition 3, hoppeStep θ twoAlleles π' = 1 :=
  sum_hoppeStep hθ twoAlleles

/-- The Ewens weights are a probability distribution on the partitions of four genes:
nonnegative (`ewensProb_nonneg`) and summing to one (`sum_ewensProb`). -/
example (θ : ℝ) (hθ : 0 < θ) :
    (∀ π : Nat.Partition 4, 0 ≤ ewensProb θ π) ∧ ∑ π : Nat.Partition 4, ewensProb θ π = 1 :=
  ⟨fun π => ewensProb_nonneg hθ π, sum_ewensProb θ hθ 4⟩

/-- The Hoppe-urn law is nonnegative (`hoppeLaw_nonneg`). -/
example (θ : ℝ) (hθ : 0 < θ) (π : Nat.Partition 3) : 0 ≤ hoppeLaw θ 3 π :=
  hoppeLaw_nonneg hθ π

end MathlibExtTest.Biology.PopulationGenetics.Ewens
