/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.TwoLocusCoalescent
public import Mathlib.Tactic.NormNum

@[expose] public section

open Filter Topology MeasureTheory MvPolynomial ProbabilityTheory Matrix
open MathlibExt.Biology.PopulationGenetics.Linkage
open MathlibExt.Biology.PopulationGenetics.TwoLocusCoalescent
open MathlibExt.Biology.PopulationGenetics.TwoLocusCoalescent.TwoLocusState

namespace MathlibExtTest.Biology.PopulationGenetics.TwoLocusCoalescent

/-! ### The two-locus ancestral process -/

/-- Complete linkage (`ρ = 0`) and a positive recombination rate give rate matrices. -/
example : IsRateMatrix (twoLocusRate 0) := isRateMatrix_twoLocusRate le_rfl
example : IsRateMatrix (twoLocusRate 2) := isRateMatrix_twoLocusRate (by norm_num)

/-- Exit rates: `1 + ρ` from `linked`, `3 + ρ / 2` from `partlySplit`, `6` from `split`. -/
example : twoLocusRate 2 linked linked = -3 ∧ twoLocusRate 2 partlySplit partlySplit = -4 ∧
    twoLocusRate 2 split split = -6 ∧ twoLocusRate 2 linked partlySplit = 2 := by
  norm_num [twoLocusRate]

/-- `bothCoalesced` is absorbing. -/
example (ρ : ℝ) (j : TwoLocusState) : twoLocusRate ρ bothCoalesced j = 0 := by
  cases j <;> rfl

/-- Values of the covariance: `1` at `ρ = 0`, `19/32` at `ρ = 1`, `5/12` at `ρ = 2`. -/
example : twoLocusCov 0 = 1 := twoLocusCov_zero
example : twoLocusCov 1 = 19 / 32 := by norm_num [twoLocusCov, twoLocusDenom]
example : twoLocusCov 2 = 5 / 12 := by norm_num [twoLocusCov, twoLocusDenom]

/-- Outside the biological domain `ρ ≥ 0` the formula is not a correlation: at `ρ = -1` it
exceeds `1`. -/
example : twoLocusCov (-1) = 17 / 6 := by norm_num [twoLocusCov, twoLocusDenom]

/-- The backward equations are consistent (non-vacuity of `covariance_of_productMoment`): the
explicit solutions satisfy them, and the theorem recovers the covariances at `ρ = 2`. -/
example : productMoment 2 linked - meanTimeA linked * meanTimeB linked = 5 / 12 ∧
    productMoment 2 partlySplit - meanTimeA partlySplit * meanTimeB partlySplit = 1 / 8 ∧
    productMoment 2 split - meanTimeA split * meanTimeB split = 1 / 12 := by
  obtain ⟨hA, hB, h0, h⟩ := productMoment_solution (ρ := 2) (by norm_num)
  have hA0 : ∀ i, coalescedA i = true → meanTimeA i = 0 := fun i hi => by simp [meanTimeA, hi]
  have hB0 : ∀ i, coalescedB i = true → meanTimeB i = 0 := fun i hi => by simp [meanTimeB, hi]
  obtain ⟨h1, h2, h3⟩ := covariance_of_productMoment (by norm_num) hA0 hA hB0 hB h0 h
  rw [h1, h2, h3]
  norm_num [twoLocusCov, twoLocusDenom]

/-- The mean coalescence time is `1` before the locus coalesces. -/
example (m : TwoLocusState → ℝ) (h0 : ∀ i, coalescedA i = true → m i = 0)
    (h : ∀ i, coalescedA i = false → (twoLocusRate 3 *ᵥ m) i = -1) : m split = 1 :=
  eq_one_of_meanTimeA (by norm_num) h0 h split rfl

/-! ### The Ohta–Kimura moment system -/

/-- Complete coupling disequilibrium: only `AB` and `ab` gametes, each at frequency `1/2`. -/
noncomputable def xCoupling : Bool × Bool → ℝ := fun g => if g.1 = g.2 then 1 / 2 else 0

theorem sum_xCoupling : ∑ g, xCoupling g = 1 := by
  norm_num [xCoupling, Fintype.sum_prod_type]

/-- At complete coupling (`D = 1/4`, `p = q = 1/2`) the first row reads
`L D² = (1 - (3 + ρ + 8ν)) / 16`. -/
example (ρ ν : ℝ) :
    eval xCoupling (twoLocusGenerator ρ ν (diseqPoly ^ 2)) = (1 - (3 + ρ + 8 * ν)) / 16 := by
  rw [twoLocusGenerator_diseqSq sum_xCoupling]
  norm_num [linkageDiseq, alleleFreqFst, alleleFreqSnd, xCoupling]
  ring

/-- At complete coupling `z = 0`, so the second row reads `L (D z) = 4 D² = 1/4`. -/
example (ρ ν : ℝ) : eval xCoupling (twoLocusGenerator ρ ν diseqZPoly) = 1 / 4 := by
  rw [twoLocusGenerator_diseqZ sum_xCoupling]
  norm_num [linkageDiseq, alleleFreqFst, alleleFreqSnd, xCoupling]

/-- The drift of `x_AB` without mutation at complete coupling, `-(ρ/2) D = -ρ/8`, matches
`2 N` times one generation of `recombine` when `ρ = 4 N r`. -/
example (N r : ℝ) :
    eval xCoupling (twoLocusGenerator (4 * N * r) 0 (X (true, true))) = -(N * r) / 2 := by
  rw [twoLocusGenerator_X sum_xCoupling rfl, recombine_eq_sub sum_xCoupling]
  norm_num [linkageDiseq, xCoupling]
  ring

/-- The fixed gamete `AB`: a vertex of the simplex. -/
noncomputable def xFixed : Bool × Bool → ℝ := fun g => if g = (true, true) then 1 else 0

/-- **Non-vacuity witness for `IsStationaryLaw`.** Without mutation, the point mass at a fixed
gamete is stationary for every `ρ`: the diffusion coefficients and the drift vanish there. (Its
`E Π` is `0`, so it is excluded by the hypothesis `0 < E Π` of `sigmaDSq_eq`; with `ν > 0` the
stationary law is not constructed here.) -/
theorem isStationaryLaw_dirac_fixed (ρ : ℝ) :
    IsStationaryLaw ρ 0 (Measure.dirac xFixed) where
  isProbabilityMeasure := inferInstance
  ae_mem_simplex := by
    rw [ae_dirac_eq, Filter.eventually_pure]
    refine ⟨fun g => by unfold xFixed; split_ifs <;> norm_num, ?_⟩
    simp [xFixed]
  integral_generator f := by
    rw [integral_dirac]
    simp [twoLocusGenerator, Fintype.sum_prod_type, xFixed, diseqPoly]

/-- The low-mutation value at `ρ = 0` is `10 / 22`, and at `ρ = 1` it is `11 / 36`. -/
example : sigmaDSq 0 0 = 5 / 11 := by norm_num [sigmaDSq]
example : sigmaDSq 1 0 = 11 / 36 := by norm_num [sigmaDSq]

/-- Mutation lowers `σ_d²`: at `ρ = 0`, `ν = 1/16`, the value is `11 / 30.5`. -/
example : sigmaDSq 0 (1 / 16) = 22 / 61 := by norm_num [sigmaDSq]

end MathlibExtTest.Biology.PopulationGenetics.TwoLocusCoalescent
