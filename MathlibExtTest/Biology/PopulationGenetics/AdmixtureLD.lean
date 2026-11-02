/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.AdmixtureLD
public import Mathlib.Tactic.NormNum

/-!
# Admixture LD and ALDER weighted LD tests

* Non-vacuity of the pulse model: `α = 1/4`, source frequencies `0.9, 0.8` (`A`) and
  `0.1, 0.3` (`B`) give nonnegative gamete frequencies with `D₀ = 3/40`, checked both by
  `linkageDiseq_sourceMix` and by direct evaluation.
* Decay: `D_2 = (9/10)^2 D₀` and the diploid covariance `z = 2 D_2`, by the theorems and by
  direct evaluation of two rounds of `recombine`.
* Boundaries: `α = 0` (no admixture), `δ(x) = 0`, `r = 0` (no decay), `r = 1/2`.
* Local ancestry: `Cov(I_x, I_y) = 1/4` at the pulse for `α = 1/2` (direct), and `1/32` after
  three generations of free recombination; a junk-value probe (`α = 2`) has a negative "gamete
  frequency", outside the domain.
* Haldane: `d = 0` gives no decay; the `e^{-n d}` lower bound at `d = 1`.
* Weighted LD on a Dirac measure (fixed frequencies), and in a five-edge tree drift model
  (Figure 1 of Loh et al. 2013) with the two-reference and one-reference amplitudes, each
  cross-checked against the edge-sum `f4`.
-/

@[expose] public section

open MeasureTheory Real
open MathlibExt.Biology.PopulationGenetics.Linkage
open MathlibExt.Biology.PopulationGenetics.FStatistics
open MathlibExt.Biology.PopulationGenetics.AdmixtureLD
open scoped ENNReal


namespace MathlibExtTest.Biology.PopulationGenetics.AdmixtureLD

/-! ### The pulse model -/

/-- A concrete pulse: `α = 1/4`, `p_A = (9/10, 4/5)`, `p_B = (1/10, 3/10)`. -/
noncomputable def x0 : Bool × Bool → ℝ := sourceMix (1/4) (9/10) (4/5) (1/10) (3/10)

/-- Non-vacuity: the pulse gamete frequencies are nonnegative and sum to `1`. -/
example : (∀ g, 0 ≤ x0 g) ∧ ∑ g, x0 g = 1 := by
  refine ⟨fun g => ?_, sum_sourceMix _ _ _ _ _⟩
  obtain ⟨a, b⟩ := g
  cases a <;> cases b <;> norm_num [x0, sourceMix, bernFreq]

/-- `D₀ = α β δ(x) δ(y) = (1/4)(3/4)(4/5)(1/2) = 3/40`. -/
example : linkageDiseq x0 = 3 / 40 := by
  rw [x0, linkageDiseq_sourceMix]; norm_num

/-- The same value by direct evaluation of `D = x_AB x_ab - x_Ab x_aB`. -/
example : linkageDiseq x0 = 3 / 40 := by
  norm_num [x0, linkageDiseq, sourceMix, bernFreq]

/-- After two generations with `r = 1/10`: `D_2 = (81/100) (3/40) = 243/4000`. -/
example : linkageDiseq ((recombine (1/10))^[2] x0) = 243 / 4000 := by
  rw [x0, linkageDiseq_admixed]; norm_num

/-- The same by evaluating two rounds of the recursion. -/
example : linkageDiseq ((recombine (1/10))^[2] x0) = 243 / 4000 := by
  norm_num [x0, Function.iterate_succ, linkageDiseq, recombine, alleleFreqFst, alleleFreqSnd,
    sourceMix, bernFreq, Fintype.sum_bool]

/-- The diploid genotype covariance is `z = 2 D_2 = 243/2000`. -/
example : genotypeCov ((recombine (1/10))^[2] x0) = 243 / 2000 := by
  rw [x0, genotypeCov_admixed]; norm_num

/-- The same at the pulse by direct evaluation of the genotype covariance: `2 D₀ = 3/20`. -/
example : genotypeCov x0 = 3 / 20 := by
  norm_num [x0, genotypeCov, alleleCount, sourceMix, bernFreq, Fintype.sum_prod_type,
    Fintype.sum_bool]

/-- Boundary `α = 0`: no admixture, no LD. -/
example (pA qA pB qB r : ℝ) (n : ℕ) :
    linkageDiseq ((recombine r)^[n] (sourceMix 0 pA qA pB qB)) = 0 := by
  rw [linkageDiseq_admixed]; ring

/-- Boundary `δ(x) = 0`: equal source frequencies at `x` give no LD. -/
example (α p qA qB r : ℝ) (n : ℕ) :
    linkageDiseq ((recombine r)^[n] (sourceMix α p qA p qB)) = 0 := by
  rw [linkageDiseq_admixed]; ring

/-- Boundary `r = 0`: complete linkage, no decay. -/
example (α pA qA pB qB : ℝ) (n : ℕ) :
    linkageDiseq ((recombine 0)^[n] (sourceMix α pA qA pB qB)) =
      linkageDiseq (sourceMix α pA qA pB qB) := by
  rw [linkageDiseq_admixed, linkageDiseq_sourceMix]; ring

/-! ### Local ancestry -/

/-- At the pulse with `α = 1/2` the ancestry covariance is `α β = 1/4` (direct evaluation). -/
example : alleleCov (ancestryPulse (1/2)) = 1 / 4 := by
  norm_num [alleleCov, ancestryPulse, sourceMix, bernFreq, alleleCount, Fintype.sum_prod_type,
    Fintype.sum_bool]

/-- Unlinked loci (`r = 1/2`), three generations: `Cov = (1/4)(1/8) = 1/32`. -/
example : alleleCov ((recombine (1/2))^[3] (ancestryPulse (1/2))) = 1 / 32 := by
  rw [alleleCov_ancestryPulse]; norm_num

/-- The ancestry law is a probability vector for `α ∈ [0, 1]`. -/
example {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1) : ∀ g, 0 ≤ ancestryPulse α g := by
  intro g
  obtain ⟨a, b⟩ := g
  cases a <;> cases b <;> norm_num [ancestryPulse, sourceMix, bernFreq] <;> linarith

/-- Junk-value probe: outside the domain (`α = 2`) the "frequency" of `B`-only gametes is
`-1`; the covariance identity still holds algebraically (`α (1 - α) = -2`). -/
example : ancestryPulse 2 (false, false) = -1 ∧ alleleCov (ancestryPulse 2) = -2 := by
  constructor
  · norm_num [ancestryPulse, sourceMix, bernFreq]
  · norm_num [alleleCov, ancestryPulse, sourceMix, bernFreq, alleleCount,
      Fintype.sum_prod_type, Fintype.sum_bool]

/-! ### Haldane's map -/

/-- Zero map length: no decay. -/
example (n : ℕ) : (1 - haldane 0) ^ n = 1 := by
  rw [pow_one_sub_haldane]; simp

/-- The continuous form underestimates the exact factor: `e^{-5} ≤ (1 - r)^5` at `d = 1`. -/
example : exp (-5) ≤ (1 - haldane 1) ^ 5 := by
  simpa using exp_neg_mul_le_pow_one_sub_haldane 1 5

/-! ### Weighted LD with fixed frequencies (Dirac measure) -/

/-- Frequencies of four populations `A, B, R, S` at one fixed outcome. -/
noncomputable def pDirac : Fin 4 → Unit → ℝ := fun X _ => ![9/10, 1/10, 7/10, 2/5] X

/-- `𝔼[z w w] = 2 α β (1 - r)^n ((p_A - p_B)(p_R - p_S))^2` with `α = 1/2`, `r = 1/10`,
`n = 1`: `2 (1/4) (9/10) ((4/5)(3/10))^2 = 162/6250`. -/
example : weightedLD (Measure.dirac ()) pDirac (1/2) (1/10) 1 0 1 2 3 = 162 / 6250 := by
  rw [weightedLD_eq]
  norm_num [f4, pDirac]

/-! ### A tree drift model with references (Loh et al. 2013, Figure 1) -/

section Tree

/-- The uniform probability measure on `Fin 8`. -/
noncomputable def μ8 : Measure (Fin 8) := (8⁻¹ : ℝ≥0∞) • Measure.count

instance : IsProbabilityMeasure μ8 :=
  ⟨by simpa [μ8] using ENNReal.inv_mul_cancel (by norm_num : (8 : ℝ≥0∞) ≠ 0) (by norm_num)⟩

/-- Integration against `μ8` is averaging over the eight outcomes. -/
theorem integral_μ8 (f : Fin 8 → ℝ) :
    ∫ ω, f ω ∂μ8 = (f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7) / 8 := by
  simp only [μ8, integral_smul_measure, integral_count, Fin.sum_univ_eight]
  norm_num
  ring

/-- Orthogonal drift increments (scaled Walsh functions): edge `0` (the `A″–B″` path) has
second moment `1/25`, edges `1`–`4` (`A″–A`, `B″–B`, `A″–A′`, `B″–B′`) have `1/100`. -/
noncomputable def incr8 : Fin 5 → Fin 8 → ℝ :=
  ![![1/5, -1/5, 1/5, -1/5, 1/5, -1/5, 1/5, -1/5],
    ![1/10, 1/10, -1/10, -1/10, 1/10, 1/10, -1/10, -1/10],
    ![1/10, 1/10, 1/10, 1/10, -1/10, -1/10, -1/10, -1/10],
    ![1/10, -1/10, -1/10, 1/10, 1/10, -1/10, -1/10, 1/10],
    ![1/10, -1/10, 1/10, -1/10, -1/10, 1/10, -1/10, 1/10]]

/-- The tree of Figure 1A rooted at `A″`. Populations: `0 = A`, `1 = B`, `2 = A′`, `3 = B′`,
`4 = A″`, `5 = B″`, and `6 = C`, the `1/4 : 3/4` mixture of `A` and `B`. Frequencies stay in
`[1/5, 4/5]`. -/
noncomputable def T : DriftModel μ8 (Fin 5) (Fin 7) where
  root := fun _ => 1/2
  incr := incr8
  len := ![1/25, 1/100, 1/100, 1/100, 1/100]
  weight := ![![0, 1, 0, 0, 0], ![1, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![1, 0, 0, 0, 1],
    ![0, 0, 0, 0, 0], ![1, 0, 0, 0, 0], ![3/4, 1/4, 3/4, 0, 0]]
  memLp_root := MemLp.of_discrete
  memLp_incr := fun _ => MemLp.of_discrete
  inner_incr := by
    intro e f h
    fin_cases e <;> fin_cases f <;> simp_all [integral_μ8, incr8] <;> norm_num
  sq_incr := by
    intro e
    fin_cases e <;> simp [integral_μ8, incr8] <;> norm_num

/-- Two references `A′`, `B′` (Loh et al. 2013, Eq. 6): with `α = 1/4` the amplitude is
`2 (3/16) (1 - r)^n F2(A″, B″)^2` with `F2(A″, B″) = 1/25`. -/
example (r : ℝ) (n : ℕ) :
    weightedLD μ8 T.freq (1/4) r n 0 1 2 3 = 2 * (3/16) * (1 - r) ^ n * (1/25) ^ 2 := by
  rw [_root_.MathlibExt.Biology.PopulationGenetics.AdmixtureLD.DriftModel.weightedLD_branch
    T (1/4) r n (A'' := 4) (B'' := 5)
    (uA := ![0, 1, 0, 0, 0]) (uB := ![0, 0, 1, 0, 0]) (uA' := ![0, 0, 0, 1, 0])
    (uB' := ![0, 0, 0, 0, 1])]
  · rw [T.f2_freq]
    simp [T, Fin.sum_univ_five]
    norm_num
  all_goals first
    | (ext e; fin_cases e <;> simp [T])
    | (intro e; fin_cases e <;> simp [T])

/-- Cross-check: the edge-sum `f4 A B A′ B′` equals `F2(A″, B″) = 1/25`. -/
example : f4 μ8 T.freq 0 1 2 3 = 1 / 25 := by
  rw [T.f4_freq]
  simp [T, Fin.sum_univ_five]

/-- One reference `R′ = A′` branching at `R″ = A″`, and `C` itself (Eq. 8):
`α F2(A, R″) - β F2(B, R″) = (1/4)(1/100) - (3/4)(1/20) = -7/200`. -/
example (r : ℝ) (n : ℕ) :
    weightedLD μ8 T.freq (1/4) r n 0 1 2 6 = 2 * (3/16) * (1 - r) ^ n * (7/200) ^ 2 := by
  rw [_root_.MathlibExt.Biology.PopulationGenetics.AdmixtureLD.DriftModel.weightedLD_oneRef
    T (1/4) r n (R'' := 4)
    (uA := ![0, 1, 0, 0, 0]) (uB := ![1, 0, 1, 0, 0]) (uR := ![0, 0, 0, 1, 0])]
  · rw [T.f2_freq, T.f2_freq]
    simp [T, Fin.sum_univ_five]
    norm_num
  all_goals first
    | (ext e; fin_cases e <;> simp [T] <;> norm_num)
    | (intro e; fin_cases e <;> simp)

/-- Cross-check: the edge-sum `f4 A B A′ C = 7/200`, whose square is the amplitude above. -/
example : f4 μ8 T.freq 0 1 2 6 = 7 / 200 := by
  rw [T.f4_freq]
  simp [T, Fin.sum_univ_five]
  norm_num

/-- True mixing population `A` and `C` itself (Eq. 7): `2 α β^3 F2(A, B)^2` with
`F2(A, B) = 1/25 + 1/100 + 1/100 = 3/50`. -/
example (r : ℝ) (n : ℕ) :
    weightedLD μ8 T.freq (1/4) r n 0 1 0 6 =
      2 * ((1/4) * (3/4) ^ 3) * (1 - r) ^ n * (3/50) ^ 2 := by
  rw [_root_.MathlibExt.Biology.PopulationGenetics.AdmixtureLD.DriftModel.weightedLD_admixedRef
    T (1/4) r n]
  · rw [T.f2_freq]
    simp [T, Fin.sum_univ_five]
    norm_num
  · ext e; fin_cases e <;> simp [T] <;> norm_num

end Tree

end MathlibExtTest.Biology.PopulationGenetics.AdmixtureLD
