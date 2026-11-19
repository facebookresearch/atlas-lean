/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.StatisticalGenetics.LDScoreRegression
public import MathlibExt.Biology.StatisticalGenetics.LDScoreVariance
public import Mathlib.Probability.Independence.InfinitePi
public import Mathlib.Probability.Independence.Integration

/-!
# LD-score regression along a sequence of block designs

`LDScoreRegression.tendstoInMeasure_olsH2Hat` (consistency of the unweighted LD-score
regression estimator `ĥ² = b̂ · M / N`) takes `Var(ĥ²) → 0` as a hypothesis, and
`LDScoreVariance` (T161) derives that limit from the LD-block model `LDBlockModel`
(block sizes at most `K`, statistics of different blocks independent, `Var(χ²_j) ≤ V`). This
file builds an actual sequence of designs on one probability space that satisfies the
hypotheses of both, proves them, and instantiates the variance bound, the variance limit and
the consistency theorem along it.

## The probability space

`Ω = ℕ → ℝ` with the product measure `coordMeasure ν = Measure.infinitePi (fun _ => ν)`: the
coordinates are i.i.d. with law `ν`, which is centred, has unit variance and is supported in
`[-C, C]` (`IsBoundedUnitLaw`; for example the Rademacher law with `C = 1`). The coordinates are
therefore orthonormal in `L²`, and every design of the sequence uses finitely many of them. For
`N` individuals and `M` markers with heritability `h² ∈ [0, 1]` (`model`):

* the effect of marker `k` is `β_k = √(h² / M) · ω (2 k)` (even coordinates);
* the noise of individual `i` is `ε_i = √(1 - h²) · ω (2 i + 1)` (odd coordinates).

These satisfy the second-moment conditions of `LDScore.Model` exactly, with mean-zero effects
and noise.

## The designs

A `BlockDesign N M K G` is a standardized genotype matrix `X` together with an LD block for
every marker and a cohort for every individual, such that

* every block has at most `K` markers and every cohort at most `G` individuals;
* `X i j ≠ 0` only when individual `i` belongs to the cohort of the block of marker `j`.

Within a block the LD is arbitrary (`ldCorr` may take any value in `[-1, 1]`); markers of
different blocks are uncorrelated (`ldCorr = 0`). The cohort condition is what makes the
statistics of different blocks independent for non-Gaussian noise: `β̂_j` involves only the
effects of the block of `j` and the noise of its cohort, and these sets of coordinates are
disjoint for different blocks. (For Gaussian effects and noise, uncorrelated columns would
already suffice; that case is not treated here.)

`replicate T b` is the concrete sequence: `b` copies of a standardized template block
`T : Matrix (Fin g) (Fin k) ℝ`, each on its own cohort of `g` individuals, rescaled by `√b` so
that the `b g × b k` matrix is standardized. Its LD scores are those of the template, repeated
`b` times, so `S_ℓℓ = b · S_ℓℓ(T)` and `N / M = g / k` for every `b`.

## Main results

* `model`: the random-effects model on the product space.
* `chiSqStrat_mem_Icc`, `indepFun_chiSqStrat`, `ldBlockModel`: along a block design with
  `N ≤ λ M`, the statistics are bounded by `chiSqBound K G C λ = G · 2 C² (K² λ + 1)`,
  statistics of different blocks are independent, and `LDBlockModel` holds with
  `V = (chiSqBound K G C λ / 2)²`.
* `variance_olsH2Hat_le`: the T161 variance bound
  `Var(ĥ²) ≤ (M / N)² · K V / S_ℓℓ` for one design.
* `tendsto_variance_olsH2Hat`, `tendstoInMeasure_olsH2Hat_blockDesign`: along designs with
  `M → ∞`, `κ M ≤ N ≤ λ M` and `S_ℓℓ ≥ c M`, `Var(ĥ²) → 0` and `ĥ² → h²` in probability.
* `replicate`, `ldScore_replicate`, `sxy_ldScore_replicate`: the replicated designs and their
  LD scores.
* `tendsto_variance_olsH2Hat_replicate`, `tendstoInMeasure_olsH2Hat_replicate`: for a template
  whose LD scores are not all equal and any numbers of copies `b n → ∞`, `Var(ĥ²) → 0` and
  `ĥ² → h²` in probability, with every hypothesis discharged.

## Assumptions, stated

The bounded support of `ν` gives the fourth-moment bound `Var(χ²_j) ≤ V` by an almost-sure
bound, which needs `N ≤ λ M`; the T161 limit needs `N ≥ κ M`. The cohort condition is a real
restriction on the genotype matrix (see above). The template must have LD scores that are not
all equal (`0 < S_ℓℓ(T)`): if every marker had the same LD score, the slope would not be
identified.

## References

* B. K. Bulik-Sullivan, P.-R. Loh, H. K. Finucane, S. Ripke, J. Yang, Schizophrenia Working
  Group of the Psychiatric Genomics Consortium, N. Patterson, M. J. Daly, A. L. Price,
  B. M. Neale, *LD Score regression distinguishes confounding from polygenicity in
  genome-wide association studies*, Nat. Genet. 47 (2015), 291–295.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Topology Finset
open MathlibExt.Biology.StatisticalGenetics.LDScore
  MathlibExt.Biology.StatisticalGenetics.LDScoreInflation
  MathlibExt.Biology.StatisticalGenetics.LDScoreRegression
  MathlibExt.Biology.StatisticalGenetics.LDScoreVariance
  MathlibExt.Probability.FiniteProbability

namespace MathlibExt.Biology.StatisticalGenetics.LDScoreDesignSequence

/-! ### The product space -/

/-- The product space `ℝ^ℕ` with i.i.d. coordinates of law `ν`. -/
noncomputable abbrev coordMeasure (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    Measure (ℕ → ℝ) :=
  Measure.infinitePi fun _ : ℕ => ν

/-- `ν` is centred, has unit variance, and is supported in `[-C, C]`. -/
structure IsBoundedUnitLaw (ν : Measure ℝ) (C : ℝ) : Prop where
  /-- `ν` is centred. -/
  integral_id : ∫ x, x ∂ν = 0
  /-- `ν` has unit variance. -/
  integral_sq : ∫ x, x ^ 2 ∂ν = 1
  /-- `ν` is supported in `[-C, C]`. -/
  ae_abs_le : ∀ᵐ x ∂ν, |x| ≤ C

variable {ν : Measure ℝ} [IsProbabilityMeasure ν] {C : ℝ}

theorem map_coord (s : ℕ) : (coordMeasure ν).map (fun ω => ω s) = ν :=
  Measure.infinitePi_map_eval _ s

/-- Almost surely every coordinate lies in `[-C, C]`. -/
theorem ae_abs_coord_le (hν : IsBoundedUnitLaw ν C) :
    ∀ᵐ ω ∂coordMeasure ν, ∀ s, |ω s| ≤ C := by
  rw [ae_all_iff]
  intro s
  have h : ∀ᵐ x ∂(coordMeasure ν).map (fun ω => ω s), |x| ≤ C := by
    rw [map_coord]
    exact hν.ae_abs_le
  exact ae_of_ae_map (measurable_pi_apply s).aemeasurable h

theorem memLp_coord (hν : IsBoundedUnitLaw ν C) (s : ℕ) :
    MemLp (fun ω : ℕ → ℝ => ω s) 2 (coordMeasure ν) :=
  MemLp.of_bound (measurable_pi_apply s).aestronglyMeasurable C
    ((ae_abs_coord_le hν).mono fun ω h => by simpa [Real.norm_eq_abs] using h s)

theorem integral_coord (hν : IsBoundedUnitLaw ν C) (s : ℕ) :
    ∫ ω, ω s ∂coordMeasure ν = 0 := by
  have h := integral_map (μ := coordMeasure ν) (measurable_pi_apply s).aemeasurable
    (f := fun x : ℝ => x) aestronglyMeasurable_id
  rw [map_coord] at h
  rw [← h, hν.integral_id]

/-- The coordinates are independent. -/
theorem iIndepFun_coord : iIndepFun (fun s (ω : ℕ → ℝ) => ω s) (coordMeasure ν) :=
  iIndepFun_infinitePi (P := fun _ => ν) (X := fun _ => id) fun _ => measurable_id

/-- The coordinates are orthonormal in `L²`. -/
theorem integral_coord_mul (hν : IsBoundedUnitLaw ν C) (s t : ℕ) :
    ∫ ω, ω s * ω t ∂coordMeasure ν = if s = t then 1 else 0 := by
  split_ifs with h
  · subst h
    have h := integral_map (μ := coordMeasure ν) (measurable_pi_apply s).aemeasurable
      (f := fun x : ℝ => x ^ 2) (by fun_prop)
    rw [map_coord] at h
    simp only [← sq]
    rw [← h, hν.integral_sq]
  · rw [(iIndepFun_coord.indepFun h).integral_fun_mul_eq_mul_integral
      (measurable_pi_apply s).aestronglyMeasurable (measurable_pi_apply t).aestronglyMeasurable,
      integral_coord hν, zero_mul]

/-! ### The random-effects model on the product space -/

private theorem sqrt_mul_sqrt_mul {a : ℝ} (ha : 0 ≤ a) (x y : ℝ) :
    √a * x * (√a * y) = a * (x * y) := by
  have h := Real.mul_self_sqrt ha
  calc √a * x * (√a * y) = (√a * √a) * (x * y) := by ring
    _ = a * (x * y) := by rw [h]

/-- **The model on the product space.** For `N` individuals and `M` markers with heritability
`h² ∈ [0, 1]`: the effect of marker `k` is `√(h² / M) · ω (2 k)` and the noise of individual
`i` is `√(1 - h²) · ω (2 i + 1)`. -/
noncomputable def model (hν : IsBoundedUnitLaw ν C) {h2 : ℝ} (h0 : 0 ≤ h2) (h1 : h2 ≤ 1)
    (N M : ℕ) : Model (coordMeasure ν) N M where
  h2 := h2
  beta k ω := √(h2 / M) * ω (2 * k)
  eps i ω := √(1 - h2) * ω (2 * i + 1)
  memLp_beta k := (memLp_coord hν _).const_mul _
  memLp_eps i := (memLp_coord hν _).const_mul _
  integral_beta_mul k l := by
    simp_rw [sqrt_mul_sqrt_mul (div_nonneg h0 M.cast_nonneg)]
    rw [integral_const_mul, integral_coord_mul hν]
    have e : (2 * (k : ℕ) = 2 * l) ↔ k = l := by rw [Fin.ext_iff]; omega
    by_cases hkl : k = l
    · subst hkl
      simp
    · rw [ite_eq_right (mt e.1 hkl), ite_eq_right hkl, mul_zero]
  integral_eps_mul i i' := by
    simp_rw [sqrt_mul_sqrt_mul (sub_nonneg.2 h1)]
    rw [integral_const_mul, integral_coord_mul hν]
    have e : (2 * (i : ℕ) + 1 = 2 * i' + 1) ↔ i = i' := by rw [Fin.ext_iff]; omega
    by_cases hii : i = i'
    · subst hii
      simp
    · rw [ite_eq_right (mt e.1 hii), ite_eq_right hii, mul_zero]
  integral_beta_mul_eps k i := by
    have e : ∀ ω : ℕ → ℝ, √(h2 / M) * ω (2 * k) * (√(1 - h2) * ω (2 * i + 1)) =
        √(h2 / M) * √(1 - h2) * (ω (2 * k) * ω (2 * i + 1)) := fun ω => by ring
    simp_rw [e]
    rw [integral_const_mul, integral_coord_mul hν, ite_eq_right_iff.2 fun h => by omega, mul_zero]

section Model

variable (hν : IsBoundedUnitLaw ν C) {h2 : ℝ} (h0 : 0 ≤ h2) (h1 : h2 ≤ 1) {N M : ℕ}

/-- The heritability of `model` is `h²`. -/
theorem model_h2 : (model hν h0 h1 N M).h2 = h2 := rfl

/-- The effects have mean zero. -/
theorem integral_model_beta (k : Fin M) :
    ∫ ω, (model hν h0 h1 N M).beta k ω ∂coordMeasure ν = 0 := by
  change ∫ ω, √(h2 / M) * ω (2 * k) ∂coordMeasure ν = 0
  rw [integral_const_mul, integral_coord hν, mul_zero]

/-- The noise has mean zero. -/
theorem integral_model_eps (i : Fin N) :
    ∫ ω, (model hν h0 h1 N M).eps i ω ∂coordMeasure ν = 0 := by
  change ∫ ω, √(1 - h2) * ω (2 * i + 1) ∂coordMeasure ν = 0
  rw [integral_const_mul, integral_coord hν, mul_zero]

/-- The statistic of marker `j` without stratification, written out:
`χ²_j = (∑ i, X i j * y i) ² / N` with `y i = ∑ k, X i k β_k + ε_i`. -/
theorem chiSqStrat_model (X : Matrix (Fin N) (Fin M) ℝ) (j : Fin M) (ω : ℕ → ℝ) :
    chiSqStrat (model hν h0 h1 N M) X 0 0 j ω =
      (∑ i, X i j * (∑ k, X i k * (√(h2 / M) * ω (2 * k)) +
        √(1 - h2) * ω (2 * i + 1))) ^ 2 / N := by
  simp only [chiSqStrat, betaHatStrat, phenoStrat, Model.pheno, model, zero_mul, add_zero]
  rcases eq_or_ne (N : ℝ) 0 with hN | hN
  · simp [hN]
  · field_simp
    congr 1
    refine sum_congr rfl fun i _ => ?_
    congr 2
    exact sum_congr rfl fun k _ => by ring

end Model

/-! ### Block designs -/

/-- A **block design** with `N` individuals and `M` markers: a standardized genotype matrix, an
LD block for every marker and a cohort for every individual, with at most `K` markers per
block and at most `G` individuals per cohort, such that `X i j ≠ 0` only when individual `i`
is in the cohort of the block of marker `j`. -/
structure BlockDesign (N M K G : ℕ) where
  /-- The genotype matrix. -/
  X : Matrix (Fin N) (Fin M) ℝ
  /-- The LD block of each marker. -/
  block : Fin M → ℕ
  /-- The cohort (labelled by an LD block) of each individual. -/
  group : Fin N → ℕ
  /-- The genotype matrix is standardized. -/
  isStandardized : IsStandardized X
  /-- Genotypes vanish (are at their mean) outside the cohort of the marker's block. -/
  support : ∀ i j, X i j ≠ 0 → group i = block j
  /-- Every LD block has at most `K` markers. -/
  card_block_le : ∀ b, #{k | block k = b} ≤ K
  /-- Every cohort has at most `G` individuals. -/
  card_group_le : ∀ b, #{i | group i = b} ≤ G

namespace BlockDesign

variable {N M K G : ℕ} (D : BlockDesign N M K G)

/-- Every genotype satisfies `X i j ^ 2 ≤ N`. -/
theorem sq_le (i : Fin N) (j : Fin M) : D.X i j ^ 2 ≤ N := by
  rw [← (D.isStandardized j).2]
  exact single_le_sum (f := fun i => D.X i j ^ 2) (fun _ _ => sq_nonneg _) (mem_univ i)

/-- Markers of different blocks are uncorrelated. -/
theorem ldCorr_eq_zero {j k : Fin M} (h : D.block j ≠ D.block k) : ldCorr D.X j k = 0 := by
  rw [ldCorr]
  have : ∀ i, D.X i j * D.X i k = 0 := fun i => by
    by_contra hne
    exact h ((D.support i j (left_ne_zero_of_mul hne)).symm.trans
      (D.support i k (right_ne_zero_of_mul hne)))
  simp [this]

end BlockDesign

/-! ### The almost-sure bound on the statistics -/

/-- The almost-sure bound `G · 2 C² (K² λ + 1)` on the statistics. -/
noncomputable def chiSqBound (K G : ℕ) (C lam : ℝ) : ℝ := G * (2 * C ^ 2 * (K ^ 2 * lam + 1))

section Bound

variable {N M K G : ℕ} (D : BlockDesign N M K G) {h2 : ℝ} (h0 : 0 ≤ h2) (h1 : h2 ≤ 1)
  {lam : ℝ} (hlam : 0 ≤ lam) (hNM : (N : ℝ) ≤ lam * M)

include h0 h1 hlam hNM in
/-- Pointwise bound on the phenotype: if every coordinate lies in `[-C, C]`, then
`y i ^ 2 ≤ 2 C² (K² λ + 1)`. -/
theorem pheno_sq_le {ω : ℕ → ℝ} (hω : ∀ s, |ω s| ≤ C) (i : Fin N) :
    (∑ k, D.X i k * (√(h2 / M) * ω (2 * k)) + √(1 - h2) * ω (2 * i + 1)) ^ 2 ≤
      2 * C ^ 2 * (K ^ 2 * lam + 1) := by
  have hsq : ∀ s, ω s ^ 2 ≤ C ^ 2 := fun s => by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (hω s) 2
  set T := ({k | D.block k = D.group i} : Finset (Fin M))
  have hT : #T ≤ K := D.card_block_le _
  have hsum : ∑ k, D.X i k * (√(h2 / M) * ω (2 * k)) =
      ∑ k ∈ T, D.X i k * (√(h2 / M) * ω (2 * k)) := by
    refine (sum_filter_of_ne fun k _ hk => ?_).symm
    exact (D.support i k (left_ne_zero_of_mul hk)).symm
  have hM : (0 : ℝ) ≤ h2 / M := div_nonneg h0 M.cast_nonneg
  -- the genetic part
  have hA : (∑ k ∈ T, D.X i k * (√(h2 / M) * ω (2 * k))) ^ 2 ≤ C ^ 2 * (K ^ 2 * lam) := by
    refine (sum_mul_sq_le_sq_mul_sq T _ _).trans ?_
    have hX : ∑ k ∈ T, D.X i k ^ 2 ≤ K * N := by
      calc ∑ k ∈ T, D.X i k ^ 2 ≤ #T • (N : ℝ) := sum_le_card_nsmul _ _ _ fun k _ => D.sq_le i k
        _ ≤ K * N := by
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hT) N.cast_nonneg
    have hb : ∑ k ∈ T, (√(h2 / M) * ω (2 * k)) ^ 2 ≤ K * (h2 / M * C ^ 2) := by
      calc ∑ k ∈ T, (√(h2 / M) * ω (2 * k)) ^ 2 ≤ #T • (h2 / M * C ^ 2) := by
            refine sum_le_card_nsmul _ _ _ fun k _ => ?_
            rw [mul_pow, Real.sq_sqrt hM]
            exact mul_le_mul_of_nonneg_left (hsq _) hM
        _ ≤ K * (h2 / M * C ^ 2) := by
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast hT) (by positivity)
    have hNM' : h2 / M * N ≤ lam := by
      rcases Nat.eq_zero_or_pos M with hM0 | hM0
      · simp [hM0, hlam]
      · have hMr : (0 : ℝ) < M := by exact_mod_cast hM0
        rw [div_mul_eq_mul_div, div_le_iff₀ hMr]
        nlinarith [N.cast_nonneg (α := ℝ)]
    calc (∑ k ∈ T, D.X i k ^ 2) * ∑ k ∈ T, (√(h2 / M) * ω (2 * k)) ^ 2
        ≤ (K * N) * (K * (h2 / M * C ^ 2)) :=
          mul_le_mul hX hb (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
      _ = C ^ 2 * K ^ 2 * (h2 / M * N) := by ring
      _ ≤ C ^ 2 * K ^ 2 * lam := mul_le_mul_of_nonneg_left hNM' (by positivity)
      _ = C ^ 2 * (K ^ 2 * lam) := by ring
  -- the noise part
  have hB : (√(1 - h2) * ω (2 * i + 1)) ^ 2 ≤ C ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (sub_nonneg.2 h1)]
    nlinarith [hsq (2 * i + 1), sq_nonneg (ω (2 * i + 1))]
  rw [hsum]
  nlinarith [sq_nonneg ((∑ k ∈ T, D.X i k * (√(h2 / M) * ω (2 * k))) -
    √(1 - h2) * ω (2 * i + 1))]

include h0 h1 hlam hNM in
/-- **Almost-sure bound on the statistics.** Along a block design with `N ≤ λ M`, on the event
that every coordinate lies in `[-C, C]`, `0 ≤ χ²_j ≤ chiSqBound K G C λ`. -/
theorem chiSqStrat_mem_Icc (hν : IsBoundedUnitLaw ν C) {ω : ℕ → ℝ} (hω : ∀ s, |ω s| ≤ C)
    (j : Fin M) :
    chiSqStrat (model hν h0 h1 N M) D.X 0 0 j ω ∈ Set.Icc 0 (chiSqBound K G C lam) := by
  rw [chiSqStrat_model]
  set y := fun i : Fin N =>
    ∑ k, D.X i k * (√(h2 / M) * ω (2 * k)) + √(1 - h2) * ω (2 * i + 1)
  change (∑ i, D.X i j * y i) ^ 2 / N ∈ Set.Icc 0 (chiSqBound K G C lam)
  refine ⟨by positivity, ?_⟩
  set S := ({i | D.group i = D.block j} : Finset (Fin N))
  have hP : 0 ≤ 2 * C ^ 2 * (K ^ 2 * lam + 1) := by positivity
  have hsum : ∑ i, D.X i j * y i = ∑ i ∈ S, D.X i j * y i :=
    (sum_filter_of_ne fun i _ hi => D.support i j (left_ne_zero_of_mul hi)).symm
  rcases eq_or_ne (N : ℝ) 0 with hN | hN
  · rw [hN, div_zero]
    exact mul_nonneg G.cast_nonneg hP
  have hNpos : (0 : ℝ) < N := lt_of_le_of_ne N.cast_nonneg hN.symm
  rw [div_le_iff₀ hNpos, hsum]
  have hX : ∑ i ∈ S, D.X i j ^ 2 ≤ N := by
    rw [← (D.isStandardized j).2]
    exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun _ _ _ => sq_nonneg _
  have hy : ∑ i ∈ S, y i ^ 2 ≤ G * (2 * C ^ 2 * (K ^ 2 * lam + 1)) := by
    calc ∑ i ∈ S, y i ^ 2 ≤ #S • (2 * C ^ 2 * (K ^ 2 * lam + 1)) :=
          sum_le_card_nsmul _ _ _ fun i _ => pheno_sq_le D h0 h1 hlam hNM hω i
      _ ≤ G * (2 * C ^ 2 * (K ^ 2 * lam + 1)) := by
          rw [nsmul_eq_mul]
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast D.card_group_le _) hP
  calc (∑ i ∈ S, D.X i j * y i) ^ 2 ≤ (∑ i ∈ S, D.X i j ^ 2) * ∑ i ∈ S, y i ^ 2 :=
        sum_mul_sq_le_sq_mul_sq S _ _
    _ ≤ N * (G * (2 * C ^ 2 * (K ^ 2 * lam + 1))) :=
        mul_le_mul hX hy (sum_nonneg fun _ _ => sq_nonneg _) N.cast_nonneg
    _ = chiSqBound K G C lam * N := by rw [chiSqBound]; ring

end Bound

/-! ### Independence of the statistics of different blocks -/

/-- The coordinates used by block `b`: the effects of its markers and the noise of its
cohort. -/
def coordSet {N M K G : ℕ} (D : BlockDesign N M K G) (b : ℕ) : Set ℕ :=
  {s | (∃ k : Fin M, D.block k = b ∧ s = 2 * k) ∨ (∃ i : Fin N, D.group i = b ∧ s = 2 * i + 1)}

theorem disjoint_coordSet {N M K G : ℕ} (D : BlockDesign N M K G) {b b' : ℕ} (h : b ≠ b') :
    Disjoint (coordSet D b) (coordSet D b') := by
  rw [Set.disjoint_left]
  rintro s (⟨k, hk, rfl⟩ | ⟨i, hi, rfl⟩) (⟨k', hk', e⟩ | ⟨i', hi', e⟩)
  · exact h (hk.symm.trans ((congrArg D.block (Fin.ext (by omega))).trans hk'))
  · omega
  · omega
  · exact h (hi.symm.trans ((congrArg D.group (Fin.ext (by omega))).trans hi'))

/-- The σ-algebra generated by the coordinates of block `b`. -/
abbrev blockSigma {N M K G : ℕ} (D : BlockDesign N M K G) (b : ℕ) : MeasurableSpace (ℕ → ℝ) :=
  ⨆ s ∈ coordSet D b, MeasurableSpace.comap (fun ω : ℕ → ℝ => ω s) inferInstance

theorem measurable_coord_blockSigma {N M K G : ℕ} (D : BlockDesign N M K G) {b s : ℕ}
    (hs : s ∈ coordSet D b) : Measurable[blockSigma D b] (fun ω : ℕ → ℝ => ω s) :=
  measurable_iff_comap_le.2 (le_iSup₂ (f := fun s (_ : s ∈ coordSet D b) =>
    MeasurableSpace.comap (fun ω : ℕ → ℝ => ω s) inferInstance) s hs)

section Indep

variable {N M K G : ℕ} (D : BlockDesign N M K G) (hν : IsBoundedUnitLaw ν C) {h2 : ℝ}
  (h0 : 0 ≤ h2) (h1 : h2 ≤ 1)

/-- The statistic of marker `j` depends only on the coordinates of its block. -/
theorem measurable_chiSqStrat_blockSigma (j : Fin M) :
    Measurable[blockSigma D (D.block j)] (chiSqStrat (model hν h0 h1 N M) D.X 0 0 j) := by
  have e : chiSqStrat (model hν h0 h1 N M) D.X 0 0 j = fun ω =>
      (∑ i, D.X i j * (∑ k, D.X i k * (√(h2 / M) * ω (2 * k)) +
        √(1 - h2) * ω (2 * i + 1))) ^ 2 / N := funext (chiSqStrat_model hν h0 h1 D.X j)
  rw [e]
  refine Measurable.div_const (Measurable.pow_const (Finset.measurable_sum _ fun i _ => ?_) 2) _
  by_cases hij : D.X i j = 0
  · simp only [hij, zero_mul]
    exact measurable_const
  have hg := D.support i j hij
  refine Measurable.const_mul (Measurable.add (Finset.measurable_sum _ fun k _ => ?_) ?_) _
  · by_cases hik : D.X i k = 0
    · simp only [hik, zero_mul]
      exact measurable_const
    · have hk : D.block k = D.block j := (D.support i k hik).symm.trans hg
      exact ((measurable_coord_blockSigma D (Or.inl ⟨k, hk, rfl⟩)).const_mul _).const_mul _
  · exact (measurable_coord_blockSigma D (Or.inr ⟨i, hg, rfl⟩)).const_mul _

/-- **Statistics of different blocks are independent.** -/
theorem indepFun_chiSqStrat {j k : Fin M} (h : D.block j ≠ D.block k) :
    IndepFun (chiSqStrat (model hν h0 h1 N M) D.X 0 0 j)
      (chiSqStrat (model hν h0 h1 N M) D.X 0 0 k) (coordMeasure ν) := by
  rw [IndepFun_iff_Indep]
  have hind := indep_iSup_of_disjoint
    (m := fun s => MeasurableSpace.comap (fun ω : ℕ → ℝ => ω s) inferInstance)
    (fun s => (measurable_pi_apply s).comap_le)
    ((iIndepFun_iff_iIndep _ _ _).1 (iIndepFun_coord (ν := ν))) (disjoint_coordSet D h)
  exact indep_of_indep_of_le hind
    (measurable_iff_comap_le.1 (measurable_chiSqStrat_blockSigma D hν h0 h1 j))
    (measurable_iff_comap_le.1 (measurable_chiSqStrat_blockSigma D hν h0 h1 k))

end Indep

/-! ### The LD-block model along a block design -/

section LDBlock

variable {N M K G : ℕ} (D : BlockDesign N M K G) (hν : IsBoundedUnitLaw ν C) {h2 : ℝ}
  (h0 : 0 ≤ h2) (h1 : h2 ≤ 1) {lam : ℝ} (hlam : 0 ≤ lam) (hNM : (N : ℝ) ≤ lam * M)

theorem measurable_chiSqStrat (j : Fin M) :
    Measurable (chiSqStrat (model hν h0 h1 N M) D.X 0 0 j) :=
  (measurable_chiSqStrat_blockSigma D hν h0 h1 j).mono
    (iSup₂_le fun s _ => (measurable_pi_apply s).comap_le) le_rfl

include hlam hNM in
/-- **The T161 hypotheses hold along a block design.** With `N ≤ λ M`, the statistics
`χ²_j = chiSqStrat` of `model` satisfy the LD-block model with block size at most `K` and
`Var(χ²_j) ≤ (chiSqBound K G C λ / 2)²`. -/
noncomputable def ldBlockModel :
    LDBlockModel (coordMeasure ν) (chiSqStrat (model hν h0 h1 N M) D.X 0 0) K
      ((chiSqBound K G C lam / 2) ^ 2) where
  block := D.block
  card_block_le j := D.card_block_le (D.block j)
  indepFun _ _ h := indepFun_chiSqStrat D hν h0 h1 h
  memLp j := MemLp.of_bound (measurable_chiSqStrat D hν h0 h1 j).aestronglyMeasurable
    (chiSqBound K G C lam) ((ae_abs_coord_le hν).mono fun ω hω => by
      have h := chiSqStrat_mem_Icc D h0 h1 hlam hNM hν hω j
      rw [Real.norm_eq_abs, abs_of_nonneg h.1]
      exact h.2)
  variance_le j := by
    have h := variance_le_sq_of_bounded ((ae_abs_coord_le hν).mono fun ω hω =>
      chiSqStrat_mem_Icc D h0 h1 hlam hNM hν hω j)
      (measurable_chiSqStrat D hν h0 h1 j).aemeasurable
    rwa [sub_zero] at h

include hlam hNM in
/-- **The T161 variance bound along a block design.** With `N ≤ λ M`,
`Var(ĥ²) ≤ (M / N)² · K V / S_ℓℓ` for `V = (chiSqBound K G C λ / 2)²`. -/
theorem variance_olsH2Hat_le :
    Var[fun ω => olsH2Hat N M (ldScore D.X) fun j => chiSqStrat (model hν h0 h1 N M) D.X 0 0 j ω;
      coordMeasure ν] ≤
      ((M : ℝ) / N) ^ 2 * (K * (chiSqBound K G C lam / 2) ^ 2 / sxy (ldScore D.X) (ldScore D.X)) :=
  variance_h2Hat_le (ldScore D.X) (ldBlockModel D hν h0 h1 hlam hNM).memLp
    (ldBlockModel D hν h0 h1 hlam hNM).sum_abs_covariance_le fun _ => rfl

end LDBlock

/-! ### The limit along a sequence of block designs -/

section Sequence

variable {ι : Type*} {l : Filter ι} {N M : ι → ℕ} {K G : ℕ}
  (D : ∀ n, BlockDesign (N n) (M n) K G) (hν : IsBoundedUnitLaw ν C) {h2 : ℝ}
  (h0 : 0 ≤ h2) (h1 : h2 ≤ 1) {κ lam c : ℝ} (hκ : 0 < κ) (hNM : ∀ n, κ * M n ≤ N n)
  (hNM' : ∀ n, (N n : ℝ) ≤ lam * M n) (hc : 0 < c)
  (hspread : ∀ n, c * M n ≤ sxy (ldScore (D n).X) (ldScore (D n).X)) (hM : Tendsto M l atTop)

omit [IsProbabilityMeasure ν] in
include hNM' in
/-- `N ≤ λ M` gives `N ≤ max λ 0 · M`. -/
theorem le_max_mul (n : ι) : (N n : ℝ) ≤ max lam 0 * M n :=
  (hNM' n).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (M n).cast_nonneg)

include hκ hNM hNM' hc hspread hM in
/-- **`Var(ĥ²) → 0` along a sequence of block designs** with `M → ∞`, `κ M ≤ N ≤ λ M`
(`κ > 0`) and LD-score spread `S_ℓℓ ≥ c M` (`c > 0`). -/
theorem tendsto_variance_olsH2Hat :
    Tendsto (fun n => Var[fun ω => olsH2Hat (N n) (M n) (ldScore (D n).X) fun j =>
      chiSqStrat (model hν h0 h1 (N n) (M n)) (D n).X 0 0 j ω; coordMeasure ν]) l (𝓝 0) := by
  exact tendsto_variance_h2Hat_of_ldBlock (fun n => ldScore (D n).X)
    (fun n => ldBlockModel (D n) hν h0 h1 (le_max_right lam 0) (le_max_mul hNM' n)) hc hκ hspread
    hNM hM fun _ _ => rfl

include hκ hNM hNM' hc hspread hM in
/-- **Consistency of LD-score regression along a sequence of block designs.** On the product
space, with the effects and noise of `model`, along block designs with `M → ∞` (every
`M n ≠ 0`), `κ M ≤ N ≤ λ M` (`κ > 0`) and LD-score spread `S_ℓℓ ≥ c M` (`c > 0`), the
unweighted LD-score regression estimator converges to `h²` in probability. Every hypothesis of
`tendstoInMeasure_olsH2Hat` is discharged; vanishing variance comes from T161. -/
theorem tendstoInMeasure_olsH2Hat_blockDesign (hM0 : ∀ n, M n ≠ 0) :
    TendstoInMeasure (coordMeasure ν) (fun n ω => olsH2Hat (N n) (M n) (ldScore (D n).X)
      fun j => chiSqStrat (model hν h0 h1 (N n) (M n)) (D n).X 0 0 j ω) l fun _ => h2 := by
  have hMr : ∀ n, (0 : ℝ) < M n := fun n => by exact_mod_cast Nat.pos_of_ne_zero (hM0 n)
  have hN : ∀ n, N n ≠ 0 := fun n => by
    have h := (mul_pos hκ (hMr n)).trans_le (hNM n)
    exact_mod_cast h.ne'
  have hℓ : ∀ n, sxy (ldScore (D n).X) (ldScore (D n).X) ≠ 0 := fun n =>
    ((mul_pos hc (hMr n)).trans_le (hspread n)).ne'
  have hvar := tendsto_evariance_h2Hat_chiSqStrat (fun n => model hν h0 h1 (N n) (M n))
    (fun n => (D n).X) (fun _ => 0) (fun n => (0 : Fin (N n) → ℝ))
    (fun n => ldBlockModel (D n) hν h0 h1 (le_max_right lam 0) (le_max_mul hNM' n)) hc hκ hspread
    hNM hM (est := fun n ω => olsH2Hat (N n) (M n) (ldScore (D n).X) fun j =>
      chiSqStrat (model hν h0 h1 (N n) (M n)) (D n).X 0 0 j ω) fun _ _ => rfl
  exact tendstoInMeasure_olsH2Hat (fun n => model hν h0 h1 (N n) (M n)) (fun n => (D n).X)
    (fun _ => rfl) hN hM0 (fun n => (D n).isStandardized) hℓ
    (fun _ => integral_model_beta hν h0 h1) (fun _ => integral_model_eps hν h0 h1) (fun _ => 0)
    (fun n => (0 : Fin (N n) → ℝ)) (fun _ => 0) (fun _ _ => by simp) hvar

end Sequence

/-! ### The replicated designs -/

section Replicate

/-- A sum over `Fin (b * n)` as a double sum over copies `u : Fin b` and positions
`r : Fin n`. -/
theorem sum_fin_mul {b n : ℕ} (f : Fin (b * n) → ℝ) :
    ∑ i, f i = ∑ u : Fin b, ∑ r : Fin n, f (finProdFinEquiv (u, r)) := by
  rw [← finProdFinEquiv.sum_comp, Fintype.sum_prod_type]

/-- A function of the position within the copy, summed over all `b` copies. -/
theorem sum_comp_snd {b n : ℕ} (f : Fin n → ℝ) :
    ∑ i : Fin (b * n), f (finProdFinEquiv.symm i).2 = b * ∑ r, f r := by
  rw [sum_fin_mul]
  simp

variable {g k : ℕ} (T : Matrix (Fin g) (Fin k) ℝ)

/-- **The replicated design.** `b` copies of the template block `T : Matrix (Fin g) (Fin k) ℝ`,
each on its own cohort of `g` individuals, rescaled by `√b`: the genotype of individual
`(u, r)` at marker `(u', a)` is `√b · T r a` if `u = u'` and `0` otherwise. -/
noncomputable def replicate (b : ℕ) : Matrix (Fin (b * g)) (Fin (b * k)) ℝ := fun i j =>
  if (finProdFinEquiv.symm i).1 = (finProdFinEquiv.symm j).1 then
    √(b : ℝ) * T (finProdFinEquiv.symm i).2 (finProdFinEquiv.symm j).2
  else 0

theorem replicate_apply (b : ℕ) (u u' : Fin b) (r : Fin g) (a : Fin k) :
    replicate T b (finProdFinEquiv (u, r)) (finProdFinEquiv (u', a)) =
      if u = u' then √(b : ℝ) * T r a else 0 := by
  simp only [replicate, Equiv.symm_apply_apply]

/-- The replicated design of a standardized template is standardized. -/
theorem isStandardized_replicate (hT : IsStandardized T) (b : ℕ) :
    IsStandardized (replicate T b) := by
  intro j
  obtain ⟨⟨u, a⟩, rfl⟩ := finProdFinEquiv.surjective j
  constructor
  · rw [sum_fin_mul]
    simp only [replicate_apply]
    rw [sum_eq_single u (fun u' _ h => by simp [h]) (by simp)]
    simp [← mul_sum, (hT a).1]
  · rw [sum_fin_mul]
    simp only [replicate_apply]
    rw [sum_eq_single u (fun u' _ h => by simp [h]) (by simp)]
    simp only [ite_true, mul_pow, Real.sq_sqrt (Nat.cast_nonneg b), ← mul_sum, (hT a).2]
    push_cast
    ring

/-- The LD of the replicated design: markers of the same copy have the template's LD, markers
of different copies are uncorrelated. -/
theorem ldCorr_replicate {b : ℕ} (hb : b ≠ 0) (u u' : Fin b) (a a' : Fin k) :
    ldCorr (replicate T b) (finProdFinEquiv (u, a)) (finProdFinEquiv (u', a')) =
      if u = u' then ldCorr T a a' else 0 := by
  have hb' : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hb
  rw [ldCorr, sum_fin_mul]
  simp only [replicate_apply]
  by_cases h : u = u'
  · subst h
    rw [sum_eq_single u (fun u'' _ h => by simp [h]) (by simp)]
    simp only [ite_true, ldCorr]
    have e : ∀ r, √(b : ℝ) * T r a * (√(b : ℝ) * T r a') = b * (T r a * T r a') := fun r =>
      sqrt_mul_sqrt_mul (Nat.cast_nonneg b) _ _
    simp only [e, ← mul_sum]
    push_cast
    rcases eq_or_ne (g : ℝ) 0 with hg | hg
    · simp [hg]
    · field_simp
  · rw [ite_eq_right h]
    refine div_eq_zero_iff.2 (Or.inl (sum_eq_zero fun u'' _ => sum_eq_zero fun r _ => ?_))
    by_cases h' : u'' = u
    · subst h'
      simp [h]
    · simp [h']

/-- **The LD scores of the replicated design** are those of the template. -/
theorem ldScore_replicate {b : ℕ} (hb : b ≠ 0) :
    ldScore (replicate T b) = fun j => ldScore T (finProdFinEquiv.symm j).2 := by
  funext j
  obtain ⟨⟨u, a⟩, rfl⟩ := finProdFinEquiv.surjective j
  rw [ldScore, sum_fin_mul]
  simp only [ldCorr_replicate T hb, Equiv.symm_apply_apply]
  rw [sum_eq_single u (fun u' _ h => by simp [Ne.symm h]) (by simp)]
  simp [ldScore]

/-- **The LD-score spread of the replicated design** is `b` times that of the template. -/
theorem sxy_ldScore_replicate {b : ℕ} (hb : b ≠ 0) :
    sxy (ldScore (replicate T b)) (ldScore (replicate T b)) =
      b * sxy (ldScore T) (ldScore T) := by
  have hb' : (b : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hb
  have hmean : sampleMean (fun j : Fin (b * k) => ldScore T (finProdFinEquiv.symm j).2) =
      sampleMean (ldScore T) := by
    rw [sampleMean_eq_sum_div, sampleMean_eq_sum_div, sum_comp_snd, Fintype.card_fin,
      Fintype.card_fin]
    push_cast
    rcases eq_or_ne (k : ℝ) 0 with hk | hk
    · simp [hk]
    · field_simp
  rw [ldScore_replicate T hb, sxy, hmean, sum_comp_snd (fun r =>
    (ldScore T r - sampleMean (ldScore T)) * (ldScore T r - sampleMean (ldScore T))), sxy]

/-- **The replicated block design**: blocks and cohorts are the copies; every block has `k`
markers and every cohort `g` individuals. -/
noncomputable def replicateDesign (hT : IsStandardized T) (b : ℕ) :
    BlockDesign (b * g) (b * k) k g where
  X := replicate T b
  block j := (finProdFinEquiv.symm j).1
  group i := (finProdFinEquiv.symm i).1
  isStandardized := isStandardized_replicate T hT b
  support i j h := by
    by_contra hne
    exact h (ite_eq_right fun e => hne (congrArg Fin.val e))
  card_block_le c := by
    calc #{j : Fin (b * k) | ((finProdFinEquiv.symm j).1 : ℕ) = c}
        ≤ #(univ : Finset (Fin k)) := card_le_card_of_injOn (fun j => (finProdFinEquiv.symm j).2)
          (fun _ _ => mem_coe.2 (mem_univ _)) fun j hj j' hj' e => by
            simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hj hj'
            exact finProdFinEquiv.symm.injective (Prod.ext (Fin.ext (hj.trans hj'.symm)) e)
      _ = k := by simp
  card_group_le c := by
    calc #{i : Fin (b * g) | ((finProdFinEquiv.symm i).1 : ℕ) = c}
        ≤ #(univ : Finset (Fin g)) := card_le_card_of_injOn (fun i => (finProdFinEquiv.symm i).2)
          (fun _ _ => mem_coe.2 (mem_univ _)) fun i hi i' hi' e => by
            simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hi hi'
            exact finProdFinEquiv.symm.injective (Prod.ext (Fin.ext (hi.trans hi'.symm)) e)
      _ = g := by simp

/-- A template whose LD scores are not all equal has at least one individual and one
marker. -/
theorem pos_of_sxy_ldScore (hspread : 0 < sxy (ldScore T) (ldScore T)) : 0 < g ∧ 0 < k := by
  refine ⟨Nat.pos_of_ne_zero fun hg => ?_, Nat.pos_of_ne_zero fun hk => ?_⟩
  · subst hg
    simp [sxy, ldScore, ldCorr, sampleMean_eq_sum_div] at hspread
  · subst hk
    simp [sxy] at hspread

variable {ι : Type*} {l : Filter ι} (hν : IsBoundedUnitLaw ν C) {h2 : ℝ} (h0 : 0 ≤ h2)
  (h1 : h2 ≤ 1) (hT : IsStandardized T) (hspread : 0 < sxy (ldScore T) (ldScore T))
  {b : ι → ℕ} (hb0 : ∀ n, b n ≠ 0) (hb : Tendsto b l atTop)

include hT hspread hb0 hb in
/-- **`Var(ĥ²) → 0` along the replicated designs.** For a standardized template whose LD scores
are not all equal and numbers of copies `b n → ∞`, the variance of the unweighted LD-score
regression estimator tends to `0`. -/
theorem tendsto_variance_olsH2Hat_replicate :
    Tendsto (fun n => Var[fun ω => olsH2Hat (b n * g) (b n * k) (ldScore (replicate T (b n)))
      fun j => chiSqStrat (model hν h0 h1 (b n * g) (b n * k)) (replicate T (b n)) 0 0 j ω;
      coordMeasure ν]) l (𝓝 0) := by
  obtain ⟨hg, hk⟩ := pos_of_sxy_ldScore T hspread
  have hk' : (k : ℝ) ≠ 0 := by positivity
  exact tendsto_variance_olsH2Hat (fun n => replicateDesign T hT (b n)) hν h0 h1
    (κ := g / k) (lam := g / k) (c := sxy (ldScore T) (ldScore T) / k) (by positivity)
    (fun n => le_of_eq (by push_cast; field_simp)) (fun n => le_of_eq (by push_cast; field_simp))
    (by positivity)
    (fun n => le_of_eq (by
      change _ = sxy (ldScore (replicate T (b n))) (ldScore (replicate T (b n)))
      rw [sxy_ldScore_replicate T (hb0 n)]
      push_cast
      field_simp))
    (tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right (b n) hk) hb)

include hT hspread hb0 hb in
/-- **Consistency of LD-score regression along the replicated designs.** On the product space,
for a standardized template block `T` whose LD scores are not all equal and numbers of copies
`b n → ∞` (each `b n ≠ 0`), the unweighted LD-score regression estimator of the
`b n g × b n k` replicated design converges in probability to `h²`. Every hypothesis of
`tendstoInMeasure_olsH2Hat` and of T161 is discharged: `κ = λ = g / k`, `c = S_ℓℓ(T) / k`,
`K = k`, `G = g`. -/
theorem tendstoInMeasure_olsH2Hat_replicate :
    TendstoInMeasure (coordMeasure ν) (fun n ω => olsH2Hat (b n * g) (b n * k)
      (ldScore (replicate T (b n))) fun j =>
        chiSqStrat (model hν h0 h1 (b n * g) (b n * k)) (replicate T (b n)) 0 0 j ω)
      l fun _ => h2 := by
  obtain ⟨hg, hk⟩ := pos_of_sxy_ldScore T hspread
  have hk' : (k : ℝ) ≠ 0 := by positivity
  exact tendstoInMeasure_olsH2Hat_blockDesign (fun n => replicateDesign T hT (b n)) hν h0 h1
    (κ := g / k) (lam := g / k) (c := sxy (ldScore T) (ldScore T) / k) (by positivity)
    (fun n => le_of_eq (by push_cast; field_simp)) (fun n => le_of_eq (by push_cast; field_simp))
    (by positivity)
    (fun n => le_of_eq (by
      change _ = sxy (ldScore (replicate T (b n))) (ldScore (replicate T (b n)))
      rw [sxy_ldScore_replicate T (hb0 n)]
      push_cast
      field_simp))
    (tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right (b n) hk) hb)
    fun n => mul_ne_zero (hb0 n) hk.ne'

end Replicate

end MathlibExt.Biology.StatisticalGenetics.LDScoreDesignSequence
