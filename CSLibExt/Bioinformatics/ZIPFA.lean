/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Sigmoid
public import MathlibExt.Probability.Statistics.PoissonLikelihood

/-!
# Zero-inflated Poisson factor analysis

Xu, Demmer, and Li, *Zero-inflated Poisson factor model with application to microbiome read
counts*, Biometrics 77(1), 91–101 (2021), §2.1 and equation (1), DOI 10.1111/biom.13272.

The log of the normalized rate is a dot product of scores and loadings. The structural-zero
probability depends on that rate, not on the sample-specific offset. The law on count arrays
is the finite product of the cell laws. Library-size offsets are supplied fixed positive
numbers: this is a likelihood at supplied offsets, not a conditional law obtained by taking
offsets to be random functions of the generated count array. This file does not model the
calculation of offsets from a dataset, EM fitting, or selection of the factor dimension.
-/

@[expose] public section

set_option autoImplicit false

namespace Cslib.Bioinformatics.ZIPFA

open MeasureTheory ProbabilityTheory Real
open MathlibExt.Probability.Statistics.PoissonLikelihood (poissonLik)
open scoped ENNReal NNReal unitInterval

/-- A zero-inflated Poisson law: return zero with probability `p` and otherwise draw from
`poissonMeasure μ`. The Poisson component can itself produce zeros. -/
noncomputable def zipMeasure (p : I) (μ : ℝ≥0) : Measure ℕ :=
  ENNReal.ofReal (p : ℝ) • Measure.dirac 0 + ENNReal.ofReal (1 - (p : ℝ)) • poissonMeasure μ

instance (p : I) (μ : ℝ≥0) : IsProbabilityMeasure (zipMeasure p μ) := by
  constructor
  simp only [zipMeasure, add_apply, smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [← ENNReal.ofReal_add p.property.1 (sub_nonneg.mpr p.property.2), add_sub_cancel,
    ENNReal.ofReal_one]

/-- The probability of an observed count, with the structural term present only at zero. -/
theorem zipMeasure_real_singleton (p : I) (μ : ℝ≥0) (k : ℕ) :
    (zipMeasure p μ).real {k} = (if k = 0 then (p : ℝ) else 0) +
      (1 - (p : ℝ)) * poissonLik μ k := by
  have h₁ : (ENNReal.ofReal (p : ℝ) • Measure.dirac (0 : ℕ)) {k} ≠ ∞ := by
    rw [smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  have h₂ : (ENNReal.ofReal (1 - (p : ℝ)) • poissonMeasure μ) {k} ≠ ∞ := by
    rw [smul_apply, smul_eq_mul]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)
  rw [zipMeasure, measureReal_add_apply h₁ h₂, measureReal_ennreal_smul_apply,
    measureReal_ennreal_smul_apply, ENNReal.toReal_ofReal p.property.1,
    ENNReal.toReal_ofReal (sub_nonneg.mpr p.property.2), poissonMeasure_real_singleton]
  cases k <;> simp [poissonLik, measureReal_def]

/-- The probability of observing zero includes both the structural and sampling zeros. -/
theorem zipMeasure_real_zero (p : I) (μ : ℝ≥0) :
    (zipMeasure p μ).real {0} = (p : ℝ) + (1 - (p : ℝ)) * exp (-(μ : ℝ)) := by
  simp [zipMeasure_real_singleton, poissonLik]

/-- **Parameters of the ZIPFA model.** `n`, `m`, and `K` count samples, taxa, and factors.
The factor dimension is strictly below both array dimensions, but the log-rate matrix need
not have rank exactly `K`. The same positive shape parameter is used at every cell. -/
structure Parameters (n m K : ℕ) where
  /-- The sample scores, indexed by sample and factor. -/
  scores : Fin n → Fin K → ℝ
  /-- The taxon loadings, indexed by taxon and factor. -/
  loadings : Fin m → Fin K → ℝ
  /-- A fixed relative library size for each sample. -/
  offset : Fin n → ℝ≥0
  offset_pos : ∀ i, 0 < offset i
  /-- The shared shape parameter. -/
  shape : ℝ
  shape_pos : 0 < shape
  dimension_lt : K < min n m

namespace Parameters

variable {n m K : ℕ}

/-- The factored normalized log-rate at sample `i` and taxon `j`. -/
noncomputable def logRate (P : Parameters n m K) (i : Fin n) (j : Fin m) : ℝ :=
  ∑ k, P.scores i k * P.loadings j k

/-- The Poisson-component mean after applying the sample offset. -/
noncomputable def mean (P : Parameters n m K) (i : Fin n) (j : Fin m) : ℝ≥0 :=
  P.offset i * ⟨exp (P.logRate i j), (exp_pos _).le⟩

/-- The probability of a structural zero is the sigmoid of the negative shared shape
parameter times the normalized log-rate. It does not depend on the offset. -/
noncomputable def zeroProb (P : Parameters n m K) (i : Fin n) (j : Fin m) : I :=
  unitInterval.sigmoid (-(P.shape * P.logRate i j))

/-- The structural-zero log odds are minus the common shape times the normalized log-rate. -/
theorem log_odds_zeroProb (P : Parameters n m K) (i : Fin n) (j : Fin m) :
    log ((P.zeroProb i j : ℝ) / (1 - (P.zeroProb i j : ℝ))) = -(P.shape * P.logRate i j) := by
  let x := -(P.shape * P.logRate i j)
  change log (sigmoid x / (1 - sigmoid x)) = x
  have h : sigmoid x * exp (-x) = 1 - sigmoid x :=
    (sigmoid_mul_rexp_neg x).trans (sigmoid_neg x)
  rw [← h, div_mul_eq_div_div, div_self (sigmoid_pos x).ne', one_div, ← exp_neg, neg_neg, log_exp]

/-- The count law at a single sample–taxon pair. -/
noncomputable def cellLaw (P : Parameters n m K) (i : Fin n) (j : Fin m) : Measure ℕ :=
  zipMeasure (P.zeroProb i j) (P.mean i j)

instance (P : Parameters n m K) (i : Fin n) (j : Fin m) :
    IsProbabilityMeasure (P.cellLaw i j) :=
  inferInstanceAs (IsProbabilityMeasure (zipMeasure _ _))

/-- **ZIPFA count-array law.** The sample–taxon counts are independent given the supplied
parameters and fixed offsets, with the zero-inflated Poisson law at each cell. -/
noncomputable def countLaw (P : Parameters n m K) : Measure ((Fin n × Fin m) → ℕ) :=
  Measure.pi (fun ij : Fin n × Fin m => P.cellLaw ij.1 ij.2)

instance (P : Parameters n m K) : IsProbabilityMeasure P.countLaw :=
  inferInstanceAs (IsProbabilityMeasure (Measure.pi _))

/-- **ZIPFA likelihood.** An array has probability equal to the product of its cell masses.
The structural-zero term is included exactly at the cells whose observed count is zero. -/
theorem countLaw_real_singleton (P : Parameters n m K) (a : (Fin n × Fin m) → ℕ) :
    P.countLaw.real {a} = ∏ ij : Fin n × Fin m,
      ((if a ij = 0 then (P.zeroProb ij.1 ij.2 : ℝ) else 0) +
        (1 - (P.zeroProb ij.1 ij.2 : ℝ)) * poissonLik (P.mean ij.1 ij.2) (a ij)) := by
  rw [countLaw, measureReal_def, ← Set.univ_pi_singleton a, Measure.pi_pi, ENNReal.toReal_prod]
  exact Finset.prod_congr rfl (fun ij _ => zipMeasure_real_singleton _ _ _)

end Parameters

end Cslib.Bioinformatics.ZIPFA
