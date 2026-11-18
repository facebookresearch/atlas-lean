/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Biology.PopulationGenetics.FStatistics
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# The Gaussian (TreeMix) surrogate of the drift model

The multivariate normal law `N(m 1, W diag(len) Wᵀ)` of population allele frequencies has
the same f-statistics as every drift model with the same lineage weights and edge lengths,
since f-statistics only see second moments. Unlike genuine allele frequencies it does not
stay in `[0, 1]`: if a population has positive variance, its frequency is negative with
positive probability. With zero variance the frequency is the root mean almost surely.

## Main results

* `Admixture.f4_gaussianSurrogate`: the f4 formula for the surrogate.
* `Admixture.f4_gaussianSurrogate_eq`, `Admixture.f2_gaussianSurrogate_eq`,
  `Admixture.f3_gaussianSurrogate_eq`: agreement with every drift model with the same
  weights and lengths.
* `Admixture.gaussianSurrogate_coord_neg_pos`: positive variance gives a negative
  frequency with positive probability.
* `Admixture.gaussianSurrogate_coord_ae_eq`: the zero-variance endpoint.

## References

* J. K. Pickrell and J. K. Pritchard, "Inference of population splits and mixtures from
  genome-wide allele frequency data", *PLoS Genetics* 8 (2012), e1002967.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix MathlibExt.Biology.PopulationGenetics.FStatistics
open scoped NNReal

namespace MathlibExt.Biology.PopulationGenetics.Admixture

variable {P E : Type*} [Fintype P] [DecidableEq P] [Fintype E] [DecidableEq E]

/-- The TreeMix covariance `W diag(len) Wᵀ` of a weight matrix `w : P → E → ℝ` and edge
lengths `len : E → ℝ≥0`. -/
noncomputable def driftCov (w : P → E → ℝ) (len : E → ℝ≥0) : Matrix P P ℝ :=
  Matrix.of w * diagonal (fun e => (len e : ℝ)) * (Matrix.of w)ᵀ

omit [Fintype P] [DecidableEq P] in
/-- Entries of the TreeMix covariance: `Σ X Y = ∑ e, w X e * w Y e * len e`. -/
theorem driftCov_apply (w : P → E → ℝ) (len : E → ℝ≥0) (X Y : P) :
    driftCov w len X Y = ∑ e, w X e * w Y e * (len e : ℝ) := by
  rw [driftCov, Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, Matrix.of_apply]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

omit [Fintype P] [DecidableEq P] in
/-- The TreeMix covariance is positive semidefinite. -/
theorem posSemidef_driftCov [Finite P] (w : P → E → ℝ) (len : E → ℝ≥0) :
    (driftCov w len).PosSemidef := by
  have hd : (diagonal fun e => (len e : ℝ)).PosSemidef :=
    Matrix.PosSemidef.diagonal fun e => (len e).2
  simpa [driftCov, Matrix.conjTranspose_eq_transpose_of_trivial] using
    hd.mul_mul_conjTranspose_same (Matrix.of w)

/-- The Gaussian drift surrogate (TreeMix): the law `N(m 1, W diag(len) Wᵀ)` of the vector of
population allele frequencies, on `EuclideanSpace ℝ P`. -/
noncomputable def gaussianSurrogate (m : ℝ) (w : P → E → ℝ) (len : E → ℝ≥0) :
    Measure (EuclideanSpace ℝ P) :=
  multivariateGaussian (WithLp.toLp 2 fun _ => m) (driftCov w len)

instance (m : ℝ) (w : P → E → ℝ) (len : E → ℝ≥0) :
    IsProbabilityMeasure (gaussianSurrogate m w len) := by
  unfold gaussianSurrogate
  infer_instance

/-- The frequency of population `X` under the surrogate: the `X` coordinate. -/
def coordFreq : P → EuclideanSpace ℝ P → ℝ := fun X x => x X

private theorem mp_eval (m : ℝ) (w : P → E → ℝ) (len : E → ℝ≥0) (X : P) :
    MeasurePreserving (fun x : EuclideanSpace ℝ P => x X) (gaussianSurrogate m w len)
      (gaussianReal m (driftCov w len X X).toNNReal) := by
  simpa [gaussianSurrogate] using
    measurePreserving_eval_multivariateGaussian (μ := WithLp.toLp 2 fun _ => m)
      (posSemidef_driftCov w len) (i := X)

private theorem memLp_eval (m : ℝ) (w : P → E → ℝ) (len : E → ℝ≥0) (X : P) : MemLp (fun x : EuclideanSpace ℝ P => x X) 2 (gaussianSurrogate m w len) :=
  (memLp_id_gaussianReal' 2 (by simp)).comp_measurePreserving (mp_eval m w len X)

private theorem integral_eval (m : ℝ) (w : P → E → ℝ) (len : E → ℝ≥0) (X : P) : ∫ x, x X ∂(gaussianSurrogate m w len) = m := by
  have h := integral_map (μ := gaussianSurrogate m w len) (mp_eval m w len X).aemeasurable
    (f := id) aestronglyMeasurable_id
  rw [(mp_eval m w len X).map_eq] at h
  simp only [id] at h
  rw [integral_id_gaussianReal] at h
  exact h.symm

private theorem integral_centered_mul (m : ℝ) (w : P → E → ℝ) (len : E → ℝ≥0) (X Y : P) :
    ∫ x, (x X - m) * (x Y - m) ∂(gaussianSurrogate m w len) = driftCov w len X Y := by
  have h := covariance_eval_multivariateGaussian (μ := WithLp.toLp 2 fun _ => m)
    (posSemidef_driftCov w len) X Y
  unfold covariance at h
  change ∫ ω, (ω X - ∫ x, x X ∂(gaussianSurrogate m w len)) *
      (ω Y - ∫ x, x Y ∂(gaussianSurrogate m w len)) ∂(gaussianSurrogate m w len) = _ at h
  rwa [integral_eval m w len X, integral_eval m w len Y] at h

/-- f-statistics of the Gaussian surrogate: `f4 A B C D = ∑ e, (w A e - w B e) (w C e - w D e) len e`,
the drift-model formula. -/
theorem f4_gaussianSurrogate (m : ℝ) (w : P → E → ℝ) {len : E → ℝ≥0}
    (A B C D : P) :
    f4 (gaussianSurrogate m w len) coordFreq A B C D =
      ∑ e, (w A e - w B e) * (w C e - w D e) * (len e : ℝ) := by
  set ν := gaussianSurrogate m w len
  have hc : ∀ X, MemLp (fun x : EuclideanSpace ℝ P => x X - m) 2 ν := fun X =>
    (memLp_eval m w len X).sub (memLp_const m)
  have hi : ∀ X Y, Integrable (fun x : EuclideanSpace ℝ P => (x X - m) * (x Y - m)) ν :=
    fun X Y => (hc X).integrable_mul (hc Y)
  have hpt : ∀ x : EuclideanSpace ℝ P, (x A - x B) * (x C - x D) =
      (x A - m) * (x C - m) - (x A - m) * (x D - m) - ((x B - m) * (x C - m)) +
        (x B - m) * (x D - m) := fun x => by ring
  unfold f4 coordFreq
  simp_rw [hpt]
  have e1 := integral_add (μ := ν) (((hi A C).sub (hi A D)).sub (hi B C)) (hi B D)
  have e2 := integral_sub (μ := ν) ((hi A C).sub (hi A D)) (hi B C)
  have e3 := integral_sub (μ := ν) (hi A C) (hi A D)
  simp only [Pi.sub_apply] at e1 e2
  rw [e1, e2, e3]
  simp only [ν, integral_centered_mul m w len, driftCov_apply, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun e _ => ?_
  ring

/-- The surrogate has the same f-statistics as every drift model with the same weights and
lengths: `f4` agrees, whatever the probability space and increment laws of the drift model. -/
theorem f4_gaussianSurrogate_eq {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (M : DriftModel μ E P) (m : ℝ) (A B C D : P) :
    f4 (gaussianSurrogate m M.weight (fun e => ⟨M.len e, M.len_nonneg e⟩)) coordFreq A B C D =
      f4 μ M.freq A B C D := by
  have h := f4_gaussianSurrogate (len := fun e => ⟨M.len e, M.len_nonneg e⟩) m M.weight A B C D
  rw [h, M.f4_freq]
  exact Finset.sum_congr rfl fun e _ => rfl

/-- `f2` agrees with every drift model with the same weights and lengths. -/
theorem f2_gaussianSurrogate_eq {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (M : DriftModel μ E P) (m : ℝ) (X Y : P) :
    f2 (gaussianSurrogate m M.weight (fun e => ⟨M.len e, M.len_nonneg e⟩)) coordFreq X Y =
      f2 μ M.freq X Y := by
  rw [f2_eq_f4, f2_eq_f4, f4_gaussianSurrogate_eq]

/-- `f3` agrees with every drift model with the same weights and lengths. -/
theorem f3_gaussianSurrogate_eq {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    (M : DriftModel μ E P) (m : ℝ) (C A B : P) :
    f3 (gaussianSurrogate m M.weight (fun e => ⟨M.len e, M.len_nonneg e⟩)) coordFreq C A B =
      f3 μ M.freq C A B := by
  rw [f3_eq_f4, f3_eq_f4, f4_gaussianSurrogate_eq]

/-- The surrogate does not preserve the frequency simplex: if `Σ_XX > 0`, the frequency of `X` is
negative with positive probability, whatever the root mean `m`. -/
theorem gaussianSurrogate_coord_neg_pos (m : ℝ) (w : P → E → ℝ) {len : E → ℝ≥0} {X : P} (hX : 0 < driftCov w len X X) :
    0 < gaussianSurrogate m w len {x | x X < 0} := by
  have hv : (driftCov w len X X).toNNReal ≠ 0 := by simpa using hX
  have hset : {x : EuclideanSpace ℝ P | x X < 0} = (fun x => x X) ⁻¹' Set.Iio 0 := rfl
  rw [hset, ← Measure.map_apply (mp_eval m w len X).measurable measurableSet_Iio,
    (mp_eval m w len X).map_eq, pos_iff_ne_zero]
  intro h0
  have := gaussianReal_absolutelyContinuous' m hv h0
  simp at this

/-- If `Σ_XX > 0`, the frequency of `X` leaves `[0, 1]` with positive probability. -/
theorem gaussianSurrogate_coord_not_mem_Icc_pos (m : ℝ) (w : P → E → ℝ) {len : E → ℝ≥0} {X : P} (hX : 0 < driftCov w len X X) :
    0 < gaussianSurrogate m w len {x | x X ∉ Set.Icc (0 : ℝ) 1} :=
  (gaussianSurrogate_coord_neg_pos m w hX).trans_le
    (measure_mono fun _ hx h => absurd h.1 (not_le.mpr hx))

/-- Zero-variance endpoint: if `Σ_XX = 0`, the frequency of `X` is the root mean `m` almost
surely, so the hypothesis `Σ_XX > 0` above cannot be dropped. -/
theorem gaussianSurrogate_coord_ae_eq (m : ℝ) (w : P → E → ℝ) {len : E → ℝ≥0} {X : P} (hX : driftCov w len X X = 0) :
    ∀ᵐ x ∂(gaussianSurrogate m w len), x X = m := by
  have hmap := (mp_eval m w len X).map_eq
  rw [hX, Real.toNNReal_zero, gaussianReal_zero_var] at hmap
  have h : ∀ᵐ y ∂(Measure.dirac m), y = m := (ae_dirac_iff (measurableSet_singleton m)).2 rfl
  rw [← hmap] at h
  exact ae_of_ae_map (mp_eval m w len X).aemeasurable h

end MathlibExt.Biology.PopulationGenetics.Admixture
