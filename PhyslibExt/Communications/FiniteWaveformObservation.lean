/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
public import Mathlib.Probability.Moments.Covariance
public import PhyslibExt.Communications.BPSKSignError
public import PhyslibExt.Communications.FiniteIQSignalSpace

/-!
# Gaussian observation of a finite orthonormal waveform family

## i. Overview

On an observation window `[0, T]` with the real inner product
`⟪u, v⟫ = ∫ t in 0..T, u t * v t`, let `φ i`, `i : ι`, be a finite
orthonormal family of real waveforms whose pairwise products are
interval integrable. A signal with real coefficients `a i` is
synthesized as `∑ i, a i * φ i`, and the received waveform adds the
synthesized noise `∑ i, Z i ω * φ i`, whose coefficients are
independent with law `N(0, N0/2)` for `N0 > 0`. Projecting the
received waveform on `φ j` returns exactly `a j + Z j ω`. The
projection vector therefore has independent coordinates of law
`N(a j, N0/2)`; equivalently, it is the multivariate Gaussian with
mean `a` and covariance `(N0/2) • 1`. This is the finite-dimensional
correlator-receiver model for an orthonormal signal set in additive
Gaussian noise.

Two specializations connect the projection model to existing
developments. When the family contains the in-phase and quadrature
carriers of `PhyslibExt.Communications.FiniteIQSignalSpace`, the two
carrier projections are the corresponding coefficients plus
independent Gaussian coordinates. In the single-axis antipodal case,
amplitude `sqrt Eb` on one axis with an equiprobable label `±1`
independent of that axis's noise, the projection is the matched-filter
sample of `PhyslibExt.Communications.BPSKSignError`, and the sign
detector errs with probability `Q(sqrt(2 Eb / N0))`.

The variance `N0/2` is a declared signal-space convention for the
noise coordinates, not a derivation from a function-valued white-noise
process. Pairwise product integrability is assumed because, without
it, a non-integrable cross product integrates to `0` by convention and
the projection is no longer linear in the coefficients. The final
section shows that orthogonality cannot be dropped: a normalized but
nonorthogonal pair leaks one coefficient into the other projection
and correlates the noise projections.

## ii. Key results

- `projectionObservation_eq`: each projection equals the signal
  coefficient plus the noise coordinate.
- `projectionObservation_hasLaw_pi` and
  `projectionObservation_hasLaw_multivariateGaussian`: the projection
  vector has independent `N(a j, N0/2)` coordinates, i.e. law
  `multivariateGaussian a ((N0/2) • 1)`.
- `orthonormalObservation_correct`: the combined pathwise and
  distributional statement.
- `iqProjection_correct`: the in-phase and quadrature projections and
  their independent Gaussian laws.
- `antipodalObservation_signError_eq_gaussianQ`: the sign-detector
  error on the antipodal projection is `Q(sqrt(2 Eb / N0))`.

## iii. Table of contents

- A. Inner product, synthesis and projection
- B. Projection and the observation law
- C. The in-phase and quadrature carriers
- D. Antipodal signalling and the sign-detector error
- E. Validations: unused directions and a nonorthogonal pair

## iv. References

- J. M. Wozencraft and I. M. Jacobs, *Principles of Communication
  Engineering*, Wiley, 1965: orthonormal expansion of the received
  signal and the Gaussian law of the correlator outputs.
- J. G. Proakis and M. Salehi, *Communication Systems Engineering*,
  second edition, Prentice Hall, 2002: signal-space representation
  and optimum reception of digital signals in additive white Gaussian
  noise.

## A. Inner product, synthesis and projection
-/

@[expose] public section

namespace PhyslibExt.Communications.FiniteWaveformObservation

open MeasureTheory ProbabilityTheory
open PhyslibExt.Communications.FiniteIQSignalSpace
open PhyslibExt.Communications.BPSKSignError

/-- The real waveform inner product `∫ t in 0..T, u t * v t` on the
observation window. -/
noncomputable def waveformInner (T : ℝ) (u v : ℝ → ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..T, u t * v t

/-- Orthonormality of a finite waveform family on `[0, T]`. -/
def IsOrthonormalOn (T : ℝ) {ι : Type*} [DecidableEq ι] (φ : ι → ℝ → ℝ) : Prop :=
  ∀ i j, waveformInner T (φ i) (φ j) = if i = j then 1 else 0

/-- Synthesis `∑ i, c i * φ i t` of a waveform from real coefficients. -/
noncomputable def synthesize {ι : Type*} [Fintype ι] (φ : ι → ℝ → ℝ) (c : ι → ℝ)
    (t : ℝ) : ℝ :=
  ∑ i, c i * φ i t

/-- Received waveform: the synthesized signal plus the synthesized
noise with random coefficients `Z i ω`. -/
noncomputable def receivedWaveform {Ω ι : Type*} [Fintype ι] (φ : ι → ℝ → ℝ)
    (a : ι → ℝ) (Z : ι → Ω → ℝ) (ω : Ω) (t : ℝ) : ℝ :=
  synthesize φ a t + synthesize φ (fun i => Z i ω) t

/-- Projection of the received waveform on the family member `φ j`. -/
noncomputable def projectionObservation {Ω ι : Type*} [Fintype ι] (T : ℝ)
    (φ : ι → ℝ → ℝ) (a : ι → ℝ) (Z : ι → Ω → ℝ) (ω : Ω) (j : ι) : ℝ :=
  waveformInner T (receivedWaveform φ a Z ω) (φ j)

/-- The declared signal-space noise variance `N0 / 2`, as a
nonnegative real. -/
noncomputable def noiseVariance (N0 : ℝ) : NNReal :=
  (N0 / 2).toNNReal

private lemma waveformInner_synthesize_eq_sum {ι : Type*} [Fintype ι] (T : ℝ)
    (φ : ι → ℝ → ℝ) (ψ : ℝ → ℝ)
    (hint : ∀ i, IntervalIntegrable (fun t => φ i t * ψ t) volume 0 T) (c : ι → ℝ) :
    waveformInner T (synthesize φ c) ψ = ∑ i, c i * waveformInner T (φ i) ψ := by
  unfold waveformInner synthesize
  have hpt : ∀ t, (∑ i, c i * φ i t) * ψ t = ∑ i, c i * (φ i t * ψ t) := by
    intro t
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [hpt]
  rw [intervalIntegral.integral_finsetSum (fun i _ => (hint i).const_mul (c i))]
  simp only [intervalIntegral.integral_const_mul]

private lemma receivedWaveform_eq_synthesize {Ω ι : Type*} [Fintype ι] (φ : ι → ℝ → ℝ)
    (a : ι → ℝ) (Z : ι → Ω → ℝ) (ω : Ω) :
    receivedWaveform φ a Z ω = synthesize φ (fun i => a i + Z i ω) := by
  funext t
  simp only [receivedWaveform, synthesize, add_mul, Finset.sum_add_distrib]

private lemma projectionObservation_eq_sum {Ω ι : Type*} [Fintype ι] (T : ℝ)
    (φ : ι → ℝ → ℝ) (hint : ∀ i j, IntervalIntegrable (fun t => φ i t * φ j t) volume 0 T)
    (a : ι → ℝ) (Z : ι → Ω → ℝ) (ω : Ω) (j : ι) :
    projectionObservation T φ a Z ω j = ∑ i, (a i + Z i ω) * waveformInner T (φ i) (φ j) := by
  unfold projectionObservation
  rw [receivedWaveform_eq_synthesize,
    waveformInner_synthesize_eq_sum T φ (φ j) (fun i => hint i j)]

private lemma hasLaw_const_add_noise {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X : Ω → ℝ) (c N0 : ℝ) (hX : HasLaw X (gaussianReal 0 (noiseVariance N0)) P) :
    HasLaw ((fun x => c + x) ∘ X) (gaussianReal c (noiseVariance N0)) P := by
  have hY : HasLaw (fun x : ℝ => c + x) (gaussianReal c (noiseVariance N0))
      (gaussianReal 0 (noiseVariance N0)) :=
    { aemeasurable := (measurable_const_add c).aemeasurable
      map_eq := by rw [gaussianReal_map_const_add, zero_add] }
  exact hY.comp hX

/-! ## B. Projection and the observation law -/

/-- Projection of a synthesized waveform on an orthonormal family
member recovers its coefficient. -/
lemma waveformInner_synthesize {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ℝ)
    (φ : ι → ℝ → ℝ) (horth : IsOrthonormalOn T φ)
    (hint : ∀ i j, IntervalIntegrable (fun t => φ i t * φ j t) volume 0 T)
    (c : ι → ℝ) (j : ι) :
    waveformInner T (synthesize φ c) (φ j) = c j := by
  have h : ∀ i, waveformInner T (φ i) (φ j) = if i = j then 1 else 0 := fun i => horth i j
  rw [waveformInner_synthesize_eq_sum T φ (φ j) (fun i => hint i j)]
  simp [h]

/-- Pathwise projection: the projection of the received waveform on
`φ j` is the signal coefficient plus the noise coordinate. -/
theorem projectionObservation_eq {Ω ι : Type*} [Fintype ι] [DecidableEq ι] (T : ℝ)
    (φ : ι → ℝ → ℝ) (horth : IsOrthonormalOn T φ)
    (hint : ∀ i j, IntervalIntegrable (fun t => φ i t * φ j t) volume 0 T)
    (a : ι → ℝ) (Z : ι → Ω → ℝ) (ω : Ω) (j : ι) :
    projectionObservation T φ a Z ω j = a j + Z j ω := by
  unfold projectionObservation
  rw [receivedWaveform_eq_synthesize, waveformInner_synthesize T φ horth hint]

set_option linter.unusedVariables false in
/-- Law of the projections: independent coordinates with law
`N(a j, N0/2)`. -/
theorem projectionObservation_hasLaw_pi {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ)
    (φ : ι → ℝ → ℝ) (horth : IsOrthonormalOn T φ)
    (hint : ∀ i j, IntervalIntegrable (fun t => φ i t * φ j t) volume 0 T)
    (a : ι → ℝ) (Z : ι → Ω → ℝ) (N0 : ℝ) (hN0 : 0 < N0)
    (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 (noiseVariance N0)) P)
    (hind : iIndepFun Z P) :
    HasLaw (fun ω j => projectionObservation T φ a Z ω j)
      (Measure.pi fun j => gaussianReal (a j) (noiseVariance N0)) P := by
  have hlaw : ∀ j, HasLaw ((fun x => a j + x) ∘ Z j) (gaussianReal (a j) (noiseVariance N0)) P :=
    fun j => hasLaw_const_add_noise P (Z j) (a j) N0 (hZ j)
  have h := (hind.comp (fun j x => a j + x) (fun j => measurable_const_add (a j))).hasLaw_pi hlaw
  have heq : (fun ω j => projectionObservation T φ a Z ω j)
      = fun ω j => ((fun x => a j + x) ∘ Z j) ω := by
    funext ω j
    exact projectionObservation_eq T φ horth hint a Z ω j
  rw [heq]
  exact h

/-- Law of the projection vector as the canonical multivariate
Gaussian with mean `a` and covariance `(N0/2) • 1`. -/
theorem projectionObservation_hasLaw_multivariateGaussian {Ω ι : Type*} [Fintype ι]
    [DecidableEq ι] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ)
    (φ : ι → ℝ → ℝ) (horth : IsOrthonormalOn T φ)
    (hint : ∀ i j, IntervalIntegrable (fun t => φ i t * φ j t) volume 0 T)
    (a : ι → ℝ) (Z : ι → Ω → ℝ) (N0 : ℝ) (hN0 : 0 < N0)
    (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 (noiseVariance N0)) P)
    (hind : iIndepFun Z P) :
    HasLaw (fun ω => (WithLp.toLp 2 (fun j => projectionObservation T φ a Z ω j) :
        EuclideanSpace ℝ ι))
      (multivariateGaussian (WithLp.toLp 2 a) ((N0 / 2) • (1 : Matrix ι ι ℝ))) P := by
  have hpi := projectionObservation_hasLaw_pi P T φ horth hint a Z N0 hN0 hZ hind
  have hS : ((N0 / 2) • (1 : Matrix ι ι ℝ)).PosSemidef :=
    Matrix.PosSemidef.one.smul (by positivity)
  have hv : ((noiseVariance N0 : NNReal) : ℝ) = N0 / 2 := Real.coe_toNNReal _ (by positivity)
  have hmap : (Measure.pi fun j => gaussianReal (a j) (noiseVariance N0)).map (WithLp.toLp 2)
      = multivariateGaussian (WithLp.toLp 2 a) ((N0 / 2) • (1 : Matrix ι ι ℝ)) := by
    apply Measure.ext_of_charFun (E := EuclideanSpace ℝ ι)
    funext t
    rw [charFun_pi, charFun_multivariateGaussian hS]
    simp only [charFun_gaussianReal, hv, ← Complex.exp_sum]
    congr 1
    simp only [PiLp.inner_apply, dotProduct, Matrix.smul_mulVec, Matrix.one_mulVec,
      Finset.sum_sub_distrib, Finset.sum_div, Pi.smul_apply, smul_eq_mul, Complex.ofReal_sum,
      Complex.ofReal_mul, Complex.ofReal_div, Finset.sum_mul,
      RCLike.inner_apply, conj_trivial]
    push_cast
    congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring
  have hY : HasLaw (fun x : ι → ℝ => (WithLp.toLp 2 x : EuclideanSpace ℝ ι))
      (multivariateGaussian (WithLp.toLp 2 a) ((N0 / 2) • (1 : Matrix ι ι ℝ)))
      (Measure.pi fun j => gaussianReal (a j) (noiseVariance N0)) :=
    { aemeasurable := (MeasurableEquiv.toLp 2 (ι → ℝ)).measurable.aemeasurable
      map_eq := hmap }
  exact hY.comp hpi

/-- **Orthonormal observation.** For a finite orthonormal family with
independent `N(0, N0/2)` noise coefficients, every projection is the
signal coefficient plus the noise coordinate, and the projection
vector has independent `N(a j, N0/2)` coordinates, equivalently the
multivariate Gaussian with mean `a` and covariance `(N0/2) • 1`. -/
theorem orthonormalObservation_correct {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ)
    (φ : ι → ℝ → ℝ) (horth : IsOrthonormalOn T φ)
    (hint : ∀ i j, IntervalIntegrable (fun t => φ i t * φ j t) volume 0 T)
    (a : ι → ℝ) (Z : ι → Ω → ℝ) (N0 : ℝ) (hN0 : 0 < N0)
    (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 (noiseVariance N0)) P)
    (hind : iIndepFun Z P) :
    (∀ ω j, projectionObservation T φ a Z ω j = a j + Z j ω) ∧
      HasLaw (fun ω j => projectionObservation T φ a Z ω j)
        (Measure.pi fun j => gaussianReal (a j) (noiseVariance N0)) P ∧
      HasLaw (fun ω => (WithLp.toLp 2 (fun j => projectionObservation T φ a Z ω j) :
          EuclideanSpace ℝ ι))
        (multivariateGaussian (WithLp.toLp 2 a) ((N0 / 2) • (1 : Matrix ι ι ℝ))) P := by
  exact ⟨fun ω j => projectionObservation_eq T φ horth hint a Z ω j,
    projectionObservation_hasLaw_pi P T φ horth hint a Z N0 hN0 hZ hind,
    projectionObservation_hasLaw_multivariateGaussian P T φ horth hint a Z N0 hN0 hZ hind⟩

/-! ## C. The in-phase and quadrature carriers -/

/-- The in-phase/quadrature pair is an orthonormal family with
integrable pairwise products, from the unit-energy and orthogonality
results for the in-phase and quadrature waveforms. -/
lemma iqPair_isOrthonormalOn (T : ℝ) (k : ℕ) (hT : 0 < T) (hk : 1 ≤ k) :
    IsOrthonormalOn T ![inPhaseWaveform T k, quadratureWaveform T k] ∧
      ∀ i j : Fin 2, IntervalIntegrable
        (fun t => ![inPhaseWaveform T k, quadratureWaveform T k] i t *
          ![inPhaseWaveform T k, quadratureWaveform T k] j t) volume 0 T := by
  have hU : Continuous (inPhaseWaveform T k) := by
    unfold inPhaseWaveform
    fun_prop
  have hV : Continuous (quadratureWaveform T k) := by
    unfold quadratureWaveform
    fun_prop
  have hUU := inPhaseWaveform_norm T k hT hk
  have hVV := quadratureWaveform_norm T k hT hk
  have hUV := inPhaseWaveform_quadratureWaveform_orthogonal T k hT hk
  have hVU : (∫ t in (0 : ℝ)..T, quadratureWaveform T k t * inPhaseWaveform T k t) = 0 := by
    calc (∫ t in (0 : ℝ)..T, quadratureWaveform T k t * inPhaseWaveform T k t)
        = ∫ t in (0 : ℝ)..T, inPhaseWaveform T k t * quadratureWaveform T k t :=
          intervalIntegral.integral_congr fun t _ =>
            mul_comm (quadratureWaveform T k t) (inPhaseWaveform T k t)
      _ = 0 := hUV
  refine ⟨?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;> simp [waveformInner, hUU, hVV, hUV, hVU]
  · intro i j
    fin_cases i <;> fin_cases j
    · exact (hU.mul hU).intervalIntegrable _ _
    · exact (hU.mul hV).intervalIntegrable _ _
    · exact (hV.mul hU).intervalIntegrable _ _
    · exact (hV.mul hV).intervalIntegrable _ _

set_option linter.unusedVariables false in
/-- I/Q projections: in a family that contains the in-phase and
quadrature carriers at distinct indices, projecting on those carriers
returns the coefficient plus the noise coordinate, the two projections
have laws `N(a iI, N0/2)` and `N(a iQ, N0/2)`, and they are
independent. -/
theorem iqProjection_correct {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ) (k : ℕ)
    (φ : ι → ℝ → ℝ) (horth : IsOrthonormalOn T φ)
    (hint : ∀ i j, IntervalIntegrable (fun t => φ i t * φ j t) volume 0 T)
    (iI iQ : ι) (hIQ : iI ≠ iQ) (hφI : φ iI = inPhaseWaveform T k)
    (hφQ : φ iQ = quadratureWaveform T k)
    (a : ι → ℝ) (Z : ι → Ω → ℝ) (N0 : ℝ) (hN0 : 0 < N0)
    (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 (noiseVariance N0)) P)
    (hind : iIndepFun Z P) :
    (∀ ω, waveformInner T (receivedWaveform φ a Z ω) (inPhaseWaveform T k) = a iI + Z iI ω) ∧
      (∀ ω, waveformInner T (receivedWaveform φ a Z ω) (quadratureWaveform T k)
        = a iQ + Z iQ ω) ∧
      HasLaw (fun ω => waveformInner T (receivedWaveform φ a Z ω) (inPhaseWaveform T k))
        (gaussianReal (a iI) (noiseVariance N0)) P ∧
      HasLaw (fun ω => waveformInner T (receivedWaveform φ a Z ω) (quadratureWaveform T k))
        (gaussianReal (a iQ) (noiseVariance N0)) P ∧
      IndepFun (fun ω => waveformInner T (receivedWaveform φ a Z ω) (inPhaseWaveform T k))
        (fun ω => waveformInner T (receivedWaveform φ a Z ω) (quadratureWaveform T k)) P := by
  have hpe := projectionObservation_eq T φ horth hint a Z
  have hI : ∀ ω, waveformInner T (receivedWaveform φ a Z ω) (inPhaseWaveform T k)
      = a iI + Z iI ω := by
    intro ω
    rw [← hφI]
    exact hpe ω iI
  have hQ : ∀ ω, waveformInner T (receivedWaveform φ a Z ω) (quadratureWaveform T k)
      = a iQ + Z iQ ω := by
    intro ω
    rw [← hφQ]
    exact hpe ω iQ
  have eI : (fun ω => waveformInner T (receivedWaveform φ a Z ω) (inPhaseWaveform T k))
      = (fun x => a iI + x) ∘ Z iI := funext hI
  have eQ : (fun ω => waveformInner T (receivedWaveform φ a Z ω) (quadratureWaveform T k))
      = (fun x => a iQ + x) ∘ Z iQ := funext hQ
  refine ⟨hI, hQ, ?_, ?_, ?_⟩
  · rw [eI]
    exact hasLaw_const_add_noise P (Z iI) (a iI) N0 (hZ iI)
  · rw [eQ]
    exact hasLaw_const_add_noise P (Z iQ) (a iQ) N0 (hZ iQ)
  · rw [eI, eQ]
    exact (hind.indepFun hIQ).comp (measurable_const_add (a iI)) (measurable_const_add (a iQ))

/-! ## D. Antipodal signalling and the sign-detector error -/

set_option linter.unusedVariables false in
/-- Antipodal signal energy: amplitude `sqrt Eb` times a label `±1` on
one axis has energy `Eb`. -/
lemma antipodalSignal_energy {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ℝ)
    (φ : ι → ℝ → ℝ) (horth : IsOrthonormalOn T φ)
    (hint : ∀ i j, IntervalIntegrable (fun t => φ i t * φ j t) volume 0 T)
    (i0 : ι) (Eb : ℝ) (hEb : 0 ≤ Eb) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    waveformInner T (synthesize φ (Pi.single i0 (Real.sqrt Eb * (s : ℝ))))
      (synthesize φ (Pi.single i0 (Real.sqrt Eb * (s : ℝ)))) = Eb := by
  have hsyn : synthesize φ (Pi.single i0 (Real.sqrt Eb * (s : ℝ)))
      = fun t => (Real.sqrt Eb * (s : ℝ)) * φ i0 t := by
    funext t
    simp [synthesize, Pi.single_apply]
  have h1 : (∫ t in (0 : ℝ)..T, φ i0 t * φ i0 t) = 1 := by
    have := horth i0 i0
    simpa [waveformInner] using this
  rw [hsyn]
  unfold waveformInner
  have hpt : ∀ t, Real.sqrt Eb * (s : ℝ) * φ i0 t * (Real.sqrt Eb * (s : ℝ) * φ i0 t)
      = (Real.sqrt Eb * (s : ℝ)) ^ 2 * (φ i0 t * φ i0 t) := fun t => by ring
  simp only [hpt, intervalIntegral.integral_const_mul, h1, mul_one]
  rcases hs with rfl | rfl <;> simp [Real.sq_sqrt hEb]

/-- Antipodal observation is the BPSK matched-filter sample with
amplitude `sqrt Eb` and noise `Z i0`. -/
lemma antipodalObservation_eq_receivedSample {Ω ι : Type*} [Fintype ι] [DecidableEq ι]
    (T : ℝ) (φ : ι → ℝ → ℝ) (horth : IsOrthonormalOn T φ)
    (hint : ∀ i j, IntervalIntegrable (fun t => φ i t * φ j t) volume 0 T)
    (i0 : ι) (Eb : ℝ) (S : Ω → ℤ) (Z : ι → Ω → ℝ) (ω : Ω) :
    projectionObservation T φ (Pi.single i0 (Real.sqrt Eb * (S ω : ℝ))) Z ω i0
      = receivedSample (Real.sqrt Eb) (S ω) (Z i0 ω) := by
  rw [projectionObservation_eq T φ horth hint]
  simp [receivedSample]

/-- Single-axis antipodal transfer of the BPSK error: with an
equiprobable label `S = ±1` sent with amplitude `sqrt Eb` on axis
`i0` and independent of that axis's `N(0, N0/2)` noise coordinate,
the sign detector on the projection on `φ i0` errs with probability
`Q(sqrt(2 Eb / N0))`. -/
theorem antipodalObservation_signError_eq_gaussianQ {Ω ι : Type*} [Fintype ι]
    [DecidableEq ι] [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (T : ℝ)
    (φ : ι → ℝ → ℝ) (horth : IsOrthonormalOn T φ)
    (hint : ∀ i j, IntervalIntegrable (fun t => φ i t * φ j t) volume 0 T)
    (i0 : ι) (S : Ω → ℤ) (Z : ι → Ω → ℝ) (Eb N0 : ℝ) (hEb : 0 ≤ Eb) (hN0 : 0 < N0)
    (hSmeas : Measurable S) (hSval : ∀ ω, S ω = 1 ∨ S ω = -1)
    (hprior : P.real {ω | S ω = 1} = 1 / 2)
    (hZ : HasLaw (Z i0) (gaussianReal 0 (noiseVariance N0)) P)
    (hindep : IndepFun S (Z i0) P) :
    P.real {ω | signDetector
        (projectionObservation T φ (Pi.single i0 (Real.sqrt Eb * (S ω : ℝ))) Z ω i0) ≠ S ω}
      = gaussianQ (Real.sqrt (2 * Eb / N0)) := by
  have hset : {ω | signDetector
        (projectionObservation T φ (Pi.single i0 (Real.sqrt Eb * (S ω : ℝ))) Z ω i0) ≠ S ω}
      = signErrorEvent Ω (Real.sqrt Eb) S (Z i0) := by
    ext ω
    simp only [Set.mem_ofPred_eq, signErrorEvent,
      antipodalObservation_eq_receivedSample T φ horth hint i0 Eb S Z ω]
  rw [hset]
  have hσ : 0 < Real.sqrt (N0 / 2) := Real.sqrt_pos.mpr (by positivity)
  have hvar : Real.sqrt (N0 / 2) ^ 2 = N0 / 2 := Real.sq_sqrt (by positivity)
  have hN : HasLaw (Z i0) (gaussianReal 0 (Real.sqrt (N0 / 2) ^ 2).toNNReal) P := by
    rw [hvar]
    exact hZ
  rw [prob_signError_eq_gaussianQ_sqrt_two_bitEnergy_div Ω P S (Z i0) (Real.sqrt Eb)
    (Real.sqrt (N0 / 2)) N0 (Real.sqrt_nonneg _) hσ hN0 hvar hSmeas hSval hprior hN hindep]
  unfold bitEnergy
  rw [Real.sq_sqrt hEb]

/-! ## E. Validations: unused directions and a nonorthogonal pair -/

/-- Noise in an orthogonal unused direction does not alter the
selected projection. -/
lemma waveformInner_add_orthogonal {ι : Type*} [Fintype ι] [DecidableEq ι] (T : ℝ)
    (φ : ι → ℝ → ℝ) (horth : IsOrthonormalOn T φ)
    (hint : ∀ i j, IntervalIntegrable (fun t => φ i t * φ j t) volume 0 T)
    (c : ι → ℝ) (j m : ι) (hjm : j ≠ m) (z : ℝ) :
    waveformInner T (fun t => synthesize φ c t + z * φ m t) (φ j) = c j := by
  have h : (fun t => synthesize φ c t + z * φ m t)
      = synthesize φ (fun i => c i + if i = m then z else 0) := by
    funext t
    simp [synthesize, add_mul, Finset.sum_add_distrib, ite_mul]
  rw [h, waveformInner_synthesize T φ horth hint]
  simp [hjm]

/-- A normalized but nonorthogonal pair on `[0, 1]`: the constant `1`
and `sqrt 3 * t`. -/
noncomputable def skewWaveformPair : Fin 2 → ℝ → ℝ :=
  ![fun _ => 1, fun t => Real.sqrt 3 * t]

/-- The skew pair is normalized but has inner product `sqrt 3 / 2`, so
projecting `0 * u0 + 1 * u1` on `u0` returns the interference
`sqrt 3 / 2` instead of the coefficient `0`. -/
lemma skewWaveformPair_interference :
    waveformInner 1 (skewWaveformPair 0) (skewWaveformPair 0) = 1 ∧
      waveformInner 1 (skewWaveformPair 1) (skewWaveformPair 1) = 1 ∧
      waveformInner 1 (skewWaveformPair 0) (skewWaveformPair 1) = Real.sqrt 3 / 2 ∧
      waveformInner 1 (synthesize skewWaveformPair ![0, 1]) (skewWaveformPair 0)
        = Real.sqrt 3 / 2 := by
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [waveformInner, skewWaveformPair]
  · simp only [waveformInner, skewWaveformPair, Matrix.cons_val_one, Matrix.cons_val_zero]
    have : ∀ t : ℝ, Real.sqrt 3 * t * (Real.sqrt 3 * t) = 3 * t ^ 2 := by
      intro t; rw [show Real.sqrt 3 * t * (Real.sqrt 3 * t) = (Real.sqrt 3 * Real.sqrt 3) * t ^ 2
        by ring, h3]
    simp only [this, intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  · simp only [waveformInner, skewWaveformPair, Matrix.cons_val_one, Matrix.cons_val_zero,
      one_mul]
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring
  · simp only [waveformInner, synthesize, skewWaveformPair, Fin.sum_univ_two,
      Matrix.cons_val_one, Matrix.cons_val_zero, one_mul, zero_add, mul_one]
    rw [intervalIntegral.integral_const_mul, integral_id]
    ring

/-- With the skew pair and independent `N(0, N0/2)` noise
coefficients, the two noise projections are correlated: their
covariance is `(N0/2) * sqrt 3`, not `0`. -/
lemma skewWaveformPair_projection_covariance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Z : Fin 2 → Ω → ℝ) (N0 : ℝ) (hN0 : 0 < N0)
    (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 (noiseVariance N0)) P)
    (hind : iIndepFun Z P) :
    covariance (fun ω => projectionObservation 1 skewWaveformPair 0 Z ω 0)
        (fun ω => projectionObservation 1 skewWaveformPair 0 Z ω 1) P
      = N0 / 2 * Real.sqrt 3 := by
  have hcont : ∀ i, Continuous (skewWaveformPair i) := by
    intro i
    fin_cases i
    · exact continuous_const
    · exact continuous_const.mul continuous_id
  have hint : ∀ i j, IntervalIntegrable
      (fun t => skewWaveformPair i t * skewWaveformPair j t) volume 0 1 :=
    fun i j => ((hcont i).mul (hcont j)).intervalIntegrable _ _
  obtain ⟨h00, h11, h01, -⟩ := skewWaveformPair_interference
  have h10 : waveformInner 1 (skewWaveformPair 1) (skewWaveformPair 0) = Real.sqrt 3 / 2 := by
    rw [← h01]
    exact intervalIntegral.integral_congr fun t _ => mul_comm _ _
  have hX0 : (fun ω => projectionObservation 1 skewWaveformPair 0 Z ω 0)
      = Z 0 + fun ω => Real.sqrt 3 / 2 * Z 1 ω := by
    funext ω
    rw [projectionObservation_eq_sum 1 skewWaveformPair hint]
    simp [Fin.sum_univ_two, h00, h10]
    ring
  have hX1 : (fun ω => projectionObservation 1 skewWaveformPair 0 Z ω 1)
      = (fun ω => Real.sqrt 3 / 2 * Z 0 ω) + Z 1 := by
    funext ω
    rw [projectionObservation_eq_sum 1 skewWaveformPair hint]
    simp [Fin.sum_univ_two, h01, h11]
    ring
  have hm : ∀ i, MemLp (Z i) 2 P := fun i => (hZ i).memLp IsGaussian.memLp_two_id
  have hmc : ∀ i (c : ℝ), MemLp (fun ω => c * Z i ω) 2 P := fun i c => (hm i).const_mul c
  have hv : ∀ i, cov[Z i, Z i; P] = N0 / 2 := by
    intro i
    rw [covariance_self (hZ i).aemeasurable, (hZ i).variance_eq, variance_id_gaussianReal]
    exact Real.coe_toNNReal _ (by positivity)
  have h01z : cov[Z 0, Z 1; P] = 0 :=
    (hind.indepFun (by decide)).covariance_eq_zero (hm 0) (hm 1)
  have h10z : cov[Z 1, Z 0; P] = 0 := by
    rw [covariance_comm]
    exact h01z
  rw [hX0, hX1, covariance_add_left (hm 0) (hmc 1 _) ((hmc 0 _).add (hm 1)),
    covariance_add_right (hm 0) (hmc 0 _) (hm 1),
    covariance_add_right (hmc 1 _) (hmc 0 _) (hm 1),
    covariance_const_mul_right, covariance_const_mul_left, covariance_const_mul_left,
    covariance_const_mul_right, hv 0, hv 1, h01z, h10z]
  have h3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  ring

end PhyslibExt.Communications.FiniteWaveformObservation
