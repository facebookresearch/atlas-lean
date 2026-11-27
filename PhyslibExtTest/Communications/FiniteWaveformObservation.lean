/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Communications.FiniteWaveformObservation
import Mathlib.Tactic.NormNum

@[expose] public section

open MeasureTheory ProbabilityTheory
open PhyslibExt.Communications.FiniteIQSignalSpace
open PhyslibExt.Communications.BPSKSignError
open PhyslibExt.Communications.FiniteWaveformObservation

namespace PhyslibExtTest.Communications.FiniteWaveformObservation

/-- The declared noise variance at `N0 = 2` is `1`. -/
example : noiseVariance 2 = 1 := by
  simp [noiseVariance]

/-- The first-carrier I/Q pair on `[0, 2]` is an orthonormal family. -/
example : IsOrthonormalOn 2 ![inPhaseWaveform 2 1, quadratureWaveform 2 1] :=
  (iqPair_isOrthonormalOn 2 1 (by norm_num) le_rfl).1

/-- Projecting `3 * u + 4 * v` on the quadrature carrier of the
first-carrier I/Q pair on `[0, 2]` recovers `4`. -/
example :
    waveformInner 2 (synthesize ![inPhaseWaveform 2 1, quadratureWaveform 2 1] ![3, 4])
      (quadratureWaveform 2 1) = 4 := by
  obtain ⟨horth, hint⟩ := iqPair_isOrthonormalOn 2 1 (by norm_num) le_rfl
  simpa using waveformInner_synthesize 2 _ horth hint ![3, 4] 1

/-- Pathwise projection on the I/Q pair with coefficients `3` and `4`:
the in-phase projection is `3` plus the in-phase noise coordinate. -/
example {Ω : Type*} (Z : Fin 2 → Ω → ℝ) (ω : Ω) :
    projectionObservation 2 ![inPhaseWaveform 2 1, quadratureWaveform 2 1] ![3, 4] Z ω 0
      = 3 + Z 0 ω := by
  obtain ⟨horth, hint⟩ := iqPair_isOrthonormalOn 2 1 (by norm_num) le_rfl
  simpa using projectionObservation_eq 2 _ horth hint ![3, 4] Z ω 0

/-- Observation law on the I/Q pair at `N0 = 2`: the two projections are
independent with laws `N(3, 1)` and `N(4, 1)`. -/
example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Fin 2 → Ω → ℝ) (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 (noiseVariance 2)) P)
    (hind : iIndepFun Z P) :
    HasLaw
      (fun ω j =>
        projectionObservation 2 ![inPhaseWaveform 2 1, quadratureWaveform 2 1] ![3, 4] Z ω j)
      (Measure.pi fun j => gaussianReal (![3, 4] j) (noiseVariance 2)) P := by
  obtain ⟨horth, hint⟩ := iqPair_isOrthonormalOn 2 1 (by norm_num) le_rfl
  exact (orthonormalObservation_correct P 2 _ horth hint ![3, 4] Z 2 (by norm_num) hZ
    hind).2.1

/-- The same observation on the I/Q pair, as the multivariate Gaussian
with mean `(3, 4)` and covariance `1 • 1`. -/
example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Fin 2 → Ω → ℝ) (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 (noiseVariance 2)) P)
    (hind : iIndepFun Z P) :
    HasLaw
      (fun ω => (WithLp.toLp 2 (fun j =>
        projectionObservation 2 ![inPhaseWaveform 2 1, quadratureWaveform 2 1] ![3, 4] Z ω j) :
          EuclideanSpace ℝ (Fin 2)))
      (multivariateGaussian (WithLp.toLp 2 ![3, 4]) ((2 / 2 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)))
      P := by
  obtain ⟨horth, hint⟩ := iqPair_isOrthonormalOn 2 1 (by norm_num) le_rfl
  exact projectionObservation_hasLaw_multivariateGaussian P 2 _ horth hint ![3, 4] Z 2
    (by norm_num) hZ hind

/-- In-phase projection law from the I/Q result: inside the I/Q pair at
`N0 = 2`, the in-phase projection has law `N(3, 1)`. -/
example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Fin 2 → Ω → ℝ) (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 (noiseVariance 2)) P)
    (hind : iIndepFun Z P) :
    HasLaw
      (fun ω => waveformInner 2
        (receivedWaveform ![inPhaseWaveform 2 1, quadratureWaveform 2 1] ![3, 4] Z ω)
        (inPhaseWaveform 2 1))
      (gaussianReal 3 (noiseVariance 2)) P := by
  obtain ⟨horth, hint⟩ := iqPair_isOrthonormalOn 2 1 (by norm_num) le_rfl
  simpa using (iqProjection_correct P 2 1 _ horth hint 0 1 (by decide) rfl rfl ![3, 4] Z 2
    (by norm_num) hZ hind).2.2.1

/-- Sufficiency on the first-carrier I/Q pair on `[0, 2]` at `N0 = 2`:
the two correlator outputs are a sufficient statistic for the
received-waveform family indexed by the I/Q coefficients. -/
example :
    MathlibExt.Probability.Statistics.Sufficiency.IsSufficient
      (MeasurableSpace.comap
        (projectionStatistic 2 ![inPhaseWaveform 2 1, quadratureWaveform 2 1])
        MeasurableSpace.pi)
      (receivedWaveformLaw 2 ![inPhaseWaveform 2 1, quadratureWaveform 2 1] 2) := by
  obtain ⟨horth, hint⟩ := iqPair_isOrthonormalOn 2 1 (by norm_num) le_rfl
  exact projectionStatistic_isSufficient 2 _ horth hint 2

/-- Under the coefficients `(3, 4)` on the same I/Q pair at `N0 = 2`, the
sufficient statistic has independent coordinates of laws `N(3, 1)` and
`N(4, 1)`. -/
example :
    HasLaw (projectionStatistic 2 ![inPhaseWaveform 2 1, quadratureWaveform 2 1])
      (Measure.pi fun j => gaussianReal (![3, 4] j) (noiseVariance 2))
      (receivedWaveformLaw 2 ![inPhaseWaveform 2 1, quadratureWaveform 2 1] 2 ![3, 4]) := by
  obtain ⟨horth, hint⟩ := iqPair_isOrthonormalOn 2 1 (by norm_num) le_rfl
  exact (projectionStatistic_sufficient_correct 2 _ horth hint 2 (by norm_num)).2.2 ![3, 4]

/-- Reconstruction on the I/Q pair: the received waveform with
coefficients `(3, 4)` and noise coordinates `(1, -1)` is the synthesis
of its two projections. -/
example :
    synthesize ![inPhaseWaveform 2 1, quadratureWaveform 2 1]
        (projectionStatistic 2 ![inPhaseWaveform 2 1, quadratureWaveform 2 1]
          (receivedWaveform ![inPhaseWaveform 2 1, quadratureWaveform 2 1] ![3, 4]
            (fun (i : Fin 2) (z : Fin 2 → ℝ) => z i) ![1, -1]))
      = receivedWaveform ![inPhaseWaveform 2 1, quadratureWaveform 2 1] ![3, 4]
          (fun (i : Fin 2) (z : Fin 2 → ℝ) => z i) ![1, -1] := by
  obtain ⟨horth, hint⟩ := iqPair_isOrthonormalOn 2 1 (by norm_num) le_rfl
  exact (projectionStatistic_sufficient_correct 2 _ horth hint 2 (by norm_num)).1 ![3, 4]
    ![1, -1]

/-- Antipodal energy: amplitude `sqrt 4` with label `-1` on the in-phase
axis has energy `4`. -/
example :
    waveformInner 2
        (synthesize ![inPhaseWaveform 2 1, quadratureWaveform 2 1]
          (Pi.single 0 (Real.sqrt 4 * ((-1 : ℤ) : ℝ))))
        (synthesize ![inPhaseWaveform 2 1, quadratureWaveform 2 1]
          (Pi.single 0 (Real.sqrt 4 * ((-1 : ℤ) : ℝ)))) = 4 := by
  obtain ⟨horth, hint⟩ := iqPair_isOrthonormalOn 2 1 (by norm_num) le_rfl
  exact antipodalSignal_energy 2 _ horth hint 0 4 (by norm_num) (-1) (Or.inr rfl)

/-- BPSK on the in-phase axis at `Eb = 1`, `N0 = 2`: the sign detector
on the projection errs with probability `Q(1)`. -/
example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Ω → ℤ) (Z : Fin 2 → Ω → ℝ) (hSmeas : Measurable S)
    (hSval : ∀ ω, S ω = 1 ∨ S ω = -1) (hprior : P.real {ω | S ω = 1} = 1 / 2)
    (hZ : HasLaw (Z 0) (gaussianReal 0 (noiseVariance 2)) P)
    (hindep : IndepFun S (Z 0) P) :
    P.real {ω | signDetector
        (projectionObservation 2 ![inPhaseWaveform 2 1, quadratureWaveform 2 1]
          (Pi.single 0 (Real.sqrt 1 * (S ω : ℝ))) Z ω 0) ≠ S ω}
      = gaussianQ 1 := by
  obtain ⟨horth, hint⟩ := iqPair_isOrthonormalOn 2 1 (by norm_num) le_rfl
  rw [antipodalObservation_signError_eq_gaussianQ P 2 _ horth hint 0 S Z 1 2 (by norm_num)
    (by norm_num) hSmeas hSval hprior hZ hindep]
  norm_num

/-- Noise of amplitude `5` on the quadrature carrier leaves the in-phase
coefficient `3` unchanged. -/
example :
    waveformInner 2
        (fun t => synthesize ![inPhaseWaveform 2 1, quadratureWaveform 2 1] ![3, 4] t
          + 5 * quadratureWaveform 2 1 t)
        (inPhaseWaveform 2 1) = 3 := by
  obtain ⟨horth, hint⟩ := iqPair_isOrthonormalOn 2 1 (by norm_num) le_rfl
  simpa using waveformInner_add_orthogonal 2 _ horth hint ![3, 4] 0 1 (by decide) 5

/-- The skew pair leaks `sqrt 3 / 2` of the second coefficient into the
first projection. -/
example :
    waveformInner 1 (synthesize skewWaveformPair ![0, 1]) (skewWaveformPair 0)
      = Real.sqrt 3 / 2 :=
  skewWaveformPair_interference.2.2.2

/-- At `N0 = 2` the skew-pair noise projections have covariance
`sqrt 3`. -/
example {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : Fin 2 → Ω → ℝ) (hZ : ∀ i, HasLaw (Z i) (gaussianReal 0 (noiseVariance 2)) P)
    (hind : iIndepFun Z P) :
    covariance (fun ω => projectionObservation 1 skewWaveformPair 0 Z ω 0)
        (fun ω => projectionObservation 1 skewWaveformPair 0 Z ω 1) P
      = Real.sqrt 3 := by
  rw [skewWaveformPair_projection_covariance P Z 2 (by norm_num) hZ hind]
  norm_num

end PhyslibExtTest.Communications.FiniteWaveformObservation
