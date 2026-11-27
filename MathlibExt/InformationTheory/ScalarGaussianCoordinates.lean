/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.InnerProductSpace.LineIsometry
public import MathlibExt.InformationTheory.ConditionalEntropy
public import MathlibExt.InformationTheory.LinearGaussianJointLaw
public import MathlibExt.InformationTheory.ReferenceOutputKL
public import MathlibExt.InformationTheory.VectorGaussianKL
public import Mathlib.InformationTheory.KullbackLeibler.ChainRule
public import Mathlib.InformationTheory.KullbackLeibler.DataProcessing
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Scalar Gaussian coordinates

The coordinate map `x ↦ (x)` from `ℝ` to `EuclideanSpace ℝ (Fin 1)`, the bundled isometry
`MathlibExt.Analysis.InnerProductSpace.LineIsometry.lineIsometry`, identifies the scalar
additive Gaussian channel `X + Z`, with `Z ~ N(0, N)` independent of `X`, with the vector channel
of `MathlibExt.InformationTheory.LinearGaussianJointLaw` at gain `[1]` and noise covariance `[N]`.

Main results:
* `map_scalarCoord_gaussianReal`: the real Gaussian `N(m, s)` maps to the one-dimensional
  multivariate Gaussian with mean `(m)` and covariance `[s]`.
* `condDistrib_scalarCoord_add`, `map_prod_scalarCoord_add`: the conditional and joint laws of the
  embedded channel are given by the canonical noise kernel.
* `scalarPowerBound_iff_powerConstraint`: the scalar power bound
  `0 ≤ P ∧ ∫⁻ ofReal (X²) ≤ ofReal P` is the vector `PowerConstraint` of the embedded input.
* `klDiv_map_scalarCoord`, `klDiv_map_scalarCoordPair`,
  `measureMutualInformation_map_scalarCoordPair`: the embedding preserves Kullback-Leibler
  divergence and mutual information as extended reals, so a top value stays top.
* `klDiv_map_scalarCoordPair_compProd_eq_add`, `klDiv_map_scalarCoordPair_prod_reference_eq_add`:
  the Kullback-Leibler chain rule in scalar coordinates, for embedded composition-product joint
  laws and for an embedded joint law against an embedded input marginal times a reference output.
* `scalarGaussian_klDiv_eq_vector`: the scalar Gaussian divergence is the closed form of
  `MathlibExt.InformationTheory.VectorGaussianKL` at dimension one.
* `scalarGaussianChannel_identification`: the noise law, conditional law, joint law and power
  identification together.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal

namespace MathlibExt.InformationTheory.ScalarGaussianCoordinates

open MathlibExt.InformationTheory.LinearGaussianJointLaw
open _root_.InformationTheory
open MathlibExt.Analysis.InnerProductSpace.LineIsometry

/-- The scalar coordinate embedding `x ↦ (x)` into the one-dimensional Euclidean space: the
coordinate action of the bundled isometry `lineIsometry`, whose API applies directly. -/
noncomputable abbrev scalarCoord : ℝ → EuclideanSpace ℝ (Fin 1) := lineIsometry

/-- The coordinate projection back to the real line: the inverse isometry `lineIsometry.symm`. -/
noncomputable abbrev scalarCoordInv : EuclideanSpace ℝ (Fin 1) → ℝ := lineIsometry.symm

/-- The scalar power bound: the budget `P` is nonnegative and the lower integral of
`ofReal (x^2)` under the law of `X` is at most `ofReal P`. The nonnegativity conjunct matters
because `ENNReal.ofReal` sends every negative budget to `0`. -/
def scalarPowerBound {Ω : Type*} {mΩ : MeasurableSpace Ω} (μ : Measure Ω)
    (X : Ω → ℝ) (P : ℝ) : Prop :=
  0 ≤ P ∧ ∫⁻ ω, ENNReal.ofReal ((X ω) ^ 2) ∂μ ≤ ENNReal.ofReal P

/-- The scalar power bound carries a nonnegative budget. -/
theorem scalarPowerBound.nonneg {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    {X : Ω → ℝ} {P : ℝ} (h : scalarPowerBound μ X P) : 0 ≤ P :=
  h.1

/-- The coordinate projection inverts the embedding. -/
theorem scalarCoordInv_scalarCoord (x : ℝ) : scalarCoordInv (scalarCoord x) = x :=
  lineIsometry.symm_apply_apply x

/-- The embedding inverts the coordinate projection. -/
theorem scalarCoord_scalarCoordInv (y : EuclideanSpace ℝ (Fin 1)) :
    scalarCoord (scalarCoordInv y) = y :=
  lineIsometry.apply_symm_apply y

/-- The embedding is measurable. -/
theorem measurable_scalarCoord : Measurable scalarCoord :=
  lineIsometry.continuous.measurable

/-- The coordinate projection is measurable. -/
theorem measurable_scalarCoordInv : Measurable scalarCoordInv :=
  lineIsometry.symm.continuous.measurable

/-- The embedding is linear: it preserves real linear combinations. -/
theorem scalarCoord_linear (a b x y : ℝ) :
    scalarCoord (a * x + b * y) = a • scalarCoord x + b • scalarCoord y := by
  rw [← smul_eq_mul a x, ← smul_eq_mul b y]
  change lineIsometry (a • x + b • y) = a • lineIsometry x + b • lineIsometry y
  rw [map_add, map_smul, map_smul]

/-- The embedding preserves the norm: the Euclidean norm of `(x)` is `|x|`. -/
theorem norm_scalarCoord (x : ℝ) : ‖scalarCoord x‖ = |x| :=
  (lineIsometry.norm_map x).trans (Real.norm_eq_abs x)

/-- The gain matrix `[1]` acts as the identity on embedded scalars. -/
theorem toEuclideanLin_one_scalarCoord (x : ℝ) :
    toEuclideanLin (!![1] : Matrix (Fin 1) (Fin 1) ℝ) (scalarCoord x) = scalarCoord x := by
  have h1 : (!![1] : Matrix (Fin 1) (Fin 1) ℝ) = 1 := by
    ext i j
    rw [Fin.eq_zero i, Fin.eq_zero j, Matrix.one_apply_eq]
    rfl
  rw [h1]
  change (Matrix.toLpLin 2 2 (1 : Matrix (Fin 1) (Fin 1) ℝ)) (scalarCoord x) = scalarCoord x
  rw [Matrix.toLpLin_one, LinearMap.id_apply]

/-- The embedded sum is the vector channel output at gain `[1]`: the embedding of `X + Z` is `[1]`
applied to the embedding of `X`, plus the embedding of `Z`. -/
theorem scalarCoord_add (x z : ℝ) :
    scalarCoord (x + z) =
      toEuclideanLin (!![1] : Matrix (Fin 1) (Fin 1) ℝ) (scalarCoord x) + scalarCoord z := by
  rw [toEuclideanLin_one_scalarCoord]
  exact map_add lineIsometry x z

/-- Evaluation at the sole coordinate is measure-preserving from the one-dimensional
multivariate Gaussian to the real Gaussian. Shared by the two Gaussian-law theorems. -/
private theorem measurePreserving_scalarCoordInv_multivariateGaussian_aux (m s : ℝ)
    (hs : 0 ≤ s) :
    MeasurePreserving scalarCoordInv
      (multivariateGaussian (scalarCoord m) (!![s] : Matrix (Fin 1) (Fin 1) ℝ))
      (gaussianReal m ⟨s, hs⟩) := by
  have hS : (!![s] : Matrix (Fin 1) (Fin 1) ℝ).PosSemidef := by
    have hdiag : (!![s] : Matrix (Fin 1) (Fin 1) ℝ)
        = Matrix.diagonal (fun _ : Fin 1 => s) := by
      ext i j
      rw [Fin.eq_zero i, Fin.eq_zero j]
      rfl
    rw [hdiag]
    apply Matrix.PosSemidef.diagonal
    intro i
    exact hs
  have h := ProbabilityTheory.measurePreserving_eval_multivariateGaussian
    (μ := scalarCoord m) (S := (!![s] : Matrix (Fin 1) (Fin 1) ℝ)) hS (i := (0 : Fin 1))
  have hmean : (scalarCoord m) 0 = m := lineIsometry_apply m 0
  have h00 : (!![s] : Matrix (Fin 1) (Fin 1) ℝ) 0 0 = s := rfl
  have hvar : ((!![s] : Matrix (Fin 1) (Fin 1) ℝ) 0 0).toNNReal = ⟨s, hs⟩ := by
    rw [h00]
    exact Real.toNNReal_of_nonneg hs
  have heval : (fun y : EuclideanSpace ℝ (Fin 1) => y 0) = scalarCoordInv :=
    funext fun y => (lineIsometry_symm_apply y).symm
  rw [hmean, hvar, heval] at h
  exact h

/-- **Gaussian law.** The embedding sends a real Gaussian of mean `m` and variance `0 ≤ s` to the
one-dimensional multivariate Gaussian of mean `(m)` and covariance `[s]`. -/
theorem map_scalarCoord_gaussianReal (m s : ℝ) (hs : 0 ≤ s) :
    (gaussianReal m ⟨s, hs⟩).map scalarCoord =
      multivariateGaussian (scalarCoord m) (!![s] : Matrix (Fin 1) (Fin 1) ℝ) := by
  have hmp := measurePreserving_scalarCoordInv_multivariateGaussian_aux m s hs
  have hmap : (multivariateGaussian (scalarCoord m) (!![s] : Matrix (Fin 1) (Fin 1) ℝ)).map
      scalarCoordInv = gaussianReal m ⟨s, hs⟩ := hmp.map_eq
  have hcomp : scalarCoord ∘ scalarCoordInv = id := funext scalarCoord_scalarCoordInv
  calc (gaussianReal m ⟨s, hs⟩).map scalarCoord
      = ((multivariateGaussian (scalarCoord m) (!![s] : Matrix (Fin 1) (Fin 1) ℝ)).map
        scalarCoordInv).map scalarCoord := by rw [hmap]
    _ = (multivariateGaussian (scalarCoord m) (!![s] : Matrix (Fin 1) (Fin 1) ℝ)).map
        (scalarCoord ∘ scalarCoordInv) :=
        Measure.map_map measurable_scalarCoord measurable_scalarCoordInv
    _ = multivariateGaussian (scalarCoord m) (!![s] : Matrix (Fin 1) (Fin 1) ℝ) := by
        rw [hcomp, Measure.map_id]

/-- **Gaussian law, read back.** Evaluation at the sole coordinate is measure-preserving from the
one-dimensional multivariate Gaussian to the real Gaussian, by the canonical evaluation theorem
at the sole index. -/
theorem measurePreserving_scalarCoordInv_multivariateGaussian (m s : ℝ) (hs : 0 ≤ s) :
    MeasurePreserving scalarCoordInv
      (multivariateGaussian (scalarCoord m) (!![s] : Matrix (Fin 1) (Fin 1) ℝ))
      (gaussianReal m ⟨s, hs⟩) :=
  measurePreserving_scalarCoordInv_multivariateGaussian_aux m s hs

/-- **Conditional channel law.** For independent measurable `X` and `Z` with `Z` centred Gaussian of
variance `N`, the conditional distribution of the embedded output given the embedded input is
the canonical noise kernel at gain `[1]` and noise `[N]`. -/
theorem condDistrib_scalarCoord_add {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Z : Ω → ℝ} (hX : Measurable X)
    (hZ : Measurable Z) (hind : IndepFun X Z μ) (N : ℝ) (hN : 0 < N)
    (hZlaw : μ.map Z = gaussianReal 0 ⟨N, hN.le⟩) :
    condDistrib (fun ω => scalarCoord (X ω + Z ω)) (fun ω => scalarCoord (X ω)) μ =ᵐ[
      μ.map (fun ω => scalarCoord (X ω))]
      MetaMathlibExt.noiseKernel (toEuclideanLin (!![1] : Matrix (Fin 1) (Fin 1) ℝ))
        (MetaMathlibExt.continuous_toEuclideanLin (!![1] : Matrix (Fin 1) (Fin 1) ℝ)).measurable
        (multivariateGaussian 0 (!![N] : Matrix (Fin 1) (Fin 1) ℝ)) := by
  have hY : Measurable (fun ω => scalarCoord (X ω)) := measurable_scalarCoord.comp hX
  have hZZ : Measurable (fun ω => scalarCoord (Z ω)) := measurable_scalarCoord.comp hZ
  have hcompX : (fun ω => scalarCoord (X ω)) = scalarCoord ∘ X := rfl
  have hcompZ : (fun ω => scalarCoord (Z ω)) = scalarCoord ∘ Z := rfl
  have hind' : IndepFun (fun ω => scalarCoord (X ω)) (fun ω => scalarCoord (Z ω)) μ := by
    rw [hcompX, hcompZ]
    exact hind.comp measurable_scalarCoord measurable_scalarCoord
  have h0 : scalarCoord 0 = 0 := map_zero lineIsometry
  have hZlaw' : μ.map (fun ω => scalarCoord (Z ω)) =
      multivariateGaussian 0 (!![N] : Matrix (Fin 1) (Fin 1) ℝ) := by
    rw [hcompZ, ← Measure.map_map measurable_scalarCoord hZ, hZlaw,
      map_scalarCoord_gaussianReal 0 N hN.le, h0]
  have hfun : (fun ω => scalarCoord (X ω + Z ω))
      = fun ω => toEuclideanLin (!![1] : Matrix (Fin 1) (Fin 1) ℝ) (scalarCoord (X ω))
        + scalarCoord (Z ω) := funext fun ω => scalarCoord_add _ _
  rw [hfun]
  have hmir := MetaMathlibExt.condDistrib_add_of_indepFun
    (Y := fun ω => scalarCoord (X ω)) (Z := fun ω => scalarCoord (Z ω))
    (f := toEuclideanLin (!![1] : Matrix (Fin 1) (Fin 1) ℝ)) hY hZZ hind'
    (MetaMathlibExt.continuous_toEuclideanLin (!![1] : Matrix (Fin 1) (Fin 1) ℝ)).measurable
  rw [hZlaw'] at hmir
  exact hmir

/-- **Joint channel law.** The joint law of embedded input and embedded output is the embedded input
law composed with the canonical noise kernel at gain `[1]` and noise `[N]`. -/
theorem map_prod_scalarCoord_add {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Z : Ω → ℝ} (hX : Measurable X)
    (hZ : Measurable Z) (hind : IndepFun X Z μ) (N : ℝ) (hN : 0 < N)
    (hZlaw : μ.map Z = gaussianReal 0 ⟨N, hN.le⟩) :
    μ.map (fun ω => (scalarCoord (X ω), scalarCoord (X ω + Z ω))) =
      (μ.map (fun ω => scalarCoord (X ω))) ⊗ₘ
        MetaMathlibExt.noiseKernel (toEuclideanLin (!![1] : Matrix (Fin 1) (Fin 1) ℝ))
          (MetaMathlibExt.continuous_toEuclideanLin
            (!![1] : Matrix (Fin 1) (Fin 1) ℝ)).measurable
          (multivariateGaussian 0 (!![N] : Matrix (Fin 1) (Fin 1) ℝ)) := by
  have hcond := condDistrib_scalarCoord_add hX hZ hind N hN hZlaw
  have hX' : AEMeasurable (fun ω => scalarCoord (X ω)) μ :=
    (measurable_scalarCoord.comp hX).aemeasurable
  have hY' : AEMeasurable (fun ω => scalarCoord (X ω + Z ω)) μ :=
    (measurable_scalarCoord.comp (hX.add hZ)).aemeasurable
  rw [← ProbabilityTheory.compProd_map_condDistrib hX' hY']
  exact Measure.compProd_congr hcond

/-- **Power identification.** The scalar power bound is exactly the vector total-power condition
for the embedded input, including its nonzero-mean contribution through the norm. -/
theorem scalarPowerBound_iff_powerConstraint {Ω : Type*} {mΩ : MeasurableSpace Ω}
    (μ : Measure Ω) (X : Ω → ℝ) (P : ℝ) :
    PowerConstraint μ (fun ω => scalarCoord (X ω)) P ↔ scalarPowerBound μ X P := by
  have h : ∀ ω : Ω, ENNReal.ofReal (‖scalarCoord (X ω)‖ ^ 2)
      = ENNReal.ofReal ((X ω) ^ 2) := fun ω => by
    rw [norm_scalarCoord, sq_abs]
  unfold PowerConstraint scalarPowerBound
  simp only [h]

/-- Finite second moment of the embedded input from the scalar power bound. -/
theorem memLp_scalarCoord_of_scalarPowerBound {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {X : Ω → ℝ} {P : ℝ} (h : scalarPowerBound μ X P)
    (hX : AEStronglyMeasurable X μ) :
    MemLp (fun ω => scalarCoord (X ω)) 2 μ := by
  have hPC : PowerConstraint μ (fun ω => scalarCoord (X ω)) P :=
    (scalarPowerBound_iff_powerConstraint μ X P).mpr h
  have hX' : AEStronglyMeasurable (fun ω => scalarCoord (X ω)) μ :=
    lineIsometry.continuous.comp_aestronglyMeasurable hX
  exact PowerConstraint.memLp_two hPC hX'

/-- Finite second moment of the scalar input from the scalar power bound, with no finite-power
conclusion drawn from an infinite lower integral. -/
theorem memLp_of_scalarPowerBound {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {X : Ω → ℝ} {P : ℝ} (h : scalarPowerBound μ X P)
    (hX : AEStronglyMeasurable X μ) : MemLp X 2 μ := by
  have hmem : MemLp (scalarCoord ∘ X) 2 μ :=
    memLp_scalarCoord_of_scalarPowerBound h hX
  have h0 : scalarCoord 0 = 0 := map_zero lineIsometry
  exact MeasureTheory.MemLp.of_comp_antilipschitzWith hmem
    lineIsometry.isometry.uniformContinuous lineIsometry.antilipschitzWith h0

/-- Divergence transport: embedding both laws does not change Kullback-Leibler divergence, by data
processing in both directions along the invertible coordinate map. -/
theorem klDiv_map_scalarCoord (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map scalarCoord) (ν.map scalarCoord) = klDiv μ ν := by
  have hμ : (μ.map scalarCoord).map scalarCoordInv = μ := by
    rw [Measure.map_map measurable_scalarCoordInv measurable_scalarCoord]
    have hc : scalarCoordInv ∘ scalarCoord = id := funext scalarCoordInv_scalarCoord
    rw [hc, Measure.map_id]
  have hν : (ν.map scalarCoord).map scalarCoordInv = ν := by
    rw [Measure.map_map measurable_scalarCoordInv measurable_scalarCoord]
    have hc : scalarCoordInv ∘ scalarCoord = id := funext scalarCoordInv_scalarCoord
    rw [hc, Measure.map_id]
  have h1 := InformationTheory.klDiv_map_le μ ν measurable_scalarCoord
  have h2 := InformationTheory.klDiv_map_le (μ.map scalarCoord) (ν.map scalarCoord)
    measurable_scalarCoordInv
  rw [hμ, hν] at h2
  exact le_antisymm h1 h2

/-- Pair divergence transport: embedding both coordinates of both joint laws does not change
Kullback-Leibler divergence. -/
theorem klDiv_map_scalarCoordPair (μ ν : Measure (ℝ × ℝ))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] :
    klDiv (μ.map (Prod.map scalarCoord scalarCoord))
        (ν.map (Prod.map scalarCoord scalarCoord)) = klDiv μ ν := by
  have hsc : Measurable (Prod.map scalarCoord scalarCoord) :=
    measurable_scalarCoord.prodMap measurable_scalarCoord
  have hsi : Measurable (Prod.map scalarCoordInv scalarCoordInv) :=
    measurable_scalarCoordInv.prodMap measurable_scalarCoordInv
  have hc : (Prod.map scalarCoordInv scalarCoordInv) ∘ (Prod.map scalarCoord scalarCoord)
      = id := by
    funext ⟨a, b⟩
    exact Prod.ext (scalarCoordInv_scalarCoord a) (scalarCoordInv_scalarCoord b)
  have hμ : (μ.map (Prod.map scalarCoord scalarCoord)).map
      (Prod.map scalarCoordInv scalarCoordInv) = μ := by
    rw [Measure.map_map hsi hsc, hc, Measure.map_id]
  have hν : (ν.map (Prod.map scalarCoord scalarCoord)).map
      (Prod.map scalarCoordInv scalarCoordInv) = ν := by
    rw [Measure.map_map hsi hsc, hc, Measure.map_id]
  have h1 := InformationTheory.klDiv_map_le μ ν hsc
  have h2 := InformationTheory.klDiv_map_le (μ.map (Prod.map scalarCoord scalarCoord))
    (ν.map (Prod.map scalarCoord scalarCoord)) hsi
  rw [hμ, hν] at h2
  exact le_antisymm h1 h2

/-- Mutual-information transport: embedding both coordinates does not change mutual information in
bits, including the top value, by data processing in both directions and symmetry. -/
theorem measureMutualInformation_map_scalarCoordPair
    (μ : ProbabilityMeasure (ℝ × ℝ)) :
    measureMutualInformation (μ.map (Prod.map scalarCoord scalarCoord)) =
      measureMutualInformation μ := by
  have hsc : Measurable (Prod.map scalarCoord scalarCoord) :=
    measurable_scalarCoord.prodMap measurable_scalarCoord
  have hfst : Prod.fst ∘ (Prod.map scalarCoord scalarCoord)
      = scalarCoord ∘ Prod.fst := by
    funext ⟨a, b⟩
    rfl
  have hsnd : Prod.snd ∘ (Prod.map scalarCoord scalarCoord)
      = scalarCoord ∘ Prod.snd := by
    funext ⟨a, b⟩
    rfl
  have hcoe : ((μ.map (Prod.map scalarCoord scalarCoord) :
        ProbabilityMeasure (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) :
        Measure (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1))) =
      (μ : Measure (ℝ × ℝ)).map (Prod.map scalarCoord scalarCoord) := rfl
  have hmarg1 : (((μ : Measure (ℝ × ℝ)).map (Prod.map scalarCoord scalarCoord)).map Prod.fst)
      = ((μ : Measure (ℝ × ℝ)).map Prod.fst).map scalarCoord := by
    rw [Measure.map_map measurable_fst hsc, hfst,
      ← Measure.map_map measurable_scalarCoord measurable_fst]
  have hmarg2 : (((μ : Measure (ℝ × ℝ)).map (Prod.map scalarCoord scalarCoord)).map Prod.snd)
      = ((μ : Measure (ℝ × ℝ)).map Prod.snd).map scalarCoord := by
    rw [Measure.map_map measurable_snd hsc, hsnd,
      ← Measure.map_map measurable_scalarCoord measurable_snd]
  have hkl := klDiv_map_scalarCoordPair (μ : Measure (ℝ × ℝ))
    (((μ : Measure (ℝ × ℝ)).map Prod.fst).prod ((μ : Measure (ℝ × ℝ)).map Prod.snd))
  unfold measureMutualInformation
  rw [hcoe, hmarg1, hmarg2,
    Measure.map_prod_map _ _ measurable_scalarCoord measurable_scalarCoord, hkl]

/-- **KL chain rule in scalar coordinates.** For finite input laws `μ`, `ν` on `ℝ` and Markov
kernels `κ`, `η` from `ℝ` to `ℝ`, the divergence between the embedded joint laws `μ ⊗ₘ κ` and
`ν ⊗ₘ η` is the divergence between the embedded input laws plus the embedded conditional term
`KL(μ ⊗ₘ κ ‖ μ ⊗ₘ η)`, as an identity in `ℝ≥0∞`. -/
theorem klDiv_map_scalarCoordPair_compProd_eq_add (μ ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (κ η : Kernel ℝ ℝ)
    [IsMarkovKernel κ] [IsMarkovKernel η] :
    klDiv ((μ ⊗ₘ κ).map (Prod.map scalarCoord scalarCoord))
        ((ν ⊗ₘ η).map (Prod.map scalarCoord scalarCoord)) =
      klDiv (μ.map scalarCoord) (ν.map scalarCoord) +
        klDiv ((μ ⊗ₘ κ).map (Prod.map scalarCoord scalarCoord))
          ((μ ⊗ₘ η).map (Prod.map scalarCoord scalarCoord)) := by
  rw [klDiv_map_scalarCoordPair, klDiv_map_scalarCoordPair, klDiv_map_scalarCoord]
  exact InformationTheory.klDiv_compProd_eq_add μ ν κ η

/-- **KL chain rule in scalar coordinates, reference-output form.** For a joint probability law `μ`
on `ℝ × ℝ` and a reference output probability `Q` on `ℝ`, the divergence from the embedded joint law
to the embedded input marginal times the embedded reference splits into the divergence to the
product of the embedded marginals plus the divergence from the embedded output marginal to the
embedded reference, as an identity in `ℝ≥0∞`. -/
theorem klDiv_map_scalarCoordPair_prod_reference_eq_add (μ : ProbabilityMeasure (ℝ × ℝ))
    (Q : Measure ℝ) [IsProbabilityMeasure Q] :
    klDiv ((μ : Measure (ℝ × ℝ)).map (Prod.map scalarCoord scalarCoord))
        ((((μ : Measure (ℝ × ℝ)).map Prod.fst).map scalarCoord).prod (Q.map scalarCoord)) =
      klDiv ((μ : Measure (ℝ × ℝ)).map (Prod.map scalarCoord scalarCoord))
          ((((μ : Measure (ℝ × ℝ)).map Prod.fst).map scalarCoord).prod
            (((μ : Measure (ℝ × ℝ)).map Prod.snd).map scalarCoord)) +
        klDiv (((μ : Measure (ℝ × ℝ)).map Prod.snd).map scalarCoord) (Q.map scalarCoord) := by
  rw [Measure.map_prod_map _ _ measurable_scalarCoord measurable_scalarCoord,
    Measure.map_prod_map _ _ measurable_scalarCoord measurable_scalarCoord,
    klDiv_map_scalarCoordPair, klDiv_map_scalarCoordPair, klDiv_map_scalarCoord]
  exact MathlibExt.InformationTheory.ReferenceOutputKL.klDiv_prod_reference_eq_add μ Q

/-- **Scalar Gaussian divergence in vector form.** For positive variances, the scalar Gaussian
divergence is the embedded vector Gaussian divergence closed form at dimension one. -/
theorem scalarGaussian_klDiv_eq_vector (m q s t : ℝ) (hs : 0 < s) (ht : 0 < t) :
    klDiv (gaussianReal m ⟨s, hs.le⟩) (gaussianReal q ⟨t, ht.le⟩) =
      ENNReal.ofReal (MathlibExt.InformationTheory.VectorGaussianKL.multivariateGaussianKLReal
        (scalarCoord m) (scalarCoord q) (!![s] : Matrix (Fin 1) (Fin 1) ℝ)
        (!![t] : Matrix (Fin 1) (Fin 1) ℝ)) := by
  have hs' : (!![s] : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
    have hdiag : (!![s] : Matrix (Fin 1) (Fin 1) ℝ)
        = Matrix.diagonal (fun _ : Fin 1 => s) := by
      ext i j
      rw [Fin.eq_zero i, Fin.eq_zero j]
      rfl
    rw [hdiag]
    exact Matrix.PosDef.diagonal (fun _ => hs)
  have ht' : (!![t] : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
    have hdiag : (!![t] : Matrix (Fin 1) (Fin 1) ℝ)
        = Matrix.diagonal (fun _ : Fin 1 => t) := by
      ext i j
      rw [Fin.eq_zero i, Fin.eq_zero j]
      rfl
    rw [hdiag]
    exact Matrix.PosDef.diagonal (fun _ => ht)
  have : IsProbabilityMeasure (gaussianReal m ⟨s, hs.le⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal m ⟨s, hs.le⟩
  have : IsProbabilityMeasure (gaussianReal q ⟨t, ht.le⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal q ⟨t, ht.le⟩
  have : IsFiniteMeasure (gaussianReal m ⟨s, hs.le⟩) := ⟨by simp⟩
  have : IsFiniteMeasure (gaussianReal q ⟨t, ht.le⟩) := ⟨by simp⟩
  have hkl := klDiv_map_scalarCoord (gaussianReal m ⟨s, hs.le⟩)
    (gaussianReal q ⟨t, ht.le⟩)
  rw [← hkl, map_scalarCoord_gaussianReal m s hs.le,
    map_scalarCoord_gaussianReal q t ht.le]
  exact MathlibExt.InformationTheory.VectorGaussianKL.klDiv_multivariateGaussian
    (scalarCoord m) (scalarCoord q) (!![s] : Matrix (Fin 1) (Fin 1) ℝ)
    (!![t] : Matrix (Fin 1) (Fin 1) ℝ) hs' ht'

/-- **Scalar Gaussian channel identification.** Under the channel hypotheses, the embedded Gaussian
noise law, the conditional law at gain `[1]`, the joint law as input law composed with the noise
kernel, and the power identification all hold together. This is the headline identification;
divergence and mutual-information transport are the separate corollaries above. -/
theorem scalarGaussianChannel_identification {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X Z : Ω → ℝ} (hX : Measurable X)
    (hZ : Measurable Z) (hind : IndepFun X Z μ) (N P : ℝ) (hN : 0 < N)
    (hZlaw : μ.map Z = gaussianReal 0 ⟨N, hN.le⟩) :
    (gaussianReal 0 ⟨N, hN.le⟩).map scalarCoord =
        multivariateGaussian 0 (!![N] : Matrix (Fin 1) (Fin 1) ℝ) ∧
      (condDistrib (fun ω => scalarCoord (X ω + Z ω)) (fun ω => scalarCoord (X ω)) μ =ᵐ[
        μ.map (fun ω => scalarCoord (X ω))]
        MetaMathlibExt.noiseKernel (toEuclideanLin (!![1] : Matrix (Fin 1) (Fin 1) ℝ))
          (MetaMathlibExt.continuous_toEuclideanLin
            (!![1] : Matrix (Fin 1) (Fin 1) ℝ)).measurable
          (multivariateGaussian 0 (!![N] : Matrix (Fin 1) (Fin 1) ℝ))) ∧
      (μ.map (fun ω => (scalarCoord (X ω), scalarCoord (X ω + Z ω))) =
        (μ.map (fun ω => scalarCoord (X ω))) ⊗ₘ
          MetaMathlibExt.noiseKernel (toEuclideanLin (!![1] : Matrix (Fin 1) (Fin 1) ℝ))
            (MetaMathlibExt.continuous_toEuclideanLin
              (!![1] : Matrix (Fin 1) (Fin 1) ℝ)).measurable
            (multivariateGaussian 0 (!![N] : Matrix (Fin 1) (Fin 1) ℝ))) ∧
      (PowerConstraint μ (fun ω => scalarCoord (X ω)) P ↔ scalarPowerBound μ X P) := by
  have h0 : scalarCoord 0 = 0 := map_zero lineIsometry
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := map_scalarCoord_gaussianReal 0 N hN.le
    rwa [h0] at h
  · exact condDistrib_scalarCoord_add hX hZ hind N hN hZlaw
  · exact map_prod_scalarCoord_add hX hZ hind N hN hZlaw
  · exact scalarPowerBound_iff_powerConstraint μ X P

/-- Validation, point mass and nonzero mean: a point mass at `2` meets the scalar power bound at `P
= 4` and fails it at `P = 3`; its embedded second moment is `4`. -/
theorem scalarPowerBound_dirac_two :
    scalarPowerBound (Measure.dirac 2) id 4 ∧
      ¬ scalarPowerBound (Measure.dirac 2) id 3 := by
  constructor
  · unfold scalarPowerBound
    refine ⟨by norm_num, ?_⟩
    rw [lintegral_dirac]
    change ENNReal.ofReal ((2 : ℝ) ^ 2) ≤ ENNReal.ofReal 4
    exact ENNReal.ofReal_le_ofReal (by norm_num)
  · rintro ⟨-, h⟩
    rw [lintegral_dirac] at h
    change ENNReal.ofReal ((2 : ℝ) ^ 2) ≤ ENNReal.ofReal 3 at h
    have h4 : (2 : ℝ) ^ 2 = 4 := by norm_num
    rw [h4] at h
    have hle := (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 3)).mp h
    norm_num at hle

/-- Validation, `P = 0` boundary and infinite integral guard: a nonzero constant input fails the
scalar bound at `P = 0`. -/
theorem not_scalarPowerBound_zero_const {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {c : ℝ} (hc : c ≠ 0) :
    ¬ scalarPowerBound μ (fun _ => c) 0 := by
  rintro ⟨-, h⟩
  change ∫⁻ ω, ENNReal.ofReal (c ^ 2) ∂μ ≤ ENNReal.ofReal 0 at h
  rw [lintegral_const, IsProbabilityMeasure.measure_univ, mul_one] at h
  have h' : c ^ 2 ≤ 0 := (ENNReal.ofReal_le_ofReal_iff le_rfl).mp h
  have h0 : c ^ 2 = 0 := le_antisymm h' (sq_nonneg c)
  exact hc (sq_eq_zero_iff.mp h0)

/-- Validation, positive-variance Gaussian input: a real Gaussian of mean `m` and variance `0 ≤ s`
meets the scalar power bound at `P = m^2 + s`, so a nonzero mean contributes to total power. -/
theorem scalarPowerBound_gaussianReal (m s : ℝ) (hs : 0 ≤ s) :
    scalarPowerBound (gaussianReal m ⟨s, hs⟩) id (m ^ 2 + s) := by
  have hmem : MemLp id 2 (gaussianReal m ⟨s, hs⟩) :=
    ProbabilityTheory.memLp_id_gaussianReal' 2 ENNReal.ofNat_ne_top
  have hvar : ProbabilityTheory.variance id (gaussianReal m ⟨s, hs⟩) = s :=
    ProbabilityTheory.variance_id_gaussianReal
  have : IsProbabilityMeasure (gaussianReal m ⟨s, hs⟩) :=
    ProbabilityTheory.instIsProbabilityMeasureGaussianReal m ⟨s, hs⟩
  have hdecomp := ProbabilityTheory.variance_eq_sub hmem
  rw [hvar] at hdecomp
  simp only [Pi.pow_apply, id_eq] at hdecomp
  have hmean : (∫ x, x ∂(gaussianReal m ⟨s, hs⟩)) = m :=
    ProbabilityTheory.integral_id_gaussianReal (μ := m) (v := ⟨s, hs⟩)
  rw [hmean] at hdecomp
  have hint : Integrable (fun x : ℝ => (id x) ^ 2) (gaussianReal m ⟨s, hs⟩) :=
    hmem.integrable_sq
  have hconv := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint
    (ae_of_all _ fun x => sq_nonneg (id x))
  have hEq : (∫ x, ((id x) ^ 2 : ℝ) ∂(gaussianReal m ⟨s, hs⟩)) = m ^ 2 + s := by
    have hdecomp' : s
        = (∫ x, ((id x) ^ 2 : ℝ) ∂(gaussianReal m ⟨s, hs⟩)) - m ^ 2 := hdecomp
    linarith
  unfold scalarPowerBound
  refine ⟨by positivity, ?_⟩
  rw [← hconv, hEq]

/-- Validation, negative budget: no input, not even the zero input, meets the scalar power bound
at a negative budget, although `ENNReal.ofReal` sends that budget to `0`. -/
theorem not_scalarPowerBound_of_neg {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {μ : Measure Ω} {X : Ω → ℝ} {P : ℝ} (hP : P < 0) : ¬ scalarPowerBound μ X P :=
  fun h => absurd h.nonneg (not_le.mpr hP)

end MathlibExt.InformationTheory.ScalarGaussianCoordinates
