/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.InformationTheory.ScalarGaussianCoordinates
public import MathlibExt.InformationTheory.VectorGaussianKernelKL

/-!
# KL divergence of the scalar Gaussian channel kernel

Let `N > 0` and `V > 0` be noise and reference variances and `m` a real reference mean. For an
input law `μ` on `ℝ` with finite second moment (no density assumed), let `k` be the scalar
additive Gaussian noise kernel `x ↦ N(x, N)`, the canonical `MetaMathlibExt.noiseKernel` at
identity gain with noise law `N(0, N)` (`noiseKernel_id_gaussianReal_apply`). Then, in nats,

`KL(μ ⊗ₘ k ‖ μ × N(m, V)) = ofReal ((log (V / N) + (N + ∫ (x - m)² dμ) / V - 1) / 2)`

(`klDiv_compProd_gaussianNoiseKernel`, closed form `scalarGaussianKernelKLReal`).

The proof specializes the vector Gaussian-kernel divergence
`MathlibExt.InformationTheory.VectorGaussianKernelKL.klDiv_compProd_noiseKernel` at gain `[1]`,
noise covariance `[N]` and reference covariance `[V]`, transporting through the scalar coordinate
`MathlibExt.InformationTheory.ScalarGaussianCoordinates.scalarCoord`: the joint law
(`map_compProd_noiseKernel_scalarCoord`), the reference law
(`map_prod_gaussianReal_scalarCoord`), the moment hypothesis (`memLp_id_map_scalarCoord`) and the
closed form (`gaussianKernelKLReal_scalarCoord`) each transport separately, and the embedding
preserves divergence. Integrability and absolute continuity come from the vector theorem.

The finite second moment is the vector theorem's hypothesis `MemLp id 2 μ`; a corollary takes the
scalar power bound `0 ≤ Pw ∧ ∫⁻ ofReal (x²) dμ ≤ ofReal Pw` instead
(`klDiv_compProd_gaussianNoiseKernel_of_scalarPowerBound`), and an infinite second lower moment
fails both guards (`not_memLp_two_of_lintegral_sq_eq_top`,
`not_scalarPowerBound_of_lintegral_sq_eq_top`).

Validation: a point-mass input (`scalarGaussianKernelKLReal_dirac`,
`klDiv_compProd_gaussianNoiseKernel_dirac`, `klDiv_compProd_gaussianNoiseKernel_dirac_three`)
and a Gaussian input with arbitrary mean (`scalarGaussianKernelKLReal_gaussianReal`,
`klDiv_compProd_gaussianNoiseKernel_gaussianReal`). No coding theorem is claimed.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix WithLp
open scoped ENNReal NNReal

namespace MathlibExt.InformationTheory.ScalarGaussianKernelKL

open _root_.InformationTheory
open MathlibExt.InformationTheory.VectorGaussianKernelKL
open MathlibExt.InformationTheory.ScalarGaussianCoordinates
open MathlibExt.Analysis.InnerProductSpace.LineIsometry

/-- The scalar Gaussian channel kernel divergence closed form, in nats:
`(log (V / N) + (N + ∫ (x - m)² dμ) / V - 1) / 2`. -/
noncomputable def scalarGaussianKernelKLReal (m N V : ℝ) (μ : Measure ℝ) : ℝ :=
  (Real.log (V / N) + (N + ∫ x, (x - m) ^ 2 ∂μ) / V - 1) / 2

/-- The scalar noise kernel at identity gain is `x ↦ N(x, N)`. -/
theorem noiseKernel_id_gaussianReal_apply (N : ℝ≥0) (x : ℝ) :
    MetaMathlibExt.noiseKernel id measurable_id (gaussianReal 0 N) x = gaussianReal x N := by
  rw [MetaMathlibExt.noiseKernel_apply, id, gaussianReal_map_const_add, zero_add]

/-- Joint-law transport: embedding both coordinates of the scalar joint law gives the embedded
input law composed with the vector noise kernel at gain `[1]` and noise covariance `[N]`. -/
theorem map_compProd_noiseKernel_scalarCoord (N : ℝ≥0) (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (μ ⊗ₘ MetaMathlibExt.noiseKernel id measurable_id (gaussianReal 0 N)).map
        (Prod.map scalarCoord scalarCoord) =
      (μ.map scalarCoord) ⊗ₘ
        MetaMathlibExt.noiseKernel (toEuclideanLin (!![1] : Matrix (Fin 1) (Fin 1) ℝ))
          (MetaMathlibExt.continuous_toEuclideanLin
            (!![1] : Matrix (Fin 1) (Fin 1) ℝ)).measurable
          (multivariateGaussian 0 (!![(N : ℝ)] : Matrix (Fin 1) (Fin 1) ℝ)) := by
  have hsc := measurable_scalarCoord
  have hsc2 : Measurable (Prod.map scalarCoord scalarCoord) := hsc.prodMap hsc
  have hH : Measurable (toEuclideanLin (!![1] : Matrix (Fin 1) (Fin 1) ℝ)) :=
    (MetaMathlibExt.continuous_toEuclideanLin _).measurable
  have hG : multivariateGaussian 0 (!![(N : ℝ)] : Matrix (Fin 1) (Fin 1) ℝ) =
      (gaussianReal 0 N).map scalarCoord := by
    have h := map_scalarCoord_gaussianReal 0 N N.2
    have h0 : scalarCoord 0 = 0 := map_zero lineIsometry
    rw [h0] at h
    exact h.symm
  rw [compProd_noiseKernel_eq_map, compProd_noiseKernel_eq_map, hG,
    Measure.map_prod_map _ _ hsc hsc, Measure.map_map hsc2 (by fun_prop),
    Measure.map_map (by fun_prop) hsc2]
  congr 1
  funext p
  exact Prod.ext rfl (scalarCoord_add p.1 p.2)

/-- Reference-law transport: embedding both coordinates of `μ × N(m, V)` gives the embedded input
law times the one-dimensional Gaussian with mean `(m)` and covariance `[V]`. -/
theorem map_prod_gaussianReal_scalarCoord (m : ℝ) (V : ℝ≥0) (μ : Measure ℝ)
    [IsProbabilityMeasure μ] :
    (μ.prod (gaussianReal m V)).map (Prod.map scalarCoord scalarCoord) =
      (μ.map scalarCoord).prod
        (multivariateGaussian (scalarCoord m) (!![(V : ℝ)] : Matrix (Fin 1) (Fin 1) ℝ)) := by
  have hG : (gaussianReal m V).map scalarCoord =
      multivariateGaussian (scalarCoord m) (!![(V : ℝ)] : Matrix (Fin 1) (Fin 1) ℝ) :=
    map_scalarCoord_gaussianReal m V V.2
  rw [← hG, Measure.map_prod_map _ _ measurable_scalarCoord measurable_scalarCoord]

/-- Finite second moment transports to the embedded input law. -/
theorem memLp_id_map_scalarCoord (μ : Measure ℝ) (hμ : MemLp id 2 μ) :
    MemLp id 2 (μ.map scalarCoord) := by
  rw [memLp_map_measure_iff aestronglyMeasurable_id measurable_scalarCoord.aemeasurable]
  refine hμ.of_le measurable_scalarCoord.aestronglyMeasurable
    (Filter.Eventually.of_forall fun x => le_of_eq ?_)
  rw [Function.comp_apply, id, id, norm_scalarCoord, Real.norm_eq_abs]

/-- Closed-form transport: the vector closed form at gain `[1]`, reference mean `(m)`, noise
covariance `[N]`, reference covariance `[V]` and the embedded input law is the scalar closed
form. An identity for every input law and all real parameters. -/
theorem gaussianKernelKLReal_scalarCoord (m N V : ℝ) (μ : Measure ℝ) :
    gaussianKernelKLReal (!![1] : Matrix (Fin 1) (Fin 1) ℝ) (scalarCoord m)
        (!![N] : Matrix (Fin 1) (Fin 1) ℝ) (!![V] : Matrix (Fin 1) (Fin 1) ℝ)
        (μ.map scalarCoord) =
      scalarGaussianKernelKLReal m N V μ := by
  rw [gaussianKernelKLReal, scalarGaussianKernelKLReal,
    integral_map measurable_scalarCoord.aemeasurable (by fun_prop)]
  have hq : ∀ x : ℝ,
      ofLp (toEuclideanLin (!![1] : Matrix (Fin 1) (Fin 1) ℝ) (scalarCoord x) - scalarCoord m) ⬝ᵥ
          (!![V] : Matrix (Fin 1) (Fin 1) ℝ)⁻¹ *ᵥ
          ofLp (toEuclideanLin (!![1] : Matrix (Fin 1) (Fin 1) ℝ) (scalarCoord x) - scalarCoord m)
        = (x - m) ^ 2 * V⁻¹ := by
    intro x
    rw [toEuclideanLin_one_scalarCoord]
    simp [dotProduct, mulVec]
    ring
  simp_rw [hq]
  rw [integral_mul_const]
  simp [Matrix.trace_fin_one]
  ring

/-- **Scalar Gaussian channel kernel divergence.** For positive noise and reference variances
`N`, `V`, a reference mean `m`, and an input probability law `μ` with finite second moment,
`klDiv (μ ⊗ₘ (x ↦ N(x, N))) (μ × N(m, V)) =
ofReal ((log (V / N) + (N + ∫ (x - m)² dμ) / V - 1) / 2)`. -/
theorem klDiv_compProd_gaussianNoiseKernel (m : ℝ) (N V : ℝ≥0) (hN : 0 < N) (hV : 0 < V)
    (μ : Measure ℝ) [IsProbabilityMeasure μ] (hμ : MemLp id 2 μ) :
    klDiv (μ ⊗ₘ MetaMathlibExt.noiseKernel id measurable_id (gaussianReal 0 N))
        (μ.prod (gaussianReal m V)) =
      ENNReal.ofReal (scalarGaussianKernelKLReal m N V μ) := by
  have hpd : ∀ c : ℝ≥0, 0 < c → (!![(c : ℝ)] : Matrix (Fin 1) (Fin 1) ℝ).PosDef := by
    intro c hc
    have h : (!![(c : ℝ)] : Matrix (Fin 1) (Fin 1) ℝ) = diagonal fun _ => (c : ℝ) := by
      ext i j
      fin_cases i
      fin_cases j
      rfl
    rw [h, posDef_diagonal_iff]
    intro _
    exact_mod_cast hc
  rw [← klDiv_map_scalarCoordPair
      (μ ⊗ₘ MetaMathlibExt.noiseKernel id measurable_id (gaussianReal 0 N))
      (μ.prod (gaussianReal m V)),
    map_compProd_noiseKernel_scalarCoord, map_prod_gaussianReal_scalarCoord,
    klDiv_compProd_noiseKernel _ _ _ _ (hpd N hN) (hpd V hV) _ (memLp_id_map_scalarCoord μ hμ),
    gaussianKernelKLReal_scalarCoord]

/-- Power-bound form: the same divergence under the scalar finite-power model
`0 ≤ Pw ∧ ∫⁻ ofReal (x²) dμ ≤ ofReal Pw`. -/
theorem klDiv_compProd_gaussianNoiseKernel_of_scalarPowerBound (m : ℝ) (N V : ℝ≥0)
    (hN : 0 < N) (hV : 0 < V) (μ : Measure ℝ) [IsProbabilityMeasure μ] (Pw : ℝ)
    (hpow : scalarPowerBound μ id Pw) :
    klDiv (μ ⊗ₘ MetaMathlibExt.noiseKernel id measurable_id (gaussianReal 0 N))
        (μ.prod (gaussianReal m V)) =
      ENNReal.ofReal (scalarGaussianKernelKLReal m N V μ) :=
  klDiv_compProd_gaussianNoiseKernel m N V hN hV μ
    (memLp_of_scalarPowerBound hpow aestronglyMeasurable_id)

/-- Feasibility guard, moment form: an input law with infinite second lower moment does not have a
finite second moment, so it cannot meet the headline hypothesis. -/
theorem not_memLp_two_of_lintegral_sq_eq_top (μ : Measure ℝ)
    (h : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂μ = ∞) : ¬ MemLp id 2 μ := by
  intro hm
  have hfin := hm.integrable_sq.hasFiniteIntegral
  rw [HasFiniteIntegral] at hfin
  have : ∫⁻ x, ‖(id x) ^ 2‖ₑ ∂μ = ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂μ := by
    refine lintegral_congr fun x => ?_
    rw [id, Real.enorm_of_nonneg (sq_nonneg x)]
  rw [this, h] at hfin
  exact lt_irrefl _ hfin

/-- Feasibility guard, power form: an input law with infinite second lower moment fails the scalar
power bound at every level. -/
theorem not_scalarPowerBound_of_lintegral_sq_eq_top (μ : Measure ℝ)
    (h : ∫⁻ x, ENNReal.ofReal (x ^ 2) ∂μ = ∞) (Pw : ℝ) : ¬ scalarPowerBound μ id Pw := by
  rintro ⟨-, hb⟩
  simp only [id] at hb
  rw [h] at hb
  exact ENNReal.ofReal_ne_top (top_le_iff.mp hb)

/-- Validation, point-mass input, closed form: at the input `δ_a` the closed form equals
`(log (V / N) + (N + (a - m)²) / V - 1) / 2`, an identity of real expressions for all real `m`,
`N`, `V` and `a`, with `x / 0 = 0`, `log 0 = 0` and `log t = log |t|` for `t < 0`. When `N > 0`
and `V > 0` the value is `KL(N(a, N) ‖ N(m, V))` (`klDiv_compProd_gaussianNoiseKernel_dirac`);
for `N = 0 < V` that divergence is infinite while the expression is finite (`-1 / 2` at
`m = a = 0` and `V = 1`). -/
theorem scalarGaussianKernelKLReal_dirac (m N V a : ℝ) :
    scalarGaussianKernelKLReal m N V (Measure.dirac a) =
      (Real.log (V / N) + (N + (a - m) ^ 2) / V - 1) / 2 := by
  rw [scalarGaussianKernelKLReal, integral_dirac]

/-- Validation, point-mass input, measure level. -/
theorem klDiv_compProd_gaussianNoiseKernel_dirac (m : ℝ) (N V : ℝ≥0) (hN : 0 < N) (hV : 0 < V)
    (a : ℝ) :
    klDiv ((Measure.dirac a) ⊗ₘ MetaMathlibExt.noiseKernel id measurable_id (gaussianReal 0 N))
        ((Measure.dirac a).prod (gaussianReal m V)) =
      ENNReal.ofReal ((Real.log (V / N) + (N + (a - m) ^ 2) / V - 1) / 2) := by
  have hmem : MemLp id 2 (Measure.dirac a) :=
    (memLp_const (id a)).ae_eq (ae_eq_dirac id).symm
  rw [klDiv_compProd_gaussianNoiseKernel m N V hN hV _ hmem, scalarGaussianKernelKLReal_dirac]

/-- Validation, point mass with nonzero mean: input `3`, reference `N(0, 1)`, noise variance `1`;
the divergence is `9 / 2`, all of it from the input mean. -/
theorem klDiv_compProd_gaussianNoiseKernel_dirac_three :
    klDiv ((Measure.dirac (3 : ℝ)) ⊗ₘ
          MetaMathlibExt.noiseKernel id measurable_id (gaussianReal 0 1))
        ((Measure.dirac (3 : ℝ)).prod (gaussianReal 0 1)) =
      ENNReal.ofReal (9 / 2) := by
  rw [klDiv_compProd_gaussianNoiseKernel_dirac 0 1 1 one_pos one_pos 3]
  congr 1
  norm_num

/-- Validation, Gaussian input, closed form: for input `N(μ₀, s)` the expected square deviation is
`s + (μ₀ - m)²`, so a nonzero input mean adds to the quadratic term. -/
theorem scalarGaussianKernelKLReal_gaussianReal (m N V μ₀ : ℝ) (s : ℝ≥0) :
    scalarGaussianKernelKLReal m N V (gaussianReal μ₀ s) =
      (Real.log (V / N) + (N + (s + (μ₀ - m) ^ 2)) / V - 1) / 2 := by
  have hmem : MemLp (fun x : ℝ => x - m) 2 (gaussianReal μ₀ s) :=
    (memLp_id_gaussianReal 2).sub (memLp_const m)
  have hvar := variance_eq_sub hmem
  have hsub : Var[fun x : ℝ => x - m; gaussianReal μ₀ s] = s := by
    rw [show (fun x : ℝ => x - m) = fun x => id x - m from rfl,
      variance_sub_const (measurable_id.aestronglyMeasurable), variance_id_gaussianReal]
  have hmean : ∫ x, (x - m) ∂(gaussianReal μ₀ s) = μ₀ - m := by
    rw [integral_sub (f := fun x : ℝ => x) (g := fun _ => m)
      ((memLp_id_gaussianReal 1).integrable le_rfl) (integrable_const m),
      integral_id_gaussianReal]
    simp
  rw [hsub] at hvar
  simp only [Pi.pow_apply] at hvar
  rw [hmean] at hvar
  have hint : ∫ x, (x - m) ^ 2 ∂(gaussianReal μ₀ s) = s + (μ₀ - m) ^ 2 := by linarith
  rw [scalarGaussianKernelKLReal, hint]

/-- Validation, Gaussian input, measure level. -/
theorem klDiv_compProd_gaussianNoiseKernel_gaussianReal (m μ₀ : ℝ) (N V s : ℝ≥0) (hN : 0 < N)
    (hV : 0 < V) :
    klDiv ((gaussianReal μ₀ s) ⊗ₘ MetaMathlibExt.noiseKernel id measurable_id (gaussianReal 0 N))
        ((gaussianReal μ₀ s).prod (gaussianReal m V)) =
      ENNReal.ofReal ((Real.log (V / N) + (N + (s + (μ₀ - m) ^ 2)) / V - 1) / 2) := by
  rw [klDiv_compProd_gaussianNoiseKernel m N V hN hV _ (memLp_id_gaussianReal 2),
    scalarGaussianKernelKLReal_gaussianReal]

end MathlibExt.InformationTheory.ScalarGaussianKernelKL
