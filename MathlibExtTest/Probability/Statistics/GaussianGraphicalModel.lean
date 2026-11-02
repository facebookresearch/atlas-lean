/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.GaussianGraphicalModel

@[expose] public section

open Matrix MeasureTheory ProbabilityTheory
open MathlibExt.Probability.Statistics.GaussianGraphicalModel

namespace MathlibExtTest.Probability.Statistics.GaussianGraphicalModel

/-- Non-vacuity of `IsSupportedOn`: a diagonal matrix is supported on the empty graph. -/
example (d : Fin 3 → ℝ) : IsSupportedOn (⊥ : SimpleGraph (Fin 3)) (diagonal d) :=
  fun _ _ hij _ => diagonal_apply_ne d hij

/-- Every matrix is supported on the complete graph. -/
example (K : Matrix (Fin 3) (Fin 3) ℝ) : IsSupportedOn (⊤ : SimpleGraph (Fin 3)) K :=
  fun i j hij h => absurd ((SimpleGraph.top_adj i j).2 hij) h

/-- With identity covariance the partial correlation is `0`. -/
example : partialCorrelation (1 : Matrix (Fin 2 ⊕ Fin 1) (Fin 2 ⊕ Fin 1) ℝ) = 0 := by
  rw [partialCorrelation_eq PosDef.one, inv_one]
  simp

/-- For a standard Gaussian vector `(X₀, X₁, Y) ~ N(0, I)`, `X₀ ⟂ X₁ | Y`. -/
example {Ω : Type*} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {V : Ω → EuclideanSpace ℝ (Fin 2 ⊕ Fin 1)} (hV : Measurable V)
    (hlaw : P.map V = multivariateGaussian 0 1) :
    (fun ω => V ω (.inl 0)) ⟂ᵢ[fun ω => rest (V ω), measurable_rest.comp hV; P]
      (fun ω => V ω (.inl 1)) :=
  (condIndepFun_iff_inv_apply_eq_zero hV PosDef.one hlaw).2 (by simp)

/-- The sample-moment identity for one observation `x = (1, 2)` and `K = I`:
`xᵀ x = 5 = 1 · tr (x xᵀ)`. -/
example : ∑ _s : Fin 1, ![(1 : ℝ), 2] ⬝ᵥ (1 : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![(1 : ℝ), 2] =
    (1 : ℕ) * (sampleCov (fun _ : Fin 1 => ![(1 : ℝ), 2]) * 1).trace :=
  sum_dotProduct_mulVec_eq one_pos _ 1

/-- Dempster's theorem on the complete graph is the closed-form MLE `K̂ = S⁻¹`. -/
example {S K : Matrix (Fin 3) (Fin 3) ℝ} (hS : S.PosDef) (hK : K.PosDef) :
    gaussLogLik S K ≤ gaussLogLik S S⁻¹ :=
  gaussLogLik_le_of_inv_eq_on_graph (G := ⊤) hS.inv (fun i j hij h => absurd
    ((SimpleGraph.top_adj i j).2 hij) h)
    (fun _ _ _ => by rw [nonsing_inv_nonsing_inv S (isUnit_iff_ne_zero.2 hS.det_pos.ne')])
    hK fun i j hij h => absurd ((SimpleGraph.top_adj i j).2 hij) h

/-- Junk value outside the domain: `gaussLogLik` of the zero matrix uses `log 0 = 0`; the
theorems require positive definite precision matrices. -/
example (S : Matrix (Fin 2) (Fin 2) ℝ) : gaussLogLik S 0 = 0 := by
  simp [gaussLogLik]

#print axioms condIndepFun_iff_inv_apply_eq_zero
#print axioms eq_of_gaussLogLik_eq

end MathlibExtTest.Probability.Statistics.GaussianGraphicalModel
