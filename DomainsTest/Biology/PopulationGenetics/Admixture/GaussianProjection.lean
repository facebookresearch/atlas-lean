/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Domains.Biology.PopulationGenetics.Admixture.GaussianProjection

/-!
# Tests for the Gaussian projection lemma

Generic restatements of the results, the endpoints `T = ⊥` (the Hotelling form) and `T = ⊤`
(whose Dirac law is no chi-square law), the identity covariance, and a line in the plane.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Matrix Module

namespace MathlibExtTest.Biology.PopulationGenetics.Admixture.GaussianProjection

open MathlibExt.Biology.PopulationGenetics.Admixture
open MathlibExt.LinearAlgebra.Matrix.QuadraticFormCongruence (quadForm)

section Generic

variable {n : Type*} [Fintype n] [DecidableEq n] {V : Matrix n n ℝ}

/-- On the coordinates of a Euclidean vector `w`, `quadForm A` is `wᵀ A w` in coordinates. -/
example (A : Matrix n n ℝ) (w : EuclideanSpace ℝ n) :
    quadForm A (fun i => w i) = (fun i => w i) ⬝ᵥ A *ᵥ (fun i => w i) :=
  rfl

/-- The statistic is the minimum of the residual quadratic form over the subspace. -/
example (hV : V.PosDef) (T : Submodule ℝ (EuclideanSpace ℝ n)) (z : EuclideanSpace ℝ n) :
    gaussProjStat V T z = ⨅ u : T, quadForm V⁻¹ (fun i => (z - (u : EuclideanSpace ℝ n)) i) :=
  (gaussProjStat_eq_iInf hV T z).1

/-- The minimum is attained in the subspace. -/
example (hV : V.PosDef) (T : Submodule ℝ (EuclideanSpace ℝ n)) (z : EuclideanSpace ℝ n) :
    ∃ u ∈ T, gaussProjStat V T z = quadForm V⁻¹ (fun i => (z - u) i) :=
  (gaussProjStat_eq_iInf hV T z).2

/-- The Gaussian projection lemma: codimension `c > 0` gives the chi-square law with `c`
degrees of freedom. -/
example (hV : V.PosDef) (T : Submodule ℝ (EuclideanSpace ℝ n))
    (hc : 0 < Fintype.card n - finrank ℝ T) :
    (multivariateGaussian 0 V).map (gaussProjStat V T) =
      chiSquareMeasure (Fintype.card n - finrank ℝ T) :=
  map_gaussProjStat_multivariateGaussian hV T hc

/-- The Hotelling form: `Zᵀ V⁻¹ Z` is chi-square with `card n` degrees of freedom. -/
example (hV : V.PosDef) (hm : 0 < Fintype.card n) :
    (multivariateGaussian 0 V).map (fun w => quadForm V⁻¹ (fun i => w i)) =
      chiSquareMeasure (Fintype.card n) :=
  map_quadForm_multivariateGaussian hV hm

/-- `T = ⊥`: nothing is fitted, the statistic is the full quadratic form. -/
example (hV : V.PosDef) (z : EuclideanSpace ℝ n) :
    gaussProjStat V ⊥ z = quadForm V⁻¹ (fun i => z i) :=
  gaussProjStat_bot hV z

/-- `T = ⊥` through the main law: codimension `card n`. -/
example (hV : V.PosDef) (hm : 0 < Fintype.card n) :
    (multivariateGaussian 0 V).map (gaussProjStat V ⊥) = chiSquareMeasure (Fintype.card n) := by
  simpa using map_gaussProjStat_multivariateGaussian hV ⊥ (by simpa using hm)

/-- `T = ⊤`: every point is fitted exactly and the statistic vanishes. -/
example (hV : V.PosDef) (z : EuclideanSpace ℝ n) : gaussProjStat V ⊤ z = 0 :=
  gaussProjStat_top hV z

/-- `T = ⊤`: the law is the Dirac mass at `0`. -/
example (hV : V.PosDef) :
    (multivariateGaussian 0 V).map (gaussProjStat V ⊤) = Measure.dirac 0 :=
  map_gaussProjStat_top hV

/-- The codimension-zero law is no chi-square law, since chi-square laws have no atoms. In
particular it is not `chiSquareMeasure 0`, which is the zero measure. -/
example (hV : V.PosDef) (p : ℕ) :
    (multivariateGaussian 0 V).map (gaussProjStat V ⊤) ≠ chiSquareMeasure p := by
  rw [map_gaussProjStat_top hV]
  intro h
  have h0 := congrArg (fun μ : Measure ℝ => μ {0}) h
  simp at h0

end Generic

section Examples

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Identity covariance, `T = ⊥`: the statistic is `‖z‖²`. -/
example (z : EuclideanSpace ℝ n) : gaussProjStat 1 ⊥ z = ‖z‖ ^ 2 := by
  rw [gaussProjStat_bot PosDef.one, inv_one, quadForm, one_mulVec,
    EuclideanSpace.real_norm_sq_eq]
  simp [dotProduct, pow_two]

/-- Identity covariance: `‖Z‖²` for a standard Gaussian `Z` is chi-square with `card n` degrees
of freedom. -/
example (hm : 0 < Fintype.card n) :
    (stdGaussian (EuclideanSpace ℝ n)).map (fun w => quadForm 1 (fun i => w i)) =
      chiSquareMeasure (Fintype.card n) := by
  simpa using map_quadForm_multivariateGaussian (V := (1 : Matrix n n ℝ)) PosDef.one hm

/-- A line in the plane, for every positive definite covariance: codimension one gives the
chi-square law with one degree of freedom. -/
example {V : Matrix (Fin 2) (Fin 2) ℝ} (hV : V.PosDef) :
    (multivariateGaussian 0 V).map
        (gaussProjStat V (Submodule.span ℝ {EuclideanSpace.single 0 1})) =
      chiSquareMeasure 1 := by
  have h1 : finrank ℝ (Submodule.span ℝ
      {(EuclideanSpace.single 0 1 : EuclideanSpace ℝ (Fin 2))}) = 1 :=
    finrank_span_singleton (by simp)
  have h := map_gaussProjStat_multivariateGaussian hV
    (Submodule.span ℝ {EuclideanSpace.single 0 1}) (by simp [h1])
  simpa [h1] using h

end Examples

#print axioms MathlibExt.Biology.PopulationGenetics.Admixture.gaussProjStat_eq_iInf
#print axioms MathlibExt.Biology.PopulationGenetics.Admixture.map_gaussProjStat_multivariateGaussian
#print axioms MathlibExt.Biology.PopulationGenetics.Admixture.map_gaussProjStat_top
#print axioms MathlibExt.Biology.PopulationGenetics.Admixture.map_quadForm_multivariateGaussian

end MathlibExtTest.Biology.PopulationGenetics.Admixture.GaussianProjection
