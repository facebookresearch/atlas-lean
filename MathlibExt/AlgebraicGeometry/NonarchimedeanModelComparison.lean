/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NonarchimedeanCartierModels
public import MathlibExt.AlgebraicGeometry.TestConfigurationWeightSeries
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Actual Gauss model evaluation and test-configuration compactification data

A model extension is a genuine centered valuation on the model function
field. Its value on every polynomial in the actual parameter is the
Gauss supremum of the actual base-coefficient values. Consequently neither
the field valuation nor the model value is a freely chosen metric score.
The divisor function is evaluated using actual Cartier local equations.

A compactification uses an actual open copy of the test configuration,
its actual line bundle, and a proper birational dominating model. The
affine polarization comparison is an actual module pullback isomorphism;
common refinements retain actual module pullback maps. The canonical
action-normalized extension over the complement of zero is a further
compactification bridge, not asserted by the affine compactification data.
Generic Cartier pullback, valuations and projective compactification are
completed public-source integration. The remaining Wanted boundary is
the normalized geometric Gauss/center realization on the fixed model.
Full metric completions and entropy inequalities are not asserted here.

Source: Boucksom--Hisamoto--Jonsson, arXiv1504.06568v3,
Definitions 6.1, 6.11 and the valuation description of model metrics.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NonarchimedeanModelComparison

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.AlgebraicGeometry
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open MathlibExt.AlgebraicGeometry.LogPairs
open MathlibExt.AlgebraicGeometry.PolarizedTestConfigurations
open MathlibExt.AlgebraicGeometry.NonarchimedeanCartierModels
open MathlibExt.AlgebraicGeometry.CenteredValuationSections
open MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries
open MathlibExt.AlgebraicGeometry.LineBundleTaskContracts

variable {k : Type} [Field k] {n : ℕ} {P : LogPair k n}
  {L : P.variety.X.left.Modules}

/-- The actual Cartier equations have exactly the fixed vertical-divisor coefficients. -/
structure ModelCartierEquations (M : VerticalModel P L) where
  atlas : CartierAtlas M.model
  normalized : ∀ p : PrimePoint M.model, atlas.coefficient p = M.divisor p

/-- Actual Gauss evaluation of the parameter polynomial in the model function field. -/
def parameterPolynomial (M : VerticalModel P L) (p : Polynomial (FunctionField P.variety)) :
    FunctionField M.model :=
  Polynomial.eval₂ (fieldMap M) (M.rationalParameter : FunctionField M.model) p

/-- Genuine valuation extension with the full coefficientwise Gauss normalization. -/
structure GaussModelExtension (M : VerticalModel P L) (v : CenteredValuation P.variety) where
  valuation : CenteredValuation M.model
  center : (baseProjection M).left valuation.center = v.center
  gauss : ∀ p : Polynomial (FunctionField P.variety),
    valuation.valuation (parameterPolynomial M p) =
      p.support.sup (fun i => v.valuation (p.coeff i) *
        Real.toNNReal (Real.exp (-(i : ℝ))))

/-- Literal valuation of the actual local Cartier equation at its actual center. -/
def metricValue {M : VerticalModel P L} (C : ModelCartierEquations M)
    {v : CenteredValuation P.variety} (E : GaussModelExtension M v) : ℝ :=
  order E.valuation
    (C.atlas.functions (Classical.choose (C.atlas.covers E.valuation.center))) / M.exponent

/-- A compactification of the normalized test configuration `T` dominated by the model `M`: a scheme
proper over the projective parameter line of `M`, with an open subscheme identified with the total
space of `T` compatibly with the maps to the line (through its affine chart), a line bundle whose
restriction to this open corresponds to the polarization of `T`, and a proper birational map to it
from the model of `M`, compatible with the maps to the parameter line, along which the line bundle
pulls back to `modelPolarization M`; the exponents of `M` and `T` agree. -/
structure CompatibleCompactification (T : NormalizedTestConfiguration k P.variety.X L)
    (M : VerticalModel P L) where
  compact : Over (Base k)
  projection : compact ⟶ M.parameter.line
  [proper : IsProper projection.left]
  affine : compact.left.Opens
  affineIso : Over.mk (affine.ι ≫ compact.hom) ≅ T.total
  affineOver : affineIso.hom ≫ T.projection ≫ M.parameter.affineChart =
    Over.homMk affine.ι ≫ projection
  polarization : compact.left.Modules
  line : IsLineBundle polarization
  affineLine : (Scheme.Modules.pullback affine.ι).obj polarization ≅
    (Scheme.Modules.pullback affineIso.hom.left).obj T.polarization
  modelMap : M.model.X ⟶ compact
  [modelProper : IsProper modelMap.left]
  modelBirational : MathlibExt.AlgebraicGeometry.BirationalResolution.IsBirationalMorphism
    modelMap.left
  modelOver : modelMap ≫ projection = M.map ≫ snd P.variety.X M.parameter.line
  exponent : M.exponent = T.exponent
  lineComparison : modelPolarization M ≅ (Scheme.Modules.pullback modelMap.left).obj polarization

/-- A refinement of the vertical model $M_1$ by the vertical model $M_2$: a proper birational
morphism $\mu$ from the model of $M_2$ to the model of $M_1$ and an isomorphism from the parameter
line of $M_2$ to that of $M_1$ compatible with their affine charts, such that $\mu$ commutes with
the maps of the models to the product of the base variety with the parameter line (through this
isomorphism on the second factor) and the exponents of $M_1$ and $M_2$ agree, together with an
isomorphism from the pullback along $\mu$ of the model polarization of $M_1$ to the model
polarization of $M_2$ (`modelPolarization`). -/
structure ModelRefinement (M₁ M₂ : VerticalModel P L) where
  map : M₂.model.X ⟶ M₁.model.X
  [proper : IsProper map.left]
  birational : MathlibExt.AlgebraicGeometry.BirationalResolution.IsBirationalMorphism map.left
  parameter : M₂.parameter.line ≅ M₁.parameter.line
  parameterChart : M₂.parameter.affineChart ≫ parameter.hom = M₁.parameter.affineChart
  over : map ≫ M₁.map = M₂.map ≫ (P.variety.X ◁ parameter.hom)
  exponent : M₂.exponent = M₁.exponent
  polarization : (Scheme.Modules.pullback map.left).obj (modelPolarization M₁) ≅
    modelPolarization M₂

end MathlibExt.AlgebraicGeometry.NonarchimedeanModelComparison
