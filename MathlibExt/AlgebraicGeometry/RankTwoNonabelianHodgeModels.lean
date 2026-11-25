/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RankTwoProjectiveMonodromy
public import MathlibExt.AlgebraicGeometry.BettiFunctoriality

/-!
# The source-normalized degree-one nonabelian Hodge map

The two spaces are the actual degree-one stable Higgs moduli and the
actual twisted invariant character scheme. Every Higgs point has an
actual pulled universal fibre, its evaluated algebraic frames, a central
harmonic metric and actual punctured parallel monodromy. The homeomorphism
is fixed pointwise by that monodromy, for every such choice. Existence of
the geometric realizations is included, so this condition is not vacuous.

The cohomology map is literally the native Betti cohomology pullback
of this normalized continuous map, including the canonical coefficient
unit and shift comparisons. No unrelated cohomology equivalence is supplied.

Source: de Cataldo--Hausel--Migliorini, arXiv:1004.1420v2, Theorem 1.2.4
and equation (1.2.9); Hitchin (1987), Sections 2,4,9.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RankTwoNonabelianHodgeModels

open _root_.CategoryTheory _root_.AlgebraicGeometry
open RankTwoHiggsCurveFamilies RankTwoHiggsModuliModels RankTwoHiggsAnalyticFrames
open RankTwoProjectiveMonodromy ComplexAnalytification KahlerClassGeometry
open ManifoldDifferentialForms CentralCurvatureHarmonicBundles GeneralLinearFrameSchemes
open RankTwoMatrixGroupModels TwistedRankTwoRepresentations TwistedCharacterQuotientModels
open BettiRealization
open scoped Manifold ContDiff

variable (C : ComplexScheme) [CoherentCurveLinearSeries.IsProperCurve C.hom]
    [SmoothOfRelativeDimension 1 C.hom]
  [IsIntegral C.left] [AnalyticRealization.AnalyticManifold C 1]
  [IsManifold 𝓘(ℝ, Coordinates 1) ∞ (space C)]
  [ExteriorTheory ℝ (Coordinates 1) (space C)]
  [FrameTheory 2] [GL2MatrixTheory] [Conjugation (CoherentCurveLinearSeries.genus C.hom)]
  (B : BaseChanges C) (M : ModuliModel C B)
  (P : CurveNormalization (space C)) (puncture : space C)
  (R : ReferenceLine C P puncture) (T : SurfaceMarking C puncture)

/-- The actual NAH homeomorphism is determined by all geometric harmonic monodromies. -/
structure NAHModel where
  point : ∀ p : ComplexPoints M.scheme.hom, HiggsPointModel C M p
  frames : ∀ p, AnalyticFrames C (point p).object
  harmonic : ∀ p, HarmonicSolution C P R (frames p)
  monodromy : ∀ p, SchemeMonodromy C P R T (frames p) (harmonic p)
  homeomorphism : space M.scheme ≃ₜ space (bettiScheme (CoherentCurveLinearSeries.genus C.hom))
  normalized : ∀ p, homeomorphism p = monodromyClass C P (monodromy p)
  choices : ∀ (p : ComplexPoints M.scheme.hom) (E : HiggsPointModel C M p)
      (V : AnalyticFrames C E.object) (A : HarmonicSolution C P R V)
      (N : SchemeMonodromy C P R T V A),
    homeomorphism p = monodromyClass C P N

def nahMap (N : NAHModel C B M P puncture R T) :
    space M.scheme ⟶ space (bettiScheme (CoherentCurveLinearSeries.genus C.hom)) :=
  TopCat.ofHom ⟨N.homeomorphism, N.homeomorphism.continuous⟩

def nahInverse (N : NAHModel C B M P puncture R T) :
    space (bettiScheme (CoherentCurveLinearSeries.genus C.hom)) ⟶ space M.scheme :=
  TopCat.ofHom ⟨N.homeomorphism.symm, N.homeomorphism.symm.continuous⟩

/-- The native coefficient- and shift-normalized pullback on actual Betti cohomology. -/
def cohomologyMap (N : NAHModel C B M P puncture R T) (d : ℤ) :
    Cohomology (space (bettiScheme (CoherentCurveLinearSeries.genus C.hom))) d →ₗ[ℚ]
      Cohomology (space M.scheme) d :=
  BettiFunctoriality.cohomologyPullback (nahMap C B M P puncture R T N) d

end MathlibExt.AlgebraicGeometry.RankTwoNonabelianHodgeModels
