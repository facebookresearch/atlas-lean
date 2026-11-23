/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarChangeOfCategory
public import MathlibExt.AlgebraicTopology.LocalCoefficient.NervePullbackBarIdentityComparison
public import MathlibExt.Algebra.Homology.ExactColimits
public import MathlibExt.Algebra.Homology.FirstQuadrantConvergence
public import MathlibExt.Algebra.Homology.VerticalHomologyComplex
public import Mathlib.AlgebraicTopology.DoldKan.HomotopyEquivalence
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.Algebra.Category.Grp.AB

/-!
# The coefficient-chain bar bicomplex

The existing coefficient bar is applied to a diagram of chain complexes.
The canonical target-change comparison, specialized to a homology functor,
identifies its vertical homology with the bar of the actual homology
coefficient diagram. Only discrete coproduct preservation is required.

This applies to the actual relative quotient chain diagram in the H-space
comparison. The spectral sequence and stable filtration are the existing
generic first-quadrant construction; no comparison, convergence, or edge
isomorphism witness is supplied.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.CategoryHomology
open scoped Simplicial

universe w vA uA vB uB uJ vJ

public section

namespace CategoryTheory.CategoryHomology

section ChangeCategory

variable {J : Type uJ} [Category.{vJ} J]
  {A : Type uA} [Category.{vA} A] [Preadditive A] [HasCoproducts.{max uJ vJ} A]
  {B : Type uB} [Category.{vB} B] [Preadditive B] [HasCoproducts.{max uJ vJ} B]
  (F : A ⥤ B) [F.Additive]
  [∀ I : Type (max uJ vJ), PreservesColimitsOfShape (Discrete I) F]
  (D : J ⥤ A)

/-- The coefficient-bar comparison reuses the existing identity-bar
and target-change isomorphisms. -/
def coefficientBarComplexChangeOfCategoryIso :
    ((F.mapHomologicalComplex (ComplexShape.down ℕ)).obj (coefficientBarComplex D)) ≅
      coefficientBarComplex (D ⋙ F) :=
  (F.mapHomologicalComplex (ComplexShape.down ℕ)).mapIso
      (nervePullbackCoefficientComplexIdIso D).symm ≪≫
    nervePullbackCoefficientComplexChangeOfCategoryIso F (𝟙 (CategoryTheory.nerve J)) D ≪≫
      nervePullbackCoefficientComplexIdIso (D ⋙ F)

end ChangeCategory

section ChainDiagram

variable {J : Type w} [Category.{0} J]
  (D : J ⥤ ChainComplex AddCommGrpCat.{w} ℕ)

private theorem homologyFunctor_preservesDiscrete (q : ℕ) (I : Type w) :
    PreservesColimitsOfShape (Discrete I)
      (HomologicalComplex.homologyFunctor AddCommGrpCat.{w} (ComplexShape.down ℕ) q) := by
  let L := colim (J := Discrete I) (C := AddCommGrpCat.{w})
  let : L.PreservesHomology :=
    Functor.preservesHomology_of_preservesMonos_and_cokernels L
  infer_instance

/-- The existing alternating coefficient bar, now with chain-valued
coefficients, is the actual first-quadrant bicomplex. -/
abbrev coefficientChainBicomplex :
    HomologicalComplex₂ AddCommGrpCat.{w} (ComplexShape.down ℕ) (ComplexShape.down ℕ) :=
  coefficientBarComplex D

/-- Vertical homology gives the actual coefficient bar of the chain
diagram's homology, using exact coproducts of abelian groups. -/
def coefficientChainVerticalHomologyIso (q : ℕ) :
    (coefficientChainBicomplex D).verticalHomologyComplex q ≅
      coefficientBarComplex
        (D ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{w} (ComplexShape.down ℕ) q) := by
  let H := HomologicalComplex.homologyFunctor AddCommGrpCat.{w} (ComplexShape.down ℕ) q
  letI : ∀ I : Type w, PreservesColimitsOfShape (Discrete I) H :=
    fun I => homologyFunctor_preservesDiscrete q I
  exact coefficientBarComplexChangeOfCategoryIso H D

/-- The spectral sequence is the existing signed-total first-quadrant
construction on this actual coefficient-chain bicomplex. -/
abbrev coefficientChainSpectralSequence :=
  HomologicalComplex₂.horizontalFirstQuadrantSpectralSequence (coefficientChainBicomplex D)

/-- The actual second page is category homology of the original chain
diagram's actual homology coefficients. -/
def coefficientChainSecondPageIso (p q : ℕ) :
    ((coefficientChainSpectralSequence D).page 2).X (p, q) ≅
      homologyWithCoefficients
        (D ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{w} (ComplexShape.down ℕ) q) p :=
  HomologicalComplex₂.horizontalSecondPageVerticalHorizontalHomologyIso
      (coefficientChainBicomplex D) p q ≪≫
    HomologicalComplex.homologyMapIso (coefficientChainVerticalHomologyIso D q) p ≪≫
      ((AlgebraicTopology.DoldKan.homotopyEquivNormalizedMooreComplexAlternatingFaceMapComplex
        (Y := coefficientBarSimplicial
          (D ⋙ HomologicalComplex.homologyFunctor AddCommGrpCat.{w}
              (ComplexShape.down ℕ) q))).toHomologyIso p).symm

end ChainDiagram

end CategoryTheory.CategoryHomology
