/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedSourceResidueForms

/-!
# Coupled source frames for isotropic maps and derived intersections

The relative and fibre frames share the same actual NC, cotangent,
pullback, dual-pair and represented cone[-1] models. Both Lagrangian
tests use their computed relative Theta. The residue is the actual
universal fibre path and exact normalized h+u-j-s0(left) coefficient.
No independent b, h, residue, tangent or Theta endpoint is supplied.

Source: PTVV arXiv:1111.3209v4, Definitions 2.7--2.8, Theorem 2.9
and its proof, pp.39--40. Native source and license notices remain.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedSourceFibreFrames

open _root_.CategoryTheory
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
open MathlibExt.AlgebraicGeometry.DerivedStackFibreModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.AlgebraicGeometry.DerivedCotangentFormSources
open MathlibExt.AlgebraicGeometry.DerivedSourceRelativeIsotropicMaps
open MathlibExt.AlgebraicGeometry.DerivedRelativeTangentModels
open MathlibExt.AlgebraicGeometry.DerivedLinearClosingPaths
open MathlibExt.AlgebraicGeometry.DerivedFibreClosingPaths
open MathlibExt.AlgebraicGeometry.DerivedSourceResidueForms
open MathlibExt.AlgebraicGeometry.DerivedIsotropicResidues
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k] [Algebra ℚ k]
    {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {NC : NegativeCyclicDiagram D.functor (2 : ℤ)} {N : ShuffleAlgebraFunctor k}
    {S : AffineScalarSystem N} {M : AffineModuleFibration N S} {U : RegularUnitSystem M}
    {R : RawModuleRealization M} {L : CochainLiftModel k}

/-- Relative source choices are made together, before an isotropic path is selected. -/
structure RelativeSourceFrame {X Y : Prestack k} (f : X ⟶ Y) where
  domain : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC) X
  target : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC) Y
  geometry : RelativeGeometry domain target f
  pullback : ContractionPullbackHomotopy geometry
  relative : RelativeTangent (tangentArrow geometry) (tangentArrow_closed geometry)

/-- Isotropy retains the actual path and the boundary of its computed native h. -/
structure SourceIsotropicStructure {X Y : Prestack k} {f : X ⟶ Y}
    (F : RelativeSourceFrame (U := U) (R := R) (L := L) (D := D) (NC := NC) f)
    (n : ℤ) (ω : SourceClosedForm F.target n) where
  path : IsotropicPath F.domain.forms n
    ((closedPullback f F.target.forms F.domain.forms n).app (Opposite.op ⦋0⦌) ω)
  boundary : IsotropicBoundaryWitness F.pullback n ω path

/-- Lagrangian nondegeneracy is tested on i*h-c*b on that same actual cone[-1]. -/
structure SourceLagrangianStructure {X Y : Prestack k} {f : X ⟶ Y}
    (F : RelativeSourceFrame (U := U) (R := R) (L := L) (D := D) (NC := NC) f)
    (n : ℤ) (ω : SourceClosedForm F.target n) where
  isotropic : SourceIsotropicStructure F n ω
  nondegenerate : IsSourceLagrangian F.pullback F.relative n ω isotropic.path isotropic.boundary

/-- The fibre frame retains one source NC/cotangent presentation for the full native fibre diagram. -/
structure FibreSourceFrame {X Y T : DerivedStack Q} {P : NaturalPathModel T}
    {f : StackMap X T} {g : StackMap Y T} (Z : FibreStackModel P f g) (n : ℤ) where
  ambient : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC) T.functor
  first : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC) X.functor
  second : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC) Y.functor
  intersection : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC) Z.stack.functor
  firstGeometry : RelativeGeometry first ambient f
  firstPullback : ContractionPullbackHomotopy firstGeometry
  firstRelative : RelativeTangent (tangentArrow firstGeometry) (tangentArrow_closed firstGeometry)
  secondGeometry : RelativeGeometry second ambient g
  secondPullback : ContractionPullbackHomotopy secondGeometry
  secondRelative : RelativeTangent (tangentArrow secondGeometry) (tangentArrow_closed secondGeometry)
  firstProjection : RelativeGeometry intersection first (DerivedStackFibreModels.first Z)
  secondProjection : RelativeGeometry intersection second (DerivedStackFibreModels.second Z)
  pathForms : GlobalNCModel D 2 NC P.P
  path : FibreNCPathModel Z ambient.forms first.forms second.forms pathForms intersection.forms n

/-- The residue paths use the same source models and the actual universal fibre homotopy. -/
def sourceFibreResiduePaths {X Y T : DerivedStack Q} {P : NaturalPathModel T}
    {f : StackMap X T} {g : StackMap Y T} {Z : FibreStackModel P f g} {n : ℤ}
    (F : FibreSourceFrame (U := U) (R := R) (L := L) (D := D) (NC := NC) Z n)
    (ω : SourceClosedForm F.ambient n)
    (J : LinearPath F.path.firstEndpoint F.path.secondEndpoint F.path.homotopy F.path.homotopy_d ω)
    (h : IsotropicPath F.first.forms n
      ((closedPullback f F.ambient.forms F.first.forms n).app (Opposite.op ⦋0⦌) ω))
    (j : IsotropicPath F.second.forms n
      ((closedPullback g F.ambient.forms F.second.forms n).app (Opposite.op ⦋0⦌) ω)) :=
  derivedResiduePaths F.path ω J h j

end MathlibExt.AlgebraicGeometry.DerivedSourceFibreFrames
