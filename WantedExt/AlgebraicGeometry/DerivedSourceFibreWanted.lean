/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.DerivedSourceFibreFrames
public import MathlibExt.AlgebraicGeometry.DerivedArtinAtlasModels

/-!
# Source construction and nondegeneracy requests for actual isotropic fibres

Factories choose coupled source presentations. Boundary and residue
requests concern their already computed b, h, cone[-1] and exact NC
loop coefficients. The intersection nondegeneracy request assumes the
original ambient symplectic form and both actual source Lagrangian
maps; it concerns the new residue Theta on the derived intersection.

Source: PTVV arXiv:1111.3209v4, Definitions 2.7--2.8 and Theorem 2.9.
These are direct Batteries ProofWanted entries, with provider proofs
separate from the objects and maps needed by paper-specific tasks.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.DerivedSourceFibreWanted

open _root_.CategoryTheory _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedEtaleStackModels
open MathlibExt.AlgebraicGeometry.DerivedArtinAtlasModels
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
open MathlibExt.AlgebraicGeometry.DerivedSourceFibreFrames
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

/-- Choose actual cotangent/dual/exterior, corrected injective eta and source-compatible NC cochain models. -/
def_wanted native_cotangent_form_sources [IsNoetherianRing k] (X : DerivedStack Q)
    (geometric : IsDerivedArtin X) (lfp : IsLocallyOfFinitePresentationStack X) :
    CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC) X.functor

/-- Choose the coupled full native differential, pullback homotopy and actual relative cone[-1]. -/
def_wanted native_relative_source_frame [IsNoetherianRing k] (X Y : DerivedStack Q)
    (f : StackMap X Y) (gx : IsDerivedArtin X) (gy : IsDerivedArtin Y)
    (lx : IsLocallyOfFinitePresentationStack X) (ly : IsLocallyOfFinitePresentationStack Y) :
    RelativeSourceFrame (U := U) (R := R) (L := L) (D := D) (NC := NC) f

/-- Prove the isotropic boundary of the literal source NC/DK coefficient and computed correction. -/
def_wanted native_isotropic_boundary {X Y : Prestack k} {f : X ⟶ Y}
    (F : RelativeSourceFrame (U := U) (R := R) (L := L) (D := D) (NC := NC) f)
    (n : ℤ) (ω : SourceClosedForm F.target n)
    (h : IsotropicPath F.domain.forms n
      ((closedPullback f F.target.forms F.domain.forms n).app (op ⦋0⦌) ω)) :
    IsotropicBoundaryWitness F.pullback n ω h

/-- Choose one compatible NC/cotangent source for the entire actual derived-fibre diagram. -/
def_wanted native_fibre_source_frame [IsNoetherianRing k] (X Y T : DerivedStack Q)
    (P : NaturalPathModel T) (f : StackMap X T) (g : StackMap Y T)
    (Z : FibreStackModel P f g) (n : ℤ)
    (gx : IsDerivedArtin X) (gy : IsDerivedArtin Y) (gt : IsDerivedArtin T)
    (lx : IsLocallyOfFinitePresentationStack X) (ly : IsLocallyOfFinitePresentationStack Y)
    (lt : IsLocallyOfFinitePresentationStack T) :
    FibreSourceFrame (U := U) (R := R) (L := L) (D := D) (NC := NC) Z n

/-- Realize the fixed entire cochain-homotopy coefficient by its native DK edge. -/
def_wanted native_linear_closing_path {A B : GlobalComplex k} (a b : A ⟶ B)
    (h : CochainComplex.HomComplex.Cochain A B (-1))
    (dh : CochainComplex.HomComplex.δ (-1) 0 h =
      CochainComplex.HomComplex.Cochain.ofHom b - CochainComplex.HomComplex.Cochain.ofHom a)
    (ω : ((realize k).obj A) _⦋0⦌) : LinearPath a b h dh ω

/-- Realize the exact closed NC cochain h+u-j-s0(left), with the native form degree n-1. -/
def_wanted native_residue_closed_vertex {X : Prestack k} {F : GlobalNCModel D 2 NC X}
    {n : ℤ} (P : ResiduePaths F n) : ResidueClosedFormSource P

/-- PTVV nondegeneracy concerns the same computed residue Theta and actual source Lagrangian maps. -/
theorem_wanted native_intersection_residue_nondegenerate [IsNoetherianRing k]
    {X Y T : DerivedStack Q} {P : NaturalPathModel T} {f : StackMap X T} {g : StackMap Y T}
    {Z : FibreStackModel P f g} {n : ℤ}
    (F : FibreSourceFrame (U := U) (R := R) (L := L) (D := D) (NC := NC) Z n)
    (gx : IsDerivedArtin X) (gy : IsDerivedArtin Y) (gt : IsDerivedArtin T)
    (lx : IsLocallyOfFinitePresentationStack X) (ly : IsLocallyOfFinitePresentationStack Y)
    (lt : IsLocallyOfFinitePresentationStack T)
    (ω : SourceClosedForm F.ambient n) (symplectic : IsSourceSymplectic F.ambient n ω)
    (J : LinearPath F.path.firstEndpoint F.path.secondEndpoint F.path.homotopy F.path.homotopy_d ω)
    (h : IsotropicPath F.first.forms n
      ((closedPullback f F.ambient.forms F.first.forms n).app (op ⦋0⦌) ω))
    (j : IsotropicPath F.second.forms n
      ((closedPullback g F.ambient.forms F.second.forms n).app (op ⦋0⦌) ω))
    (wh : IsotropicBoundaryWitness F.firstPullback n ω h)
    (wj : IsotropicBoundaryWitness F.secondPullback n ω j)
    (leftLagrangian : IsSourceLagrangian F.firstPullback F.firstRelative n ω h wh)
    (rightLagrangian : IsSourceLagrangian F.secondPullback F.secondRelative n ω j wj)
    (V : ResidueClosedFormSource (sourceFibreResiduePaths F ω J h j)) :
    IsSourceSymplectic F.intersection (n - 1) V.vertex

end WantedExt.AlgebraicGeometry.DerivedSourceFibreWanted
