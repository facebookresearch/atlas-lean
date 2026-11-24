/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.ThetaQuotientOpenSources
public import MathlibExt.AlgebraicGeometry.ThetaSchemeParameters
public import Batteries.Util.ProofWanted
public import WantedExt.AlgebraicGeometry.ThetaQuotientSourcesWanted

/-!
# Native filtration and elementary-modification integration requests

These constructors assemble the existing affine Hopf group, quotient
torsor categories and whole mapping groupoids into their normalized
native source models. The actual group laws, coactions, all source
coordinates, all reindexing arrows and their identity/composition
cells are fixed by the public result types.

No Θ-reductivity, S-completeness or good-moduli-space theorem is assumed
as a source constructor. Those lifting predicates remain independent.

The standard contracting action on `𝔸¹` and the weight `(1, -1)` action on
`st = π` that these charts take as instances are themselves requested, over
every base ring, as `contractingAction` and `oppositeWeightAction` in the
imported `WantedExt.AlgebraicGeometry.ThetaQuotientSourcesWanted`.

The open source of an arbitrary open `V` is the full substack of points whose
whole orbit lands in `V`; it is an open substack when `V` is `G`-invariant, as
for the Θ and ST punctures.

References: Alper–Halpern-Leistner–Heinloth, arXiv:1812.01128v5,
§2.3 and §3.5. Generic fppf torsor/quotient integration is completed
AxiomMath/Stacks source at c496df0d9beea9deaeabcea8492605f9a0a2313b.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.ThetaNativeSourcesWanted

open MathlibExt.AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.GeneralStackGeometry
open GroupTorsorGeometry ThetaQuotientSources ThetaTraitCharts
open ThetaQuotientOpenSources StackSourceFiltrations

def_wanted nativeAffineQuotientSource
    {R : Type} [CommRing R] (G W : Over (Spec (.of R))) [GrpObj G] [ModObj G W]
    [IsAffine G.left] [Flat G.hom] [LocallyOfFinitePresentation G.hom] :
    QuotientSource R (G := G) (W := W)

def_wanted nativeThetaChart
    (R : Type) [CommRing R] [A : ContractingAction R]
    (Q : @QuotientSource R _ (multiplicativeGroup R) (affineLine R) _ A.action)
    (a : R) : ThetaChart R Q a

def_wanted nativeSurfaceChart
    {R : Type} [CommRing R] {π : R} [A : OppositeWeightAction R π]
    (Q : @QuotientSource R _ (multiplicativeGroup R) (nodeSurface R π) _ A.action)
    (first : Bool) : SurfaceChart Q first

def_wanted nativeSurfaceTraitSource
    {R : Type} [CommRing R] (π : R) [OppositeWeightAction R π]
    (K : Over (Spec (.of R))) (h : IsUnit (coordinate K.hom π)) :
    SurfaceTraitSource π K

def_wanted nativeQuotientOpenSource
    {R : Type} [CommRing R] {G W : Over (Spec (.of R))} [GrpObj G] [ModObj G W]
    (Q : QuotientSource R (G := G) (W := W)) (V : W.left.Opens) : OpenSource Q V

def_wanted nativeStackSourceParameterReindex
    {S : Scheme} (Y X : RelativeStack S) {T V : Over S} (f : V ⟶ T) :
    ParameterReindex Y X f

theorem_wanted nativeRelativeStackRestriction
    {S V : Scheme} (X : RelativeStack S) (b : V ⟶ S) :
    (ThetaSchemeParameters.restriction X b).IsStack (Scheme.fppfTopology.over V)

end WantedExt.AlgebraicGeometry.ThetaNativeSourcesWanted
