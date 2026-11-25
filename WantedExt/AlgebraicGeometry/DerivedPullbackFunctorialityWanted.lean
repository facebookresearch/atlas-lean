/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.DerivedGlobalCotangentModels
public import MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
public import Mathlib.Algebra.Homology.Homotopy

/-!
# Well-definedness and functoriality of the global pullback maps

The global NC pullback, the global closed-form pullback and the maps of global derivation
spaces are limits of a lift through an injectively fibrant replacement. Lifts against levelwise
trivial cofibrations into a fibrant diagram exist but are not unique; they are unique up to
homotopy, and limits of fibrant diagrams preserve such homotopies. So the pullback maps do not
depend on the lift up to cochain homotopy (for complexes) or after inverting weak equivalences
(for spaces), and they are functorial in the same sense. These statements are requested here:
the strict maps are not functors.

For the identity and composition laws, note that the identity is a lift of the identity and a
composite of lifts is a lift of the composite, so they follow from the independence of the lift.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.DerivedPullbackFunctorialityWanted

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams
open MathlibExt.AlgebraicGeometry.DerivedFamilyDerivations
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedGlobalCotangentModels

universe u

variable {k : Type u} [CommRing k]

section NC

variable {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q} {p : ℕ}
  {NC : NegativeCyclicDiagram D.functor (p : ℤ)}

/-- Two lifts give cochain-homotopic global NC pullbacks. -/
theorem_wanted ncPullbackOf_homotopic {X Y : Prestack k} (f : X ⟶ Y)
    (GY : GlobalNCModel D p NC Y) (GX : GlobalNCModel D p NC X)
    {ℓ ℓ' : reindex f ⋙ GY.closed.diagram ⟶ GX.closed.diagram}
    (hℓ : IsNCPullbackLift f GY GX ℓ) (hℓ' : IsNCPullbackLift f GY GX ℓ') :
    Nonempty (Homotopy (ncPullbackOf f GY GX ℓ) (ncPullbackOf f GY GX ℓ'))

/-- Pullback along the identity is homotopic to the identity. -/
theorem_wanted ncPullback_id_homotopic {X : Prestack k} (G : GlobalNCModel D p NC X) :
    Nonempty (Homotopy (ncPullback (𝟙 X) G G) (𝟙 (ncComplex G)))

/-- Pullback along a composite is homotopic to the composite of the pullbacks. -/
theorem_wanted ncPullback_comp_homotopic {X Y Z : Prestack k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (GX : GlobalNCModel D p NC X) (GY : GlobalNCModel D p NC Y) (GZ : GlobalNCModel D p NC Z) :
    Nonempty (Homotopy (ncPullback (f ≫ g) GZ GX) (ncPullback g GZ GY ≫ ncPullback f GY GX))

end NC

section Forms

variable {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q} {p : ℕ} {n : ℤ}
  {NC : NegativeCyclicDiagram D.functor (p : ℤ)}

/-- Two lifts give the same global closed-form pullback after inverting weak equivalences. -/
theorem_wanted globalClosedPullbackOf_localized {X Y : Prestack k} (f : X ⟶ Y)
    (MY : GlobalFormModel D p n NC Y) (MX : GlobalFormModel D p n NC X)
    {ℓ ℓ' : reindex f ⋙ MY.closed.diagram ⟶ MX.closed.diagram}
    (hℓ : IsClosedPullbackLift f MY MX ℓ) (hℓ' : IsClosedPullbackLift f MY MX ℓ') :
    (spaceQ.{u}).map (globalClosedPullbackOf f MY MX ℓ) =
      (spaceQ.{u}).map (globalClosedPullbackOf f MY MX ℓ')

/-- After inverting weak equivalences, pullback along the identity is the identity. -/
theorem_wanted globalClosedPullback_localized_id {X : Prestack k}
    (M : GlobalFormModel D p n NC X) :
    (spaceQ.{u}).map (globalClosedPullback (𝟙 X) M M) = 𝟙 _

/-- After inverting weak equivalences, pullback along a composite is the composite of the
pullbacks. -/
theorem_wanted globalClosedPullback_localized_comp {X Y Z : Prestack k} (f : X ⟶ Y) (g : Y ⟶ Z)
    (MX : GlobalFormModel D p n NC X) (MY : GlobalFormModel D p n NC Y)
    (MZ : GlobalFormModel D p n NC Z) :
    (spaceQ.{u}).map (globalClosedPullback (f ≫ g) MZ MX) =
      (spaceQ.{u}).map (globalClosedPullback g MZ MY) ≫
        (spaceQ.{u}).map (globalClosedPullback f MY MX)

end Forms

section Derivations

variable {X : Prestack k} {B : DerivationBase X}

/-- Two lifts give the same map of global derivation spaces after inverting weak equivalences. -/
theorem_wanted derivationMapOf_localized {E F : SquareZeroFamily X} (f : SquareZeroFamilyMap E F)
    (h : liftMap f ≫ liftProjection X F = liftProjection X E)
    (DE : DerivationModel B E) (DF : DerivationModel B F)
    {ℓ ℓ' : DE.replacement.diagram ⟶ DF.replacement.diagram}
    (hℓ : IsDerivationLift f h DE DF ℓ) (hℓ' : IsDerivationLift f h DE DF ℓ') :
    (spaceQ.{u}).map (derivationMapOf ℓ) = (spaceQ.{u}).map (derivationMapOf ℓ')

/-- After inverting weak equivalences, the identity induces the identity of derivation spaces. -/
theorem_wanted derivationMap_localized_id {E : SquareZeroFamily X} (DE : DerivationModel B E)
    (h : liftMap (squareZeroFamilyId E) ≫ liftProjection X E = liftProjection X E) :
    (spaceQ.{u}).map (derivationMap (squareZeroFamilyId E) h DE DE) = 𝟙 _

/-- After inverting weak equivalences, the maps of derivation spaces compose. -/
theorem_wanted derivationMap_localized_comp {E F H : SquareZeroFamily X}
    (f : SquareZeroFamilyMap E F) (g : SquareZeroFamilyMap F H)
    (hf : liftMap f ≫ liftProjection X F = liftProjection X E)
    (hg : liftMap g ≫ liftProjection X H = liftProjection X F)
    (hfg : liftMap (squareZeroFamilyComp f g) ≫ liftProjection X H = liftProjection X E)
    (DE : DerivationModel B E) (DF : DerivationModel B F) (DH : DerivationModel B H) :
    (spaceQ.{u}).map (derivationMap (squareZeroFamilyComp f g) hfg DE DH) =
      (spaceQ.{u}).map (derivationMap f hf DE DF) ≫ (spaceQ.{u}).map (derivationMap g hg DF DH)

end Derivations

end WantedExt.AlgebraicGeometry.DerivedPullbackFunctorialityWanted
