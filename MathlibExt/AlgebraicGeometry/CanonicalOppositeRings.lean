/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.NativeIndDifferentialContexts
public import MathlibExt.AlgebraicGeometry.NativeIndModuleInverseModels
public import MathlibExt.CategoryTheory.NativeOppositeBimoduleModels

/-!
# The canonical anti-identification of the opposite differential ring

The opposite differential ring is the sheafification of the opposite finite-order operator rings.
Its coefficient sheaf is identified with that of the differential ring by the map sending the
sheafified opposite of every local operator to that operator. Sections of a sheafification are
locally of this form, so this condition determines the map.

An opposite monoid structure between the β-images of the two rings is an anti-isomorphism; any two
differ by a ring automorphism of the differential ring, for instance `∂ ↦ ∂ + f` for a holomorphic
function `f`, which changes de Rham monodromy. The predicates below single out the β-image of the
canonical identification, and its images under inverse images, so that every right-module view,
duality and de Rham comparison uses the same anti-identification.

Source: D'Agnolo--Kashiwara, arXiv:1311.2374v2, §2.5 (right D-modules and the side-changing
operation).
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.CanonicalOppositeRings

open _root_.CategoryTheory _root_.Opposite TopologicalSpace
open CompactSupportIndSheaves NativeIndDifferentialContexts BetaDifferentialRingModels
open DifferentialOperatorSheaves DifferentialOperatorScalars RightDifferentialModules
open MathlibExt.CategoryTheory.NativeOppositeBimoduleModels

section Canonical

variable (M : Type) [TopologicalSpace M] (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} ℂ)
  [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
  [HasSheafify (Opens.grothendieckTopology M) (ModuleCat.{0} ℂ)]
  [CompactSheafSource ℂ (TopCat.of M)] [IndSpaceSource (TopCat.of M)]
  [DifferentialBetaSource M O] [OppositeDifferentialBetaSource M O]

/-- The canonical map from the coefficient sheaf of the opposite differential ring to that of the
differential ring: it sends the sheafified opposite of every finite-order operator to the
sheafified operator. -/
structure CanonicalOppositeCarrier where
  map : ringCoefficientSheaf (TopCat.of M) (rightDifferentialRing ℂ M O)
      (BetaRingSource.coefficient (X := TopCat.of M) (R := rightDifferentialRing ℂ M O)) ⟶
    ringCoefficientSheaf (TopCat.of M) (differentialRing ℂ M O)
      (BetaRingSource.coefficient (X := TopCat.of M) (R := differentialRing ℂ M O))
  unop_value : ∀ (U : Opens M) (P : finiteOperatorRing ℂ M O U),
    (map.hom.app (op U)).hom
        (((toSheafify (Opens.grothendieckTopology M) (rightOperatorPresheaf ℂ M O)).app
          (op U)).hom (MulOpposite.op P)) =
      ((toSheafify (Opens.grothendieckTopology M) (operatorPresheaf ℂ M O)).app (op U)).hom P

variable {M O}

/-- The β-image of the canonical carrier, as a map of the underlying ind-sheaves. -/
abbrev CanonicalOppositeCarrier.betaMap (c : CanonicalOppositeCarrier M O) :
    (betaRing (TopCat.of M) (rightDifferentialRing ℂ M O)).X ⟶
      (betaRing (TopCat.of M) (differentialRing ℂ M O)).X :=
  (IndSheafAlphaBetaModels.beta ℂ (TopCat.of M) (IndSpaceSource.alpha (X := TopCat.of M))
    (IndSpaceSource.beta (X := TopCat.of M))).map c.map

/-- An opposite monoid structure from the differential ring to its opposite is canonical when its
carrier is the β-image of the canonical carrier. -/
def IsCanonicalOpposite (c : CanonicalOppositeCarrier M O)
    (RO : OppositeMonoidSource (betaRing (TopCat.of M) (differentialRing ℂ M O))
      (betaRing (TopCat.of M) (rightDifferentialRing ℂ M O))) : Prop :=
  RO.carrier.hom = c.betaMap

/-- An opposite monoid structure from the opposite ring back to the differential ring is canonical
when its carrier is the inverse of the β-image of the canonical carrier. -/
def IsCanonicalBack (c : CanonicalOppositeCarrier M O)
    (RBack : OppositeMonoidSource (betaRing (TopCat.of M) (rightDifferentialRing ℂ M O))
      (betaRing (TopCat.of M) (differentialRing ℂ M O))) : Prop :=
  RBack.carrier.inv = c.betaMap

end Canonical

section InverseImage

variable {X Y : TopCat.{0}} (f : Y ⟶ X)
  [HasSheafify (Opens.grothendieckTopology X) (ModuleCat.{0} ℂ)]
  [HasSheafify (Opens.grothendieckTopology Y) (ModuleCat.{0} ℂ)]
  [CompactSheafSource ℂ X] [CompactSheafSource ℂ Y]
  [IndSpaceSource X] [IndSpaceSource Y]
  (I : NativeIndModuleInverseModels.InverseMonoidalSource f)

/-- An opposite monoid structure from the inverse image of an opposite ring back to the inverse
image of the ring has the inverse image of `g` as the inverse of its carrier. -/
def IsInverseImageBack {R Rop : Mon (IndSheaf ℂ X)} (g : Rop.X ⟶ R.X)
    (S : OppositeMonoidSource (NativeIndModuleInverseModels.inverseRing f I Rop)
      (NativeIndModuleInverseModels.inverseRing f I R)) : Prop :=
  S.carrier.inv = (NativeIndModuleInverseModels.originalInverse f I).map g

/-- An opposite monoid structure from the inverse image of a ring to the inverse image of its
opposite has the inverse image of `g` as its carrier. -/
def IsInverseImageOpposite {R Rop : Mon (IndSheaf ℂ X)} (g : Rop.X ⟶ R.X)
    (S : OppositeMonoidSource (NativeIndModuleInverseModels.inverseRing f I R)
      (NativeIndModuleInverseModels.inverseRing f I Rop)) : Prop :=
  S.carrier.hom = (NativeIndModuleInverseModels.originalInverse f I).map g

end InverseImage

end MathlibExt.AlgebraicGeometry.CanonicalOppositeRings
