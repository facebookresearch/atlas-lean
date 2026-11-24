/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.EtaleMonoidInverseImage
public import MathlibExt.AlgebraicGeometry.EtaleBaseChangeCoherence
public import Mathlib.CategoryTheory.Adjunction.Unique

/-!
# The native identity and composition maps of small-etale monoid inverse images

These maps are constructed from the actual sheaf direct-image maps, native
scheme base-change comparisons and uniqueness of left adjoints. Their unit
equations retain the actual adjunction-unit generators. They are completed
category/sheaf mathematics, rather than additional root-stack assumptions.

Source: Mathlib revision 56a005855ea17e0b0958f73ec801ae140b0a1679,
CategoryTheory/Sites/Continuous.lean (copyright Joël Riou; authors Joël Riou,
Andrew Yang) and CategoryTheory/Adjunction/Unique.lean (copyright Bhavik Mehta;
authors Bhavik Mehta, Thomas Read, Andrew Yang, Dagur Asgeirsson, Joël Riou),
both released under Apache License 2.0:
https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Sites/Continuous.lean
https://github.com/leanprover-community/mathlib4/blob/56a005855ea17e0b0958f73ec801ae140b0a1679/Mathlib/CategoryTheory/Adjunction/Unique.lean
This is a native adapter to those completed maps, as required for
Borne--Vistoli, https://arxiv.org/abs/1001.0466v2, Proposition 3.9/Remark 3.11.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.EtaleMonoidCoherence
open _root_.CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.EtaleMonoidInverseImage

universe u

abbrev monoidPushforward {X T : Scheme.{u}} (f : T ⟶ X) [HasInverseImage f] :=
  (etaleBaseChange f).sheafPushforwardContinuous CommMonCat.{u}
    X.smallEtaleTopology T.smallEtaleTopology

/-- The direct-image identity is the native site identity comparison. -/
def pushforwardIdentity (X : Scheme.{u}) [HasInverseImage (𝟙 X)] :
    monoidPushforward (𝟙 X) ≅ 𝟭 (MonoidSheaf X) :=
  Functor.sheafPushforwardContinuousId' (EtaleBaseChangeCoherence.identity X)
    CommMonCat.{u} X.smallEtaleTopology

/-- The direct-image composition is the literal precomposition comparison. -/
def pushforwardComposition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasInverseImage f] [HasInverseImage g] [HasInverseImage (f ≫ g)] :
    monoidPushforward f ⋙ monoidPushforward g ≅ monoidPushforward (f ≫ g) :=
  Functor.sheafPushforwardContinuousComp' (EtaleBaseChangeCoherence.composition f g)
    CommMonCat.{u} Z.smallEtaleTopology Y.smallEtaleTopology X.smallEtaleTopology

/-- Transport the given native identity adjunction, without changing its left functor. -/
def identityAdjunction (X : Scheme.{u}) [HasInverseImage (𝟙 X)] :
    monoidPullback (𝟙 X) ⊣ 𝟭 (MonoidSheaf X) :=
  (adjunction (𝟙 X)).ofNatIsoRight (pushforwardIdentity X)

/-- The inverse-image identity is computed by uniqueness of the native adjoint. -/
def identity (X : Scheme.{u}) [HasInverseImage (𝟙 X)] :
    monoidPullback (𝟙 X) ≅ 𝟭 (MonoidSheaf X) :=
  Adjunction.leftAdjointUniq (identityAdjunction X) (Adjunction.id)

/-- Its actual generator equation is the native adjunction-unit equation. -/
theorem identity_unit (X : Scheme.{u}) [HasInverseImage (𝟙 X)] (A : MonoidSheaf X) :
    (identityAdjunction X).unit.app A ≫ (identity X).hom.app A = 𝟙 A := by
  exact Adjunction.unit_leftAdjointUniq_hom_app (identityAdjunction X) Adjunction.id A

/-- The composed adjunction uses the actual native direct-image comparison. -/
def compositionAdjunction {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasInverseImage f] [HasInverseImage g] [HasInverseImage (f ≫ g)] :
    monoidPullback g ⋙ monoidPullback f ⊣ monoidPushforward (f ≫ g) :=
  ((adjunction g).comp (adjunction f)).ofNatIsoRight (pushforwardComposition f g)

/-- The inverse-image composition is a completed native adjoint comparison. -/
def composition {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasInverseImage f] [HasInverseImage g] [HasInverseImage (f ≫ g)] :
    monoidPullback g ⋙ monoidPullback f ≅ monoidPullback (f ≫ g) :=
  Adjunction.leftAdjointUniq (compositionAdjunction f g) (adjunction (f ≫ g))

/-- The comparison is pinned on every native adjunction-unit generator. -/
theorem composition_unit {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    [HasInverseImage f] [HasInverseImage g] [HasInverseImage (f ≫ g)]
    (A : MonoidSheaf Z) :
    (compositionAdjunction f g).unit.app A ≫
      (monoidPushforward (f ≫ g)).map ((composition f g).hom.app A) =
        (adjunction (f ≫ g)).unit.app A := by
  exact Adjunction.unit_leftAdjointUniq_hom_app (compositionAdjunction f g)
    (adjunction (f ≫ g)) A

end MathlibExt.AlgebraicGeometry.EtaleMonoidCoherence
