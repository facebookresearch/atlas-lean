/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.SmallEtaleGeometry
public import Mathlib.CategoryTheory.Sites.Pullback

/-!
# Fixed small-etale inverse images for denominator families

The site functor is actual scheme-theoretic base change. The inverse-image
functor is the native left adjoint of its actual sheaf direct image, and
its generator map is the actual adjunction unit. Continuity/adjoint choices
are implementation inputs for the universe spelling of the small site,
not new algebraic-geometry conclusions or arbitrary pullback operations.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace MathlibExt.AlgebraicGeometry.EtaleMonoidInverseImage
open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
universe u

/-- The same native site operations as the general log-family layer. -/
abbrev etaleBaseChange {X T : Scheme.{u}} (f : T ⟶ X) :=
  SmallEtaleGeometry.etaleBaseChange f

abbrev HasInverseImage {X T : Scheme.{u}} (f : T ⟶ X) :=
  SmallEtaleGeometry.HasInverseImage f

abbrev MonoidSheaf (X : Scheme.{u}) := Sheaf X.smallEtaleTopology CommMonCat.{u}

abbrev monoidPullback {X T : Scheme.{u}} (f : T ⟶ X) [HasInverseImage f] :
    MonoidSheaf X ⥤ MonoidSheaf T :=
  (etaleBaseChange f).sheafPullback CommMonCat.{u}
    X.smallEtaleTopology T.smallEtaleTopology

abbrev adjunction {X T : Scheme.{u}} (f : T ⟶ X) [HasInverseImage f] :=
  (etaleBaseChange f).sheafAdjunctionContinuous CommMonCat.{u}
    X.smallEtaleTopology T.smallEtaleTopology

/-- The inverse-image generator is the actual adjunction-unit map. -/
def generator {X T : Scheme.{u}} (f : T ⟶ X) [HasInverseImage f]
    (A : MonoidSheaf X) (U : X.Etale) :
    A.obj.obj (op U) →* ((monoidPullback f).obj A).obj.obj
      (op ((etaleBaseChange f).obj U)) :=
  ((adjunction f).unit.app A).hom.app (op U) |>.hom

/-- The actual universal base-change projection. -/
abbrev projection {X T : Scheme.{u}} (f : T ⟶ X) (U : X.Etale) :=
  SmallEtaleGeometry.projection f U

end MathlibExt.AlgebraicGeometry.EtaleMonoidInverseImage
