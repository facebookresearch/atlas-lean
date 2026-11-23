/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyExtension

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory
open scoped unitInterval

universe u v w

namespace MathlibExtTest.Topology.Category.TopCat.HomotopyExtension

section CrossUniverse

variable {A X : Type u} {Y : Type v} {Z : Type w}
variable [TopologicalSpace A] [TopologicalSpace X]
variable [TopologicalSpace Y] [TopologicalSpace Z]
variable {i : C(A, X)} {f : C(X, Y)} {H : C(unitInterval × A, Y)}
variable {h0 : ∀ a, H (0, a) = f (i a)}

example (d : _root_.Topology.HomotopyExtensionData i f H h0) :
    ContinuousMap.Homotopy f d.endpoint :=
  d.toHomotopy

example (d : _root_.Topology.HomotopyExtensionData i f H h0)
    (k : C(Y, Z)) :
    _root_.Topology.HomotopyExtensionData i (k.comp f) (k.comp H)
      (fun a => congrArg k (h0 a)) :=
  d.postcomp k

example :
    _root_.Topology.HasHomotopyExtensionProperty.{u, v}
      (ContinuousMap.id X) :=
  _root_.Topology.hasHomotopyExtensionProperty_id

end CrossUniverse

section TopCat

variable {W X Y Z : _root_.TopCat.{u}}

example : _root_.TopCat.IsHurewiczCofibration (𝟙 X) :=
  _root_.TopCat.hurewiczCofibrations_id X

example (i : W ⟶ X) (j : X ⟶ Y)
    (hi : _root_.TopCat.IsHurewiczCofibration i)
    (hj : _root_.TopCat.IsHurewiczCofibration j) :
    _root_.TopCat.IsHurewiczCofibration (i ≫ j) :=
  _root_.TopCat.hurewiczCofibrations_comp i j hi hj

example (e : W ≅ X) (f : X ⟶ Y)
    (hf : _root_.TopCat.IsHurewiczCofibration f) :
    _root_.TopCat.IsHurewiczCofibration (e.hom ≫ f) :=
  MorphismProperty.RespectsIso.precomp
    _root_.TopCat.hurewiczCofibrations e.hom f hf

example (e : Y ≅ Z) (f : X ⟶ Y)
    (hf : _root_.TopCat.IsHurewiczCofibration f) :
    _root_.TopCat.IsHurewiczCofibration (f ≫ e.hom) :=
  MorphismProperty.RespectsIso.postcomp
    _root_.TopCat.hurewiczCofibrations e.hom f hf

end TopCat

end MathlibExtTest.Topology.Category.TopCat.HomotopyExtension

end
