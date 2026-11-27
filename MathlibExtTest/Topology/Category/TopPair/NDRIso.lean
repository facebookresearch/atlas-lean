/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.Topology.Category.TopPair.NDRIso

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Topology
open scoped unitInterval

universe u

namespace MathlibExtTest.Topology.Category.TopPair.NDRIso

variable {P Q : _root_.TopPair.{u}} (d : _root_.TopPair.NDRData P)
  (e : P ≅ Q)

example : _root_.TopPair.NDRData Q :=
  d.ofIso e

example (y : Q.fst) :
    (d.ofIso e).control y =
      d.control (_root_.TopPair.Hom.fst e.inv y) :=
  d.ofIso_control e y

example (x : P.fst) :
    (d.ofIso e).control (_root_.TopPair.Hom.fst e.hom x) =
      d.control x := by
  simp

example (y : Q.fst) :
    (d.ofIso e).endpoint y =
      _root_.TopPair.Hom.fst e.hom
        (d.endpoint (_root_.TopPair.Hom.fst e.inv y)) :=
  d.ofIso_endpoint e y

example (x : P.fst) :
    (d.ofIso e).endpoint (_root_.TopPair.Hom.fst e.hom x) =
      _root_.TopPair.Hom.fst e.hom (d.endpoint x) := by
  simp

example (t : unitInterval) (y : Q.fst) :
    (d.ofIso e).deformation (t, y) =
      _root_.TopPair.Hom.fst e.hom
        (d.deformation (t, _root_.TopPair.Hom.fst e.inv y)) :=
  d.ofIso_deformation e t y

example (t : unitInterval) (x : P.fst) :
    (d.ofIso e).deformation (t, _root_.TopPair.Hom.fst e.hom x) =
      _root_.TopPair.Hom.fst e.hom (d.deformation (t, x)) := by
  simp

example : d.ofIso (CategoryTheory.Iso.refl P) = d := by
  apply _root_.TopPair.NDRData.ext
  · intro x
    exact d.ofIso_control_hom (CategoryTheory.Iso.refl P) x
  · intro x
    exact d.ofIso_endpoint_hom (CategoryTheory.Iso.refl P) x
  · intro t x
    exact d.ofIso_deformation_hom (CategoryTheory.Iso.refl P) t x

end MathlibExtTest.Topology.Category.TopPair.NDRIso

end
