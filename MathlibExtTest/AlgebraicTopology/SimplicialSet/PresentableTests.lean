/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado

import MathlibExt.AlgebraicTopology.SimplicialSet.Presentable

/-!
# Tests for local presentability of simplicial sets
-/

set_option autoImplicit false

open CategoryTheory

universe u

namespace MathlibExtTest.SSet.Presentable

#check SSet.isLocallyPresentable
#check @SSet.isLocallyPresentable.{u}
#check @SSet.isLocallyPresentable.{1}
#check @SSet.isLocallyPresentable.{0}

example : IsLocallyPresentable.{u} SSet.{u} :=
  SSet.isLocallyPresentable

example : IsLocallyPresentable.{1} SSet.{1} :=
  SSet.isLocallyPresentable

example : IsLocallyPresentable.{0} SSet.{0} :=
  SSet.isLocallyPresentable

/-- Pinned Mathlib also infers local presentability through its presheaf
instance for essentially small index categories; the named theorem is the
same proposition. -/
example : (inferInstance : IsLocallyPresentable.{u} SSet.{u}) =
    SSet.isLocallyPresentable :=
  rfl

example : IsLocallyPresentable.{u} SSet.{u} := by
  let _ : IsLocallyPresentable.{u} SSet.{u} :=
    SSet.isLocallyPresentable
  infer_instance

example (X : SSet.{u}) : IsPresentable.{u} X := by
  let _ : IsLocallyPresentable.{u} SSet.{u} :=
    SSet.isLocallyPresentable
  infer_instance

#guard_msgs (error, substring := true) in
#check SSet.instIsLocallyPresentable

#guard_msgs (error, substring := true) in
#check SSet.combinatorialModelCategory

#guard_msgs (error, substring := true) in
#check SSet.monoidalModelCategory

#guard_msgs (error, substring := true) in
#check SSet.monoidAxiom

#guard_msgs (error, substring := true) in
#check PointedSSet.isLocallyPresentable

#guard_msgs (error, substring := true) in
#check SSet.localization

#guard_msgs (error, substring := true) in
#check SSet.spectra

#print axioms SSet.isLocallyPresentable

end MathlibExtTest.SSet.Presentable
