/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Basic.UnivLE

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicTopology

/-- Exact coproducts in `ModuleCat` at any indexing universe no larger than
the coefficient universe. This named construction avoids a global instance
overlap with Mathlib's equal-universe `AB4` instance. -/
public theorem moduleCatAB4OfSizeOfUnivLE
    (R : Type u) [CommRing R] [UnivLE.{w, u}] :
    AB4OfSize.{w} (ModuleCat.{u} R) := by
  let _ : HasFilteredColimitsOfSize.{w, w} (ModuleCat.{u} R) :=
    hasFilteredColimitsOfSize_of_univLE
  let _ : UnivLE.{u, u} := inferInstance
  let _ : AB5OfSize.{w, w} (ModuleCat.{u} R) :=
    AB5OfSize_of_univLE.{w, w, u, u} (ModuleCat.{u} R)
  let _ : HasFiniteBiproducts (ModuleCat.{u} R) :=
    Abelian.hasFiniteBiproducts
  exact AB4.of_AB5 (ModuleCat.{u} R)

end AlgebraicTopology

end
