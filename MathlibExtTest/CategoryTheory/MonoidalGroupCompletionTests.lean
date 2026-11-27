/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.CategoryTheory.Monoidal.GroupCompletion
public import MathlibExt.Algebra.Category.FGProjectiveCat.Basic

/-! # Tests for additive S⁻¹S component invariants -/

@[expose] public section

noncomputable section

open CategoryTheory Limits ZeroObject Algebra

universe u

namespace CategoryTheory.SInverseSGroupCompletionTests

variable {R : Type u} [Ring R]

example (X : SInverseS.Pair (FGProjectiveCat.{u} R)) :
    GrothendieckAddGroup (Skeleton (FGProjectiveCat.{u} R)) :=
  X.difference

example :
    SInverseS.Pair (FGProjectiveCat.{u} R) ⥤
      Discrete
        (GrothendieckAddGroup (Skeleton (FGProjectiveCat.{u} R))) :=
  SInverseS.differenceFunctor

example :
    (SInverseS.differenceFunctor (C := FGProjectiveCat.{u} R)).EssSurj :=
  inferInstance

example {X Y : SInverseS.Pair (FGProjectiveCat.{u} R)} (f : X ⟶ Y) :
    X.difference = Y.difference :=
  SInverseS.Hom.difference_eq f

example {X Y : SInverseS.Pair (FGProjectiveCat.{u} R)} :
    Zigzag X Y ↔ X.difference = Y.difference :=
  SInverseS.Pair.zigzag_iff_difference_eq

example :
    ConnectedComponents (SInverseS.Pair (FGProjectiveCat.{u} R)) ≃
      GrothendieckAddGroup (Skeleton (FGProjectiveCat.{u} R)) :=
  SInverseS.connectedComponentsEquivGrothendieck

example : Type (u + 1) :=
  SInverseS.ZeroComponent (C := FGProjectiveCat.{u} R)

example :
    IsConnected
      (SInverseS.ZeroComponent (C := FGProjectiveCat.{u} R)) :=
  inferInstance

end CategoryTheory.SInverseSGroupCompletionTests
