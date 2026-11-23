/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowProjectiveZeroSpace

noncomputable section

open CategoryTheory AlgebraicKTheory.StableGL

universe u v

variable (R : Type u) [Ring R]

example :
    ContinuousMap.HomotopyEquiv
      (SInverseS.ComponentTranslation.zeroSpace (C := FGProjectiveCat.IdempotentModel R))
      (SInverseS.ComponentTranslation.zeroSpace (C := FGProjectiveCat.{max u v} R)) :=
  finiteFreeRowProjectiveZeroHomotopyEquiv.{u, v} R

example :
    Path ((finiteFreeRowProjectiveZeroHomotopyEquiv.{u, v} R).toFun
      (SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.IdempotentModel R)))
      (SInverseS.ComponentTranslation.zeroSpacePoint (C := FGProjectiveCat.{max u v} R)) :=
  finiteFreeRowProjectiveZeroUnitPath.{u, v} R

example : Nonempty (ContinuousMap.Homotopy
    ((finiteFreeRowProjectiveZeroHomotopyEquiv.{u, v} R).invFun.comp
      (finiteFreeRowProjectiveZeroHomotopyEquiv.{u, v} R).toFun)
    (ContinuousMap.id
      (SInverseS.ComponentTranslation.zeroSpace (C := FGProjectiveCat.IdempotentModel R)))) :=
  (finiteFreeRowProjectiveZeroHomotopyEquiv.{u, v} R).left_inv

example : Nonempty (ContinuousMap.Homotopy
    ((finiteFreeRowProjectiveZeroHomotopyEquiv.{u, v} R).toFun.comp
      (finiteFreeRowProjectiveZeroHomotopyEquiv.{u, v} R).invFun)
    (ContinuousMap.id
      (SInverseS.ComponentTranslation.zeroSpace (C := FGProjectiveCat.{max u v} R)))) :=
  (finiteFreeRowProjectiveZeroHomotopyEquiv.{u, v} R).right_inv

end
