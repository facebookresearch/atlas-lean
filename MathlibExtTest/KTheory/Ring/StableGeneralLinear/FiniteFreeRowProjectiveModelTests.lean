/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.KTheory.Ring.StableGeneralLinear.FiniteFreeRowProjectiveModel

noncomputable section

open CategoryTheory
open AlgebraicKTheory.StableGL

universe u v

variable (R : Type u) [Ring R]

example : SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R) ≌
    SInverseS.ZeroComponent (C := FGProjectiveCat.{u} R) :=
  finiteFreeRowProjectiveZeroEquivalence R

example :
    (finiteFreeRowProjectiveZeroEquivalence R).functor.obj
        (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R)) ≅
      SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{u} R) :=
  finiteFreeRowProjectiveZeroPointIso R

example :
    (finiteFreeRowProjectiveZeroEquivalence R).functor ⋙
        (SInverseS.zeroComponentProperty (C := FGProjectiveCat.{u} R)).ι ≅
      (SInverseS.zeroComponentProperty (C := FGProjectiveCat.IdempotentModel R)).ι ⋙
        (SInverseS.pairEquivalence (FGProjectiveCat.IdempotentModel.equivalence R)).functor :=
  finiteFreeRowProjectiveZeroInclusionIso R

example : SInverseS.ZeroComponent (C := FGProjectiveCat.IdempotentModel R) ≌
    SInverseS.ZeroComponent (C := FGProjectiveCat.{max u v} R) :=
  finiteFreeRowProjectiveUniverseZeroEquivalence.{u, v} R

example :
    (finiteFreeRowProjectiveUniverseZeroEquivalence.{u, v} R).functor.obj
        (SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.IdempotentModel R)) ≅
      SInverseS.zeroComponentBaseObject (C := FGProjectiveCat.{max u v} R) :=
  finiteFreeRowProjectiveUniverseZeroPointIso.{u, v} R

end
