/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.CategoryTheory.Monoidal.SInverseSZeroComponentOrdinaryUnitTransport
import MathlibExt.Algebra.Category.FGProjectiveCat.IdempotentModel

noncomputable section

open CategoryTheory Limits ZeroObject

universe u

#check @CategoryTheory.SInverseS.ComponentTranslation.zeroSpace_fundamentalGroup_mul_comm
#print axioms CategoryTheory.SInverseS.ComponentTranslation.zeroSpace_fundamentalGroup_mul_comm

example {C : Type u} [Category.{u} C] [Preadditive C]
    [HasZeroObject C] [HasBinaryBiproducts C]
    (p q : FundamentalGroup
      (SInverseS.ComponentTranslation.zeroSpace (C := C))
      (SInverseS.ComponentTranslation.zeroSpacePoint (C := C))) : p * q = q * p :=
  SInverseS.ComponentTranslation.zeroSpace_fundamentalGroup_mul_comm (C := C) p q

example {R : Type u} [Ring R]
    (p q : FundamentalGroup
      (SInverseS.ComponentTranslation.zeroSpace (C := FGProjectiveCat.IdempotentModel R))
      (SInverseS.ComponentTranslation.zeroSpacePoint
        (C := FGProjectiveCat.IdempotentModel R))) : p * q = q * p :=
  SInverseS.ComponentTranslation.zeroSpace_fundamentalGroup_mul_comm
    (C := FGProjectiveCat.IdempotentModel R) p q

end
