/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

import MathlibExt.CategoryTheory.Operad.FinBijSmallEquiv
import Batteries.Tactic.Lint

set_option autoImplicit false
noncomputable section
open CategoryTheory
open CategoryTheory.Operad CategoryTheory.Operad.SmallFinBijGroupoid

example (A : SmallFinBijGroupoid) :
    smallEquivOfHom (𝟙 A) = Equiv.refl (Fin A.of.len) := smallEquivOfHom_id A

example {A B D : SmallFinBijGroupoid} (f : A ⟶ B) (g : B ⟶ D) :
    smallEquivOfHom (f ≫ g) = (smallEquivOfHom f).trans (smallEquivOfHom g) :=
  smallEquivOfHom_comp f g

#print axioms CategoryTheory.Operad.SmallFinBijGroupoid.smallEquivOfHom
#print axioms CategoryTheory.Operad.SmallFinBijGroupoid.smallEquivOfHom_id
#print axioms CategoryTheory.Operad.SmallFinBijGroupoid.smallEquivOfHom_comp

#lint only unusedArguments in MathlibExt.CategoryTheory.Operad.FinBijSmallEquiv
