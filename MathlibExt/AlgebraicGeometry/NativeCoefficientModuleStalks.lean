/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Stalk

/-!
# Native commutative coefficient stalk module specialization

This is the original native module structure on the actual filtered
stalk colimit. Keeping the coefficient presheaf and module abstract
avoids expanding a whole local-filtration/cokernel diagram during instance
resolution. Source: Mathlib56a005 ModuleCat/Stalk, Andrew Yang, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeCoefficientModuleStalks

open _root_.CategoryTheory

variable (X : TopCat.{0}) (R : TopCat.Presheaf CommRingCat.{0} X)
  (F : PresheafOfModules.{0} (R ⋙ forget₂ CommRingCat.{0} RingCat.{0})) (x : X)

@[instance_reducible] def actualStalkModule : Module ↑(TopCat.Presheaf.stalk R x)
    ↑(TopCat.Presheaf.stalk F.presheaf x) := inferInstance

end MathlibExt.AlgebraicGeometry.NativeCoefficientModuleStalks
