/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Symmetric.SphereDayMonoid
public import MathlibExt.CategoryTheory.Monoidal.PreservesColimits

/-!
# The sphere Day monoid under the conventional closed-base hypotheses

Closedness supplies the left tensor adjoints. Symmetry gives the right
tensor preservation as well. Thus an arbitrary stabilizing object in a
closed symmetric monoidal category with small colimits gives the same
actual sphere Day monoid without separate preservation hypotheses.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe uV vV

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.MonoidalCategory

namespace CategoryTheory

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V] [SymmetricCategory V]
  [MonoidalClosed V] [HasColimitsOfSize.{0, 0} V]

/-- Closedness and small colimits suffice to construct the actual `S(T)` Day monoid. -/
def genericSphereDayMonoidOfClosed (T : V) :
    CommMon (DayFunctor Operad.SmallFinBijGroupoid V) :=
  genericSphereDayMonoid T

/-- The closed-base construction retains all the original ordered tensor-power values. -/
theorem genericSphereDayMonoidOfClosed_obj (T : V) (A : Operad.SmallFinBijGroupoid) :
    (genericSphereDayMonoidOfClosed T).X.functor.obj A =
      TensorPower.tensorPowObj T A.of.len := rfl

/-- The closed-base construction retains every original finite-bijection action. -/
theorem genericSphereDayMonoidOfClosed_map (T : V)
    {A B : Operad.SmallFinBijGroupoid} (f : A ⟶ B) :
    (genericSphereDayMonoidOfClosed T).X.functor.map f =
      (SymmetricTensorPower.permutationIso T
        (Operad.SmallFinBijGroupoid.smallEquivOfHom f)).hom := rfl

end CategoryTheory
