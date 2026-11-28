/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Authors: @toskua, Codex -/
module

import MathlibExt.CategoryTheory.Monoidal.TensorPowers
import Mathlib.CategoryTheory.Monoidal.Types.Basic

/-!
# Ordered finite tensor powers in the cartesian category of types

Finite powers are left bracketed products beginning with PUnit. Splitting degrees one and
two keeps each factor in its original order. The identity lax monoidal functor concatenates
the ordered factors, including a degree-zero unit and unequal three-block degrees.
-/

noncomputable section

namespace MathlibExtTest.TensorPowers

open CategoryTheory MonoidalCategory
open CategoryTheory.MonoidalCategory.TensorPower

example (X : Type) : tensorPowObj X 2 = (𝟙_ (Type) ⊗ X) ⊗ X := rfl

example (X : Type) (x y : X) :
    (tensorPowAddIso X 1 1).hom ((PUnit.unit, x), y) =
      ((PUnit.unit, x), (PUnit.unit, y)) := rfl

example (X : Type) (x y z : X) :
    (tensorPowAddIso X 1 2).hom (((PUnit.unit, x), y), z) =
      ((PUnit.unit, x), ((PUnit.unit, y), z)) := rfl

example (X : Type) (x y z : X) :
    (tensorPowAddIso X 1 2).inv ((PUnit.unit, x), ((PUnit.unit, y), z)) =
      (((PUnit.unit, x), y), z) := rfl

example (X : Type) (x y z : X) :
    laxTensorPowerPairing (𝟭 (Type)) X 1 2
      ((PUnit.unit, x), ((PUnit.unit, y), z)) = (((PUnit.unit, x), y), z) := rfl

example (X : Type) (x y : X) :
    laxTensorPowerPairing (𝟭 (Type)) X 0 2 (PUnit.unit, ((PUnit.unit, x), y)) =
      ((PUnit.unit, x), y) := rfl

example (X : Type) (a b c d e f : X) :
    laxTensorPowerPairing (𝟭 (Type)) X 3 3
      (laxTensorPowerPairing (𝟭 (Type)) X 1 2
        ((PUnit.unit, a), ((PUnit.unit, b), c)), (((PUnit.unit, d), e), f)) =
      laxTensorPowerPairing (𝟭 (Type)) X 1 5
        ((PUnit.unit, a), laxTensorPowerPairing (𝟭 (Type)) X 2 3
          (((PUnit.unit, b), c), (((PUnit.unit, d), e), f))) := rfl

example (X : Type) :
    (laxTensorPowerUnit (𝟭 (Type)) X ▷ tensorPowObj X 2) ≫
        laxTensorPowerPairing (𝟭 (Type)) X 0 2 =
      (λ_ (tensorPowObj X 2)).hom ≫
        eqToHom (congrArg (fun n => tensorPowObj X n) (Nat.zero_add 2).symm) :=
  laxTensorPowerPairing_zero_left (𝟭 (Type)) X 2

example (X : Type) :
    (laxTensorPowerPairing (𝟭 (Type)) X 1 2 ▷ tensorPowObj X 3) ≫
        laxTensorPowerPairing (𝟭 (Type)) X (1 + 2) 3 ≫
        eqToHom (congrArg (fun n => tensorPowObj X n) (Nat.add_assoc 1 2 3)) =
      (α_ (tensorPowObj X 1) (tensorPowObj X 2) (tensorPowObj X 3)).hom ≫
        (tensorPowObj X 1 ◁ laxTensorPowerPairing (𝟭 (Type)) X 2 3) ≫
        laxTensorPowerPairing (𝟭 (Type)) X 1 (2 + 3) :=
  laxTensorPowerPairing_assoc (𝟭 (Type)) X 1 2 3

example (X : Type) :
    eqToHom (congrArg (tensorPowObj X) (Nat.add_assoc 1 2 3)) ≫
        (tensorPowAddIso X 1 (2 + 3)).hom ≫
        (tensorPowObj X 1 ◁ (tensorPowAddIso X 2 3).hom) =
      (tensorPowAddIso X (1 + 2) 3).hom ≫
        ((tensorPowAddIso X 1 2).hom ▷ tensorPowObj X 3) ≫
        (α_ (tensorPowObj X 1) (tensorPowObj X 2) (tensorPowObj X 3)).hom :=
  tensorPowAddIso_hom_assoc X 1 2 3

end MathlibExtTest.TensorPowers
