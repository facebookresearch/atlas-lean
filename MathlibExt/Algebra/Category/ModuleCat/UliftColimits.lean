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

public import Mathlib.Algebra.Category.ModuleCat.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.Grp.Ulift

/-!
# Carrier-sized colimits of the original module universe lift

The actual module lift preserves the original scalar ring. Its underlying
additive-group functor is the original group lift. Carrier-sized colimit
preservation follows through the original additive forgetful functors.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace ModuleCat

universe z m r

variable (R : Type r) [Ring R]

/-- The underlying original additive groups of the module and group lifts agree. -/
def uliftFunctorForget₂AddCommGrpIso :
    uliftFunctor.{z, m} R ⋙ forget₂ (ModuleCat.{max m z} R) AddCommGrpCat.{max m z} ≅
      forget₂ (ModuleCat.{m} R) AddCommGrpCat.{m} ⋙ AddCommGrpCat.uliftFunctor.{z, m} :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro M N f
    apply AddCommGrpCat.hom_ext
    ext x
    rfl)

/-- Both underlying coefficient comparisons are the identity on the actual lifted carrier. -/
theorem uliftFunctorForget₂AddCommGrpIso_apply (M : ModuleCat.{m} R) (x : ULift.{z} M) :
    (uliftFunctorForget₂AddCommGrpIso.{z, m} R).hom.app M x = x ∧
      (uliftFunctorForget₂AddCommGrpIso.{z, m} R).inv.app M x = x := ⟨rfl, rfl⟩

/-- The original module lift preserves colimits in the source carrier universe. -/
noncomputable instance uliftFunctor_preservesCarrierColimits :
    PreservesColimitsOfSize.{m, m} (uliftFunctor.{z, m} R) := by
  let U := uliftFunctor.{z, m} R
  let A := forget₂ (ModuleCat.{m} R) AddCommGrpCat.{m}
  let B := forget₂ (ModuleCat.{max m z} R) AddCommGrpCat.{max m z}
  let : HasColimitsOfSize.{m, m} AddCommGrpCat.{m} :=
    AddCommGrpCat.hasColimitsOfSize.{m, m, m}
  let : PreservesColimitsOfSize.{m, m} A := by
    change PreservesColimitsOfSize.{m, m}
      (forget₂ (ModuleCat.{m} R) AddCommGrpCat.{m})
    exact ModuleCat.forget₂PreservesColimitsOfSize (R := R)
  let : HasColimitsOfSize.{m, m} AddCommGrpCat.{max m z} :=
    AddCommGrpCat.hasColimitsOfSize.{max m z, m, m}
  let : PreservesColimitsOfSize.{m, m} (A ⋙ AddCommGrpCat.uliftFunctor.{z, m}) :=
    inferInstance
  let : PreservesColimitsOfSize.{m, m} (U ⋙ B) :=
    preservesColimits_of_natIso (uliftFunctorForget₂AddCommGrpIso.{z, m} R).symm
  refine { preservesColimitsOfShape := ?_ }
  intro J instJ
  let : ReflectsColimitsOfShape J B := by
    change ReflectsColimitsOfShape J
      (forget₂ (ModuleCat.{max m z} R) AddCommGrpCat.{max m z})
    exact ModuleCat.reflectsColimitsOfShape (J := J) (R := R)
  exact preservesColimitsOfShape_of_reflects_of_preserves U B

end ModuleCat
