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
# Carrier-universe colimits under module lifting

For a ring R, module lifting M ↦ ULift M retains the scalar ring and commutes with forgetting
to additive abelian groups. The comparison has identity maps on the lifted carriers.

For modules with carrier universe m, the lift to max(m,z) preserves colimits indexed by
categories with object and morphism universes m. The ring universe r is independent of both
carrier and lift heights.
-/

public section

noncomputable section

open CategoryTheory Limits

namespace ModuleCat

universe z m r

variable (R : Type r) [Ring R]

/-- Module lifting commutes with forgetting to additive groups.

Lifting R-modules and then forgetting gives a functor naturally isomorphic to forgetting first
and lifting the additive groups, with identity components. -/
def uliftFunctorForget₂AddCommGrpIso :
    uliftFunctor.{z, m} R ⋙ forget₂ (ModuleCat.{max m z} R) AddCommGrpCat.{max m z} ≅
      forget₂ (ModuleCat.{m} R) AddCommGrpCat.{m} ⋙ AddCommGrpCat.uliftFunctor.{z, m} :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro M N f
    apply AddCommGrpCat.hom_ext
    ext x
    rfl)

/-- Elements under the module-to-additive-group lift comparison.

Both the forward and inverse components of the comparison send each lifted element to itself. -/
theorem uliftFunctorForget₂AddCommGrpIso_apply (M : ModuleCat.{m} R) (x : ULift.{z} M) :
    (uliftFunctorForget₂AddCommGrpIso.{z, m} R).hom.app M x = x ∧
      (uliftFunctorForget₂AddCommGrpIso.{z, m} R).inv.app M x = x := ⟨rfl, rfl⟩

/-- Preservation of carrier-size colimits by module lifting.

For source carrier universe m, the module lift preserves colimits of size (m,m), with target
carrier height max(m,z) and the same scalar ring R. -/
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
