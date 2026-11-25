/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Ulift

/-!
# Native scalar restriction and module universe lifting

The comparison uses the actual module actions and the identity on lifted
values. Both ring worlds and the original carrier world remain independent.
The direct imports are the native scalar-restriction and module-lift owners.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace ModuleCat

/-- Native scalar restriction commutes with native carrier lifting on the actual module actions. -/
def uliftRestrictionIso.{t, v, r, r'}
    {P : Type r} {Q : Type r'} [Ring P] [Ring Q] (f : P →+* Q) :
    ModuleCat.restrictScalars.{v} f ⋙ ModuleCat.uliftFunctor.{max v t, v} P ≅
      ModuleCat.uliftFunctor.{max v t, v} Q ⋙ ModuleCat.restrictScalars.{max v t} f := by
  refine NatIso.ofComponents (fun X => ?_) ?_
  · let C₀ := ((ModuleCat.restrictScalars.{v} f) ⋙
        ModuleCat.uliftFunctor.{max v t, v} P).obj X
    let C₁ := ((ModuleCat.uliftFunctor.{max v t, v} Q) ⋙
        ModuleCat.restrictScalars.{max v t} f).obj X
    change C₀ ≅ C₁
    refine
      { hom := (ModuleCat.homEquiv (M := C₀) (N := C₁)).symm
          { toFun := id
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        inv := (ModuleCat.homEquiv (M := C₁) (N := C₀)).symm
          { toFun := id
            map_add' := fun _ _ => rfl
            map_smul' := fun _ _ => rfl }
        hom_inv_id := ?_
        inv_hom_id := ?_ }
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl
    · apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl
  · intro X Y g
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

/-- Its forward comparison leaves the actual lifted value unchanged. -/
theorem uliftRestrictionIso_hom_apply.{t, v, r, r'}
    {P : Type r} {Q : Type r'} [Ring P] [Ring Q] (f : P →+* Q)
    (X : ModuleCat.{v} Q) (x : ULift.{max v t} X) :
    ((uliftRestrictionIso.{t, v, r, r'} f).hom.app X).hom x = x := rfl

/-- The inverse comparison has the same original carrier identity. -/
theorem uliftRestrictionIso_inv_apply.{t, v, r, r'}
    {P : Type r} {Q : Type r'} [Ring P] [Ring Q] (f : P →+* Q)
    (X : ModuleCat.{v} Q) (x : ULift.{max v t} X) :
    ((uliftRestrictionIso.{t, v, r, r'} f).inv.app X).hom x = x := rfl

end ModuleCat
