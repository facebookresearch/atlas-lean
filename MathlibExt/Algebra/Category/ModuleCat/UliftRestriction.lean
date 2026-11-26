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
# Scalar restriction commutes with module carrier lifting

Let P,Q be rings, f : P → Q a ring homomorphism, and X a Q-module
in carrier world v. For an additional height t, put H = max(v,t).
Restricting X along f and then lifting its carrier gives the same
P-action as lifting X and then restricting:
p • up(x) = up(f(p) • x).

The identity on the lifted carrier defines a natural isomorphism
U_P ∘ Res_f ≅ Res_f ∘ U_Q from ModuleCat^v(Q) to ModuleCat^H(P).
Its forward and inverse components both preserve the lifted value.
The ring worlds of P,Q and the module and extra-height worlds are
independent; the rings may be noncommutative.
-/

@[expose] public section

noncomputable section

open CategoryTheory

namespace ModuleCat

/-- For rings P,Q, a ring homomorphism f : P → Q and
H = max(v,t), carrier lift and scalar restriction satisfy
U_P ∘ Res_f ≅ Res_f ∘ U_Q on Q-modules in world v.
The component at X is the identity on ULift^H X with P-action
p • up(x) = up(f(p) • x). All ring and carrier worlds are independent. -/
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

/-- For rings P,Q, f : P → Q, X ∈ ModuleCat^v(Q) and
x ∈ ULift^max(v,t) X, the forward component of
U_P ∘ Res_f ≅ Res_f ∘ U_Q at X sends x to itself.
The actions on both endpoints are induced by f. -/
theorem uliftRestrictionIso_hom_apply.{t, v, r, r'}
    {P : Type r} {Q : Type r'} [Ring P] [Ring Q] (f : P →+* Q)
    (X : ModuleCat.{v} Q) (x : ULift.{max v t} X) :
    ((uliftRestrictionIso.{t, v, r, r'} f).hom.app X).hom x = x := rfl

/-- For rings P,Q, f : P → Q, X ∈ ModuleCat^v(Q) and
x ∈ ULift^max(v,t) X, the inverse component of the scalar
restriction/carrier-lift comparison at X sends x to itself.
The ring worlds and the module and lift worlds remain independent. -/
theorem uliftRestrictionIso_inv_apply.{t, v, r, r'}
    {P : Type r} {Q : Type r'} [Ring P] [Ring Q] (f : P →+* Q)
    (X : ModuleCat.{v} Q) (x : ULift.{max v t} X) :
    ((uliftRestrictionIso.{t, v, r, r'} f).inv.app X).hom x = x := rfl

end ModuleCat
