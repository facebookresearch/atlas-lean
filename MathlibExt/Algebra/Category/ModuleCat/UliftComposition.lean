/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Category.ModuleCat.UliftCoherence

/-!
# Coherence for successive native module universe lifts

Composition and its unit/associativity laws reuse the existing UliftCoherence
provider. The new comparison removes a lift contained in the actual module
carrier universe, using exactly the native module equivalence.
-/

@[expose] public section

noncomputable section

open CategoryTheory

universe r v w z

namespace ModuleCat

variable (R : Type r) [Ring R]

/-- A lift already contained in the actual carrier universe has the native identity comparison. -/
def uliftFunctorWithinIso :
    uliftFunctor.{w,max v w} R ≅ 𝟭 (ModuleCat.{max v w} R) :=
  NatIso.ofComponents (fun X => (ULift.moduleEquiv : ULift.{w} X ≃ₗ[R] X).toModuleIso) (by
    intro X Y f
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rcases x with ⟨x⟩
    rfl)

/-- The actual in-universe comparison has the original value. -/
theorem uliftFunctorWithinIso_hom_up (X : ModuleCat.{max v w} R) (x : X) :
    ((uliftFunctorWithinIso.{r,v,w} R).hom.app X).hom (ULift.up x) = x := rfl

/-- The native inverse carries the original value into its prescribed wrapper. -/
theorem uliftFunctorWithinIso_inv (X : ModuleCat.{max v w} R) (x : X) :
    ((uliftFunctorWithinIso.{r,v,w} R).inv.app X).hom x = ULift.up x := rfl

end ModuleCat
