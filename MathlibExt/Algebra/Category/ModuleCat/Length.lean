/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.RingTheory.Length

/-!
# Module length under surjective scalar restriction

Restriction along a surjective ring homomorphism preserves the lattice of
submodules and therefore the extended-natural module length.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

open CategoryTheory

namespace ModuleCat

universe u v w

/-- Actual restriction along a surjective ring map retains module length,
with independent ring and module universes. -/
theorem restrictScalars_length_eq
    {R : Type u} {S : Type v} [Ring R] [Ring S]
    (f : R →+* S) (hf : Function.Surjective f) (M : ModuleCat.{w} S) :
    Module.length R ((restrictScalars f).obj M) = Module.length S M := by
  let : RingHomSurjective f := ⟨hf⟩
  let g : (restrictScalars f).obj M →ₛₗ[f] M :=
    { toFun := fun x => x
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply WithBot.coe_injective
  rw [Module.coe_length, Module.coe_length]
  exact Order.krullDim_eq_of_orderIso
    (Submodule.orderIsoMapComapOfBijective g
      ⟨fun _ _ h => h, fun x => ⟨x, rfl⟩⟩)

/-- An actual restricted-module isomorphism preserves literal module length
under a ring equivalence. -/
theorem length_eq_of_restrictScalarsIso
    {R S : Type u} [Ring R] [Ring S]
    (eR : R ≃+* S) (M : ModuleCat.{v} R) (N : ModuleCat.{v} S)
    (e : M ≅ (ModuleCat.restrictScalars eR.toRingHom).obj N) :
    Module.length R M = Module.length S N :=
  e.toLinearEquiv.length_eq.trans
    (restrictScalars_length_eq eR.toRingHom eR.surjective N)

end ModuleCat
