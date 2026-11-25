/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.CategoryTheory.Subobject.NoetherianObject
public import Mathlib.CategoryTheory.Subobject.MonoOver
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.Equivalence

@[expose] public section

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

namespace Equivalence

variable (e : C ≌ D) (X : C)

/-- The order isomorphism on subobject lattices induced by an equivalence of categories.

It is obtained by composing `MonoOver.congr` with `Subobject.lowerEquivalence` and then
`Equivalence.toOrderIso`. Using these existing equivalences avoids rebuilding subobject
transport by hand. -/
noncomputable def subobjectOrderIso :
    Subobject X ≃o Subobject (e.functor.obj X) :=
  (Subobject.lowerEquivalence (MonoOver.congr X e)).toOrderIso

/-- An equivalence of categories preserves and reflects the property of being a
Noetherian object.

The proof transports the monotone chain condition
`isNoetherianObject_iff_monotone_chain_condition` along the order isomorphism
`subobjectOrderIso e X`, which itself is built from `MonoOver.congr`,
`Subobject.lowerEquivalence`, and `Equivalence.toOrderIso`. -/
theorem isNoetherianObject_iff :
    IsNoetherianObject X ↔ IsNoetherianObject (e.functor.obj X) := by
  let iso := subobjectOrderIso e X
  rw [isNoetherianObject_iff_monotone_chain_condition,
      isNoetherianObject_iff_monotone_chain_condition]
  constructor
  · intro hX f
    let f' : ℕ →o Subobject X :=
      { toFun := fun n => iso.symm (f n)
        monotone' := fun _ _ hmn => iso.symm.le_iff_le.mpr (f.monotone hmn) }
    obtain ⟨n, hn⟩ := hX f'
    refine ⟨n, fun m hm => ?_⟩
    have h_eq : f' n = f' m := hn m hm
    have h_symm_eq : iso.symm (f n) = iso.symm (f m) := h_eq
    calc f n = iso (iso.symm (f n)) := (iso.apply_symm_apply (f n)).symm
      _ = iso (iso.symm (f m)) := by rw [h_symm_eq]
      _ = f m := iso.apply_symm_apply (f m)
  · intro hY f
    let f' : ℕ →o Subobject (e.functor.obj X) :=
      { toFun := fun n => iso (f n)
        monotone' := fun _ _ hmn => iso.le_iff_le.mpr (f.monotone hmn) }
    obtain ⟨n, hn⟩ := hY f'
    refine ⟨n, fun m hm => ?_⟩
    have h_eq : f' n = f' m := hn m hm
    have h_iso_eq : iso (f n) = iso (f m) := h_eq
    calc f n = iso.symm (iso (f n)) := (iso.symm_apply_apply (f n)).symm
      _ = iso.symm (iso (f m)) := by rw [h_iso_eq]
      _ = f m := iso.symm_apply_apply (f m)

/-- Forward direction: an equivalence sends Noetherian objects to Noetherian objects. -/
theorem isNoetherianObject [IsNoetherianObject X] :
    IsNoetherianObject (e.functor.obj X) :=
  (isNoetherianObject_iff e X).mp inferInstance

/-- Backward direction: if the image under an equivalence is Noetherian, the source is. -/
theorem isNoetherianObject_of_map [IsNoetherianObject (e.functor.obj X)] :
    IsNoetherianObject X :=
  (isNoetherianObject_iff e X).mpr inferInstance

end Equivalence

end CategoryTheory
