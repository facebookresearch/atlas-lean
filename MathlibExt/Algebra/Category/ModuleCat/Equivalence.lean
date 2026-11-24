/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Category.ModuleCat.Subobject
public import MathlibExt.CategoryTheory.Noetherian.Equivalence
public import Mathlib.RingTheory.Finiteness.Basic
public import MathlibExt.Order.CompactlyGenerated.Equivalence

@[expose] public section

open CategoryTheory

universe v₁ v₂ uR uS

namespace ModuleCat

variable {R : Type uR} [Ring R] {S : Type uS} [Ring S]
variable (e : ModuleCat.{v₁} R ≌ ModuleCat.{v₂} S) (M : ModuleCat.{v₁} R)

/-- The order isomorphism between submodule lattices induced by an equivalence
of module categories.

It is obtained by composing `ModuleCat.subobjectModule`,
`Equivalence.subobjectOrderIso`, and the target `subobjectModule`. -/
noncomputable def submoduleOrderIso :
    Submodule R M ≃o Submodule S (e.functor.obj M) :=
  (subobjectModule M).symm.trans
    ((Equivalence.subobjectOrderIso e M).trans (subobjectModule (e.functor.obj M)))

private theorem submoduleOrderIso_map_top :
    submoduleOrderIso e M (⊤ : Submodule R M) = ⊤ := by
  have h_le_top : (submoduleOrderIso e M) (⊤ : Submodule R M) ≤ ⊤ := le_top
  have h_top_le : (⊤ : Submodule S (e.functor.obj M)) ≤ (submoduleOrderIso e M) ⊤ := by
    have h_symm_le : (submoduleOrderIso e M).symm (⊤ : Submodule S (e.functor.obj M)) ≤ ⊤ :=
      le_top
    have h_mono := (submoduleOrderIso e M).monotone h_symm_le
    -- `e (e.symm ⊤) = ⊤`
    have h_apply : (submoduleOrderIso e M) ((submoduleOrderIso e M).symm ⊤) = ⊤ := by
      simp
    calc (⊤ : Submodule S (e.functor.obj M))
        = (submoduleOrderIso e M) ((submoduleOrderIso e M).symm ⊤) := h_apply.symm
      _ ≤ (submoduleOrderIso e M) (⊤ : Submodule R M) := h_mono
  exact le_antisymm h_le_top h_top_le

/-- Finite generation is preserved and reflected by any equivalence of module
categories, with no additional hypotheses.

The proof uses `Module.Finite.iff_fg`, `Submodule.fg_iff_compact`, and
`OrderIso.isCompactElement_iff`, together with the fact that an order
isomorphism sends `⊤` to `⊤`. -/
theorem finite_iff :
    Module.Finite R M ↔ Module.Finite S (e.functor.obj M) := by
  let iso := submoduleOrderIso e M
  have h_top : iso (⊤ : Submodule R M) = ⊤ := submoduleOrderIso_map_top e M
  -- bridge `Module.Finite` ↔ `IsCompactElement ⊤`
  have hf_R : Module.Finite R M ↔ IsCompactElement (⊤ : Submodule R M) := by
    rw [Module.finite_def, Submodule.fg_iff_compact]
  have hf_S : Module.Finite S (e.functor.obj M) ↔
      IsCompactElement (⊤ : Submodule S (e.functor.obj M)) := by
    rw [Module.finite_def, Submodule.fg_iff_compact]
  calc Module.Finite R M
      ↔ IsCompactElement (⊤ : Submodule R M) := hf_R
    _ ↔ IsCompactElement (iso (⊤ : Submodule R M)) := by
        rw [OrderIso.isCompactElement_iff]
    _ ↔ IsCompactElement (⊤ : Submodule S (e.functor.obj M)) := by
        rw [h_top]
    _ ↔ Module.Finite S (e.functor.obj M) := hf_S.symm

/-- Forward direction of `finite_iff`. -/
theorem finite_of_finite [h : Module.Finite R M] :
    Module.Finite S (e.functor.obj M) :=
  (finite_iff e M).mp h

/-- Backward direction of `finite_iff`. -/
theorem finite_of_map_finite [h : Module.Finite S (e.functor.obj M)] :
    Module.Finite R M :=
  (finite_iff e M).mpr h

end ModuleCat
