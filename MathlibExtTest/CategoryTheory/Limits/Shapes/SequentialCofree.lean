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

public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialCofree
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.EpiMono

/-!
# Cofree envelopes of inverse sequences

The general clients check component retractions and the coordinates of
sections of cofree transitions. A tower of integer modules with zero
transition maps shows that these sections do not require the given
transitions to be epimorphisms. The same tower distinguishes component
retractions of the unit from a retraction of the whole diagram.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Limits.SequentialCofreeTests

universe u v

section Generic

variable (C : Type u) [Category.{v} C] [HasFiniteProducts C]
variable (F : ℕᵒᵖ ⥤ C)

example : Mono ((sequentialCofreeUnit C).app F) := inferInstance

example (n : ℕ) : IsSplitMono (((sequentialCofreeUnit C).app F).app (op n)) :=
  inferInstance

/-- The preceding last coordinate of the next unit is the original transition. -/
example (n : ℕ) :
    ((sequentialCofreeUnit C).app F).app (op (n + 1)) ≫
        (sequentialCofreePrefixIso C F (n + 1)).hom ≫
          Pi.π _ (Fin.last n).castSucc =
      F.map (homOfLE (Nat.le_succ n)).op := by
  have h := sequentialCofreeUnit_app_π C F (n + 1) (Fin.last n).castSucc
  have he : (homOfLE (Nat.le_of_lt_succ (Fin.last n).castSucc.isLt)).op =
      (homOfLE (Nat.le_succ n)).op := Subsingleton.elim _ _
  simpa only [he] using h

variable [HasZeroMorphisms C]

example (n : ℕ) :
    sequentialCofreeTransitionSection C F n ≫
        ((sequentialCofreeFunctor C).obj F).map (homOfLE (Nat.le_succ n)).op =
      𝟙 (((sequentialCofreeFunctor C).obj F).obj (op n)) :=
  (sequentialCofreeTransitionSplitEpi C F n).id

/-- The actual transported section inserts zero into its new last coordinate. -/
example (n : ℕ) :
    sequentialCofreeTransitionSection C F n ≫
        (sequentialCofreePrefixIso C F (n + 1)).hom ≫ Pi.π _ (Fin.last (n + 1)) =
      0 := by
  simp only [sequentialCofreeTransitionSection, Category.assoc,
    Iso.inv_hom_id_assoc, sequentialCofreePrefixSection,
    Pi.lift_comp_π, Fin.lastCases_last, comp_zero]

/-- Every previous coordinate is preserved by the actual transported section. -/
example (n : ℕ) (i : Fin (n + 1)) :
    sequentialCofreeTransitionSection C F n ≫
        (sequentialCofreePrefixIso C F (n + 1)).hom ≫ Pi.π _ i.castSucc =
      (sequentialCofreePrefixIso C F n).hom ≫ Pi.π _ i := by
  simp only [sequentialCofreeTransitionSection, Category.assoc,
    Iso.inv_hom_id_assoc, sequentialCofreePrefixSection,
    Pi.lift_comp_π, Fin.lastCases_castSucc]

end Generic

/-- The inverse sequence of integer modules with every successor transition equal to zero. -/
abbrev zeroTower : ℕᵒᵖ ⥤ ModuleCat ℤ :=
  Functor.ofOpSequence (X := fun _ : ℕ => ModuleCat.of ℤ ℤ)
    (fun _ : ℕ => (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ))

private theorem zeroTower_step_not_epi :
    ¬ Epi (zeroTower.map (homOfLE (Nat.le_succ 0)).op) := by
  intro h
  have he : zeroTower.map (homOfLE (Nat.le_succ 0)).op =
      (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ) :=
    Functor.ofOpSequence_map_homOfLE_succ
      (X := fun _ : ℕ => ModuleCat.of ℤ ℤ)
      (fun _ : ℕ => (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ)) 0
  have hz : Epi (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ) := he ▸ h
  obtain ⟨m, hm⟩ := (ModuleCat.epi_iff_surjective
    (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ)).1 hz (1 : ℤ)
  have h01 : (0 : ℤ) = 1 := by
    simpa only [ModuleCat.hom_zero, LinearMap.zero_apply] using hm
  exact zero_ne_one h01

example : ¬ Epi (zeroTower.map (homOfLE (Nat.le_succ 0)).op) :=
  zeroTower_step_not_epi

example :
    IsSplitEpi (((sequentialCofreeFunctor (ModuleCat ℤ)).obj zeroTower).map
      (homOfLE (Nat.le_succ 0)).op) := inferInstance

example :
    ((sequentialCofreeUnit (ModuleCat ℤ)).app zeroTower).app (op 1) ≫
        (sequentialCofreePrefixIso (ModuleCat ℤ) zeroTower 1).hom ≫
          Pi.π _ (0 : Fin 2) = 0 := by
  rw [sequentialCofreeUnit_app_π]
  exact Functor.ofOpSequence_map_homOfLE_succ
    (X := fun _ : ℕ => ModuleCat.of ℤ ℤ)
    (fun _ : ℕ => (0 : ModuleCat.of ℤ ℤ ⟶ ModuleCat.of ℤ ℤ)) 0

example :
    ((sequentialCofreeUnit (ModuleCat ℤ)).app zeroTower).app (op 1) ≫
        (sequentialCofreePrefixIso (ModuleCat ℤ) zeroTower 1).hom ≫
          Pi.π _ (1 : Fin 2) = 𝟙 (ModuleCat.of ℤ ℤ) := by
  rw [sequentialCofreeUnit_app_π]
  have he : (homOfLE (Nat.le_of_lt_succ (1 : Fin 2).isLt)).op = 𝟙 (op 1) :=
    Subsingleton.elim _ _
  rw [he, zeroTower.map_id]
  rfl

/-- Component retractions of the unit do not provide a natural retraction. -/
example : ¬ ∃ r : (sequentialCofreeFunctor (ModuleCat ℤ)).obj zeroTower ⟶ zeroTower,
    (sequentialCofreeUnit (ModuleCat ℤ)).app zeroTower ≫ r = 𝟙 zeroTower := by
  rintro ⟨r, hr⟩
  have : IsSplitEpi (r.app (op 0)) := IsSplitEpi.mk'
    { section_ := ((sequentialCofreeUnit (ModuleCat ℤ)).app zeroTower).app (op 0)
      id := by simpa only [NatTrans.comp_app, NatTrans.id_app] using congr_app hr (op 0) }
  have : Epi (r.app (op 1) ≫ zeroTower.map (homOfLE (Nat.le_succ 0)).op) := by
    rw [← r.naturality]
    infer_instance
  have : Epi (zeroTower.map (homOfLE (Nat.le_succ 0)).op) :=
    epi_of_epi (r.app (op 1)) (zeroTower.map (homOfLE (Nat.le_succ 0)).op)
  exact zeroTower_step_not_epi this

end CategoryTheory.Limits.SequentialCofreeTests
