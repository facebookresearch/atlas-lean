/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































































































import Code.Walls.rc45doubledcover
import Code.Inequalities.ReimerDoubled

open Finset
open scoped FinsetFamily StatMech NNReal

namespace StatMech.Walls

open StatMech ConfigSpace

variable {α : Type*} [Fintype α] [DecidableEq α]










open Classical in




noncomputable def rc46_famCylBoxDoubled (𝒜 ℬ : Finset (Finset α)) : Finset (Finset (α ⊕ α)) :=
  (rc20_famCylBox 𝒜 ℬ).image (fun S => dbl S Sᶜ)

open Classical in



theorem rc46_famCylBoxDoubled_card_eq (𝒜 ℬ : Finset (Finset α)) :
    (rc46_famCylBoxDoubled 𝒜 ℬ).card = (rc20_famCylBox 𝒜 ℬ).card := by
  rw [rc46_famCylBoxDoubled]
  exact Finset.card_image_of_injOn (rc37_dblCompl_injOn _)










set_option linter.unusedSectionVars false in



theorem rc46_doubleCompress_card_any (i : α) (𝒜 : Finset (Finset (α ⊕ α))) :
    (doubleCompress i 𝒜).card = 𝒜.card :=
  doubleCompress_card i 𝒜



theorem rc46_doubleCompress_famCylBoxDoubled_card (i : α) (𝒜 ℬ : Finset (Finset α)) :
    (doubleCompress i (rc46_famCylBoxDoubled 𝒜 ℬ)).card = (rc46_famCylBoxDoubled 𝒜 ℬ).card :=
  doubleCompress_card i (rc46_famCylBoxDoubled 𝒜 ℬ)



theorem rc46_doubleCompress_complBoxDoubled_card (i : α) (𝒜 ℬ : Finset (Finset α)) :
    (doubleCompress i (rc37_complBoxDoubled 𝒜 ℬ)).card = (rc37_complBoxDoubled 𝒜 ℬ).card :=
  doubleCompress_card i (rc37_complBoxDoubled 𝒜 ℬ)












def rc46_Adn : Finset (Finset (Fin 3)) := {∅, {0}, {0, 1}, {0, 1, 2}, {1}, {1, 2}}


def rc46_Bdn : Finset (Finset (Fin 3)) := {∅, {1}, {2}}













theorem rc46_downDownStep_decreases_famCylBox_fin3 :
    (rc20_famCylBoxComp 3 (Down.compression 1 rc46_Adn) (Down.compression 1 rc46_Bdn)).card
      < (rc20_famCylBoxComp 3 rc46_Adn rc46_Bdn).card := by
  rw [rc46_Adn, rc46_Bdn]; decide





theorem rc46_downDownStep_reflInter_stable_fin3 :
    (rc20_reflInterComp 3 (Down.compression 1 rc46_Adn) (Down.compression 1 rc46_Bdn)).card
      = (rc20_reflInterComp 3 rc46_Adn rc46_Bdn).card := by
  rw [rc46_Adn, rc46_Bdn]; decide













def rc46_isComplementary (U : Finset (Fin 3 ⊕ Fin 3)) : Prop :=
  (Finset.univ.filter (fun x => Sum.inr x ∈ U))
    = (Finset.univ : Finset (Fin 3)) \ (Finset.univ.filter (fun x => Sum.inl x ∈ U))

instance : DecidablePred rc46_isComplementary := fun _ => by unfold rc46_isComplementary; infer_instance


def rc46_Acf : Finset (Finset (Fin 3)) := {∅, {1}}


def rc46_Bcf : Finset (Finset (Fin 3)) := {{0, 1, 2}, {0, 2}}




theorem rc46_dblEmpty02_not_complementary :
    ¬ rc46_isComplementary (dbl (∅ : Finset (Fin 3)) {0, 2}) := by decide






theorem rc46_dblEmpty02_mem_doubleCompress_complBoxDoubled :
    dbl (∅ : Finset (Fin 3)) {0, 2} ∈ doubleCompress 1 (rc37_complBoxDoubled rc46_Acf rc46_Bcf) := by
  rw [rc46_Acf, rc46_Bcf]; decide









theorem rc46_doubleCompress_breaks_complementary_fin3 :
    ∃ (𝒜 ℬ : Finset (Finset (Fin 3))) (i : Fin 3) (U : Finset (Fin 3 ⊕ Fin 3)),
      U ∈ doubleCompress i (rc37_complBoxDoubled 𝒜 ℬ) ∧ ¬ rc46_isComplementary U :=
  ⟨rc46_Acf, rc46_Bcf, 1, dbl (∅ : Finset (Fin 3)) {0, 2},
    rc46_dblEmpty02_mem_doubleCompress_complBoxDoubled, rc46_dblEmpty02_not_complementary⟩








open Classical in






theorem rc46_famCylBoxDoubled_le_at_increasing {n : ℕ} {A B : Set (ConfigSpace (Fin n))}
    (hA : IsIncreasing A) (hB : IsIncreasing B) :
    (rc46_famCylBoxDoubled (eventFamily A) (eventFamily B)).card
      ≤ (rc37_complBoxDoubled (eventFamily A) (eventFamily B)).card := by
  rw [rc46_famCylBoxDoubled_card_eq, rc37_complBoxDoubled_card_eq_reflInter]
  exact rc20_famCylBox_of_increasing hA hB








open Classical in


theorem rc46_reimer_closes_of_boxMonoResidue (h : rc44_BoxMonoResidue) :
    rc18_CylBoxReflInter :=
  rc44_reimer_closes_of_boxMonoResidue h

open Classical in


theorem rc46_boxMonoResidue_fin2 (𝒜 ℬ : Finset (Finset (Fin 2))) :
    #(rc44_famCylBoxE Finset.univ 𝒜 ℬ) ≤ #(rc44_reflInterE Finset.univ 𝒜 ℬ) :=
  rc44_boxMonoResidue_fin2 𝒜 ℬ

end StatMech.Walls
