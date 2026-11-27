/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.EpiMono

/-!
# Lifting and extension along an adjunction

For an adjunction `F ⊣ U`, a morphism from `F.obj X` lifts through any morphism whose image under
`U` has a section. Dually, a morphism into `U.obj Y` extends across any morphism whose image under
`F` has a retraction. These constructions use the adjunction hom-set equivalence and satisfy
factorization and naturality laws.
-/

@[expose] public section

open CategoryTheory

universe uC vC uD vD

namespace CategoryTheory.Adjunction

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {F : C ⥤ D} {U : D ⥤ C}

/-- Construct the lift from a free adjunction object through a restricted split epimorphism. -/
def liftOfSplitEpi (adj : F ⊣ U) {X : C} {Y Z : D}
    (g : Y ⟶ Z) (s : SplitEpi (U.map g)) (f : F.obj X ⟶ Z) : F.obj X ⟶ Y :=
  (adj.homEquiv X Y).symm (adj.homEquiv X Z f ≫ s.section_)

/-- The mate of the constructed lift is the mate composed with the section. -/
@[simp]
theorem homEquiv_liftOfSplitEpi (adj : F ⊣ U) {X : C} {Y Z : D}
    (g : Y ⟶ Z) (s : SplitEpi (U.map g)) (f : F.obj X ⟶ Z) :
    adj.homEquiv X Y (adj.liftOfSplitEpi g s f) = adj.homEquiv X Z f ≫ s.section_ :=
  (adj.homEquiv X Y).apply_symm_apply _

/-- The constructed lift factors the map through the epimorphism. -/
@[reassoc]
theorem liftOfSplitEpi_comp (adj : F ⊣ U) {X : C} {Y Z : D}
    (g : Y ⟶ Z) (s : SplitEpi (U.map g)) (f : F.obj X ⟶ Z) :
    adj.liftOfSplitEpi g s f ≫ g = f := by
  apply (adj.homEquiv X Z).injective
  rw [adj.homEquiv_naturality_right, homEquiv_liftOfSplitEpi, Category.assoc,
    s.id, Category.comp_id]

/-- The constructed lift is natural under the morphisms of free objects. -/
theorem liftOfSplitEpi_precomp (adj : F ⊣ U) {X X' : C} {Y Z : D}
    (g : Y ⟶ Z) (s : SplitEpi (U.map g)) (f : F.obj X ⟶ Z) (a : X' ⟶ X) :
    adj.liftOfSplitEpi g s (F.map a ≫ f) = F.map a ≫ adj.liftOfSplitEpi g s f := by
  apply (adj.homEquiv X' Y).injective
  rw [homEquiv_liftOfSplitEpi, adj.homEquiv_naturality_left,
    adj.homEquiv_naturality_left, homEquiv_liftOfSplitEpi, Category.assoc]

/-- Postcomposition is surjective on maps from every free adjunction object for restricted split epis. -/
theorem postcomp_surjective_of_isSplitEpi (adj : F ⊣ U) (X : C) {Y Z : D}
    (g : Y ⟶ Z) [IsSplitEpi (U.map g)] :
    Function.Surjective (fun f : F.obj X ⟶ Y => f ≫ g) := by
  intro f
  obtain ⟨s⟩ := IsSplitEpi.exists_splitEpi (f := U.map g)
  exact ⟨adj.liftOfSplitEpi g s f, adj.liftOfSplitEpi_comp g s f⟩

/-- Extend an map into a restricted object across an freely split monomorphism. -/
def extendOfSplitMono (adj : F ⊣ U) {X X' : C} {Y : D}
    (g : X ⟶ X') (s : SplitMono (F.map g)) (f : X ⟶ U.obj Y) : X' ⟶ U.obj Y :=
  adj.homEquiv X' Y (s.retraction ≫ (adj.homEquiv X Y).symm f)

/-- The inverse mate of the extension is the retraction followed by the mate. -/
@[simp]
theorem homEquiv_symm_extendOfSplitMono (adj : F ⊣ U) {X X' : C} {Y : D}
    (g : X ⟶ X') (s : SplitMono (F.map g)) (f : X ⟶ U.obj Y) :
    (adj.homEquiv X' Y).symm (adj.extendOfSplitMono g s f) =
      s.retraction ≫ (adj.homEquiv X Y).symm f :=
  (adj.homEquiv X' Y).symm_apply_apply _

/-- The constructed extension restricts to the map across the monomorphism. -/
@[reassoc]
theorem comp_extendOfSplitMono (adj : F ⊣ U) {X X' : C} {Y : D}
    (g : X ⟶ X') (s : SplitMono (F.map g)) (f : X ⟶ U.obj Y) :
    g ≫ adj.extendOfSplitMono g s f = f := by
  apply (adj.homEquiv X Y).symm.injective
  rw [adj.homEquiv_naturality_left_symm, homEquiv_symm_extendOfSplitMono,
    ← Category.assoc, s.id, Category.id_comp]

/-- The constructed extension is natural under the morphisms of restricted objects. -/
theorem extendOfSplitMono_postcomp (adj : F ⊣ U) {X X' : C} {Y Y' : D}
    (g : X ⟶ X') (s : SplitMono (F.map g)) (f : X ⟶ U.obj Y) (a : Y ⟶ Y') :
    adj.extendOfSplitMono g s (f ≫ U.map a) = adj.extendOfSplitMono g s f ≫ U.map a := by
  apply (adj.homEquiv X' Y').symm.injective
  rw [homEquiv_symm_extendOfSplitMono, adj.homEquiv_naturality_right_symm,
    adj.homEquiv_naturality_right_symm, homEquiv_symm_extendOfSplitMono, Category.assoc]

/-- Precomposition is surjective on maps into restricted objects for freely split monos. -/
theorem precomp_surjective_of_isSplitMono (adj : F ⊣ U) (Y : D) {X X' : C}
    (g : X ⟶ X') [IsSplitMono (F.map g)] :
    Function.Surjective (fun f : X' ⟶ U.obj Y => g ≫ f) := by
  intro f
  obtain ⟨s⟩ := IsSplitMono.exists_splitMono (f := F.map g)
  exact ⟨adj.extendOfSplitMono g s f, adj.comp_extendOfSplitMono g s f⟩

end CategoryTheory.Adjunction
