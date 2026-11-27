/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

/-
Completed Apache source port from TauCeti, commit 62bbc0596dc3539d488232e4e924a338548ea0a9.
Original copyright and authors are retained; module/namespace paths are adapted for Atlas.
Source: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/TauCeti/CategoryTheory/Monoidal/Mod/Free/Basic.lean
License: https://github.com/TauCetiProject/TauCeti/blob/62bbc0596dc3539d488232e4e924a338548ea0a9/LICENSE
-/

public import Mathlib.CategoryTheory.Monoidal.Mod
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Free modules over an internal monoid

For a monoid object `A` in a monoidal category, `A ⊗ X` is the free left `A`-module
on `X`. Restriction to the generators identifies module maps out of it with maps out
of `X`, naturally in both variables. No braiding or colimit hypotheses are needed.

The construction uses Mathlib's `Mod` category. It supplies, in particular, the
free sphere modules used to construct free symmetric spectra.
-/

public section

universe v u

open CategoryTheory MonoidalCategory MonObj

namespace MathlibExt.SpectraSource

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] (A : C) [MonObj A]

/-- Multiplication on the first factor makes `A ⊗ X` a left `A`-module. -/
@[instance_reducible]
def freeModObj (X : C) : ModObj A (A ⊗ X) where
  smul := (α_ A A X).inv ≫ μ[A] ▷ X
  one_smul := by
    simp only [selfLeftAction_actionHomLeft, selfLeftAction_actionUnitIso]
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight]
    simp
  mul_smul := by
    simp only [selfLeftAction_actionHomLeft, selfLeftAction_actionHomRight,
      selfLeftAction_actionAssocIso, Category.assoc, whiskerLeft_comp]
    rw [associator_inv_naturality_left_assoc, ← comp_whiskerRight, MonObj.mul_assoc]
    simp only [comp_whiskerRight,
      associator_inv_naturality_middle_assoc, pentagon_hom_inv_inv_inv_hom_assoc]

/-- The free left `A`-module functor. Its underlying object on `X` is `A ⊗ X`. -/
-- An abbreviation so that the underlying objects are tensor products without transports.
abbrev freeMod : C ⥤ Mod C A where
  obj X := letI := freeModObj A X; ⟨A ⊗ X⟩
  map {X Y} f := by
    letI := freeModObj A X
    letI := freeModObj A Y
    exact Mod.Hom.mk' (A ◁ f) (by
      dsimp only [ModObj.smul, freeModObj]
      simp only [selfLeftAction_actionHomRight, Category.assoc,
        associator_inv_naturality_right_assoc, whisker_exchange])
  map_id X := by ext; simp
  map_comp f g := by ext; simp

/-- The free-module action is multiplication on its first tensor factor. -/
@[simp]
lemma freeMod_smul (X : C) :
    ((freeMod A).obj X).mod.smul = (α_ A A X).inv ≫ μ[A] ▷ X := (rfl)

/-- The generators of a free module are obtained by inserting the monoid unit. -/
def freeModι (X : C) : X ⟶ ((freeMod A).obj X).X :=
  (λ_ X).inv ≫ η[A] ▷ X

/-- The inclusion of generators inserts the unit in the first tensor factor. -/
lemma freeModι_def (X : C) :
    freeModι A X = (λ_ X).inv ≫ η[A] ▷ X := (rfl)

/-- Extending a map to a module by the module action. -/
def freeModDesc {X : C} (M : Mod C A) (f : X ⟶ M.X) :
    (freeMod A).obj X ⟶ M :=
  Mod.Hom.mk' (A := A) (A ◁ f ≫ γ[A, M.X]) (by
    dsimp only [ModObj.smul, freeModObj]
    simp only [selfLeftAction_actionHomRight, Category.assoc, whiskerLeft_comp]
    rw [← whisker_exchange_assoc, ModObj.mul_smul_self]
    simp)

/-- The extension's underlying map applies the given map and then the action. -/
@[simp]
lemma freeModDesc_hom {X : C} (M : Mod C A) (f : X ⟶ M.X) :
    (freeModDesc A M f).hom = A ◁ f ≫ γ[A, M.X] := (rfl)

/-- An extension agrees with the given map on generators. -/
-- Restrict to generators before expanding the underlying extension map.
@[simp↓, reassoc (attr := simp↓)]
lemma freeModι_desc {X : C} (M : Mod C A) (f : X ⟶ M.X) :
    dsimp% freeModι A X ≫ (freeModDesc A M f).hom = f := by
  simp [freeModι, ← whisker_exchange_assoc]

/-- Restriction followed by extension recovers every free-module map. -/
@[simp]
lemma freeModDesc_ι {X : C} (M : Mod C A) (f : (freeMod A).obj X ⟶ M) :
    freeModDesc A M (freeModι A X ≫ f.hom) = f := by
  ext
  simp only [freeModDesc_hom, whiskerLeft_comp, Category.assoc]
  have hf := f.isModHom.smul_hom
  simp only [selfLeftAction_actionHomRight] at hf
  rw [← hf]
  simp only [freeModι, whiskerLeft_comp, Category.assoc, freeMod_smul]
  rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc]
  simp

/-- The universal property of a free module. -/
def freeModHomEquiv (X : C) (M : Mod C A) :
    ((freeMod A).obj X ⟶ M) ≃ (X ⟶ M.X) where
  toFun f := freeModι A X ≫ f.hom
  invFun f := freeModDesc A M f
  left_inv f := freeModDesc_ι A M f
  right_inv f := freeModι_desc A M f

/-- The universal bijection restricts a module map to the generators. -/
@[simp]
lemma freeModHomEquiv_apply (X : C) (M : Mod C A) (f : (freeMod A).obj X ⟶ M) :
    dsimp% freeModHomEquiv A X M f = freeModι A X ≫ f.hom := (rfl)

/-- The inverse universal bijection extends by the action. -/
@[simp]
lemma freeModHomEquiv_symm_apply (X : C) (M : Mod C A) (f : X ⟶ M.X) :
    dsimp% (freeModHomEquiv A X M).symm f = freeModDesc A M f := (rfl)

/-- Maps out of a free module are determined by their restrictions to generators. -/
@[ext]
lemma freeMod_hom_ext {X : C} {M : Mod C A} {f g : (freeMod A).obj X ⟶ M}
    (h : freeModι A X ≫ f.hom = freeModι A X ≫ g.hom) : f = g := by
  apply (freeModHomEquiv A X M).injective
  simpa only [freeModHomEquiv_apply] using h

/-- The free-module functor is left adjoint to the native forgetful functor. -/
def freeModAdjunction : freeMod A ⊣ Mod.forget (D := C) A :=
  Adjunction.mkOfHomEquiv
    { homEquiv := freeModHomEquiv A
      homEquiv_naturality_left_symm := by
        intros X Y M f g
        -- Normalize both the hom type and its EquivLike instance before applying simp lemmas.
        dsimp +instances only [Mod.forget] at g ⊢
        apply Mod.hom_ext
        simp only [freeModHomEquiv_symm_apply, freeModDesc_hom, Mod.comp_hom',
          Mod.Hom.mk'_hom, whiskerLeft_comp, Category.assoc]
      homEquiv_naturality_right := by
        intros X M N f g
        dsimp +instances only [Mod.forget] at *
        simp only [freeModHomEquiv_apply, Mod.comp_hom', Category.assoc] }

/-- The adjunction uses restriction to the chosen generators as its hom-set bijection. -/
@[simp]
lemma freeModAdjunction_homEquiv (X : C) (M : Mod C A) :
    (freeModAdjunction A).homEquiv X M = freeModHomEquiv A X M := by
  rw [freeModAdjunction, Adjunction.mkOfHomEquiv_homEquiv]

/-- The adjunction unit is the inclusion of generators. -/
@[simp]
lemma freeModAdjunction_unit_app (X : C) :
    dsimp% (freeModAdjunction A).unit.app X = freeModι A X := by
  rw [← Adjunction.homEquiv_id, freeModAdjunction_homEquiv]
  -- The coercion instance also contains the forgetful object type.
  dsimp +instances only [Mod.forget]
  rw [freeModHomEquiv_apply, Mod.id_hom', Category.comp_id]

/-- The adjunction counit extends the identity by the module action. -/
@[simp]
lemma freeModAdjunction_counit_app (M : Mod C A) :
    dsimp% (freeModAdjunction A).counit.app M = freeModDesc A M (𝟙 M.X) := by
  rw [← Adjunction.homEquiv_symm_id, freeModAdjunction_homEquiv]
  exact freeModHomEquiv_symm_apply A M.X M (𝟙 M.X)

/-- Inclusion of generators is natural in the generating object. -/
@[reassoc (attr := simp)]
lemma freeModι_naturality {X Y : C} (f : X ⟶ Y) :
    dsimp% f ≫ freeModι A Y = freeModι A X ≫ ((freeMod A).map f).hom := by
  simp only [freeModι_def, Mod.Hom.mk'_hom, leftUnitor_inv_naturality_assoc,
    Category.assoc, whisker_exchange]

/-- Extending a map commutes with post-composition by a module map. -/
@[simp, reassoc]
lemma freeModDesc_comp {X : C} {M N : Mod C A} (f : X ⟶ M.X) (g : M ⟶ N) :
    freeModDesc A M f ≫ g = freeModDesc A N (f ≫ g.hom) := by
  apply freeMod_hom_ext
  rw [Mod.comp_hom', freeModι_desc, freeModι_desc_assoc]

/-- Extending a map commutes with pre-composition on its generators. -/
@[simp, reassoc]
lemma freeMod_map_desc {X Y : C} (M : Mod C A) (f : X ⟶ Y) (g : Y ⟶ M.X) :
    dsimp% (freeMod A).map f ≫ freeModDesc A M g = freeModDesc A M (f ≫ g) := by
  apply freeMod_hom_ext
  rw [Mod.comp_hom', ← Category.assoc, ← freeModι_naturality, Category.assoc,
    freeModι_desc, freeModι_desc]

/-- Inserting the free generators commutes with tensoring on the right. -/
@[reassoc (attr := simp)]
lemma freeModι_tensor (V K : C) :
    freeModι A (V ⊗ K) ≫ (α_ A V K).inv = freeModι A V ▷ K := by
  rw [freeModι_def, freeModι_def, comp_whiskerRight, Category.assoc,
    associator_inv_naturality_left]
  monoidal

end MathlibExt.SpectraSource
