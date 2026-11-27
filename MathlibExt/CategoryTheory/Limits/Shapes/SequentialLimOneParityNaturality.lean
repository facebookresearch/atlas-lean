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

public import MathlibExt.CategoryTheory.Limits.Shapes.SequentialLimOneParity

/-!
# Naturality of even-odd product coordinates

A map of inverse sequences acts separately on even and odd product factors.
Both the ordinary reindexing comparison and the comparison negating the odd
target coordinates commute with this map. The resulting odd-sign
automorphism of the original countable product is natural.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Opposite

namespace CategoryTheory.Limits

universe v u

variable {C : Type u} [Category.{v} C]

section ProductMaps

variable [HasCountableProducts C]

/-- The map between the products of even tower terms induced by a map of towers. -/
noncomputable def parityEvenProductMap {A B : ℕᵒᵖ ⥤ C} (α : A ⟶ B) :
    parityEvenProduct A ⟶ parityEvenProduct B :=
  Pi.map fun m => α.app (op (2 * m))

/-- The even-product map is componentwise the map of towers. -/
@[reassoc (attr := simp)]
theorem parityEvenProductMap_π {A B : ℕᵒᵖ ⥤ C} (α : A ⟶ B) (m : ℕ) :
    parityEvenProductMap α ≫ Pi.π (parityEvenFamily B) m =
      Pi.π (parityEvenFamily A) m ≫ α.app (op (2 * m)) := by
  exact Pi.map_π (fun m => α.app (op (2 * m))) m

/-- Even-product maps preserve identities. -/
@[simp]
theorem parityEvenProductMap_id (A : ℕᵒᵖ ⥤ C) :
    parityEvenProductMap (𝟙 A) = 𝟙 (parityEvenProduct A) := by
  change Pi.map (fun m : ℕ => 𝟙 (A.obj (op (2 * m)))) = 𝟙 _
  exact Pi.map_id

/-- Even-product maps preserve composition. -/
@[reassoc]
theorem parityEvenProductMap_comp {A B D : ℕᵒᵖ ⥤ C}
    (α : A ⟶ B) (β : B ⟶ D) :
    parityEvenProductMap α ≫ parityEvenProductMap β =
      parityEvenProductMap (α ≫ β) := by
  change Pi.map (fun m : ℕ => α.app (op (2 * m))) ≫
      Pi.map (fun m : ℕ => β.app (op (2 * m))) =
    Pi.map (fun m : ℕ => α.app (op (2 * m)) ≫ β.app (op (2 * m)))
  exact Pi.map_comp_map _ _

/-- The map between the products of odd tower terms induced by a map of towers. -/
noncomputable def parityOddProductMap {A B : ℕᵒᵖ ⥤ C} (α : A ⟶ B) :
    parityOddProduct A ⟶ parityOddProduct B :=
  Pi.map fun m => α.app (op (2 * m + 1))

/-- The odd-product map is componentwise the map of towers. -/
@[reassoc (attr := simp)]
theorem parityOddProductMap_π {A B : ℕᵒᵖ ⥤ C} (α : A ⟶ B) (m : ℕ) :
    parityOddProductMap α ≫ Pi.π (parityOddFamily B) m =
      Pi.π (parityOddFamily A) m ≫ α.app (op (2 * m + 1)) := by
  exact Pi.map_π (fun m => α.app (op (2 * m + 1))) m

/-- Odd-product maps preserve identities. -/
@[simp]
theorem parityOddProductMap_id (A : ℕᵒᵖ ⥤ C) :
    parityOddProductMap (𝟙 A) = 𝟙 (parityOddProduct A) := by
  change Pi.map (fun m : ℕ => 𝟙 (A.obj (op (2 * m + 1)))) = 𝟙 _
  exact Pi.map_id

/-- Odd-product maps preserve composition. -/
@[reassoc]
theorem parityOddProductMap_comp {A B D : ℕᵒᵖ ⥤ C}
    (α : A ⟶ B) (β : B ⟶ D) :
    parityOddProductMap α ≫ parityOddProductMap β =
      parityOddProductMap (α ≫ β) := by
  change Pi.map (fun m : ℕ => α.app (op (2 * m + 1))) ≫
      Pi.map (fun m : ℕ => β.app (op (2 * m + 1))) =
    Pi.map (fun m : ℕ =>
      α.app (op (2 * m + 1)) ≫ β.app (op (2 * m + 1)))
  exact Pi.map_comp_map _ _

end ProductMaps

section ParityMaps

variable [Preadditive C] [HasCountableProducts C] [HasBinaryBiproducts C]

/-- The map of even/odd parity products induced by a map of towers. -/
noncomputable def parityProductMap {A B : ℕᵒᵖ ⥤ C} (α : A ⟶ B) :
    parityProduct A ⟶ parityProduct B :=
  biprod.map (parityEvenProductMap α) (parityOddProductMap α)

/-- The even projection of the parity-product map. -/
@[reassoc (attr := simp)]
theorem parityProductMap_fst {A B : ℕᵒᵖ ⥤ C} (α : A ⟶ B) :
    parityProductMap α ≫ biprod.fst =
      biprod.fst ≫ parityEvenProductMap α := by
  exact biprod.map_fst _ _

/-- The odd projection of the parity-product map. -/
@[reassoc (attr := simp)]
theorem parityProductMap_snd {A B : ℕᵒᵖ ⥤ C} (α : A ⟶ B) :
    parityProductMap α ≫ biprod.snd =
      biprod.snd ≫ parityOddProductMap α := by
  exact biprod.map_snd _ _

/-- Parity-product maps preserve identities. -/
@[simp]
theorem parityProductMap_id (A : ℕᵒᵖ ⥤ C) :
    parityProductMap (𝟙 A) = 𝟙 (parityProduct A) := by
  apply biprod.hom_ext
  · simp
  · simp

/-- Parity-product maps preserve composition. -/
@[reassoc]
theorem parityProductMap_comp {A B D : ℕᵒᵖ ⥤ C}
    (α : A ⟶ B) (β : B ⟶ D) :
    parityProductMap α ≫ parityProductMap β =
      parityProductMap (α ≫ β) := by
  apply biprod.hom_ext
  · simp only [Category.assoc, parityProductMap_fst,
      parityProductMap_fst_assoc, parityEvenProductMap_comp]
  · simp only [Category.assoc, parityProductMap_snd,
      parityProductMap_snd_assoc, parityOddProductMap_comp]

/-- Reassembly of even and odd coordinates is natural in the tower. -/
@[reassoc]
theorem parityProductIso_naturality {A B : ℕᵒᵖ ⥤ C} (α : A ⟶ B) :
    parityProductMap α ≫ (parityProductIso B).hom =
      (parityProductIso A).hom ≫ sequentialProductMap α := by
  apply Pi.hom_ext
  intro n
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · simp only [Category.assoc, parityProductIso_hom_even_π,
      sequentialProductMap_π]
    rw [parityProductMap_fst_assoc, parityEvenProductMap_π,
      parityProductIso_hom_even_π_assoc]
    exact (Category.assoc _ _ _).symm
  · simp only [Category.assoc, parityProductIso_hom_odd_π,
      sequentialProductMap_π]
    rw [parityProductMap_snd_assoc, parityOddProductMap_π,
      parityProductIso_hom_odd_π_assoc]
    exact (Category.assoc _ _ _).symm

/-- The inverse reassembly coordinate is natural in the tower. -/
@[reassoc]
theorem parityProductIso_inv_naturality {A B : ℕᵒᵖ ⥤ C} (α : A ⟶ B) :
    sequentialProductMap α ≫ (parityProductIso B).inv =
      (parityProductIso A).inv ≫ parityProductMap α := by
  apply (cancel_mono (parityProductIso B).hom).1
  calc
    (sequentialProductMap α ≫ (parityProductIso B).inv) ≫
          (parityProductIso B).hom =
        sequentialProductMap α := by simp
    _ = (parityProductIso A).inv ≫
        ((parityProductIso A).hom ≫ sequentialProductMap α) := by simp
    _ = (parityProductIso A).inv ≫
        (parityProductMap α ≫ (parityProductIso B).hom) :=
      congrArg (fun f => (parityProductIso A).inv ≫ f)
        (parityProductIso_naturality α).symm
    _ = ((parityProductIso A).inv ≫ parityProductMap α) ≫
        (parityProductIso B).hom := (Category.assoc _ _ _).symm

/-- Negate the odd factor of a parity product. -/
noncomputable def parityProductSignIso (A : ℕᵒᵖ ⥤ C) :
    parityProduct A ≅ parityProduct A :=
  biprod.mapIso (Iso.refl _) (-Iso.refl _)

/-- Negating the odd parity factor is natural in the tower. -/
@[reassoc]
theorem parityProductSignIso_naturality {A B : ℕᵒᵖ ⥤ C} (α : A ⟶ B) :
    parityProductMap α ≫ (parityProductSignIso B).hom =
      (parityProductSignIso A).hom ≫ parityProductMap α := by
  apply biprod.hom_ext
  · simp [parityProductSignIso, parityProductMap, Category.assoc]
  · simp [parityProductSignIso, parityProductMap, Category.assoc]

/-- Reassembly with negated odd coordinates is natural in the tower. -/
@[reassoc]
theorem paritySignIso_naturality {A B : ℕᵒᵖ ⥤ C} (α : A ⟶ B) :
    parityProductMap α ≫ (paritySignIso B).hom =
      (paritySignIso A).hom ≫ sequentialProductMap α := by
  change parityProductMap α ≫
      ((parityProductSignIso B).hom ≫ (parityProductIso B).hom) =
    ((parityProductSignIso A).hom ≫ (parityProductIso A).hom) ≫
      sequentialProductMap α
  rw [← Category.assoc, parityProductSignIso_naturality]
  rw [Category.assoc, parityProductIso_naturality]
  exact (Category.assoc _ _ _).symm

/-- The odd-sign change of coordinates as an automorphism of the ordinary sequential product. -/
noncomputable def paritySignedSequentialProductIso (A : ℕᵒᵖ ⥤ C) :
    sequentialProduct A ≅ sequentialProduct A :=
  (parityProductIso A).symm ≪≫ paritySignIso A

/-- The odd-sign automorphism of sequential products is natural in the tower. -/
@[reassoc]
theorem paritySignedSequentialProductIso_naturality
    {A B : ℕᵒᵖ ⥤ C} (α : A ⟶ B) :
    sequentialProductMap α ≫ (paritySignedSequentialProductIso B).hom =
      (paritySignedSequentialProductIso A).hom ≫ sequentialProductMap α := by
  simp only [paritySignedSequentialProductIso, Iso.trans_hom, Category.assoc]
  change sequentialProductMap α ≫ (parityProductIso B).inv ≫
      (paritySignIso B).hom =
    (parityProductIso A).inv ≫ (paritySignIso A).hom ≫
      sequentialProductMap α
  rw [← Category.assoc, parityProductIso_inv_naturality]
  slice_lhs 2 3 => rw [paritySignIso_naturality]

/-- The inverse odd-sign automorphism of sequential products is natural in the tower. -/
@[reassoc]
theorem paritySignedSequentialProductIso_inv_naturality
    {A B : ℕᵒᵖ ⥤ C} (α : A ⟶ B) :
    sequentialProductMap α ≫ (paritySignedSequentialProductIso B).inv =
      (paritySignedSequentialProductIso A).inv ≫ sequentialProductMap α := by
  apply (cancel_mono (paritySignedSequentialProductIso B).hom).1
  calc
    (sequentialProductMap α ≫ (paritySignedSequentialProductIso B).inv) ≫
          (paritySignedSequentialProductIso B).hom =
        sequentialProductMap α := by simp
    _ = (paritySignedSequentialProductIso A).inv ≫
        ((paritySignedSequentialProductIso A).hom ≫
          sequentialProductMap α) := by simp
    _ = (paritySignedSequentialProductIso A).inv ≫
        (sequentialProductMap α ≫
          (paritySignedSequentialProductIso B).hom) :=
      congrArg (fun f => (paritySignedSequentialProductIso A).inv ≫ f)
        (paritySignedSequentialProductIso_naturality α).symm
    _ = ((paritySignedSequentialProductIso A).inv ≫
          sequentialProductMap α) ≫
        (paritySignedSequentialProductIso B).hom :=
      (Category.assoc _ _ _).symm

end ParityMaps

end CategoryTheory.Limits

end
