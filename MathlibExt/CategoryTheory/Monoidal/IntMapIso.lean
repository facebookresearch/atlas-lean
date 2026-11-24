/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.CategoryTheory.Monoidal.IntMapMonoidal

/-!
# Monoidal natural isomorphisms between Int functors

A monoidal natural isomorphism between trace-preserving strong symmetric
monoidal functors induces a monoidal natural isomorphism between their Int
functors. Its positive component is covariant and its negative component is
contravariant, so invertibility is essential.

This is the action on invertible transformations underlying Joyal, Street and
Verity, Traced monoidal categories (1996), Sections 4–5,
https://doi.org/10.1017/S0305004100074338, in the symmetric specialization.
It does not assert the universal uniqueness theorem.
-/

@[expose] public section
universe v₁ v₂ u₁ u₂
namespace CategoryTheory
open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
open scoped MonoidalCategory
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]
namespace IntConstruction
variable (T : SymmetricTrace C) (S : SymmetricTrace D)
variable {F G H : C ⥤ D} [F.Braided] [G.Braided] [H.Braided]
variable (hF : T.Preserves S F) (hG : T.Preserves S G)
variable (i : F ≅ G) [NatTrans.IsMonoidal i.hom]

/-- A monoidal transformation intertwines the comparison-adjusted crossed maps. -/
theorem mapCrossed_naturality {A B U V : C} (f : A ⊗ V ⟶ B ⊗ U) :
    mapCrossed F f ≫ (i.hom.app B ⊗ₘ i.hom.app U) =
      (i.hom.app A ⊗ₘ i.hom.app V) ≫ mapCrossed G f := by
  apply (cancel_mono (μ G B U)).1
  simp only [mapCrossed, Category.assoc]
  rw [← NatTrans.IsMonoidal.tensor, δ_μ_assoc, δ_μ, Category.comp_id,
    i.hom.naturality, NatTrans.IsMonoidal.tensor_assoc]

set_option backward.defeqAttrib.useBackward true in
private theorem mapIso_natural {X Y : IntConstruction T} (f : X ⟶ Y) :
    (map T S F hF).map f ≫ mapPair S
      (X := (map T S F hF).obj Y) (Y := (map T S G hG).obj Y)
      (i.hom.app Y.positive) (i.inv.app Y.negative) =
      mapPair S (X := (map T S F hF).obj X) (Y := (map T S G hG).obj X)
        (i.hom.app X.positive) (i.inv.app X.negative) ≫ (map T S G hG).map f := by
  apply hom_ext S
  change compose S (mapCrossed F (hom T f)) (i.hom.app Y.positive ⊗ₘ i.inv.app Y.negative) =
    compose S (i.hom.app X.positive ⊗ₘ i.inv.app X.negative) (mapCrossed G (hom T f))
  rw [compose_tensor_right, compose_tensor_left]
  apply (cancel_epi (F.obj X.positive ◁ i.hom.app Y.negative)).1
  apply (cancel_mono (G.obj Y.positive ◁ i.hom.app X.negative)).1
  simp only [Category.assoc, ← whiskerLeft_comp_assoc, ← whiskerLeft_comp,
    Iso.hom_inv_id_app, Iso.inv_hom_id_app, whiskerLeft_id, Category.id_comp, Category.comp_id]
  rw [← tensorHom_def, ← tensorHom_def'_assoc]
  exact mapCrossed_naturality i (hom T f)

/-- Lift a monoidal natural isomorphism, using its inverse on the negative component. -/
def mapIso : map T S F hF ≅ map T S G hG :=
  NatIso.ofComponents (fun X => pairIso S (i.app X.positive) (i.app X.negative).symm)
    (by intro X Y f; exact mapIso_natural T S hF hG i f)

private theorem inv_unit : i.inv.app (𝟙_ C) ≫ η F = η G := by
  apply (cancel_epi (ε G)).1
  rw [← Category.assoc, NatTrans.IsMonoidal.unit]
  simp

private theorem inv_tensor (A B : C) :
    i.inv.app (A ⊗ B) ≫ δ F A B = δ G A B ≫ (i.inv.app A ⊗ₘ i.inv.app B) := by
  apply (cancel_mono (μ F A B)).1
  simp only [Category.assoc, δ_μ, Category.comp_id]
  rw [← NatTrans.IsMonoidal.tensor, δ_μ_assoc]

set_option backward.defeqAttrib.useBackward true in
/-- The lifted natural isomorphism is monoidal for the induced comparison maps. -/
instance mapIso_hom_isMonoidal : NatTrans.IsMonoidal (mapIso T S hF hG i).hom where
  unit := by
    change mapPair S _ _ ≫ mapPair S _ _ = mapPair S _ _
    rw [mapPair_comp]
    congr 1
    · exact NatTrans.IsMonoidal.unit
    · exact inv_unit i
  tensor X Y := by
    change mapPair S _ _ ≫ mapPair S _ _ =
      tensorMap S (mapPair S _ _) (mapPair S _ _) ≫ mapPair S _ _
    dsimp only [map]
    rw [tensorMap_mapPair, mapPair_comp, mapPair_comp]
    congr 1
    · exact NatTrans.IsMonoidal.tensor X.positive Y.positive
    · exact inv_tensor i Y.negative X.negative

/-- The lifted forward component uses the inverse on its negative wire. -/
@[simp] theorem hom_mapIso_hom_app (X : IntConstruction T) :
    hom S ((mapIso T S hF hG i).hom.app X) =
      i.hom.app X.positive ⊗ₘ i.inv.app X.negative := rfl

/-- The lifted inverse component reverses both choices. -/
@[simp] theorem hom_mapIso_inv_app (X : IntConstruction T) :
    hom S ((mapIso T S hF hG i).inv.app X) =
      i.inv.app X.positive ⊗ₘ i.hom.app X.negative := rfl

-- Supply the standard transformation instances through the isomorphism projections.
local instance : NatTrans.IsMonoidal (Iso.refl F).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (𝟙 F))
local instance (j : G ≅ H) [NatTrans.IsMonoidal j.hom] :
    NatTrans.IsMonoidal (i ≪≫ j).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (i.hom ≫ j.hom))
local instance : NatTrans.IsMonoidal i.symm.hom :=
  inferInstanceAs (NatTrans.IsMonoidal i.inv)

set_option backward.defeqAttrib.useBackward true in
/-- Lifting an identity isomorphism gives the identity. -/
@[simp] theorem mapIso_refl : mapIso T S hF hF (Iso.refl F) = Iso.refl (map T S F hF) := by
  apply Iso.ext
  ext X
  change (𝟙 (F.obj X.positive)) ⊗ₘ (𝟙 (F.obj X.negative)) = 𝟙 _
  simp

set_option backward.defeqAttrib.useBackward true in
/-- Lifting commutes with composition of monoidal natural isomorphisms. -/
theorem mapIso_trans (hH : T.Preserves S H) (j : G ≅ H) [NatTrans.IsMonoidal j.hom] :
    mapIso T S hF hH (i ≪≫ j) = mapIso T S hF hG i ≪≫ mapIso T S hG hH j := by
  apply Iso.ext
  ext X
  change mapPair S _ _ = mapPair S _ _ ≫ mapPair S _ _
  rw [mapPair_comp]
  rfl

set_option backward.defeqAttrib.useBackward true in
/-- Lifting commutes with inversion. -/
@[simp] theorem mapIso_symm : mapIso T S hG hF i.symm = (mapIso T S hF hG i).symm := by
  apply Iso.ext
  ext X
  rfl

end IntConstruction
end CategoryTheory
