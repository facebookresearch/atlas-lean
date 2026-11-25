/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.CategoryTheory.Monoidal.IntExtension
public import MathlibExt.CategoryTheory.Monoidal.IntMapIso
public import MathlibExt.CategoryTheory.Monoidal.IntRestriction

/-!
# Isomorphisms of compact-target extensions

Monoidal natural isomorphisms of traced functors induce monoidal natural
isomorphisms of their canonical Int extensions. This action respects identities,
composition and inverses, and commutes with the restriction factorization.
The lift is unique among monoidal natural isomorphisms with that restriction.
These are the invertible-transformation laws of the construction in Joyal,
Street and Verity, Traced monoidal categories (1996), Proposition 5.2,
https://doi.org/10.1017/S0305004100074338, in the symmetric specialization.
Comparison with arbitrary extensions is a separate statement.
-/

@[expose] public section
noncomputable section
universe v₁ v₂ u₁ u₂
namespace CategoryTheory
open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
open scoped MonoidalCategory
variable {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
  [MonoidalCategory C] [MonoidalCategory D] [SymmetricCategory C] [SymmetricCategory D]
  [RightRigidCategory D]
namespace IntConstruction
variable (T : SymmetricTrace C) {F G H : C ⥤ D} [F.Braided] [G.Braided] [H.Braided]
  (hF : T.Preserves (symmetricTraceOfRigid D) F)
  (hG : T.Preserves (symmetricTraceOfRigid D) G)
  (i : F ≅ G) [NatTrans.IsMonoidal i.hom]

/-- Extend an isomorphism by lifting its formal pairs and recovering the compact target. -/
def extendIso : extend T F hF ≅ extend T G hG :=
  Functor.isoWhiskerRight (mapIso T (symmetricTraceOfRigid D) hF hG i)
    (rigidEquivalence (symmetricTraceOfRigid D)).inverse

/-- The extended isomorphism is monoidal. -/
instance extendIso_hom_isMonoidal : NatTrans.IsMonoidal (extendIso T hF hG i).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (Functor.whiskerRight
    (mapIso T (symmetricTraceOfRigid D) hF hG i).hom
      (rigidEquivalence (symmetricTraceOfRigid D)).inverse))

/-- The component uses the original isomorphism on positives and its inverse on negatives. -/
theorem extendIso_hom_app (X : IntConstruction T) :
    (extendIso T hF hG i).hom.app X =
      (rigidEquivalence (symmetricTraceOfRigid D)).inverse.map
        (mapPair (symmetricTraceOfRigid D) (i.hom.app X.positive) (i.inv.app X.negative)) := rfl

local instance : NatTrans.IsMonoidal (Iso.refl F).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (𝟙 F))
local instance (j : G ≅ H) [NatTrans.IsMonoidal j.hom] :
    NatTrans.IsMonoidal (i ≪≫ j).hom :=
  inferInstanceAs (NatTrans.IsMonoidal (i.hom ≫ j.hom))
local instance : NatTrans.IsMonoidal i.symm.hom :=
  inferInstanceAs (NatTrans.IsMonoidal i.inv)

/-- Extension preserves identity isomorphisms. -/
@[simp] theorem extendIso_refl : extendIso T hF hF (Iso.refl F) = Iso.refl (extend T F hF) := by
  unfold extendIso
  rw [mapIso_refl]
  apply Iso.ext
  ext X
  exact (rigidEquivalence (symmetricTraceOfRigid D)).inverse.map_id _

/-- Extension preserves composition of monoidal natural isomorphisms. -/
theorem extendIso_trans (hH : T.Preserves (symmetricTraceOfRigid D) H)
    (j : G ≅ H) [NatTrans.IsMonoidal j.hom] :
    extendIso T hF hH (i ≪≫ j) = extendIso T hF hG i ≪≫ extendIso T hG hH j := by
  unfold extendIso
  rw [mapIso_trans T (symmetricTraceOfRigid D) hF hG i hH j]
  apply Iso.ext
  ext X
  exact (rigidEquivalence (symmetricTraceOfRigid D)).inverse.map_comp _ _

/-- Extension preserves inversion. -/
@[simp] theorem extendIso_symm :
    extendIso T hG hF i.symm = (extendIso T hF hG i).symm := by
  unfold extendIso
  rw [mapIso_symm]
  rfl

private theorem embeddingMapIso_natural_iso (A : C) :
    (mapIso T (symmetricTraceOfRigid D) hF hG i).hom.app ((embedding T).obj A) ≫
      (embeddingMapIso T (symmetricTraceOfRigid D) G hG).hom.app A =
    (embeddingMapIso T (symmetricTraceOfRigid D) F hF).hom.app A ≫
      (embedding (symmetricTraceOfRigid D)).map (i.hom.app A) := by
  change mapPair _ _ _ ≫ mapPair _ _ _ = mapPair _ _ _ ≫ _
  rw [embedding_map_eq_mapPair]
  dsimp only [embedding, map]
  rw [mapPair_comp, mapPair_comp]
  congr 1
  · simp
  · change ε G ≫ i.inv.app (𝟙_ C) = 𝟙 (𝟙_ D) ≫ ε F
    rw [← NatTrans.IsMonoidal.unit (τ := i.hom)]
    simp

set_option backward.defeqAttrib.useBackward true in
/-- Restricting the extended isomorphism recovers the original through the factorization maps. -/
theorem extensionIso_natural (A : C) :
    (extendIso T hF hG i).hom.app ((embedding T).obj A) ≫ (extensionIso T G hG).hom.app A =
      (extensionIso T F hF).hom.app A ≫ i.hom.app A := by
  let E := rigidEquivalence (symmetricTraceOfRigid D)
  change E.inverse.map ((mapIso T (symmetricTraceOfRigid D) hF hG i).hom.app
      ((embedding T).obj A)) ≫
    (𝟙 _ ≫ E.inverse.map ((embeddingMapIso T (symmetricTraceOfRigid D) G hG).hom.app A) ≫
      𝟙 _ ≫ E.unitIso.inv.app (G.obj A) ≫ 𝟙 _) =
    (𝟙 _ ≫ E.inverse.map ((embeddingMapIso T (symmetricTraceOfRigid D) F hF).hom.app A) ≫
      𝟙 _ ≫ E.unitIso.inv.app (F.obj A) ≫ 𝟙 _) ≫ i.hom.app A
  simp only [Category.id_comp, Category.comp_id, Category.assoc]
  rw [← Functor.map_comp_assoc, embeddingMapIso_natural_iso, Functor.map_comp]
  simp only [Category.assoc]
  congr 1
  exact (rigidEquivalence (symmetricTraceOfRigid D)).unitIso.inv.naturality (i.hom.app A)

/-- The factorization isomorphisms commute with the lifted transformation. -/
theorem extensionIso_natural_iso :
    Functor.isoWhiskerLeft (embedding T) (extendIso T hF hG i) ≪≫ extensionIso T G hG =
      extensionIso T F hF ≪≫ i := by
  apply Iso.ext
  ext A
  exact extensionIso_natural T hF hG i A

/-- The compatible monoidal isomorphism between canonical extensions is unique. -/
theorem extendIso_unique (j : extend T F hF ≅ extend T G hG)
    [NatTrans.IsMonoidal j.hom]
    (h : ∀ A, j.hom.app ((embedding T).obj A) ≫ (extensionIso T G hG).hom.app A =
      (extensionIso T F hF).hom.app A ≫ i.hom.app A) : j = extendIso T hF hG i := by
  apply monoidalIso_ext T j (extendIso T hF hG i)
  intro A
  rw [← cancel_mono ((extensionIso T G hG).hom.app A)]
  exact (h A).trans (extensionIso_natural T hF hG i A).symm

/-- A prescribed monoidal isomorphism has a unique compatible lift between canonical extensions. -/
theorem existsUnique_extendIso : ∃! j : extend T F hF ≅ extend T G hG,
    NatTrans.IsMonoidal j.hom ∧
      ∀ A, j.hom.app ((embedding T).obj A) ≫ (extensionIso T G hG).hom.app A =
        (extensionIso T F hF).hom.app A ≫ i.hom.app A := by
  refine ⟨extendIso T hF hG i, ⟨inferInstance, extensionIso_natural T hF hG i⟩, ?_⟩
  intro j hj
  let _ := hj.1
  exact extendIso_unique T hF hG i j hj.2

end IntConstruction
end CategoryTheory
