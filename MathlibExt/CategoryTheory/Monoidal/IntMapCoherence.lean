/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import MathlibExt.CategoryTheory.Monoidal.IntMapIso

/-!
# Identity and composition coherence of Int

The induced Int functors respect identity functors and composition through
monoidal natural comparison isomorphisms. Their components are identities,
and the comparisons satisfy the unit and associativity coherence laws.
This is the functorial structure underlying Joyal, Street and Verity,
Traced monoidal categories (1996), Sections 4–5,
https://doi.org/10.1017/S0305004100074338, in the symmetric specialization.
-/

@[expose] public section
universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
namespace CategoryTheory
open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal Functor.Monoidal
open scoped MonoidalCategory
variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {B : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} B]
  [MonoidalCategory C] [MonoidalCategory D] [MonoidalCategory E] [MonoidalCategory B]
  [SymmetricCategory C] [SymmetricCategory D] [SymmetricCategory E] [SymmetricCategory B]
namespace IntConstruction

/-- The identity functor leaves crossed maps unchanged. -/
@[simp] theorem mapCrossed_idFunctor {A U V W : C} (f : A ⊗ W ⟶ V ⊗ U) :
    mapCrossed (𝟭 C) f = f := by simp [mapCrossed]

/-- For braided strong monoidal functors `F : C ⥤ D` and `G : D ⥤ E`, applying `F ⋙ G` to a
crossed map agrees with applying `F` and then `G`. No trace preservation is needed. -/
theorem mapCrossed_compFunctor (F : C ⥤ D) (G : D ⥤ E) [F.Braided] [G.Braided]
    {A U V W : C} (f : A ⊗ W ⟶ V ⊗ U) :
    mapCrossed (F ⋙ G) f = mapCrossed G (mapCrossed F f) := by
  simp [mapCrossed, Functor.map_comp]

variable (T : SymmetricTrace C) (S : SymmetricTrace D) (R : SymmetricTrace E)

/-- Int of the identity functor is naturally isomorphic to the identity. -/
def mapIdIso : map T T (𝟭 C) T.preserves_id ≅ 𝟭 (IntConstruction T) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    apply hom_ext T
    change compose T (mapCrossed (𝟭 C) (hom T f)) (𝟙 _) = compose T (𝟙 _) (hom T f)
    simp only [mapCrossed_idFunctor, compose_id, id_compose])

variable (F : C ⥤ D) (G : D ⥤ E) [F.Braided] [G.Braided]
  (hF : T.Preserves S F) (hG : S.Preserves R G)

/-- For braided strong monoidal functors `F : C ⥤ D` and `G : D ⥤ E` that preserve the traces,
`hF : T.Preserves S F` and `hG : S.Preserves R G`, the comparison `L(F ⋙ G) ≅ L(F) ⋙ L(G)`
between the lift of the composite and the composite of the lifts, where `L` is `map`. Its
components are identities. -/
def mapCompIso : map T R (F ⋙ G) (hF.comp hG) ≅ map T S F hF ⋙ map S R G hG :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro X Y f
    apply hom_ext R
    change compose R (mapCrossed (F ⋙ G) (hom T f)) (𝟙 _) =
      compose R (𝟙 _) (mapCrossed G (mapCrossed F (hom T f)))
    simp only [mapCrossed_compFunctor, compose_id, id_compose])

/-- The identity comparison is componentwise the identity. -/
@[simp] theorem mapIdIso_hom_app (X : IntConstruction T) :
    (mapIdIso T).hom.app X = 𝟙 X := rfl

/-- The composition comparison is componentwise the identity. -/
@[simp] theorem mapCompIso_hom_app (X : IntConstruction T) :
    (mapCompIso T S R F G hF hG).hom.app X =
      𝟙 ((map T S F hF ⋙ map S R G hG).obj X) := rfl

set_option backward.defeqAttrib.useBackward true in
/-- The identity comparison respects the induced monoidal structure. -/
instance mapIdIso_hom_isMonoidal : NatTrans.IsMonoidal (mapIdIso T).hom where
  unit := by
    change mapPair T (𝟙 _) (𝟙 _) ≫ 𝟙 _ = 𝟙 _
    rw [mapPair_id, Category.id_comp]
  tensor X Y := by
    change mapPair T (𝟙 _) (𝟙 _) ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫ 𝟙 _
    simp only [mapPair_id, tensorHom_id, id_whiskerRight, Category.id_comp]

set_option backward.defeqAttrib.useBackward true in
/-- The composition comparison respects the induced monoidal structures. -/
instance mapCompIso_hom_isMonoidal :
    NatTrans.IsMonoidal (mapCompIso T S R F G hF hG).hom where
  unit := by
    have h := map_mapPair S R G hG (X := 𝟙_ (IntConstruction S))
      (Y := (map T S F hF).obj (𝟙_ (IntConstruction T))) (ε F) (η F)
    change mapPair R (ε (F ⋙ G)) (η (F ⋙ G)) ≫ 𝟙 _ =
      (mapPair R (ε G) (η G) : 𝟙_ (IntConstruction R) ⟶
        (map S R G hG).obj (𝟙_ (IntConstruction S))) ≫
      (map S R G hG).map (mapPair S (ε F) (η F) :
        𝟙_ (IntConstruction S) ⟶ (map T S F hF).obj (𝟙_ (IntConstruction T)))
    rw [Category.comp_id, h]
    dsimp only [map]
    rw [mapPair_comp]
    rfl
  tensor X Y := by
    have h := map_mapPair S R G hG
      (X := (map T S F hF).obj X ⊗ (map T S F hF).obj Y)
      (Y := (map T S F hF).obj (X ⊗ Y))
      (μ F X.positive Y.positive) (δ F Y.negative X.negative)
    change mapPair R (μ (F ⋙ G) X.positive Y.positive)
      (δ (F ⋙ G) Y.negative X.negative) ≫ 𝟙 _ = (𝟙 _ ⊗ₘ 𝟙 _) ≫
      (mapPair R (μ G (F.obj X.positive) (F.obj Y.positive))
        (δ G (F.obj Y.negative) (F.obj X.negative)) :
          (map T R (F ⋙ G) (hF.comp hG)).obj X ⊗ (map T R (F ⋙ G) (hF.comp hG)).obj Y ⟶
            (map S R G hG).obj ((map T S F hF).obj X ⊗ (map T S F hF).obj Y)) ≫
      (map S R G hG).map (mapPair S (μ F X.positive Y.positive) (δ F Y.negative X.negative) :
        (map T S F hF).obj X ⊗ (map T S F hF).obj Y ⟶ (map T S F hF).obj (X ⊗ Y))
    rw [h]
    dsimp only [map]
    rw [mapPair_comp]
    simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id]
    rfl

/-- Associativity of `mapCompIso` for a third such functor `H : E ⥤ B`, `hH : R.Preserves Q H`.
It compares two composites `L((F ⋙ G) ⋙ H) ≅ L(F) ⋙ (L(G) ⋙ L(H))`: the comparisons
`mapCompIso` followed by the associator of the lifts `Functor.associator (L F) (L G) (L H)`,
and the lift `mapIso (Functor.associator F G H)` of the input functors' associator followed by
the comparisons. -/
theorem mapCompIso_assoc (Q : SymmetricTrace B) (H : E ⥤ B) [H.Braided]
    (hH : R.Preserves Q H) :
    mapCompIso T R Q (F ⋙ G) H (hF.comp hG) hH ≪≫
      Functor.isoWhiskerRight (mapCompIso T S R F G hF hG) (map R Q H hH) ≪≫
        Functor.associator (map T S F hF) (map S R G hG) (map R Q H hH) =
    mapIso T Q (SymmetricTrace.Preserves.comp (hF.comp hG) hH)
      (SymmetricTrace.Preserves.comp hF (hG.comp hH)) (Functor.associator F G H) ≪≫
      mapCompIso T S Q F (G ⋙ H) hF (hG.comp hH) ≪≫
      Functor.isoWhiskerLeft (map T S F hF) (mapCompIso S R Q G H hG hH) := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  let Z : IntConstruction Q := ⟨H.obj (G.obj (F.obj X.positive)), H.obj (G.obj (F.obj X.negative))⟩
  change 𝟙 _ ≫ (map R Q H hH).map
    (𝟙 ((map S R G hG).obj ((map T S F hF).obj X))) ≫ 𝟙 _ =
    (mapPair Q (𝟙 _) (𝟙 _) : Z ⟶ Z) ≫ 𝟙 _ ≫ 𝟙 _
  rw [mapPair_id]
  simp only [Functor.map_id, Category.id_comp]
  rfl

/-- Left unit law for `mapCompIso`. The composite
`L(𝟭 C ⋙ F) ≅ L(𝟭 C) ⋙ L(F) ≅ 𝟭 _ ⋙ L(F) ≅ L(F)` of the comparison, `mapIdIso` and the left
unitor `(L F).leftUnitor` of the lift equals the lift `mapIso F.leftUnitor` of the input
functor's left unitor. -/
theorem mapCompIso_left_unit :
    mapCompIso T T S (𝟭 C) F T.preserves_id hF ≪≫
      Functor.isoWhiskerRight (mapIdIso T) (map T S F hF) ≪≫ (map T S F hF).leftUnitor =
        mapIso T S (SymmetricTrace.Preserves.comp T.preserves_id hF) hF F.leftUnitor := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  let Z : IntConstruction S := ⟨F.obj X.positive, F.obj X.negative⟩
  change 𝟙 _ ≫ (map T S F hF).map (𝟙 _) ≫ 𝟙 _ = (mapPair S (𝟙 _) (𝟙 _) : Z ⟶ Z)
  rw [mapPair_id]
  simp only [Functor.map_id, Category.id_comp]
  rfl

/-- Right unit law for `mapCompIso`. The composite
`L(F ⋙ 𝟭 D) ≅ L(F) ⋙ L(𝟭 D) ≅ L(F) ⋙ 𝟭 _ ≅ L(F)` of the comparison, `mapIdIso` and the right
unitor `(L F).rightUnitor` of the lift equals the lift `mapIso F.rightUnitor` of the input
functor's right unitor. -/
theorem mapCompIso_right_unit :
    mapCompIso T S S F (𝟭 D) hF S.preserves_id ≪≫
      Functor.isoWhiskerLeft (map T S F hF) (mapIdIso S) ≪≫ (map T S F hF).rightUnitor =
        mapIso T S (SymmetricTrace.Preserves.comp hF S.preserves_id) hF F.rightUnitor := by
  apply Iso.ext
  apply NatTrans.ext
  funext X
  let Z : IntConstruction S := ⟨F.obj X.positive, F.obj X.negative⟩
  change 𝟙 _ ≫ 𝟙 _ ≫ 𝟙 _ = (mapPair S (𝟙 _) (𝟙 _) : Z ⟶ Z)
  rw [mapPair_id]
  simp

end IntConstruction
end CategoryTheory
