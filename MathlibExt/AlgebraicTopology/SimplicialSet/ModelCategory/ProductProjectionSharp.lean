/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.FullProductWeakEquivalences
import MathlibExt.CategoryTheory.MorphismProperty.SharpOverPullbackRecognition

/-!
# Genuine sharpness of every full original product projection

Every native pullback of `X ⊗ B ⟶ B` is identified with the SAME
original product `X ⊗ V`. The full inverse and both projection equations
are retained. Every original weak over-map is consequently preserved,
so the original product projection is sharp without a Kan condition
on either original coordinate.
-/

noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory
open scoped Simplicial

namespace SSet.ProductProjectionSharp

/-- The entire original product presentation of the SAME native over-pullback. -/
def pullbackIso (X B : SSet.{u}) (V : Over B) :
    X ⊗ V.left ≅ ((Over.pullback (snd X B)).obj V).left where
  hom := pullback.lift (snd X V.left)
    (lift (fst X V.left) (snd X V.left ≫ V.hom)) (by rw [lift_snd])
  inv := lift (pullback.snd V.hom (snd X B) ≫ fst X B) (pullback.fst V.hom (snd X B))
  hom_inv_id := by
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, pullback.lift_snd_assoc, lift_fst]
      exact Category.id_comp _ |>.symm
    · simp only [Category.assoc, lift_snd, pullback.lift_fst]
      exact Category.id_comp _ |>.symm
  inv_hom_id := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, lift_snd, Category.id_comp]
    · simp only [Category.assoc, pullback.lift_snd, Category.id_comp]
      apply CartesianMonoidalCategory.hom_ext
      · simp only [Category.assoc, lift_fst, lift_fst]
      · simp only [Category.assoc, lift_snd, lift_snd]
        exact pullback.condition (f := V.hom) (g := snd X B)

/-- The forward comparison retains the SAME original total-space projection. -/
@[reassoc]
lemma pullbackIso_hom_fst (X B : SSet.{u}) (V : Over B) :
    (pullbackIso X B V).hom ≫ pullback.fst V.hom (snd X B) = snd X V.left :=
  pullback.lift_fst _ _ _

/-- Its other projection retains the SAME full original coefficient and base maps. -/
@[reassoc]
lemma pullbackIso_hom_snd (X B : SSet.{u}) (V : Over B) :
    (pullbackIso X B V).hom ≫ pullback.snd V.hom (snd X B) =
      lift (fst X V.left) (snd X V.left ≫ V.hom) := pullback.lift_snd _ _ _

/-- The native pullback map retains the SAME complete original tensor map
under the explicit two whole product identifications. -/
lemma pullbackIso_natural (X B : SSet.{u}) {V W : Over B} (f : V ⟶ W) :
    (pullbackIso X B V).hom ≫ ((Over.pullback (snd X B)).map f).left =
      (X ◁ f.left) ≫ (pullbackIso X B W).hom := by
  apply pullback.hom_ext
  · simp only [Over.pullback_map_left, Category.assoc, pullback.lift_fst,
      pullbackIso_hom_fst_assoc, pullbackIso_hom_fst, whiskerLeft_snd]
  · simp only [Over.pullback_map_left, Category.assoc, pullback.lift_snd,
      pullbackIso_hom_snd]
    apply CartesianMonoidalCategory.hom_ext
    · simp only [Category.assoc, lift_fst, whiskerLeft_fst]
    · simp only [Category.assoc, lift_snd, whiskerLeft_snd_assoc]
      rw [f.w]

/-- The SAME original native over-pullback preserves EVERY full original
weak map, with no finiteness or Kan condition on the fixed coefficient. -/
theorem pullback_map_weak (X B : SSet.{u}) {V W : Over B} (f : V ⟶ W)
    (hf : realizationWeakEquivalences f.left) :
    realizationWeakEquivalences ((Over.pullback (snd X B)).map f).left :=
  (realizationWeakEquivalences.arrow_mk_iso_iff
    (Arrow.isoMk' (X ◁ f.left) ((Over.pullback (snd X B)).map f).left
      (pullbackIso X B V) (pullbackIso X B W) (pullbackIso_natural X B f))).mp
    (realizationWeakEquivalences.whiskerLeft X f.left hf)

/-- EVERY full original product projection is sharp, even with non-Kan
original coefficient and non-Kan original base. -/
theorem projection_sharp (X B : SSet.{u}) :
    MorphismProperty.sharpMaps realizationWeakEquivalences (snd X B) :=
  (MorphismProperty.sharpMaps_iff_overPullback (C := SSet.{u}) realizationWeakEquivalences (snd X B)).mpr
    (pullback_map_weak X B)

end SSet.ProductProjectionSharp
