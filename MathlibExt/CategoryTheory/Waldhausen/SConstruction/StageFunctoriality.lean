/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.StageWeakCategory
public import MathlibExt.CategoryTheory.Waldhausen.Exact
public import MathlibExt.CategoryTheory.ExactCategory.Functor

/-!
# Exact-stage functoriality

For exact categories `C` and `D` equipped with their local standard
Waldhausen structures (`ExactCategory.waldhausenCategory`), an additive
exact functor `F : C ⥤ D` induces `mapStage F n : Stage C n ⥤ Stage D n`
by postcomposition, and `mapStageWeak F n` by restriction to the pointwise
weak-equivalence categories.

Reuse map: `ObjectProperty.FullSubcategory.lift` for the bundle,
`ShortComplex.map` for the triple complex, `Functor.map_admissibleExact`
for exactness preservation, the pushout/cokernel bridge
(`isAdmissibleExact_of_isCofibrationSequence` /
`isCofibrationSequence_of_isAdmissibleExact`) for the stage condition,
`F.map_isZero` for diagonals, `reindexStage` / `reindexStageWeak` for
commutation, and `inferInstance` for `IsIso (F.map _)` preservation.

No general Waldhausen-functor class is introduced, and no preservation of
non-isomorphism weak equivalences is inferred.

Nonclaims: no nerve, realization, additivity theorem, K-theory, G-theory,
spectrum, or Q/S comparison.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v₁ u₁ v₂ u₂ v₃ u₃

namespace CategoryTheory.Waldhausen.SConstruction

variable (C : Type u₁) [Category.{v₁} C] [Preadditive C] [Limits.HasZeroObject C]
  [HasBinaryBiproducts C] [ExactCategory C]
variable (D : Type u₂) [Category.{v₂} D] [Preadditive D] [Limits.HasZeroObject D]
  [HasBinaryBiproducts D] [ExactCategory D]
variable (F : C ⥤ D) [F.Additive] [Functor.IsExact F] (n : ℕ)

/-- Postcomposition preserves the finite-stage predicate, using
`F.map_isZero` on diagonals and the admissible-exact bridge on triples. -/
theorem isStage_postcomp (A : Ar n ⥤ C)
    (hA : @IsStage C _ _ (ExactCategory.waldhausenCategory C) n A) :
    @IsStage D _ _ (ExactCategory.waldhausenCategory D) n (A ⋙ F) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  refine { diag_isZero := ?_, cofiber_triple := ?_ }
  · intro i
    exact F.map_isZero (hA.diag_isZero i)
  · intro i j k hij hjk
    have hSeqC : @IsCofibrationSequence C _ _
        (ExactCategory.waldhausenCategory C) _ _ _
        (A.map (horiz hij hjk)) (A.map (vert hij hjk)) :=
      hA.cofiber_triple hij hjk
    have wC : A.map (horiz hij hjk) ≫ A.map (vert hij hjk) = 0 :=
      hSeqC.comp_eq_zero
    let S : ShortComplex C := ShortComplex.mk _ _ wC
    have hAdm : ExactCategory.IsAdmissibleExact S :=
      ExactCategory.isAdmissibleExact_of_isCofibrationSequence (C := C) (S := S)
        hSeqC
    have hAdmF : ExactCategory.IsAdmissibleExact (S.map F) :=
      Functor.map_admissibleExact F S hAdm
    have hSeqD : @IsCofibrationSequence D _ _
        (ExactCategory.waldhausenCategory D) _ _ _
        ((S.map F).f) ((S.map F).g) :=
      ExactCategory.isCofibrationSequence_of_isAdmissibleExact hAdmF
    exact hSeqD

/-- Exact-stage functoriality by postcomposition, via the full-subcategory lift.

`C` and `D` carry their local standard Waldhausen structures. -/
def mapStage :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      Stage C n ⥤ Stage D n) := by
  letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  exact (stageProperty D n).lift
    (forget C n ⋙ (Functor.whiskeringRight _ _ _).obj F)
    (fun X => isStage_postcomp C D F n X.obj X.property)

/-- Underlying diagram of `mapStage`: postcomposition with `F`. -/
@[simp]
theorem mapStage_obj (X : (letI : WaldhausenCategoryWithoutGluing C :=
    ExactCategory.waldhausenCategory C; Stage C n)) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      (forget D n).obj ((mapStage C D F n).obj X)) = X.obj ⋙ F := by
  rfl

/-- Underlying map of `mapStage`: postcomposition with `F`. -/
@[simp]
theorem mapStage_map {X Y : (letI : WaldhausenCategoryWithoutGluing C :=
    ExactCategory.waldhausenCategory C; Stage C n)}
    (φ : X ⟶ Y) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      (forget D n).map ((mapStage C D F n).map φ)) =
      (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
        Functor.whiskerRight ((forget C n).map φ) F) := by
  rfl

/-- `mapStage` preserves pointwise stage weak equivalences, since standard
weak equivalences are isomorphisms and functors map isomorphisms
(`inferInstance`). -/
theorem stageWeak_of_mapStage
    {X Y : (letI : WaldhausenCategoryWithoutGluing C :=
      ExactCategory.waldhausenCategory C; Stage C n)}
    (φ : X ⟶ Y)
    (h : (letI : WaldhausenCategoryWithoutGluing C :=
      ExactCategory.waldhausenCategory C; stageWeak C n φ)) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      stageWeak D n ((mapStage C D F n).map φ)) := by
  let : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  let : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  rw [mem_stageWeak] at h ⊢
  intro a
  have hIso : IsIso (((forget C n).map φ).app a) := h a
  have hIsoF : IsIso (F.map (((forget C n).map φ).app a)) := inferInstance
  exact hIsoF

/-- Weak-equivalence stage functoriality by restriction of `mapStage`. -/
def mapStageWeak :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      StageWeakCategory C n ⥤ StageWeakCategory D n) := by
  letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C
  letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D
  exact
    { obj := fun X => ⟨(mapStage C D F n).obj X.obj⟩
      map := fun {X Y} φ =>
        ⟨(mapStage C D F n).map φ.hom,
          stageWeak_of_mapStage C D F n φ.hom φ.property⟩
      map_id := fun X => by
        apply WideSubcategory.hom_ext
        simp
      map_comp := fun {X Y Z} φ ψ => by
        apply WideSubcategory.hom_ext
        simp }

/-- Inclusion commutes with exact-stage functoriality. -/
@[simp]
theorem mapStageWeak_inclusion :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      mapStageWeak C D F n ⋙ stageWeakInclusion D n =
        stageWeakInclusion C n ⋙ mapStage C D F n) := by
  rfl

/-- Postcomposition commutes with reindexing: pre- and post-whiskering
associate strictly. -/
@[simp]
theorem mapStage_reindex {a b : SimplexCategory} (f : a ⟶ b) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      reindexStage (C := C) f ⋙ mapStage C D F a.len =
        mapStage C D F b.len ⋙ reindexStage (C := D) f) := by
  rfl

/-- Weak restriction commutes with weak reindexing. -/
@[simp]
theorem mapStageWeak_reindex {a b : SimplexCategory} (f : a ⟶ b) :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      reindexStageWeak C f ⋙ mapStageWeak C D F a.len =
        mapStageWeak C D F b.len ⋙ reindexStageWeak D f) := by
  rfl

/-- Identity additive exact functor induces the identity stage functor. -/
@[simp]
theorem mapStage_id :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      mapStage C C (𝟭 C) n = 𝟭 (Stage C n)) := by
  rfl

/-- Composite additive exact functors induce composite stage functors. -/
@[simp]
theorem mapStage_comp (E : Type u₃) [Category.{v₃} E] [Preadditive E]
    [Limits.HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
    (G : D ⥤ E) [G.Additive] [Functor.IsExact G] :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E;
      mapStage C E (F ⋙ G) n =
        mapStage C D F n ⋙ mapStage D E G n) := by
  rfl

/-- Identity additive exact functor induces the identity weak-stage functor. -/
@[simp]
theorem mapStageWeak_id :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      mapStageWeak C C (𝟭 C) n = 𝟭 (StageWeakCategory C n)) := by
  rfl

/-- Composite additive exact functors induce composite weak-stage functors. -/
@[simp]
theorem mapStageWeak_comp (E : Type u₃) [Category.{v₃} E] [Preadditive E]
    [Limits.HasZeroObject E] [HasBinaryBiproducts E] [ExactCategory E]
    (G : D ⥤ E) [G.Additive] [Functor.IsExact G] :
    (letI : WaldhausenCategoryWithoutGluing C := ExactCategory.waldhausenCategory C;
      letI : WaldhausenCategoryWithoutGluing D := ExactCategory.waldhausenCategory D;
      letI : WaldhausenCategoryWithoutGluing E := ExactCategory.waldhausenCategory E;
      mapStageWeak C E (F ⋙ G) n =
        mapStageWeak C D F n ⋙ mapStageWeak D E G n) := by
  rfl

end CategoryTheory.Waldhausen.SConstruction
