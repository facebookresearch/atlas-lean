/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantGradedPieceMap

/-!
# Consecutive horizontal filtration stages and their comparisons

Let `K` be a first-quadrant bicomplex in a preadditive category with a zero object and finite
coproducts. The first-page filtration map for column `p` joins its lower and upper complete
stages.

For `p=0`, the lower stage is the negative stage `-1`, hence zero, and the composite with the
direct-column projection vanishes. For column `p+1`, the lower and upper stages identify with
natural stages `p` and `p+1`. Their complete-stage map agrees with the natural filtration
inclusion, also after chain-to-cochain extension.
-/

@[expose] public section

open CategoryTheory Limits CategoryTheory.Pretriangulated

noncomputable section

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasZeroObject C] [HasFiniteCoproducts C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- The consecutive-stage map of a horizontal first-page window.

Map the complete lower filtration stage of column `p` to its complete upper stage. -/
noncomputable def horizontalFirstPageFiltrationMap (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageLowerIndex p) ⟶
      (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex p) :=
  (horizontalCompleteFiltrationCochainDiagram K).map
    (homOfLE (horizontalFirstPageIndex_le p))

/-- The zero-column filtration map followed by direct-column projection.

The lower zero-column stage is zero, so its filtration map followed by the direct-column
projection is the zero chain map. -/
theorem horizontalFirstPageFiltrationMap_zero_projection :
    horizontalFirstPageFiltrationMap K 0 ≫
      horizontalDirectColumnProjectionMap K 0 = 0 := by
  let E : ChainComplex C ℕ ⥤ CochainComplex C ℤ :=
    ComplexShape.embeddingDownNat.extendFunctor C
  have hsource : IsZero
      ((horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageLowerIndex 0)) := by
    change IsZero (E.obj (horizontalCompleteFilteredTotalComplex K (-1 : ℤ)))
    rw [horizontalCompleteFilteredTotalComplex_coe_of_neg K (-1) (by omega)]
    exact E.map_isZero HomologicalComplex.isZero_zero
  exact hsource.eq_of_src _ _

/-- The natural lower stage of a positive first-page window.

The complete lower subobject for column `p+1` is natural filtration stage `p`. -/
theorem horizontalCompleteFilteredTotalMonoOver_lower_succ (p : ℕ) :
    horizontalCompleteFilteredTotalMonoOver K
        (horizontalFirstPageLowerIndex (p + 1)) =
      (horizontalTotalFiltration K).toMonoOver.obj p := by
  unfold horizontalCompleteFilteredTotalMonoOver horizontalFirstPageLowerIndex
  simp only [WithBotTop.rec_coe]
  rw [ite_eq_left (show 0 ≤ ((p + 1 : ℕ) : ℤ) - 1 by omega)]
  congr 2
  omega

/-- The natural upper stage of a positive first-page window.

The complete upper subobject for column `p+1` is natural filtration stage `p+1`. -/
theorem horizontalCompleteFilteredTotalMonoOver_upper_succ (p : ℕ) :
    horizontalCompleteFilteredTotalMonoOver K
        (horizontalFirstPageUpperIndex (p + 1)) =
      (horizontalTotalFiltration K).toMonoOver.obj (p + 1) := by
  unfold horizontalCompleteFilteredTotalMonoOver horizontalFirstPageUpperIndex
  simp only [WithBotTop.rec_coe]
  rw [ite_eq_left (show 0 ≤ ((p + 1 : ℕ) : ℤ) by omega)]
  congr 2

/-- The lower-subobject comparison for a positive first-page window.

The positive lower complete stage is canonically isomorphic to natural stage `p`. -/
noncomputable def horizontalCompleteFilteredTotalMonoOverLowerSuccIso (p : ℕ) :
    horizontalCompleteFilteredTotalMonoOver K
        (horizontalFirstPageLowerIndex (p + 1)) ≅
      (horizontalTotalFiltration K).toMonoOver.obj p :=
  eqToIso (horizontalCompleteFilteredTotalMonoOver_lower_succ K p)

/-- The upper-subobject comparison for a positive first-page window.

The positive upper complete stage is canonically isomorphic to natural stage `p+1`. -/
noncomputable def horizontalCompleteFilteredTotalMonoOverUpperSuccIso (p : ℕ) :
    horizontalCompleteFilteredTotalMonoOver K
        (horizontalFirstPageUpperIndex (p + 1)) ≅
      (horizontalTotalFiltration K).toMonoOver.obj (p + 1) :=
  eqToIso (horizontalCompleteFilteredTotalMonoOver_upper_succ K p)

/-- The positive complete filtration map in natural-stage coordinates.

The complete map of column `p+1` commutes with its lower and upper subobject comparisons and
the natural inclusion `F_p → F_(p+1)`. -/
theorem horizontalCompleteFilteredTotalMonoOverMap_succ (p : ℕ) :
    horizontalCompleteFilteredTotalMonoOverMap K
        (horizontalFirstPageIndex_le (p + 1)) ≫
        (horizontalCompleteFilteredTotalMonoOverUpperSuccIso K p).hom =
      (horizontalCompleteFilteredTotalMonoOverLowerSuccIso K p).hom ≫
        (horizontalTotalFiltration K).toMonoOver.map
          (homOfLE (Nat.le_succ p)) := by
  apply Subsingleton.elim

/-- The lower cochain-stage comparison of a positive first-page window.

Forget the lower subobject comparison and extend to identify the lower complete cochain stage
with the extension of natural stage `p`. -/
noncomputable def horizontalCompleteFiltrationCochainMonoLowerSuccIso (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageLowerIndex (p + 1)) ≅
      (ComplexShape.embeddingDownNat.extendFunctor C).obj
        ((horizontalTotalFiltration K).toMonoOver.obj p).obj.left :=
  (ComplexShape.embeddingDownNat.extendFunctor C).mapIso
    ((MonoOver.forget (K.total (ComplexShape.down ℕ)) ⋙
      Over.forget (K.total (ComplexShape.down ℕ))).mapIso
      (horizontalCompleteFilteredTotalMonoOverLowerSuccIso K p))

/-- The upper cochain-stage comparison of a positive first-page window.

Forget the upper subobject comparison and extend to identify the upper complete cochain stage
with the extension of natural stage `p+1`. -/
noncomputable def horizontalCompleteFiltrationCochainMonoUpperSuccIso (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex (p + 1)) ≅
      (ComplexShape.embeddingDownNat.extendFunctor C).obj
        ((horizontalTotalFiltration K).toMonoOver.obj (p + 1)).obj.left :=
  (ComplexShape.embeddingDownNat.extendFunctor C).mapIso
    ((MonoOver.forget (K.total (ComplexShape.down ℕ)) ⋙
      Over.forget (K.total (ComplexShape.down ℕ))).mapIso
      (horizontalCompleteFilteredTotalMonoOverUpperSuccIso K p))

/-- The positive filtration comparison square after cochain extension.

The complete first-page map followed by its upper cochain comparison equals the lower
comparison followed by the extended natural-stage inclusion. -/
theorem horizontalFirstPageFiltrationMap_succ_monoIso (p : ℕ) :
    horizontalFirstPageFiltrationMap K (p + 1) ≫
        (horizontalCompleteFiltrationCochainMonoUpperSuccIso K p).hom =
      (horizontalCompleteFiltrationCochainMonoLowerSuccIso K p).hom ≫
        (ComplexShape.embeddingDownNat.extendFunctor C).map
          ((horizontalTotalFiltration K).toMonoOver.map
            (homOfLE (Nat.le_succ p))).hom.left := by
  let T : ChainComplex C ℕ := K.total (ComplexShape.down ℕ)
  let A : MonoOver T := horizontalCompleteFilteredTotalMonoOver K
    (horizontalFirstPageLowerIndex (p + 1))
  let B : MonoOver T := (horizontalTotalFiltration K).toMonoOver.obj (p + 1)
  let G : MonoOver T ⥤ ChainComplex C ℕ := MonoOver.forget T ⋙ Over.forget T
  let E : ChainComplex C ℕ ⥤ CochainComplex C ℤ :=
    ComplexShape.embeddingDownNat.extendFunctor C
  let H : MonoOver T ⥤ CochainComplex C ℤ := G ⋙ E
  let f₁ : A ⟶ B := horizontalCompleteFilteredTotalMonoOverMap K
      (horizontalFirstPageIndex_le (p + 1)) ≫
    (horizontalCompleteFilteredTotalMonoOverUpperSuccIso K p).hom
  let f₂ : A ⟶ B := (horizontalCompleteFilteredTotalMonoOverLowerSuccIso K p).hom ≫
    (horizontalTotalFiltration K).toMonoOver.map (homOfLE (Nat.le_succ p))
  have hf : f₁ = f₂ := horizontalCompleteFilteredTotalMonoOverMap_succ K p
  have hmap :
      H.map (horizontalCompleteFilteredTotalMonoOverMap K
          (horizontalFirstPageIndex_le (p + 1))) ≫
        H.map (horizontalCompleteFilteredTotalMonoOverUpperSuccIso K p).hom =
      H.map (horizontalCompleteFilteredTotalMonoOverLowerSuccIso K p).hom ≫
        H.map ((horizontalTotalFiltration K).toMonoOver.map
          (homOfLE (Nat.le_succ p))) := by
    calc
      _ = H.map f₁ := (H.map_comp
        (horizontalCompleteFilteredTotalMonoOverMap K
          (horizontalFirstPageIndex_le (p + 1)))
        (horizontalCompleteFilteredTotalMonoOverUpperSuccIso K p).hom).symm
      _ = H.map f₂ := congrArg (fun f : A ⟶ B => H.map f) hf
      _ = _ := H.map_comp
        (horizontalCompleteFilteredTotalMonoOverLowerSuccIso K p).hom
        ((horizontalTotalFiltration K).toMonoOver.map (homOfLE (Nat.le_succ p)))
  simpa only [H, G, E, Functor.comp_map, Functor.comp_obj, Functor.mapIso_hom,
    horizontalFirstPageFiltrationMap, horizontalCompleteFiltrationCochainDiagram,
    horizontalCompleteTotalFiltration,
    horizontalCompleteFiltrationCochainMonoUpperSuccIso,
    horizontalCompleteFiltrationCochainMonoLowerSuccIso,
    horizontalCompleteTotalFiltration_diagram_map,
    horizontalCompleteTotalFiltration_diagram_obj, horizontalCompleteFilteredTotalComplex,
    horizontalCompleteFilteredTotalMap, MonoOver.forget, ObjectProperty.ι_obj,
    ObjectProperty.ι_map, Over.forget_obj, Over.forget_map] using hmap

end HomologicalComplex₂

end
