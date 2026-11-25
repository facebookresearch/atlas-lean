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
# Consecutive filtration stages and the graded-piece cokernel

For an ℕ-indexed downward bicomplex in a preadditive category with a zero
object and finite coproducts, consecutive horizontal filtration stages are
linked by their filtration morphism.

The lower stage in column zero is zero, so the column-projection composite
vanishes. At positive stages, the natural-stage comparison square commutes
in `MonoOver` and remains commutative after chain-to-cochain extension.
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

/-- The consecutive-stage map defining the `p`th horizontal graded piece. -/
noncomputable def horizontalFirstPageFiltrationMap (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageLowerIndex p) ⟶
      (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex p) :=
  (horizontalCompleteFiltrationCochainDiagram K).map
    (homOfLE (horizontalFirstPageIndex_le p))

/-- In column zero, the consecutive-stage map starts at the zero complex, so
its composite with the graded-piece projection is zero. -/
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

theorem horizontalCompleteFilteredTotalMonoOver_lower_succ (p : ℕ) :
    horizontalCompleteFilteredTotalMonoOver K
        (horizontalFirstPageLowerIndex (p + 1)) =
      (horizontalTotalFiltration K).toMonoOver.obj p := by
  unfold horizontalCompleteFilteredTotalMonoOver horizontalFirstPageLowerIndex
  simp only [WithBotTop.rec_coe]
  rw [ite_eq_left (show 0 ≤ ((p + 1 : ℕ) : ℤ) - 1 by omega)]
  congr 2
  omega

theorem horizontalCompleteFilteredTotalMonoOver_upper_succ (p : ℕ) :
    horizontalCompleteFilteredTotalMonoOver K
        (horizontalFirstPageUpperIndex (p + 1)) =
      (horizontalTotalFiltration K).toMonoOver.obj (p + 1) := by
  unfold horizontalCompleteFilteredTotalMonoOver horizontalFirstPageUpperIndex
  simp only [WithBotTop.rec_coe]
  rw [ite_eq_left (show 0 ≤ ((p + 1 : ℕ) : ℤ) by omega)]
  congr 2

noncomputable def horizontalCompleteFilteredTotalMonoOverLowerSuccIso (p : ℕ) :
    horizontalCompleteFilteredTotalMonoOver K
        (horizontalFirstPageLowerIndex (p + 1)) ≅
      (horizontalTotalFiltration K).toMonoOver.obj p :=
  eqToIso (horizontalCompleteFilteredTotalMonoOver_lower_succ K p)

noncomputable def horizontalCompleteFilteredTotalMonoOverUpperSuccIso (p : ℕ) :
    horizontalCompleteFilteredTotalMonoOver K
        (horizontalFirstPageUpperIndex (p + 1)) ≅
      (horizontalTotalFiltration K).toMonoOver.obj (p + 1) :=
  eqToIso (horizontalCompleteFilteredTotalMonoOver_upper_succ K p)

/-- The complete consecutive-stage map agrees with the original natural-stage
map after the canonical source and target identifications. -/
theorem horizontalCompleteFilteredTotalMonoOverMap_succ (p : ℕ) :
    horizontalCompleteFilteredTotalMonoOverMap K
        (horizontalFirstPageIndex_le (p + 1)) ≫
        (horizontalCompleteFilteredTotalMonoOverUpperSuccIso K p).hom =
      (horizontalCompleteFilteredTotalMonoOverLowerSuccIso K p).hom ≫
        (horizontalTotalFiltration K).toMonoOver.map
          (homOfLE (Nat.le_succ p)) := by
  apply Subsingleton.elim

/-- Canonical cochain identification of a positive lower stage with its
natural-stage presentation. -/
noncomputable def horizontalCompleteFiltrationCochainMonoLowerSuccIso (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageLowerIndex (p + 1)) ≅
      (ComplexShape.embeddingDownNat.extendFunctor C).obj
        ((horizontalTotalFiltration K).toMonoOver.obj p).obj.left :=
  (ComplexShape.embeddingDownNat.extendFunctor C).mapIso
    ((MonoOver.forget (K.total (ComplexShape.down ℕ)) ⋙
      Over.forget (K.total (ComplexShape.down ℕ))).mapIso
      (horizontalCompleteFilteredTotalMonoOverLowerSuccIso K p))

/-- Canonical cochain identification of a positive upper stage with its
natural-stage presentation. -/
noncomputable def horizontalCompleteFiltrationCochainMonoUpperSuccIso (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex (p + 1)) ≅
      (ComplexShape.embeddingDownNat.extendFunctor C).obj
        ((horizontalTotalFiltration K).toMonoOver.obj (p + 1)).obj.left :=
  (ComplexShape.embeddingDownNat.extendFunctor C).mapIso
    ((MonoOver.forget (K.total (ComplexShape.down ℕ)) ⋙
      Over.forget (K.total (ComplexShape.down ℕ))).mapIso
      (horizontalCompleteFilteredTotalMonoOverUpperSuccIso K p))

/-- The positive consecutive-stage comparison square after chain-to-cochain
extension. -/
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
    horizontalCompleteFiltrationCochainMonoUpperSuccIso,
    horizontalCompleteFiltrationCochainMonoLowerSuccIso,
    horizontalCompleteTotalFiltration_diagram_map,
    horizontalCompleteTotalFiltration_diagram_obj, horizontalCompleteFilteredTotalComplex,
    horizontalCompleteFilteredTotalMap, MonoOver.forget, ObjectProperty.ι_obj,
    ObjectProperty.ι_map, Over.forget_obj, Over.forget_map] using hmap

end HomologicalComplex₂

end
