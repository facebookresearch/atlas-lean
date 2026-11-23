/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantGradedPieceMap

/-!
# Consecutive filtration stages and the graded-piece cokernel

This file isolates the consecutive-stage map whose cokernel is the horizontal
graded piece.  The zeroth lower stage is proved zero, and for positive stages
the comparison square is proved first in `MonoOver`, where its morphism is
unique.  Factoring the column projection through the cokernel and proving the
factor is an isomorphism remain the next gate.
-/

@[expose] public section

open CategoryTheory Limits CategoryTheory.Pretriangulated

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

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
  have hsource : IsZero
      ((horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageLowerIndex 0)) := by
    change IsZero ((ComplexShape.embeddingDownNat.extendFunctor C).obj
      (horizontalCompleteFilteredTotalComplex K (-1 : ℤ)))
    rw [horizontalCompleteFilteredTotalComplex_coe_of_neg K (-1) (by omega)]
    exact (ComplexShape.embeddingDownNat.extendFunctor C).map_isZero
      HomologicalComplex.isZero_zero
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
    ((MonoOver.forget _ ⋙ Over.forget _).mapIso
      (horizontalCompleteFilteredTotalMonoOverLowerSuccIso K p))

/-- Canonical cochain identification of a positive upper stage with its
natural-stage presentation. -/
noncomputable def horizontalCompleteFiltrationCochainMonoUpperSuccIso (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex (p + 1)) ≅
      (ComplexShape.embeddingDownNat.extendFunctor C).obj
        ((horizontalTotalFiltration K).toMonoOver.obj (p + 1)).obj.left :=
  (ComplexShape.embeddingDownNat.extendFunctor C).mapIso
    ((MonoOver.forget _ ⋙ Over.forget _).mapIso
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
  let f₁ := horizontalCompleteFilteredTotalMonoOverMap K
      (horizontalFirstPageIndex_le (p + 1)) ≫
    (horizontalCompleteFilteredTotalMonoOverUpperSuccIso K p).hom
  let f₂ := (horizontalCompleteFilteredTotalMonoOverLowerSuccIso K p).hom ≫
    (horizontalTotalFiltration K).toMonoOver.map (homOfLE (Nat.le_succ p))
  have hf : f₁ = f₂ := Subsingleton.elim _ _
  calc
    _ = (ComplexShape.embeddingDownNat.extendFunctor C).map f₁.hom.left := by
      dsimp [f₁, horizontalFirstPageFiltrationMap,
        horizontalCompleteFiltrationCochainDiagram,
        horizontalCompleteTotalFiltration,
        horizontalCompleteFiltrationCochainMonoUpperSuccIso]
      rw [← Functor.map_comp]
    _ = (ComplexShape.embeddingDownNat.extendFunctor C).map f₂.hom.left :=
      congrArg (fun f => (ComplexShape.embeddingDownNat.extendFunctor C).map f.hom.left) hf
    _ = _ := by
      dsimp [f₂, horizontalCompleteFiltrationCochainMonoLowerSuccIso]
      rw [Functor.map_comp]

end HomologicalComplex₂

end
