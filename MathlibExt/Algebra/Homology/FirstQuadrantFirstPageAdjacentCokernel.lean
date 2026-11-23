/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageColumn
public import MathlibExt.CategoryTheory.Abelian.DiagramLemmas.CokernelCompShortExact

/-!
# Adjacent horizontal filtration quotients

Three consecutive horizontal filtration stages give a short exact sequence
of cokernels.  Its outside terms are canonically the two adjacent direct
columns.  This supplies the adjacent-quotient sequence needed for the later
connecting-homomorphism computation of the first-page differential.
-/

@[expose] public section

open CategoryTheory Limits

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace HomologicalComplex₂

variable {C : Type u} [Category.{v} C] [Abelian C]
  (K : HomologicalComplex₂ C (ComplexShape.down ℕ)
    (ComplexShape.down ℕ))

/-- The upper index for column `p` is the lower index for column `p+1`. -/
theorem horizontalFirstPageUpperIndex_eq_lowerIndex_succ (p : ℕ) :
    horizontalFirstPageUpperIndex p =
      horizontalFirstPageLowerIndex (p + 1) := by
  unfold horizontalFirstPageUpperIndex horizontalFirstPageLowerIndex
  congr 2
  omega

/-- Consecutive upper first-page indices are ordered. -/
theorem horizontalFirstPageUpperIndex_le_succ (p : ℕ) :
    horizontalFirstPageUpperIndex p ≤
      horizontalFirstPageUpperIndex (p + 1) := by
  unfold horizontalFirstPageUpperIndex
  exact WithBotTop.coe_monotone (by push_cast; omega)

/-- Identification of the common middle filtration stage in two consecutive
graded pieces. -/
noncomputable def horizontalCompleteFilteredTotalMonoOverMiddleIso (p : ℕ) :
    (horizontalCompleteTotalFiltration K).toMonoOver.obj
        (horizontalFirstPageUpperIndex p) ≅
      (horizontalCompleteTotalFiltration K).toMonoOver.obj
        (horizontalFirstPageLowerIndex (p + 1)) :=
  eqToIso (congrArg
    (fun i => (horizontalCompleteTotalFiltration K).toMonoOver.obj i)
    (horizontalFirstPageUpperIndex_eq_lowerIndex_succ p))

/-- Identification of the common middle filtration stage in two consecutive
graded pieces after forgetting to cochain complexes. -/
noncomputable def horizontalFirstPageMiddleStageIso (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex p) ≅
      (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageLowerIndex (p + 1)) :=
  (ComplexShape.embeddingDownNat.extendFunctor C).mapIso
    ((MonoOver.forget _ ⋙ Over.forget _).mapIso
      (horizontalCompleteFilteredTotalMonoOverMiddleIso K p))

/-- The middle-stage identification is coherent with the two successor-stage
identifications before forgetting the filtration subobjects. -/
theorem horizontalCompleteFilteredTotalMonoOver_middle_triangle (p : ℕ) :
    (horizontalCompleteFilteredTotalMonoOverUpperSuccIso K p).symm ≪≫
      horizontalCompleteFilteredTotalMonoOverMiddleIso K (p + 1) ≪≫
      horizontalCompleteFilteredTotalMonoOverLowerSuccIso K (p + 1) =
    Iso.refl _ := by
  apply Iso.ext
  apply Subsingleton.elim

/-- Degreewise form of the coherent middle-stage triangle after passing to
extended cochain complexes. -/
theorem horizontalFirstPageMiddleStageTriangle_f (p : ℕ) (i : ℤ) :
    (horizontalCompleteFiltrationCochainMonoUpperSuccIso K p).inv.f i ≫
      (horizontalFirstPageMiddleStageIso K (p + 1)).hom.f i ≫
      (horizontalCompleteFiltrationCochainMonoLowerSuccIso K (p + 1)).hom.f i =
    𝟙 _ := by
  let F := (MonoOver.forget (K.total (ComplexShape.down ℕ)) ⋙
    Over.forget (K.total (ComplexShape.down ℕ))) ⋙
    ComplexShape.embeddingDownNat.extendFunctor C
  have h := congrArg (fun e => (F.mapIso e).hom.f i)
    (horizontalCompleteFilteredTotalMonoOver_middle_triangle K p)
  simpa [F, horizontalCompleteFiltrationCochainMonoUpperSuccIso,
    horizontalCompleteFiltrationCochainMonoLowerSuccIso,
    horizontalFirstPageMiddleStageIso, Iso.trans_hom,
    HomologicalComplex.comp_f] using h

/-- Inclusion from filtration stage `p` to stage `p+1`, with the middle
index normalized to the upper-stage convention. -/
noncomputable def horizontalFirstPageNextFiltrationMap (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex p) ⟶
      (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex (p + 1)) :=
  (horizontalCompleteFiltrationCochainDiagram K).map
    (homOfLE (horizontalFirstPageUpperIndex_le_succ p))

/-- The canonical next-stage diagram map is the common-middle
identification followed by the consecutive-stage filtration map. -/
theorem horizontalFirstPageNextFiltrationMap_eq_middle (p : ℕ) :
    horizontalFirstPageNextFiltrationMap K p =
      (horizontalFirstPageMiddleStageIso K p).hom ≫
        horizontalFirstPageFiltrationMap K (p + 1) := by
  have hm :
      (horizontalCompleteFilteredTotalMonoOverMiddleIso K p).hom ≫
          horizontalCompleteFilteredTotalMonoOverMap K
            (horizontalFirstPageIndex_le (p + 1)) =
        horizontalCompleteFilteredTotalMonoOverMap K
          (horizontalFirstPageUpperIndex_le_succ p) :=
    Subsingleton.elim _ _
  have h := congrArg (fun m =>
    (ComplexShape.embeddingDownNat.extendFunctor C).map m.hom.left) hm
  symm
  simpa [horizontalFirstPageNextFiltrationMap,
    horizontalFirstPageMiddleStageIso,
    horizontalFirstPageFiltrationMap,
    horizontalCompleteFiltrationCochainDiagram,
    horizontalCompleteTotalFiltration, Functor.map_comp] using h

noncomputable instance horizontalFirstPageNextFiltrationMap_mono (p : ℕ) :
    Mono (horizontalFirstPageNextFiltrationMap K p) := by
  unfold horizontalFirstPageNextFiltrationMap
  infer_instance

/-- Short complex of the three cokernels attached to the consecutive
filtration maps `F_{p-1} → F_p → F_{p+1}`. -/
noncomputable abbrev horizontalFirstPageAdjacentCokernelShortComplex (p : ℕ) :
    ShortComplex (CochainComplex C ℤ) :=
  CategoryTheory.cokernelCompShortComplex
    (horizontalFirstPageFiltrationMap K p)
    (horizontalFirstPageNextFiltrationMap K p)

/-- The adjacent-cokernel sequence is short exact. -/
theorem horizontalFirstPageAdjacentCokernelShortExact (p : ℕ) :
    (horizontalFirstPageAdjacentCokernelShortComplex K p).ShortExact :=
  CategoryTheory.cokernelCompShortComplex_shortExact
    (horizontalFirstPageFiltrationMap K p)
    (horizontalFirstPageNextFiltrationMap K p)

/-- Precomposing a filtration map by the middle-stage identification does not
change its cokernel. -/
noncomputable def horizontalFirstPageNextCokernelIso (p : ℕ) :
    cokernel (horizontalFirstPageNextFiltrationMap K p) ≅
      cokernel (horizontalFirstPageFiltrationMap K (p + 1)) :=
  cokernel.mapIso (horizontalFirstPageNextFiltrationMap K p)
    (horizontalFirstPageFiltrationMap K (p + 1))
    (horizontalFirstPageMiddleStageIso K p) (Iso.refl _) (by
      simpa using horizontalFirstPageNextFiltrationMap_eq_middle K p)

/-- Identification of the left endpoint with column `p`. -/
noncomputable def horizontalFirstPageAdjacentLeftIso (p : ℕ) :
    (horizontalFirstPageAdjacentCokernelShortComplex K p).X₁ ≅
      horizontalDirectColumnCochain K p :=
  horizontalFirstPageCokernelIso K p

/-- Identification of the right endpoint with column `p+1`. -/
noncomputable def horizontalFirstPageAdjacentRightIso (p : ℕ) :
    (horizontalFirstPageAdjacentCokernelShortComplex K p).X₃ ≅
      horizontalDirectColumnCochain K (p + 1) :=
  horizontalFirstPageNextCokernelIso K p ≪≫
    horizontalFirstPageCokernelIso K (p + 1)

/-- The adjacent-cokernel sequence with its outside terms replaced by the
canonical direct-column presentations. -/
noncomputable def horizontalFirstPageAdjacentDirectShortComplex (p : ℕ) :
    ShortComplex (CochainComplex C ℤ) := by
  let S := horizontalFirstPageAdjacentCokernelShortComplex K p
  refine ShortComplex.mk
    ((horizontalFirstPageAdjacentLeftIso K p).inv ≫ S.f)
    (S.g ≫ (horizontalFirstPageAdjacentRightIso K p).hom) ?_
  change ((horizontalFirstPageAdjacentLeftIso K p).inv ≫ S.f) ≫
      (S.g ≫ (horizontalFirstPageAdjacentRightIso K p).hom) = 0
  calc
    _ = (horizontalFirstPageAdjacentLeftIso K p).inv ≫
        ((S.f ≫ S.g) ≫
          (horizontalFirstPageAdjacentRightIso K p).hom) := by
      simp only [Category.assoc]
    _ = 0 := by rw [S.zero, zero_comp, comp_zero]

/-- Isomorphism from the canonical cokernel-composition sequence to its
direct-column presentation. -/
noncomputable def horizontalFirstPageAdjacentShortComplexIso (p : ℕ) :
    horizontalFirstPageAdjacentCokernelShortComplex K p ≅
      horizontalFirstPageAdjacentDirectShortComplex K p :=
  ShortComplex.isoMk
    (horizontalFirstPageAdjacentLeftIso K p) (Iso.refl _)
    (horizontalFirstPageAdjacentRightIso K p)
    (by simp [horizontalFirstPageAdjacentDirectShortComplex])
    (by simp [horizontalFirstPageAdjacentDirectShortComplex])

/-- The adjacent direct-column sequence is short exact. -/
theorem horizontalFirstPageAdjacentDirectShortExact (p : ℕ) :
    (horizontalFirstPageAdjacentDirectShortComplex K p).ShortExact :=
  ShortComplex.shortExact_of_iso
    (horizontalFirstPageAdjacentShortComplexIso K p)
    (horizontalFirstPageAdjacentCokernelShortExact K p)

end HomologicalComplex₂

end
