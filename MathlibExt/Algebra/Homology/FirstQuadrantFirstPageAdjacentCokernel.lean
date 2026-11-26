/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua

module

public import MathlibExt.Algebra.Homology.FirstQuadrantFirstPageColumn
public import MathlibExt.CategoryTheory.Abelian.DiagramLemmas.CokernelCompShortExact

/-!
# The short exact sequence of two adjacent horizontal column quotients

Let K be a nonnegative homological bicomplex in an abelian category C,
and reindex its complete horizontal filtration as integer cochain
complexes. The three stages F_(p−1) → F_p → F_(p+1) are monic.

Their quotient sequence is short exact:
0 → coker(F_(p−1) → F_p)
  → coker(F_(p−1) → F_(p+1))
  → coker(F_p → F_(p+1)) → 0.
The outside terms identify with the signed shifted columns D_p and
D_(p+1). Transport gives a short exact sequence with these direct
columns as endpoints and the same middle quotient.
The common stage F_p and its successor presentations are coherently
identified before and after passage to cochain complexes.
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

/-- For p ∈ ℕ, the finite EInt indices satisfy
upper(p) = lower(p+1), since upper(p)=p and lower(p+1)=(p+1)−1.
Thus adjacent filtration intervals share the same middle stage. -/
theorem horizontalFirstPageUpperIndex_eq_lowerIndex_succ (p : ℕ) :
    horizontalFirstPageUpperIndex p =
      horizontalFirstPageLowerIndex (p + 1) := by
  unfold horizontalFirstPageUpperIndex horizontalFirstPageLowerIndex
  congr 2
  omega

/-- For p ∈ ℕ, the finite first-page upper indices satisfy
upper(p) ≤ upper(p+1) in EInt.
They are the integers p and p+1, respectively. -/
theorem horizontalFirstPageUpperIndex_le_succ (p : ℕ) :
    horizontalFirstPageUpperIndex p ≤
      horizontalFirstPageUpperIndex (p + 1) := by
  unfold horizontalFirstPageUpperIndex
  exact WithBotTop.coe_monotone (by push_cast; omega)

/-- For a nonnegative homological bicomplex K in an abelian
category, the complete filtration subobject at upper(p) is
isomorphic to the subobject at lower(p+1).
Both are the stage F_p included in Tot(K), and the identification
uses upper(p)=lower(p+1). -/
noncomputable def horizontalCompleteFilteredTotalMonoOverMiddleIso (p : ℕ) :
    (horizontalCompleteTotalFiltration K).toMonoOver.obj
        (horizontalFirstPageUpperIndex p) ≅
      (horizontalCompleteTotalFiltration K).toMonoOver.obj
        (horizontalFirstPageLowerIndex (p + 1)) :=
  eqToIso (congrArg
    (fun i => (horizontalCompleteTotalFiltration K).toMonoOver.obj i)
    (horizontalFirstPageUpperIndex_eq_lowerIndex_succ p))

/-- For a nonnegative homological bicomplex K in an abelian
category, reindexing chain degree n as cochain degree −n identifies
the complete cochain stages at upper(p) and lower(p+1).
Both represent F_p, the common stage of two consecutive intervals. -/
noncomputable def horizontalFirstPageMiddleStageIso (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex p) ≅
      (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageLowerIndex (p + 1)) :=
  (ComplexShape.embeddingDownNat.extendFunctor C).mapIso
    ((MonoOver.forget _ ⋙ Over.forget _).mapIso
      (horizontalCompleteFilteredTotalMonoOverMiddleIso K p))

/-- For a nonnegative homological bicomplex K in an abelian
category, the upper-successor presentation of F_(p+1), the
common-middle presentation of that stage, and its lower-successor
presentation are coherent. Passing from the successor upper
presentation through the common middle to the successor lower
presentation gives the identity isomorphism of the filtration subobject. -/
theorem horizontalCompleteFilteredTotalMonoOver_middle_triangle (p : ℕ) :
    (horizontalCompleteFilteredTotalMonoOverUpperSuccIso K p).symm ≪≫
      horizontalCompleteFilteredTotalMonoOverMiddleIso K (p + 1) ≪≫
      horizontalCompleteFilteredTotalMonoOverLowerSuccIso K (p + 1) =
    Iso.refl _ := by
  apply Iso.ext
  apply Subsingleton.elim

/-- For a nonnegative homological bicomplex K in an abelian
category and i ∈ ℤ, the three cochain component maps identifying
the common stage F_(p+1) compose to the identity in degree i.
They are the inverse upper-successor comparison, the middle-stage
comparison and the lower-successor comparison, in that order. -/
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

/-- For a nonnegative homological bicomplex K in an abelian
category and p ≥ 0, the next-stage cochain map is F_p → F_(p+1),
using upper(p) and upper(p+1) as its EInt indices.
It is the reindexed complete-filtration inclusion. -/
noncomputable def horizontalFirstPageNextFiltrationMap (p : ℕ) :
    (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex p) ⟶
      (horizontalCompleteFiltrationCochainDiagram K).obj
        (horizontalFirstPageUpperIndex (p + 1)) :=
  (horizontalCompleteFiltrationCochainDiagram K).map
    (homOfLE (horizontalFirstPageUpperIndex_le_succ p))

/-- For a nonnegative homological bicomplex K in an abelian
category, the map F_p → F_(p+1) equals the identification of
upper(p) with lower(p+1), followed by the consecutive-stage
filtration map for column p+1. -/
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

/-- For a nonnegative homological bicomplex K in an abelian
category, the adjacent cochain short complex has terms
coker(F_(p−1) → F_p), coker(F_(p−1) → F_(p+1)),
and coker(F_p → F_(p+1)).
Its maps are the canonical quotient inclusion and quotient projection. -/
noncomputable abbrev horizontalFirstPageAdjacentCokernelShortComplex (p : ℕ) :
    ShortComplex (CochainComplex C ℤ) :=
  CategoryTheory.cokernelCompShortComplex
    (horizontalFirstPageFiltrationMap K p)
    (horizontalFirstPageNextFiltrationMap K p)

/-- For a nonnegative homological bicomplex K in an abelian
category and p ≥ 0, the canonical cokernel sequence
0 → F_p/F_(p−1) → F_(p+1)/F_(p−1) → F_(p+1)/F_p → 0
is short exact as a sequence of integer cochain complexes. -/
theorem horizontalFirstPageAdjacentCokernelShortExact (p : ℕ) :
    (horizontalFirstPageAdjacentCokernelShortComplex K p).ShortExact :=
  CategoryTheory.cokernelCompShortComplex_shortExact
    (horizontalFirstPageFiltrationMap K p)
    (horizontalFirstPageNextFiltrationMap K p)

/-- For a nonnegative homological bicomplex K in an abelian
category, the cokernel of the normalized next inclusion
F_p → F_(p+1) is isomorphic to the cokernel of the consecutive
first-page filtration map at column p+1.
The source identification is the common stage upper(p)=lower(p+1). -/
noncomputable def horizontalFirstPageNextCokernelIso (p : ℕ) :
    cokernel (horizontalFirstPageNextFiltrationMap K p) ≅
      cokernel (horizontalFirstPageFiltrationMap K (p + 1)) :=
  cokernel.mapIso (horizontalFirstPageNextFiltrationMap K p)
    (horizontalFirstPageFiltrationMap K (p + 1))
    (horizontalFirstPageMiddleStageIso K p) (Iso.refl _) (by
      simpa using horizontalFirstPageNextFiltrationMap_eq_middle K p)

/-- For a nonnegative homological bicomplex K in an abelian
category, the left term coker(F_(p−1) → F_p) of the adjacent
quotient sequence is isomorphic to D_p.
The direct column places K_(p,q) in cochain degree −p−q and
carries the constant vertical differential sign (−1)^p. -/
noncomputable def horizontalFirstPageAdjacentLeftIso (p : ℕ) :
    (horizontalFirstPageAdjacentCokernelShortComplex K p).X₁ ≅
      horizontalDirectColumnCochain K p :=
  horizontalFirstPageCokernelIso K p

/-- For a nonnegative homological bicomplex K in an abelian
category, the right adjacent term coker(F_p → F_(p+1)) is
isomorphic to D_(p+1), the signed direct cochain column.
Its supported degrees are −(p+1)−q for q ≥ 0. -/
noncomputable def horizontalFirstPageAdjacentRightIso (p : ℕ) :
    (horizontalFirstPageAdjacentCokernelShortComplex K p).X₃ ≅
      horizontalDirectColumnCochain K (p + 1) :=
  horizontalFirstPageNextCokernelIso K p ≪≫
    horizontalFirstPageCokernelIso K (p + 1)

/-- For a nonnegative homological bicomplex K in an abelian
category, replacing the outside quotient terms by their direct
column presentations gives
D_p → coker(F_(p−1) → F_(p+1)) → D_(p+1).
The arrows are transported through the endpoint column isomorphisms. -/
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

/-- For a nonnegative homological bicomplex K in an abelian
category, the adjacent cokernel short complex is isomorphic to
its direct-column presentation.
The endpoint maps identify the two consecutive quotients with
D_p,D_(p+1), and the middle map is the identity on the middle quotient. -/
noncomputable def horizontalFirstPageAdjacentShortComplexIso (p : ℕ) :
    horizontalFirstPageAdjacentCokernelShortComplex K p ≅
      horizontalFirstPageAdjacentDirectShortComplex K p :=
  ShortComplex.isoMk
    (horizontalFirstPageAdjacentLeftIso K p) (Iso.refl _)
    (horizontalFirstPageAdjacentRightIso K p)
    (by simp [horizontalFirstPageAdjacentDirectShortComplex])
    (by simp [horizontalFirstPageAdjacentDirectShortComplex])

/-- For a nonnegative homological bicomplex K in an abelian
category and p ≥ 0, the sequence
0 → D_p → coker(F_(p−1) → F_(p+1)) → D_(p+1) → 0
is short exact as a sequence of integer cochain complexes. -/
theorem horizontalFirstPageAdjacentDirectShortExact (p : ℕ) :
    (horizontalFirstPageAdjacentDirectShortComplex K p).ShortExact :=
  ShortComplex.shortExact_of_iso
    (horizontalFirstPageAdjacentShortComplexIso K p)
    (horizontalFirstPageAdjacentCokernelShortExact K p)

end HomologicalComplex₂

end
