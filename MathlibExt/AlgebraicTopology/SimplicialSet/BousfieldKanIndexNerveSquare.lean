/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanIndexMapULift
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanElementsAugmentation

/-!
# The actual full BK index map and original nerve projection square

Every original elements chain projects to its same original index
chain. The canonical full index map commutes with these actual
projections. Original coefficient point weakness and the same index
nerve weakness therefore prove the actual BK index map weak.
-/

noncomputable section

universe u w vJ vK

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

variable {J : Type u} {K : Type (max u w)} [Category.{vJ} J] [Category.{max vJ vK} K]
variable {D : J ⥤ SSet.{max u vJ}} {E : K ⥤ SSet.{max u w vJ vK}}

/-- The same complete original BK index map commutes with both full original nerve projections. -/
theorem bkHocolimIndexMapULift_nerveSquare (Φ : J ⥤ K)
    (α : D ⋙ uliftFunctor.{max u w vJ vK,max u vJ} ⟶ Φ ⋙ E) :
    bkHocolimIndexMapULift Φ α ≫ bkHocolimToNerve E =
      uliftFunctor.{max u w vJ vK,max u vJ}.map (bkHocolimToNerve D) ≫ nerveMapULiftToTarget Φ := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  obtain ⟨x, rfl⟩ := (uliftObjEquiv.{max u vJ,max u w vJ vK} (bkHocolim D) (op ⦋n⦌)).surjective a
  let F := (bkHocolimElementsDiagonalIso D).hom.app (op ⦋n⦌) x
  let y := (bkHocolimIndexMapULift Φ α).app (op ⦋n⦌)
    (uliftObjEquiv.{max u vJ,max u w vJ vK} (bkHocolim D) (op ⦋n⦌) x)
  have hE := ConcreteCategory.congr_hom (C := Type (max u w vJ vK))
    (NatTrans.congr_app (bkElementsNerveProjection_diagonalIso E) (op ⦋n⦌)) y
  have hD := ConcreteCategory.congr_hom (C := Type (max u vJ))
    (NatTrans.congr_app (bkElementsNerveProjection_diagonalIso D) (op ⦋n⦌)) x
  have hIndex : bkElementsIndexFunctor Φ α (op ⦋n⦌) ⋙ Functor.Elements.π (E.flip.obj (op ⦋n⦌)) =
      Functor.Elements.π (D.flip.obj (op ⦋n⦌)) ⋙ Φ := rfl
  have hChain := congrArg (fun G => (G.mapComposableArrows n).obj F) hIndex
  have hMap := bkHocolimIndexMapULift_elements Φ α (op ⦋n⦌) x
  have hProjected := congrArg
    (fun G => ((Functor.Elements.π (E.flip.obj (op ⦋n⦌))).mapComposableArrows n).obj G) hMap
  have hOld := (bkElementsNerveProjection_chain D n F).symm.trans hD
  change (bkHocolimToNerve E).app (op ⦋n⦌) y =
    (Φ.mapComposableArrows n).obj ((bkHocolimToNerve D).app (op ⦋n⦌) x)
  exact (hE.symm.trans (bkElementsNerveProjection_chain E n
    ((bkHocolimElementsDiagonalIso E).hom.app (op ⦋n⦌) y))).trans
      (hProjected.trans (hChain.trans (congrArg (Φ.mapComposableArrows n).obj hOld)))

/-- The SAME actual full BK index map is weak from the actual coefficient point maps and same original index nerve
map. -/
theorem bkHocolimIndexMapULift_weak_of_pointCoefficients (Φ : J ⥤ K)
    (α : D ⋙ uliftFunctor.{max u w vJ vK,max u vJ} ⟶ Φ ⋙ E)
    (hD : ∀ j : J, realizationWeakEquivalences (stdSimplex.isTerminalObj₀.from (D.obj j)))
    (hE : ∀ k : K, realizationWeakEquivalences (stdSimplex.isTerminalObj₀.from (E.obj k)))
    (hΦ : realizationWeakEquivalences (nerveMapULiftToTarget Φ)) :
    realizationWeakEquivalences (bkHocolimIndexMapULift Φ α) := by
  have hSource := (realizationWeak_ulift_map_iff (bkHocolimToNerve D)).mpr
    (bkHocolimToNerve_weak D hD)
  have hTarget := bkHocolimToNerve_weak E hE
  have hComposite := realizationWeakEquivalences.comp_mem _ _ hSource hΦ
  exact realizationWeakEquivalences.of_postcomp _ _ hTarget
    ((bkHocolimIndexMapULift_nerveSquare Φ α).symm ▸ hComposite)

end SSet
