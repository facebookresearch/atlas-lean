/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanElementsDiagonalReadbacks
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanWeightedSimplices
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanNerveProjection
import MathlibExt.AlgebraicTopology.SimplicialSet.BousfieldKanHomotopyInvarianceUniverses

/-!
# The SAME original BK augmentation and projection on full elements chains

Both maps are the actual original BK maps through the proved full
native elements-diagonal isomorphism. Every full original chain reads
its same source coefficient and same index projection. No comparison
outcome is assumed by these complete scalar formulas.
-/

noncomputable section

universe uJ vJ

open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

variable {J : Type uJ} [Category.{vJ} J]

/-- Every entire native elements-diagonal simplex comes from a complete original weighted chain and coefficient. -/
theorem bkElementsDiagonal_simplex_has_weighted_preimage (D : J ⥤ SSet.{max uJ vJ})
    (n : ℕ) (F : ComposableArrows (D.flip.obj (op ⦋n⦌)).Elements n) :
    ∃ (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n)
      (x : (D.obj p.1.left).obj (op ⦋n⦌)),
      (bkHocolimElementsDiagonalIso D).hom.app (op ⦋n⦌)
        ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) x) = F := by
  let p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n :=
    ⟨F ⋙ Functor.Elements.π (D.flip.obj (op ⦋n⦌)), PUnit.unit⟩
  refine ⟨p, (F.obj 0).val, ?_⟩
  have h := (CategoryBar.replElementsEquiv J (D.flip.obj (op ⦋n⦌)) n).apply_symm_apply F
  exact (bkHocolimElementsDiagonalIso_weighted D n p (F.obj 0).val).trans h

variable {D : J ⥤ SSet.{max uJ vJ}} {Z : SSet.{max uJ vJ}}

/-- The same original full BK augmentation in its complete native elements-diagonal coordinates. -/
def bkElementsAugmentation (τ : D ⟶ (CategoryTheory.Functor.const J).obj Z) :
    simplicialDiagonalFunctor.obj (bkElementsRows D) ⟶ Z :=
  (bkHocolimElementsDiagonalIso D).inv ≫ bkAugmentation τ

/-- The whole original augmentation is exactly the same full original elements augmentation under both canonical inverse
maps. -/
theorem bkElementsAugmentation_diagonalIso (τ : D ⟶ (CategoryTheory.Functor.const J).obj Z) :
    (bkHocolimElementsDiagonalIso D).hom ≫ bkElementsAugmentation τ = bkAugmentation τ :=
  (bkHocolimElementsDiagonalIso D).hom_inv_id_assoc _

/-- Every original weighted coefficient reads the same full original augmentation component. -/
theorem bkElementsAugmentation_weighted (τ : D ⟶ (CategoryTheory.Functor.const J).obj Z)
    (n : ℕ) (p : StrictOrdinaryWeightedBar.WIdx J (CategoryBar.replUnit J) n)
    (x : (D.obj p.1.left).obj (op ⦋n⦌)) :
    (bkElementsAugmentation τ).app (op ⦋n⦌)
      ((bkHocolimElementsDiagonalIso D).hom.app (op ⦋n⦌)
        ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) x)) =
          (τ.app p.1.left).app (op ⦋n⦌) x := by
  have he := ConcreteCategory.congr_hom
    (NatTrans.congr_app (bkElementsAugmentation_diagonalIso τ) (op ⦋n⦌))
    ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) x)
  exact he.trans (ConcreteCategory.congr_hom (bkAugmentation_app_mk_ι τ n p) x)

/-- Every whole native elements chain augments by its entire SAME original first coefficient. -/
theorem bkElementsAugmentation_chain (τ : D ⟶ (CategoryTheory.Functor.const J).obj Z)
    (n : ℕ) (F : (simplicialDiagonalFunctor.obj (bkElementsRows D)).obj (op ⦋n⦌)) :
    (bkElementsAugmentation τ).app (op ⦋n⦌) F =
      (τ.app (F.obj 0).obj).app (op ⦋n⦌) (F.obj 0).val := by
  obtain ⟨p, x, rfl⟩ := bkElementsDiagonal_simplex_has_weighted_preimage D n F
  have hFirst := bkHocolimElementsDiagonalIso_first D n p x
  let eval : (D.flip.obj (op ⦋n⦌)).Elements → Z.obj (op ⦋n⦌) :=
    fun z => (τ.app z.obj).app (op ⦋n⦌) z.val
  have hValue := congrArg eval hFirst
  exact (bkElementsAugmentation_weighted τ n p x).trans hValue.symm

/-- The actual original full BK nerve projection in its full elements-diagonal coordinates. -/
def bkElementsNerveProjection (D : J ⥤ SSet.{max uJ vJ}) :
    simplicialDiagonalFunctor.obj (bkElementsRows D) ⟶ nerve J :=
  (bkHocolimElementsDiagonalIso D).inv ≫ bkHocolimToNerve D

/-- The same original full projection is exactly the original elements projection under the complete native diagonal
isomorphism. -/
theorem bkElementsNerveProjection_diagonalIso (D : J ⥤ SSet.{max uJ vJ}) :
    (bkHocolimElementsDiagonalIso D).hom ≫ bkElementsNerveProjection D = bkHocolimToNerve D :=
  (bkHocolimElementsDiagonalIso D).hom_inv_id_assoc _

/-- Every original full elements chain projects to its same full original native index chain. -/
theorem bkElementsNerveProjection_chain (D : J ⥤ SSet.{max uJ vJ})
    (n : ℕ) (F : (simplicialDiagonalFunctor.obj (bkElementsRows D)).obj (op ⦋n⦌)) :
    (bkElementsNerveProjection D).app (op ⦋n⦌) F =
      ((Functor.Elements.π (D.flip.obj (op ⦋n⦌))).mapComposableArrows n).obj F := by
  obtain ⟨p, x, rfl⟩ := bkElementsDiagonal_simplex_has_weighted_preimage D n F
  have he := ConcreteCategory.congr_hom
    (NatTrans.congr_app (bkElementsNerveProjection_diagonalIso D) (op ⦋n⦌))
    ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) x)
  have hIndex : ((Functor.Elements.π (D.flip.obj (op ⦋n⦌))).mapComposableArrows n).obj
      ((bkHocolimElementsDiagonalIso D).hom.app (op ⦋n⦌)
        ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) x)) = p.1 := by
    rw [bkHocolimElementsDiagonalIso_weighted]
    exact CategoryTheory.Functor.hext (fun i => rfl) (fun i j f => HEq.rfl)
  have hProjection := ConcreteCategory.congr_hom
    (bkFixedRowProjection_wbarIncl D (op ⦋n⦌) n p) x
  change (bkFixedRowProjection D (op ⦋n⦌)).app (op ⦋n⦌)
    ((StrictOrdinaryWeightedBar.wbarIncl (CategoryBar.replUnit J) D n p).app (op ⦋n⦌) x) = p.1 at hProjection
  rw [bkFixedRowProjection_diagonal] at hProjection
  exact (he.trans hProjection).trans hIndex.symm

/-- The SAME original full nerve projection is weak when every actual original coefficient point map is weak. -/
theorem bkHocolimToNerve_weak (D : J ⥤ SSet.{max uJ vJ})
    (hPoint : ∀ j : J, realizationWeakEquivalences (stdSimplex.isTerminalObj₀.from (D.obj j))) :
    realizationWeakEquivalences (bkHocolimToNerve D) :=
  realizationWeakEquivalences.comp_mem _ _
    (bkHocolimMap_weak_universes (bkDiagramToPoint D) hPoint)
    (realizationWeakEquivalences.of_isIso (bkPointIsoNerve J).hom)

end SSet
