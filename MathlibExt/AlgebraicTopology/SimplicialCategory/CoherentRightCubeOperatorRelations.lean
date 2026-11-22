/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeOperator
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeZeroPrefix

/-!
# Original front-relation compatibility of right-cube operators

Actual right-join images preserve whole original union composition.
Adjoining the structural zero to their front prefix gives an original
zero-to-middle prefix in the target. The same defining front relation
therefore identifies the two actual operator images.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.RightCubeOperatorRelations
open PathLastMaximum RightCubeRelations PathMaximumOperators RightCubeOperator
variable {n m : ℕ}

/-- The actual front-prefix image under the right-join operator, with the structural zero target source adjoined. -/
def prefixImage (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) (i : Fin (n + 1))
    (p : SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 2))) (ULift.up.{u} i.castSucc)) :
    SimplicialThickening.Path (ULift.up.{u} (0 : Fin (m + 2))) (ULift.up.{u} (θ.toOrderHom i).castSucc) where
  I := {ULift.up.{u} (0 : Fin (m + 2))} ∪ (extension θ).toOrderHom.uliftMap '' p.I
  left := Or.inl rfl
  right := Or.inr (by
    have h := Set.mem_image_of_mem (extension θ).toOrderHom.uliftMap p.right
    rw [lifted_front] at h
    exact h)
  left_le k _ := Fin.zero_le k.down
  le_right k := by
    rintro (rfl | ⟨l, hl, rfl⟩)
    · exact Fin.zero_le _
    · have h := (extension θ).toOrderHom.uliftMap.monotone (p.le_right l hl)
      rw [lifted_front] at h
      exact h

/-- The whole original front-prefix image functor at its supplied target middle label. -/
def prefixFunctor (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) (i : Fin (n + 1)) :
    SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 2))) (ULift.up.{u} i.castSucc) ⥤
      SimplicialThickening.Path (ULift.up.{u} (0 : Fin (m + 2))) (ULift.up.{u} (θ.toOrderHom i).castSucc) where
  obj := prefixImage θ i
  map f := ⟨homOfLE (Set.union_subset_union le_rfl (Set.image_mono f.hom.down.down))⟩

/-- The actual operator image of an original union is the union of its target front-prefix image and
  original last-path image. -/
theorem image_union (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) (i : Fin (n + 1))
    (p : SimplicialThickening.Path (ULift.up.{u} (0 : Fin (n + 2))) (ULift.up.{u} i.castSucc)) (r : LastPath.{u} i) :
    (RightCubeOperator.functor θ).obj (compose 0 i p r) = compose 0 (θ.toOrderHom i) (prefixImage θ i p)
      (image θ i r) := by
  apply SimplicialThickening.Path.ext
  change ({_} ∪ (extension θ).toOrderHom.uliftMap '' (p.I ∪ r.I)) = (({_} ∪ _) ∪ _)
  rw [Set.image_union, Set.union_assoc]
  rfl

/-- The original zero-adjoined image differs from the target zero-adjoined suffix by an actual original
  front-prefix relation, not a strict path equality. -/
theorem image_prepend_relation (θ : SimplexCategory.mk n ⟶ SimplexCategory.mk m) (i : Fin (n + 1))
    {q : SimplexCategoryᵒᵖ} (r : (nerve (LastPath.{u} i)).obj q) :
    (setoid.{u} m q).r
      (r ⋙ prependFunctor i ⋙ RightCubeOperator.functor θ)
      (r ⋙ imageFunctor θ i ⋙ prependFunctor (θ.toOrderHom i)) := by
  let p := CoherentRealization.RightCubeZeroPrefix.minimalChain.{u} i q
  have hP := CoherentRealization.RightCubeZeroPrefix.chain_prepend i r
  have hU : (p.prod' r ⋙ SimplicialThickening.compFunctor
      (SimplicialThickening.mk (ULift.up.{u} (0 : Fin (n + 2))))
      (SimplicialThickening.mk (ULift.up.{u} i.castSucc)) (SimplicialThickening.mk (ULift.up.{u} (Fin.last (n + 1))))) ⋙
      RightCubeOperator.functor θ =
    (p ⋙ prefixFunctor θ i).prod' (r ⋙ imageFunctor θ i) ⋙ SimplicialThickening.compFunctor
      (SimplicialThickening.mk (ULift.up.{u} (0 : Fin (m + 2))))
      (SimplicialThickening.mk (ULift.up.{u} (θ.toOrderHom i).castSucc)) (SimplicialThickening.mk
        (ULift.up.{u} (Fin.last (m + 1)))) := by
    refine Functor.ext (fun j => image_union θ i (p.obj j) (r.obj j)) ?_
    intro j k f
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _
  have hR := Relation.composition (n := m) (θ.toOrderHom i) (p ⋙ prefixFunctor θ i) (r ⋙ imageFunctor θ i)
  have h := Relation.EqvGen.rel _ _ hR
  exact (congrArg (fun p => p ⋙ RightCubeOperator.functor θ) hP) ▸ (hU ▸ h)

end CategoryTheory.CoherentRealization.RightCubeOperatorRelations
