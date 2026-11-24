/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentMaximumNerveOperators

/-!
# Exact endpoint transport of original coherent path direct images

The actual right join direct-image functor and the maximum-image functor
have the same whole original path subsets. Only their specified endpoint
labels differ, by the proved front and last equations.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.PathEndpointTransport
open PathLastMaximum PathMaximumOperators MaximumNerveOperators
variable {n m : ℕ}

/-- Transport the original path category along the two supplied endpoint equalities. -/
def retarget {J : Type u} [LinearOrder J] {a a' b b' : J} (ha : a = a') (hb : b = b') :
    SimplicialThickening.Path a b ⥤ SimplicialThickening.Path a' b' where
  obj p := ⟨p.I, ha ▸ p.left, hb ▸ p.right, fun k hk => ha ▸ p.left_le k hk,
    fun k hk => hb ▸ p.le_right k hk⟩
  map f := ⟨homOfLE f.hom.down.down⟩

/-- The actual whole path nerve of endpoint transport is precisely the whole simplicial
equality transport. -/
theorem nerve_retarget {J : Type u} [LinearOrder J] {a a' b b' : J} (ha : a = a') (hb : b = b') :
    nerveMap (retarget ha hb) =
      eqToHom (congrArg₂ (fun a b : J => nerve (SimplicialThickening.Path a b)) ha hb) := by
  subst a'
  subst b'
  apply SSet.hom_ext
  intro q
  apply ConcreteCategory.hom_ext
  intro p
  refine Functor.ext (fun _ => rfl) ?_
  intro i j f
  apply InducedCategory.Hom.ext
  exact Subsingleton.elim _ _

/-- The actual original thickening direct image becomes exactly the maximum-image path
functor under the
  specified endpoint equations. -/
theorem imageFunctor_eq (θ : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)) :
    SimplicialThickening.functorMap (extension θ).toOrderHom.uliftMap
        (.mk (ULift.up.{u} i.castSucc)) (.mk (ULift.up.{u} (Fin.last (n + 1)))) ⋙
      retarget (lifted_front θ i) (lifted_last θ) = imageFunctor θ i := by
  refine Functor.ext (fun p => rfl) ?_
  intro p q f
  apply InducedCategory.Hom.ext
  exact Subsingleton.elim _ _

/-- The whole original coherent-simplex Hom operator reads back the maximum-image nerve
after the exact
  endpoint equations. -/
theorem image_nerve (θ : ⦋n⦌ ⟶ ⦋m⦌) (i : Fin (n + 1)) :
    (SimplicialEnrichment.coherentSimplexMap (extension θ)).map
        (.mk (ULift.up.{u} i.castSucc)) (.mk (ULift.up.{u} (Fin.last (n + 1)))) ≫
      eqToHom (congrArg₂ (fun a b : ULift.{u} (Fin (m + 2)) =>
        nerve (SimplicialThickening.Path a b))
        (lifted_front θ i) (lifted_last θ)) = nerveMap (imageFunctor θ i) := by
  let F := SimplicialThickening.functorMap (extension θ).toOrderHom.uliftMap
    (SimplicialThickening.mk (ULift.up.{u} i.castSucc))
    (SimplicialThickening.mk (ULift.up.{u} (Fin.last (n + 1))))
  have hR := nerve_retarget (lifted_front θ i) (lifted_last θ)
  have h := imageFunctor_eq.{u} θ i
  have hN : nerveMap F ≫ nerveMap (retarget (lifted_front θ i) (lifted_last θ)) =
    nerveMap (imageFunctor θ i) :=
    congrArg (fun F => nerveMap F) h
  change nerveMap F ≫ _ = _
  exact (congrArg (fun g => nerveMap F ≫ g) hR.symm).trans hN

end CategoryTheory.CoherentRealization.PathEndpointTransport
