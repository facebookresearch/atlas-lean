/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentFixedFrontFamilyRecognition
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeFrontFamily
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomFrontFamilyStrictMaps
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomFrontFamilyTransport

/-!
# Whole original suspension readback of the right-cube family

The genuine free-suspension comparison sends every original interval
of the cube family to the distinguished realized interval. The proof
uses the original free generator readback and actual front-prefix
composition, retaining the whole enriched successor simplex.
-/

noncomputable section
universe u
open CategoryTheory MonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.FixedFrontSuspensionReadback
open SimplicialEnrichment PathLastMaximum HomSuspensionGenerators FixedFrontCollapse
  FixedFrontCubeMap HomFrontFamilyTransport HomFrontFamilyStrictMaps

/-- The actual source readback of the free right-cube suspension comparison. -/
theorem source_obj (n : ℕ) : (suspensionFunctor.{u} n).obj left = source n :=
  HomSuspensionFunctor.functor_left (RightCubeRelations.object n)
    (realization (FixedFrontCollapse.object n)) (source n) (target n) (cubeMap n)

/-- The actual target readback of the free right-cube suspension comparison. -/
theorem target_obj (n : ℕ) : (suspensionFunctor.{u} n).obj right = target n :=
  HomSuspensionFunctor.functor_right (RightCubeRelations.object n)
    (realization (FixedFrontCollapse.object n)) (source n) (target n) (cubeMap n)

/-- The actual family postcomposed with the free-suspension comparison, read at the same structural original
  endpoints. -/
def readFamily (n : ℕ) : HomFrontFamily.Family (C := realization (FixedFrontCollapse.object.{u} n)) (source
    n) (target n) n :=
  retarget (source_obj n) (target_obj n)
    (postFamily (C := carrier (RightCubeRelations.object.{u} n)) (D := realization (FixedFrontCollapse.object n))
      (suspensionFunctor n) left right (RightCubeFrontFamily.family n))

/-- Every actual original interval map is read back as the same distinguished realized Hom map. -/
theorem interval_readback (n : ℕ) (i : Fin (n + 1)) : (readFamily.{u} n).map i = intervalMap n i := by
  let Q := RightCubeRelations.object.{u} n
  let G := suspensionFunctor.{u} n
  let E := EqualityTransport.hom (C := realization (FixedFrontCollapse.object.{u} n)) (source_obj n) (target_obj n)
  let A : nerve (LastPath.{u} i) ⟶ nerve (LastPath.{u} (0 : Fin (n + 1))) :=
    nerveMap (RightCubeRelations.prependFunctor i)
  let B : nerve (LastPath.{u} (0 : Fin (n + 1))) ⟶ Q := RightCubeRelations.projection n
  let V : Q ⟶ SimplicialQuiver.freeHom (quiver Q) left right := HomSuspensionForward.generator Q
  let W : SimplicialQuiver.freeHom (quiver Q) left right ⟶ rightHom.{u} n := G.map left right ≫ E
  have hG : V ≫ W = cubeMap n :=
    HomSuspensionFunctor.generator_readback Q (realization (FixedFrontCollapse.object n))
      (source n) (target n) (cubeMap n)
  change (((A ≫ B ≫ V) ≫ G.map left right) ≫ E) = _
  have h₀ : ((A ≫ B ≫ V) ≫ G.map left right) ≫ E = (A ≫ B) ≫ (V ≫ W) :=
    (Category.assoc (A ≫ B ≫ V) (G.map left right) E).trans
      ((Category.assoc A (B ≫ V) W).trans
        ((congrArg (fun f => A ≫ f) (Category.assoc B V W)).trans
          (Category.assoc A B (V ≫ W)).symm))
  have h₁ : (A ≫ B) ≫ (V ≫ W) = (A ≫ B) ≫ cubeMap n :=
    congrArg (fun f : Q ⟶ rightHom.{u} n => (A ≫ B) ≫ f) hG
  have h₂ : (A ≫ B) ≫ cubeMap n = A ≫ intervalMap n 0 :=
    (Category.assoc A B (cubeMap n)).trans (congrArg (fun f => A ≫ f) (cubeMap_projection n))
  have h₃ : A ≫ intervalMap n 0 = intervalMap n i := by
    ext q r
    exact interval_prepend n i q r
  exact h₀.trans (h₁.trans (h₂.trans h₃))

/-- The actual whole readback family is precisely the distinguished original realized interval family. -/
theorem family_readback (n : ℕ) : readFamily.{u} n = FixedFrontFamilyRecognition.family n :=
  family_ext (interval_readback n)

/-- The entire original successor simplex reads back under the genuine free-suspension comparison, not just
  its vertices or classes. -/
theorem functor_readback (n : ℕ) : RightCubeFrontFamily.functor.{u} n ≫ suspensionFunctor n =
    FixedFrontInsertion.functor n :=
  (simplex_postcompose (C := carrier (RightCubeRelations.object.{u} n))
    (D := realization (FixedFrontCollapse.object n)) (suspensionFunctor n) left right
      (RightCubeFrontFamily.family n)).trans
    ((simplex_retarget (C := realization (FixedFrontCollapse.object.{u} n)) (source_obj n) (target_obj n) _).trans
      ((congrArg (HomFrontFamily.simplex (C := realization (FixedFrontCollapse.object.{u} n)) (source n)
        (target n)) (family_readback n)).trans
        (FixedFrontFamilyRecognition.functor_eq n).symm))

end CategoryTheory.CoherentRealization.FixedFrontSuspensionReadback
