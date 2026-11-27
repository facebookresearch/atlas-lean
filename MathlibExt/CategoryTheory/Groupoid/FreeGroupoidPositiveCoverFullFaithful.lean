/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidPositivePathUniqueness

/-!
# The actual native positive-cover comma functor is full and faithful

Every original full comma arrow is its SAME complete positive path
with the actual native completion triangle. Whole original cover-path
lifting and endpoint recovery supply its actual preimage; full native
projected-word injection proves faithfulness. No full, faithful or
weak outcome is supplied as a premise.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)
/-- The SAME original generating cover quiver for the full native comma functor. -/
private local instance coverQuiverForFullFaithful : Quiver.{v} (CoverVertex V z) := coverQuiver V z

/-- Every original full comma arrow retains its SAME actual projected positive path. -/
lemma coverPathsToComma_map_right {a b : CoverVertex V z}
    (p : @Quiver.Path (CoverVertex V z) (coverQuiver V z) a b) :
    ((coverPathsToComma V z).map p).right = (coverProjection V z).mapPath p := by
  exact (eq_of_heq (Functor.hcongr_hom (coverPathsToComma_projection V z) p)).trans
    (coverPathsProjection_mapPath V z p)

/-- The actual native full positive-cover path functor is faithful. -/
instance coverPathsToComma_faithful : (coverPathsToComma V z).Faithful where
  map_injective {a b} p q h := by
    apply coverProjection_mapPath_injective V z a b
    exact (coverPathsToComma_map_right V z p).symm.trans
      ((congrArg (fun h => h.right) h).trans (coverPathsToComma_map_right V z q))

/-- Every SAME original full structured arrow has an actual native full positive-cover path
preimage. -/
theorem coverPathsToComma_full_preimage (a b : CoverVertex V z)
    (h : coverVertexToComma V z a ⟶ coverVertexToComma V z b) :
    ∃ q : @Quiver.Path (CoverVertex V z) (coverQuiver V z) a b,
      (coverPathsToComma V z).map q = h := by
  obtain ⟨c, q, ht, hp⟩ := coverPathLift_exists V z a h.right
  have hend : c = b := by
    cases c with
    | mk x f =>
      cases b with
      | mk y g =>
        change x = y at ht
        subst y
        have hq := coverPathProjection_endpoint V z q
        have hw := StructuredArrow.w h
        change a.path ≫ (CategoryTheory.FreePathCompletion.pathToQuiverGroupoid V).map
          h.right = g at hw
        have he : f = g := hq.symm.trans
          ((congrArg (fun t => a.path ≫
            (CategoryTheory.FreePathCompletion.pathToQuiverGroupoid V).map t)
            (eq_of_heq hp)).trans hw)
        subst g
        rfl
  subst c
  refine ⟨q, StructuredArrow.hom_ext _ _ ?_⟩
  exact (coverPathsToComma_map_right V z q).trans (eq_of_heq hp)

/-- The actual native original positive-cover comma functor is full. -/
instance coverPathsToComma_full : (coverPathsToComma V z).Full where
  map_surjective h := coverPathsToComma_full_preimage V z _ _ h

/-- Every actual native original comma object is its SAME original cover vertex. -/
def commaToCoverVertex (a : PositiveCoverComma V z) : CoverVertex V z :=
  ⟨a.right, a.hom⟩

/-- The whole native comma object is recovered with its SAME individual target and complete
original path. -/
lemma coverVertexToComma_commaToCoverVertex (a : PositiveCoverComma V z) :
    coverVertexToComma V z (commaToCoverVertex V z a) = a := by
  apply StructuredArrow.obj_ext _ _ rfl
  exact Category.comp_id _

/-- Every original native cover vertex is recovered exactly from its SAME comma object. -/
lemma commaToCoverVertex_coverVertexToComma (a : CoverVertex V z) :
    commaToCoverVertex V z (coverVertexToComma V z a) = a := by
  cases a
  rfl

end Quiver.FreeGroupoid.OriginalWords
