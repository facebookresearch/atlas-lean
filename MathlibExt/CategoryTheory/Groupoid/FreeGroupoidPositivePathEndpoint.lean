/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidPositivePathLifting

/-!
# The full original lifted positive-path endpoint triangle

Every entire native positive-cover path keeps the prescribed original
source path, literal full original mapPath and SAME completed target
path. The native StructuredArrow triangle and exact full functor
projection give this identity without an endpoint outcome assumption.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)
/-- The SAME original generating cover quiver in all native endpoint triangles. -/
private local instance coverQuiverForEndpoint : Quiver.{v} (CoverVertex V z) := coverQuiver V z

/-- EVERY full native cover path retains its SAME actual original source-to-target
completion triangle. -/
theorem coverPathProjection_endpoint {a b : CoverVertex V z}
    (p : @Quiver.Path (CoverVertex V z) (coverQuiver V z) a b) :
    a.path ≫ (CategoryTheory.FreePathCompletion.pathToQuiverGroupoid V).map
      ((coverProjection V z).mapPath p) = b.path := by
  have he : ((coverPathsToComma V z).map p).right = (coverPathsProjection V z).map p := by
    have h := Functor.hcongr_hom (coverPathsToComma_projection V z) p
    exact eq_of_heq h
  have hw := StructuredArrow.w ((coverPathsToComma V z).map p)
  change a.path ≫ (CategoryTheory.FreePathCompletion.pathToQuiverGroupoid V).map
    (((coverPathsToComma V z).map p).right) = b.path at hw
  have hp := coverPathsProjection_mapPath V z p
  exact (congrArg (fun q => a.path ≫
    (CategoryTheory.FreePathCompletion.pathToQuiverGroupoid V).map q)
    (he.trans hp)).symm.trans hw

/-- The SAME full original projected word recovers the actual endpoint cover vertex,
including its full native path. -/
lemma coverPathEndpoint_unique {a b c : CoverVertex V z}
    (p : @Quiver.Path (CoverVertex V z) (coverQuiver V z) a b)
    (q : @Quiver.Path (CoverVertex V z) (coverQuiver V z) a c)
    (ht : b.target = c.target)
    (hp : HEq ((coverProjection V z).mapPath p) ((coverProjection V z).mapPath q)) : b = c := by
  cases b with
  | mk x f =>
    cases c with
    | mk y g =>
      change x = y at ht
      subst y
      have hproject : (coverProjection V z).mapPath p = (coverProjection V z).mapPath q :=
        eq_of_heq hp
      have hf := coverPathProjection_endpoint V z p
      have hg := coverPathProjection_endpoint V z q
      have he : f = g := hf.symm.trans
        ((congrArg (fun t => a.path ≫
          (CategoryTheory.FreePathCompletion.pathToQuiverGroupoid V).map t)
          hproject).trans hg)
      subst g
      rfl

end Quiver.FreeGroupoid.OriginalWords
