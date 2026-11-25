/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidNativeCoverPathProjection

/-!
# The SAME original full positive paths have actual unique cover lifts

Each original full quiver path is lifted from its prescribed original
native groupoid-path vertex by appending every SAME generator. The
literal original path projection and full endpoint completion triangle
are retained. Unique original generator lifts give full path uniqueness.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)
/-- The SAME original generating cover quiver for native whole positive-path lifts. -/
private local instance coverQuiverForPathLifting : Quiver.{v} (CoverVertex V z) := coverQuiver V z

/-- Append the entire SAME original full positive path to its prescribed original cover vertex. -/
def CoverVertex.appendPath (a : CoverVertex V z) {y : V}
    (p : @Quiver.Path V inferInstance a.target y) : CoverVertex V z :=
  ⟨y, a.path ≫ (CategoryTheory.FreePathCompletion.pathToQuiverGroupoid V).map p⟩

/-- Each original identity path retains the SAME prescribed native cover vertex. -/
lemma CoverVertex.appendPath_nil (a : CoverVertex V z) :
    CoverVertex.appendPath V z a (.nil : @Quiver.Path V inferInstance a.target a.target) = a := by
  cases a with
  | mk x f =>
    change (⟨x, f ≫ 𝟙 _⟩ : CoverVertex V z) = ⟨x, f⟩
    exact congrArg (fun h => (⟨x, h⟩ : CoverVertex V z)) (Category.comp_id f)

/-- Every complete original path has an actual native cover lift with its SAME full
projected path. -/
theorem coverPathLift_exists (a : CoverVertex V z) {y : V}
    (p : @Quiver.Path V inferInstance a.target y) :
    ∃ b : CoverVertex V z, ∃ q : @Quiver.Path (CoverVertex V z) (coverQuiver V z) a b,
      b.target = y ∧ HEq ((coverProjection V z).mapPath q) p := by
  induction p with
  | nil => exact ⟨a, .nil, rfl, HEq.rfl⟩
  | @cons x y p f ih =>
    obtain ⟨b, q, hb, hq⟩ := ih
    subst x
    let c := CoverVertex.append V z b f
    let e : CoverArrow V z b c := liftCoverArrow V z b f
    refine ⟨c, q.cons e, rfl, ?_⟩
    have he : (coverProjection V z).mapPath (q.cons e) =
        ((coverProjection V z).mapPath q).cons f := rfl
    have hp : (coverProjection V z).mapPath q = p := eq_of_heq hq
    have hc : HEq (((coverProjection V z).mapPath q).cons f) (p.cons f) :=
      heq_of_eq (congrArg (fun r : @Quiver.Path V inferInstance a.target b.target => r.cons f) hp)
    exact (heq_of_eq he).trans hc

end Quiver.FreeGroupoid.OriginalWords
