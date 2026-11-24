/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.CategoryTheory.Groupoid.FreeGroupoidPositivePathEndpoint

/-!
# Full native original positive-cover path injection

The original mapPath keeps every generator and path length. At a fixed
original source, its complete original word also determines each
intermediate cover vertex by the actual completion endpoint triangle.
The entire native lifted path is therefore recovered without any
faithfulness or weak assumption.
-/

noncomputable section
universe u v
open CategoryTheory
namespace Quiver.FreeGroupoid.OriginalWords
variable (V : Type u) [Quiver.{v} V] (z : V)
/-- The SAME original generating cover quiver used by full native path recovery. -/
private local instance coverQuiverForPathRecovery : Quiver.{v} (CoverVertex V z) := coverQuiver V z

/-- The full original native cover projection retains EVERY original path length. -/
lemma coverProjection_mapPath_length {a b : CoverVertex V z}
    (p : @Quiver.Path (CoverVertex V z) (coverQuiver V z) a b) :
    ((coverProjection V z).mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p f ih => exact congrArg Nat.succ ih

/-- At the SAME fixed original endpoints, the complete original projected path
recovers the entire cover path. -/
theorem coverProjection_mapPath_injective (a b : CoverVertex V z) :
    Function.Injective ((coverProjection V z).mapPath (a := a) (b := b)) := by
  intro p
  induction p with
  | nil =>
    intro q h
    have hl : q.length = 0 := (coverProjection_mapPath_length V z q).symm.trans
      ((congrArg Quiver.Path.length h).symm)
    exact (Quiver.Path.eq_nil_of_length_zero q hl).symm
  | @cons c b p f ih =>
    intro q h
    cases q with
    | nil =>
      have hl := congrArg Quiver.Path.length h
      simp only [Prefunctor.mapPath_cons, Prefunctor.mapPath_nil, Quiver.Path.length_cons,
        Quiver.Path.length_nil] at hl
      omega
    | @cons d b q g =>
      have hproject : ((coverProjection V z).mapPath p).cons f.arrow =
          ((coverProjection V z).mapPath q).cons g.arrow := h
      have h_arrow : HEq f.arrow g.arrow := Quiver.Path.hom_heq_of_cons_eq_cons hproject
      have ht : c.target = d.target := Quiver.Path.obj_eq_of_cons_eq_cons hproject
      have h_prefix : HEq ((coverProjection V z).mapPath p) ((coverProjection V z).mapPath q) :=
        Quiver.Path.heq_of_cons_eq_cons hproject
      have hc : c = d := coverPathEndpoint_unique V z p q ht h_prefix
      subst d
      have hp : p = q := ih (eq_of_heq h_prefix)
      subst q
      have hg : f = g := CoverArrow.ext_coefficient V z f g (eq_of_heq h_arrow)
      subst g
      rfl

end Quiver.FreeGroupoid.OriginalWords
