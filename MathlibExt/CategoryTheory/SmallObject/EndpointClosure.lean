/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Attribution for this imported development.
Author: @toskua, Codex
-/

-- Author: @toskua, Codex

import MathlibExt.CategoryTheory.SmallObject.Closure

/-!
# Original endpoint-leg closure for mapped relative cells

The same mapped original relative-cell complex and target closure laws
control every original endpoint leg. No endpoint membership, model or
source-Hom preservation outcome is supplied.
-/

set_option autoImplicit false
noncomputable section
universe u v w vD uD
open CategoryTheory Limits MorphismProperty HomotopicalAlgebra
namespace HomotopicalAlgebra.RelativeCellComplex

/-- Closure controls every mapped supplied endpoint leg, not just the total root arrow. -/
theorem map_incl_mem_of_le {C : Type u} [Category.{v} C] {D : Type uD} [Category.{vD} D]
    (F : C ⥤ D) (P : MorphismProperty C) (Q : MorphismProperty D)
    {O : Type w} [LinearOrder O] [OrderBot O] [SuccOrder O] [WellFoundedLT O]
    {X Y : C} {f : X ⟶ Y}
    (c : RelativeCellComplex.{w} (fun _ : O => P.homFamily) f)
    [PreservesColimitsOfSize.{w,w} F] [PreservesColimitsOfShape O F]
    [PreservesWellOrderContinuousOfShape O F]
    [Q.IsStableUnderCoproducts.{w}] [Q.IsStableUnderCobaseChange]
    [Q.IsStableUnderTransfiniteComposition.{w}] (hPQ : P ≤ Q.inverseImage F) (k : O) :
    Q (F.map (c.incl.app k)) := by
  let mapped := c.mapOfLE F P Q hPQ
  let t := mapped.transfiniteCompositionOfShape' (I := Q) (fun a => a.i.2)
  have hClosure : (Q.coproducts.{w}).pushouts ≤ Q :=
    (MorphismProperty.pushouts_monotone Q.coproducts_le).trans Q.pushouts_le
  have hLeg := (t.ofLE hClosure).mem_incl_app k
  change Q (F.map (c.incl.app k) ≫ 𝟙 _) at hLeg
  simpa only [Category.comp_id] using hLeg

end HomotopicalAlgebra.RelativeCellComplex

namespace CategoryTheory.MonoCoconeEquality

variable {C : Type u} [Category.{v} C] {O : Type w} [LinearOrder O]
  {F : O ⥤ C} (c : Limits.Cocone F) [∀ j, Mono (c.ι.app j)]

/-- Two whole maps equal after monic original endpoint legs agree through
one common original stage, without any domain presentability premise. -/
theorem equal_at_common_stage {D : C} (i k : O)
    (a : D ⟶ F.obj i) (b : D ⟶ F.obj k)
    (hab : a ≫ c.ι.app i = b ≫ c.ι.app k) :
    ∃ (l : O) (u : i ⟶ l) (v : k ⟶ l), a ≫ F.map u = b ≫ F.map v := by
  let l := max i k
  let u : i ⟶ l := homOfLE (le_max_left i k)
  let v : k ⟶ l := homOfLE (le_max_right i k)
  refine ⟨l, u, v, ?_⟩
  apply (cancel_mono (c.ι.app l)).mp
  rw [Category.assoc, c.w u, Category.assoc, c.w v]
  exact hab

end CategoryTheory.MonoCoconeEquality
