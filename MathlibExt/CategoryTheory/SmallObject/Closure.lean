/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import MathlibExt.CategoryTheory.SmallObject.FullyFaithful

/-!
# Membership of mapped relative-cell complexes

Target coproduct, cobase and transfinite closure classify the actual endpoint
and transition arrows of a relative cell complex mapped through a functor.
The cell universe and chain universe are independent.
-/

@[expose] public section

noncomputable section

universe w t vC vD uC uD

open CategoryTheory CategoryTheory.Limits

namespace HomotopicalAlgebra.RelativeCellComplex

variable {C : Type uC} [Category.{vC} C]
  {D : Type uD} [Category.{vD} D]
  (F : C ⥤ D) (P : MorphismProperty C) (Q : MorphismProperty D)
  (hPQ : P ≤ Q.inverseImage F)
  {T : Type t} [LinearOrder T] [OrderBot T] [SuccOrder T] [WellFoundedLT T]
  {X Y : C} {f : X ⟶ Y}
  (c : RelativeCellComplex.{w} (fun (_ : T) => P.homFamily) f)
  [PreservesColimitsOfSize.{w, w} F]
  [PreservesColimitsOfShape T F]
  [PreservesWellOrderContinuousOfShape T F]
  [Q.IsStableUnderCoproducts.{w}] [Q.IsStableUnderCobaseChange]

include P hPQ c

/-- The actual mapped endpoint belongs to the target property when that property
is closed under transfinite compositions of the given shape. -/
theorem map_mem_of_le [Q.IsStableUnderTransfiniteCompositionOfShape T] : Q (F.map f) := by
  let mapped := c.mapOfLE F P Q hPQ
  let transfinite := mapped.transfiniteCompositionOfShape' (I := Q) (fun s => s.i.2)
  have hClosure : (Q.coproducts.{w}).pushouts ≤ Q :=
    (MorphismProperty.pushouts_monotone Q.coproducts_le).trans Q.pushouts_le
  exact Q.transfiniteCompositionsOfShape_le T _ (transfinite.ofLE hClosure).mem

/-- Every actual mapped transition belongs to the target property when that property
is closed under all transfinite compositions in the chain universe. -/
theorem map_map_mem_of_le [Q.IsStableUnderTransfiniteComposition.{t}]
    {a b : T} (φ : a ⟶ b) : Q (F.map (c.F.map φ)) := by
  let mapped := c.mapOfLE F P Q hPQ
  let transfinite := mapped.transfiniteCompositionOfShape' (I := Q) (fun s => s.i.2)
  have hClosure : (Q.coproducts.{w}).pushouts ≤ Q :=
    (MorphismProperty.pushouts_monotone Q.coproducts_le).trans Q.pushouts_le
  exact (transfinite.ofLE hClosure).mem_map φ

end HomotopicalAlgebra.RelativeCellComplex
