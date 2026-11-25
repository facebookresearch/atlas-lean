/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.AlgebraicTopology.SimplicialSet.Basic
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.Presentable.Presheaf
public import Mathlib.CategoryTheory.Presentable.Type

/-!
# Local presentability of simplicial sets

Simplicial sets in any universe are locally presentable. The proof replaces
the small simplex index by an equivalent category whose object and morphism
universes match the value universe, applies presheaf presentability there,
and transports the result back along the induced functor-category
equivalence.

Pinned Mathlib also infers this through its presheaf instance for essentially
small index categories; the theorem names the result and records this
universe-matching proof.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

universe u

namespace SSet

/-- Simplicial sets valued in `Type u` form a locally presentable category
relative to the same universe. -/
theorem isLocallyPresentable : IsLocallyPresentable.{u} SSet.{u} := by
  let J := ULiftHom.{u} (ULift.{u} SimplexCategory)
  let e : SimplexCategory ≌ J :=
    ULiftHomULiftCategory.equiv SimplexCategory
  let E : SSet.{u} ≌ (Jᵒᵖ ⥤ Type u) :=
    Equivalence.congrLeft (E := Type u) e.op
  let _ : IsLocallyPresentable.{u} (Jᵒᵖ ⥤ Type u) := inferInstance
  exact E.symm.isLocallyPresentable

end SSet
