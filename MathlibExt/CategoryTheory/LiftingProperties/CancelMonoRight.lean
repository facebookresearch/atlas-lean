/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import Mathlib.CategoryTheory.LiftingProperties.Basic
import Mathlib.CategoryTheory.MorphismProperty.LiftingProperty

/-!
# Cancel a monic right factor from an actual lifting property

An actual lift against a composite retains the original top equation.
Monicity of the final factor recovers the original bottom equation. This
also cancels that factor from every right lifting class, without adding a
global instance or choosing a different factorization.
-/

universe v u
open CategoryTheory

namespace CategoryTheory.HasLiftingProperty

/-- A monic final factor can be cancelled from the right side of the same original lifting
problem. -/
theorem of_comp_right_of_mono {C : Type u} [Category.{v} C]
    {A D E F G : C} {i : A ⟶ D} {p : E ⟶ F} {q : F ⟶ G} [Mono q]
    (h : HasLiftingProperty i (p ≫ q)) : HasLiftingProperty i p where
  sq_hasLift {a b} sq := by
    let t : CommSq a i (p ≫ q) (b ≫ q) :=
      ⟨(Category.assoc _ _ _).symm.trans ((congrArg (fun f => f ≫
        q) sq.w).trans (Category.assoc _ _ _))⟩
    let _ : t.HasLift := h.sq_hasLift t
    refine CommSq.HasLift.mk' ⟨t.lift, t.fac_left, ?_⟩
    apply (cancel_mono q).mp
    exact (Category.assoc _ _ _).trans t.fac_right

end CategoryTheory.HasLiftingProperty

namespace CategoryTheory.MorphismProperty

/-- Every original right lifting class permits cancellation of a monic final factor. -/
theorem rlp_of_comp_right_of_mono {C : Type u} [Category.{v} C]
    (I : MorphismProperty C) {E F G : C} (p : E ⟶ F) (q : F ⟶ G) [Mono q]
    (h : I.rlp (p ≫ q)) : I.rlp p :=
  fun _ _ i hi => (h i hi).of_comp_right_of_mono

end CategoryTheory.MorphismProperty
