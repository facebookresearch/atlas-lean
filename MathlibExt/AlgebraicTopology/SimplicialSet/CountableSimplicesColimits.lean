/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialSet.CountableSimplices
import Mathlib.CategoryTheory.Limits.Types.Colimits
import Mathlib.Basic.Countable.Small

/-!
# Actual countable simplicial colimits and whole isomorphism transport

Each original colimit simplex is in the actual image of an original
stage simplex. The full native evaluated colimit gives this surjection,
so a countable object family of countable simplex sets has countable
original colimit simplices. Whole original isomorphisms retain the same
countability in every original degree.
-/

noncomputable section
universe u v w
open CategoryTheory Limits

namespace SSet

/-- The entire original isomorphism transports countability of every actual simplex set. -/
theorem countableSimplices_of_iso {X Y : SSet.{u}} (e : X ≅ Y) [Y.CountableSimplices] :
    X.CountableSimplices where
  countable_obj q := Countable.of_equiv (Y.obj q) (((SSet.evaluation.obj q).mapIso e).toEquiv).symm

/-- Every native colimit simplex comes from the countable family of SAME original stage simplices. -/
instance countableSimplices_colimit {J : Type v} [Category.{w} J] [Countable J]
    (F : J ⥤ SSet.{u}) [HasColimit F] [∀ j, (F.obj j).CountableSimplices] :
    (colimit F).CountableSimplices where
  countable_obj q := by
    let E := SSet.evaluation.obj q
    let supply : (Σ j : J, (F.obj j).obj q) → (colimit F).obj q :=
      fun p => (colimit.ι F p.1).app q p.2
    have hs : Function.Surjective supply := by
      intro y
      obtain ⟨j, x, hx⟩ := Types.jointly_surjective (F ⋙ E)
        (isColimitOfPreserves E (colimit.isColimit F)) y
      exact ⟨⟨j, x⟩, hx⟩
    exact hs.countable

/-- The genuine original coproduct retains countable whole simplex sets for every countable original index family. -/
instance countableSimplices_coproduct {I : Type v} [Countable I] (X : I → SSet.{u})
    [∀ i, (X i).CountableSimplices] : (∐ X).CountableSimplices := by
  have : Countable (Discrete I) :=
    Countable.of_equiv I ⟨Discrete.mk, Discrete.as, fun _ => rfl, fun _ => rfl⟩
  have (j : Discrete I) : ((Discrete.functor X).obj j).CountableSimplices := by
    change (X j.as).CountableSimplices
    infer_instance
  exact countableSimplices_colimit (Discrete.functor X)

end SSet
