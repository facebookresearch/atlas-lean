/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.IntervalCylinder

/-!
# Original endpoint naturality squares are actual marked pullbacks

The original source projection gives the universal lift in each endpoint
square. Its two equations follow from the two literal original product
coordinates. All supplied markings are retained, and the square is a
pullback for every original marked map, without even a monicity premise.
-/

noncomputable section
universe u
open CategoryTheory Limits Opposite
open scoped Simplicial

namespace SSet.Marked

/-- Each whole original interval endpoint naturality square is a genuine marked pullback. -/
theorem intervalCylinderEndpoint_isPullback {X Y : Marked.{u}} (f : X ⟶ Y) (ε : Fin 2) :
    IsPullback f (intervalCylinderEndpoint X ε) (intervalCylinderEndpoint Y ε)
      (prodMap f (𝟙 (max (Δ[1] : SSet.{u})))) := by
  apply IsPullback.mk' (intervalCylinderEndpoint_natural f ε)
  · intro T a b _ h
    have hp := congrArg (fun q => q ≫ prodFst X (max (Δ[1] : SSet.{u}))) h
    simpa only [Category.assoc, intervalCylinderEndpoint_projection, Category.comp_id] using hp
  · intro T a b h
    let l : T ⟶ X := b ≫ prodFst X (max (Δ[1] : SSet.{u}))
    refine ⟨l, ?_, ?_⟩
    · apply Hom.ext
      apply NatTrans.ext
      funext n
      apply ConcreteCategory.hom_ext
      intro z
      exact (congrArg (fun (q : T ⟶ prod Y (max (Δ[1] : SSet.{u}))) => (q.hom.app n z).1) h).symm
    · apply Hom.ext
      apply NatTrans.ext
      funext n
      apply ConcreteCategory.hom_ext
      intro z
      apply Prod.ext
      · rfl
      · exact congrArg (fun (q : T ⟶ prod Y (max (Δ[1] : SSet.{u}))) => (q.hom.app n z).2) h

end SSet.Marked
