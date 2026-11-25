/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module
public import Mathlib.AlgebraicTopology.SimplicialSet.Basic

/-!
# The actual contained-universe coefficient lift

When the coefficient universe already contains the lift universe,
the canonical original lift and lowering are full inverse simplicial
maps. Every coefficient and original ordinal operator is retained.
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory

namespace SSet

/-- Both full original coefficient directions are inverse when the lift universe is contained
in the original value universe. -/
def uliftContainedIso (X : SSet.{max u v}) :
    uliftFunctor.{u,max u v}.obj X ≅ X :=
  NatIso.ofComponents (fun q => (Equiv.ulift : ULift.{u} (X.obj q) ≃ X.obj q).toIso)
    (by intro q r θ; apply ConcreteCategory.hom_ext; intro x; rfl)

/-- Every same original source map retains its full coefficient-lift square. -/
theorem uliftContainedIso_naturality {X Y : SSet.{max u v}} (f : X ⟶ Y) :
    uliftFunctor.{u,max u v}.map f ≫ (uliftContainedIso Y).hom =
      (uliftContainedIso X).hom ≫ f := by
  apply NatTrans.ext
  funext q
  apply ConcreteCategory.hom_ext
  intro x
  rfl

end SSet
