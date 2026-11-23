/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import MathlibExt.AlgebraicGeometry.ProjectiveSpace

@[expose] public noncomputable section

/-!
# Projective morphisms of schemes over a field

A morphism `f : X ⟶ B` of schemes over a field `k` is projective if it factors as
a closed immersion `X ⟶ ℙᴺ_k ×ₖ B` followed by the projection to `B`.
-/

namespace MathlibExt.AlgebraicGeometry.RelativeProjectivity

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- Relative projectivity is a genuine closed immersion into projective
space over the parameter scheme, with the projection equation fixed. -/
def IsProjectiveOver {k : Type u} [Field k]
    {X B : Over (Spec (.of k))} (f : X ⟶ B) : Prop :=
  ∃ N : ℕ,
    ∃ i : X ⟶ prod (ProjectiveSpace.projectiveSpace k N) B,
      IsClosedImmersion i.left ∧
        i ≫ (prod.snd : prod (ProjectiveSpace.projectiveSpace k N) B ⟶ B) = f

end MathlibExt.AlgebraicGeometry.RelativeProjectivity
