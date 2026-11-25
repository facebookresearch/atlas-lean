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
# H-projective morphisms of schemes over a field

A morphism `f : X ⟶ B` of schemes over a field `k` is H-projective if it factors as
a closed immersion `X ⟶ ℙᴺ_k ×ₖ B = ℙᴺ_B` followed by the projection to `B`
(Stacks, Tag 01W8; this is Hartshorne's definition of a projective morphism). A
projective morphism in the sense of the Stacks Project embeds into a projective bundle
`P(E)` instead; over an affine base the two notions agree (Stacks, Tag 01WB).
-/

namespace MathlibExt.AlgebraicGeometry.RelativeProjectivity

open CategoryTheory CategoryTheory.Limits _root_.AlgebraicGeometry

universe u

/-- H-projectivity: a genuine closed immersion into projective space `ℙᴺ_B` over the
parameter scheme, with the projection equation fixed (Stacks, Tag 01W8). -/
def IsHProjectiveOver {k : Type u} [Field k]
    {X B : Over (Spec (.of k))} (f : X ⟶ B) : Prop :=
  ∃ N : ℕ,
    ∃ i : X ⟶ prod (ProjectiveSpace.projectiveSpace k N) B,
      IsClosedImmersion i.left ∧
        i ≫ (prod.snd : prod (ProjectiveSpace.projectiveSpace k N) B ⟶ B) = f

end MathlibExt.AlgebraicGeometry.RelativeProjectivity
