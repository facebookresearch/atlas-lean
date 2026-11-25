/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.RelativeProjectivity

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.RelativeProjectivity

universe u

variable {k : Type u} [Field k]

-- The projection from relative projective space `ℙᴺ ×ₖ B` to `B` is H-projective, through the
-- identity closed immersion.
example (N : ℕ) (B : Over (Spec (.of k))) :
    IsHProjectiveOver (prod.snd : prod (ProjectiveSpace.projectiveSpace k N) B ⟶ B) :=
  ⟨N, 𝟙 _, show IsClosedImmersion (𝟙 _) from inferInstance, Category.id_comp _⟩

-- An H-projective morphism factors through a closed immersion into `ℙᴺ ×ₖ B`.
example {X B : Over (Spec (.of k))} (f : X ⟶ B) (h : IsHProjectiveOver f) :
    ∃ N : ℕ, ∃ i : X ⟶ prod (ProjectiveSpace.projectiveSpace k N) B,
      IsClosedImmersion i.left ∧ i ≫ prod.snd = f := h
