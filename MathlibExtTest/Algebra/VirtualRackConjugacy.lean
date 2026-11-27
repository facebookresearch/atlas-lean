/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Algebra.VirtualRackConjugacy

open Equiv MetaMathlibExt Quandles

-- Conjugating a virtual structure gives an isomorphic virtual rack.
example {R : Type*} [Rack R] (f g : rackAut R) :
    VirtualRackIso (f : Perm R) ((g * f * g⁻¹ : rackAut R) : Perm R) :=
  (virtualRackIso_iff_isConj f _).2 (isConj_iff.mpr ⟨g, rfl⟩)

-- A nonidentity virtual structure cannot become the identity under isomorphism.
example {R : Type*} [Rack R] (f : rackAut R) (hf : f ≠ 1) :
    ¬ VirtualRackIso (f : Perm R) (1 : Perm R) := by
  intro h
  exact hf (isConj_one_left.mp ((virtualRackIso_iff_isConj f 1).mp h))

-- The definition also allows different underlying racks.
example {R₁ R₂ : Type*} [Rack R₁] [Rack R₂] (ψ : R₁ ≃ R₂)
    (hψ : ∀ x y, ψ (x ◃ y) = ψ x ◃ ψ y) : VirtualRackIso (1 : Perm R₁) (1 : Perm R₂) :=
  ⟨ψ, hψ, fun _ => rfl⟩
