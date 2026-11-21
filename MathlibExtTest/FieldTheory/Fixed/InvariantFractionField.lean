/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.Fixed.InvariantFractionField

@[expose] public section

open CerednikDrinfeld.Mumford Polynomial

open scoped CerednikDrinfeld.Mumford

noncomputable section

/-- The automorphism group of `ℚ[X]` over `ℚ`, acting on `ℚ[X]`, is a
nontrivial instance of the invariant-field setup: membership in the
invariant field is the characterization by fixed points. -/
example (x : FractionRing ℚ[X]) :
    x ∈ invariantField ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] ↔
      ∀ g : ℚ[X] ≃ₐ[ℚ] ℚ[X], g • x = x :=
  mem_invariantField_iff ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] x

/-- For a subgroup, membership is fixedness by that subgroup alone, and the
full invariant field is the top-subgroup case. -/
example (Γ : Subgroup (ℚ[X] ≃ₐ[ℚ] ℚ[X])) (x : FractionRing ℚ[X]) :
    x ∈ invariantFieldOf ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] Γ ↔
      ∀ γ : ℚ[X] ≃ₐ[ℚ] ℚ[X], γ ∈ Γ → γ • x = x :=
  mem_invariantFieldOf_iff ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] Γ x

example :
    invariantFieldOf ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] ⊤ =
      invariantField ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] :=
  invariantFieldOf_top ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X]

/-- The invariant field is contained in every subgroup fixed field. -/
example (Γ : Subgroup (ℚ[X] ≃ₐ[ℚ] ℚ[X])) :
    invariantField ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] ≤
      invariantFieldOf ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] Γ :=
  invariantField_le_invariantFieldOf ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X] Γ

/-- The residual action of the whole group on its own invariant field is
trivial on elements coming from the base field construction: the identity
ambient semilinear automorphism restricts to the identity base action. -/
example :
    AmbientSemilinearAut.coeffAct
        (1 : AmbientSemilinearAut ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X]) =
      AmbientSemilinearAut.coeffAct
        (1 : AmbientSemilinearAut ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X]) :=
  rfl

example :
    (1 : AmbientSemilinearAut ℚ (ℚ[X] ≃ₐ[ℚ] ℚ[X]) ℚ[X]).fracMap =
      RingEquiv.refl (FractionRing ℚ[X]) :=
  AmbientSemilinearAut.fracMap_one

end
