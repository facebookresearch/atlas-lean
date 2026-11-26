/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Flat.FGSubalgebraTensorProduct

@[expose] public section

open TensorProduct

example {R₀ R B₀ : Type*} [CommRing R₀] [CommRing R] [CommRing B₀]
    [Algebra R₀ R] [Algebra R₀ B₀] [Algebra.FinitePresentation R₀ B₀]
    [Module.Flat R (R ⊗[R₀] B₀)] (s : Finset R) :
    ∃ R₁ : Subalgebra R₀ R, R₁.FG ∧ (↑s : Set R) ⊆ R₁ ∧ Module.Flat R₁ (R₁ ⊗[R₀] B₀) :=
  Module.Flat.exists_fg_subalgebra_flat_tensorProduct s

/-- A concrete consumer: `ℤ[X]` is flat over itself after base change along `ℤ → ℤ[X]`. -/
example (s : Finset (Polynomial ℤ)) :
    ∃ R₁ : Subalgebra ℤ (Polynomial ℤ), R₁.FG ∧ (↑s : Set (Polynomial ℤ)) ⊆ R₁ ∧
      Module.Flat R₁ (R₁ ⊗[ℤ] Polynomial ℤ) :=
  Module.Flat.exists_fg_subalgebra_flat_tensorProduct s
