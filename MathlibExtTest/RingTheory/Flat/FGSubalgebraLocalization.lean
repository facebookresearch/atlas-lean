/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.Flat.FGSubalgebraLocalization

import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.PrincipalIdealDomain

@[expose] public section

set_option autoImplicit false

open TensorProduct

/-- Exact-source consumer, using the original binders verbatim. -/
example {R₀ R B₀ : Type*} [CommRing R₀] [CommRing R] [CommRing B₀]
    [Algebra R₀ R] [Algebra R₀ B₀] [IsNoetherianRing R₀] [Algebra.FiniteType R₀ B₀]
    (P : Ideal (R ⊗[R₀] B₀)) [P.IsPrime]
    [Module.Flat R (Localization.AtPrime P)] :
    ∃ R₁ : Subalgebra R₀ R, R₁.FG ∧
      Module.Flat R₁ (Localization.AtPrime
        (P.comap (Algebra.TensorProduct.map R₁.val (AlgHom.id R₀ B₀)).toRingHom)) :=
  Module.Flat.exists_fg_subalgebra_flat_localization_tensorProduct P

/-- Consumer with all three rings in mixed universes. -/
example {R₀ : Type} {R : Type 1} {B₀ : Type 2} [CommRing R₀] [CommRing R] [CommRing B₀]
    [Algebra R₀ R] [Algebra R₀ B₀] [IsNoetherianRing R₀] [Algebra.FiniteType R₀ B₀]
    (P : Ideal (R ⊗[R₀] B₀)) [P.IsPrime]
    [Module.Flat R (Localization.AtPrime P)] :
    ∃ R₁ : Subalgebra R₀ R, R₁.FG ∧
      Module.Flat R₁ (Localization.AtPrime
        (P.comap (Algebra.TensorProduct.map R₁.val (AlgHom.id R₀ B₀)).toRingHom)) :=
  Module.Flat.exists_fg_subalgebra_flat_localization_tensorProduct P

/-- A concrete instance: `ℤ ⊆ ℚ` and `ℤ[X]`, where every `ℚ`-module is flat. -/
example (P : Ideal (ℚ ⊗[ℤ] Polynomial ℤ)) [P.IsPrime] :
    ∃ R₁ : Subalgebra ℤ ℚ, R₁.FG ∧
      Module.Flat R₁ (Localization.AtPrime
        (P.comap (Algebra.TensorProduct.map R₁.val (AlgHom.id ℤ (Polynomial ℤ))).toRingHom)) :=
  Module.Flat.exists_fg_subalgebra_flat_localization_tensorProduct P
