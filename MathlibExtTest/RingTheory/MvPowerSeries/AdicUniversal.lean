/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.MvPowerSeries.AdicUniversal

@[expose] public section

universe u v w

-- `exactSource` consumer with the original binders.
example {σ : Type u} {𝒪 : Type v} {A : Type w} [Finite σ] [CommRing 𝒪] [CommRing A]
    [Algebra 𝒪 A] (I : Ideal A) [IsAdicComplete I A] (a : σ → A) (ha : ∀ i, a i ∈ I) :
    ∃ φ : MvPowerSeries σ 𝒪 →ₐ[𝒪] A, ∀ i, φ (MvPowerSeries.X i) = a i :=
  MvPowerSeries.exists_algHom_apply_X_eq I a ha

-- Higher-universe consumer: the index type lives in a larger universe than the rings.
example {𝒪 : Type} {A : Type} [CommRing 𝒪] [CommRing A] [Algebra 𝒪 A] (I : Ideal A)
    [IsAdicComplete I A] (a : ULift (Fin 2) → A) (ha : ∀ i, a i ∈ I) :
    ∃ φ : MvPowerSeries (ULift (Fin 2)) 𝒪 →ₐ[𝒪] A, ∀ i, φ (MvPowerSeries.X i) = a i :=
  MvPowerSeries.exists_algHom_apply_X_eq (𝒪 := 𝒪) (A := A) I a ha

-- Boundary: for the zero ideal the membership hypothesis forces every chosen
-- value to be zero, and the resulting map sends every variable to zero.
example {𝒪 : Type} [CommRing 𝒪] :
    ∃ φ : MvPowerSeries (Fin 2) 𝒪 →ₐ[𝒪] 𝒪, ∀ i, φ (MvPowerSeries.X i) = 0 :=
  MvPowerSeries.exists_algHom_apply_X_eq ⊥ (fun _ => 0) (fun _ => Ideal.zero_mem _)
