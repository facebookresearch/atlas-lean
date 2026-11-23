/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.LinearAlgebra.BilinearForm.DualLattice

@[expose] public section

open scoped nonZeroDivisors

open Submodule

variable {A K V : Type*} [CommRing A] [Field K] [Algebra A K] [IsFractionRing A K]
  [AddCommGroup V] [Module A V] [Module K V] [IsScalarTower A K V]

example {M : Submodule A V} (hspan : Submodule.span K (M : Set V) = ⊤) :
    IsLocalizedModule A⁰ M.subtype := by
  exact Submodule.isLocalizedModule_subtype_of_span_eq_top (K := K) M hspan

example [IsDomain A] [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (M : Submodule A V)
    (hM : Submodule.IsFullLattice K M) (f : Module.Dual A M) :
    ∃ x : B.dualSubmodule M, B.dualSubmoduleToDual M x = f := by
  let _ := hM
  exact B.dualSubmoduleToDual_surjective hB M IsFullLattice.span_eq_top f

example [IsDomain A] [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (M : Submodule A V)
    (hM : Submodule.IsFullLattice K M) :
    Function.Bijective (B.dualSubmoduleToDual M) := by
  let _ := hM
  exact B.dualSubmoduleToDual_bijective hB M IsFullLattice.span_eq_top

example [IsDomain A] [FiniteDimensional K V] [IsNoetherianRing A]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (M : Submodule A V)
    (hM : Submodule.IsFullLattice K M) : Module.Finite A (B.dualSubmodule M) := by
  let _ := hM
  haveI := IsLattice.finite K M
  rw [Module.Finite.iff_fg]
  exact B.dualSubmodule_fg hB M IsFullLattice.span_eq_top

example (M : Submodule A V) (hM : Submodule.IsFullLattice K M) :
    Submodule.span K ((0 : LinearMap.BilinForm K V).dualSubmodule M : Set V) = ⊤ := by
  exact LinearMap.BilinForm.dualSubmodule_span_eq_top _ M (IsLattice.fg K M)

example [IsDomain A] [IsNoetherianRing A]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (M : Submodule A V)
    (hM : Submodule.IsFullLattice K M) : Module.Finite A (B.dualSubmodule M) := by
  let := hM
  let := B.dualSubmodule_isFullLattice hB M
  exact IsLattice.finite K _

example [IsDomain A] [FiniteDimensional K V] [IsNoetherianRing A]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (M : Submodule A V)
    (hM : Submodule.IsFullLattice K M) :
    Submodule.IsFullLattice K (B.dualSubmodule M) ∧
      Function.Bijective (B.dualSubmoduleToDual M) := by
  let := hM
  obtain ⟨hLat, hBij⟩ :=
    B.dualSubmodule_isFullLattice_and_dualSubmoduleToDual_bijective hB M
  exact ⟨hLat, hBij⟩

noncomputable example [IsDomain A] [FiniteDimensional K V]
    (B : LinearMap.BilinForm K V) (hB : B.Nondegenerate) (M : Submodule A V)
    (hM : Submodule.IsFullLattice K M) :
    (B.dualSubmodule M) ≃ₗ[A] Module.Dual A M := by
  let := hM
  exact B.dualSubmoduleLinearEquiv hB M IsFullLattice.span_eq_top
