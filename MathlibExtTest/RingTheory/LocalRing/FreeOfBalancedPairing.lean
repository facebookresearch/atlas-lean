/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.LocalRing.FreeOfBalancedPairing

universe u w x

/-- The original statement, with its original binders, follows from the
public theorem. -/
example
    {𝒪 : Type u} {T : Type w} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    [CommRing T] [IsLocalRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (πT : T →ₐ[𝒪] 𝒪) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (C : T →ₗ[𝒪] T →ₗ[𝒪] 𝒪) (hC : ∀ s t u : T, C (s * t) u = C t (s * u))
    (hCb : Function.Bijective C)
    (M : Type x) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪) (hB : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n))
    (hBb : Function.Bijective B)
    (hrank : Module.finrank 𝒪 M =
      Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) * Module.finrank 𝒪 T)
    (hsat : Submodule.torsionBySet T M ↑(RingHom.ker πT) = (RingHom.ker πT).annihilator • ⊤) :
    Module.Free T M :=
  Module.free_of_torsionBySet_eq_annihilator_smul πT hη C hC hCb M B hB hBb hrank hsat

/-- Higher-universe consumer: all three types in `Type 1`. -/
example
    {𝒪 : Type 1} {T : Type 1} [CommRing 𝒪] [IsDomain 𝒪] [IsPrincipalIdealRing 𝒪]
    [CommRing T] [IsLocalRing T] [Algebra 𝒪 T] [Module.Finite 𝒪 T] [Module.Free 𝒪 T]
    (πT : T →ₐ[𝒪] 𝒪) (hη : (RingHom.ker πT).annihilator.map πT ≠ ⊥)
    (C : T →ₗ[𝒪] T →ₗ[𝒪] 𝒪) (hC : ∀ s t u : T, C (s * t) u = C t (s * u))
    (hCb : Function.Bijective C)
    (M : Type 1) [AddCommGroup M] [Module T M] [Module 𝒪 M] [IsScalarTower 𝒪 T M]
    [Module.Finite 𝒪 M] [Module.Free 𝒪 M]
    (B : M →ₗ[𝒪] M →ₗ[𝒪] 𝒪) (hB : ∀ (t : T) (m n : M), B (t • m) n = B m (t • n))
    (hBb : Function.Bijective B)
    (hrank : Module.finrank 𝒪 M =
      Module.finrank 𝒪 (Submodule.torsionBySet T M ↑(RingHom.ker πT)) * Module.finrank 𝒪 T)
    (hsat : Submodule.torsionBySet T M ↑(RingHom.ker πT) = (RingHom.ker πT).annihilator • ⊤) :
    Module.Free T M :=
  Module.free_of_torsionBySet_eq_annihilator_smul πT hη C hC hCb M B hB hBb hrank hsat
