/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.RingTheory.DedekindDomain.DiscriminantLocalization

@[expose] public section

/-!
# Tests for the discriminant ideal under canonical localization (ATLAS Prop. 12.15)

Generic application examples exercising
`Ideal.map_spanNorm_differentIdeal_eq_localization_ofField`, plus a
membership-facing consequence of the equality. These are API/inference
tests; no new definitions are introduced.
-/

set_option autoImplicit false

universe u

variable (A K : Type*) (L : Type u) (B : Type*)
  [CommRing A] [Field K] [CommRing B] [Field L]
  [Algebra A K] [Algebra B L] [Algebra A B] [Algebra K L] [Algebra A L]
  [IsScalarTower A K L] [IsScalarTower A B L]
  [IsFractionRing A K]
  [FiniteDimensional K L] [IsIntegralClosure B A L] [Algebra.IsSeparable K L]
  [IsFractionRing B L]
  [IsDedekindDomain A] [IsDedekindDomain B] [Module.IsTorsionFree A B]

variable (S : Submonoid A) (hS : S ≤ nonZeroDivisors A)

local notation "Aₛ" => Localization.subalgebra.ofField K S hS

variable [Module.Finite A B]

variable (SB : Type*) [CommRing SB] [Algebra B SB]
  [IsLocalization (Algebra.algebraMapSubmonoid B S) SB]
  [Algebra (Localization.subalgebra.ofField K S hS) SB] [Algebra SB L] [Algebra A SB]
  [IsScalarTower A (Localization.subalgebra.ofField K S hS) SB]
  [IsScalarTower A B SB] [IsScalarTower B SB L]
  [IsScalarTower A (Localization.subalgebra.ofField K S hS) L]
  [IsScalarTower (Localization.subalgebra.ofField K S hS) SB L]
  [IsScalarTower (Localization.subalgebra.ofField K S hS) K L]
  [IsFractionRing SB L] [IsDedekindDomain SB]
  [Module.IsTorsionFree (Localization.subalgebra.ofField K S hS) SB]
  [Module.IsTorsionFree B SB]
  [IsIntegralClosure SB (Localization.subalgebra.ofField K S hS) L]
  [Module.Finite (Localization.subalgebra.ofField K S hS) SB]

/-- Generic application of the discriminant-ideal localization equality. -/
example :
    Ideal.map (algebraMap A Aₛ) (Ideal.spanNorm A (differentIdeal A B)) =
      Ideal.spanNorm Aₛ (differentIdeal Aₛ SB) :=
  Ideal.map_spanNorm_differentIdeal_eq_localization_ofField A K L B S hS SB

/-- Membership-facing consequence of the discriminant-ideal equality. -/
example (x : Aₛ) :
    x ∈ Ideal.map (algebraMap A Aₛ) (Ideal.spanNorm A (differentIdeal A B)) ↔
      x ∈ Ideal.spanNorm Aₛ (differentIdeal Aₛ SB) := by
  rw [Ideal.map_spanNorm_differentIdeal_eq_localization_ofField A K L B S hS SB]
