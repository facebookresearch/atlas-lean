/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_ModularCurve_FullLevel_Diamond_exists_algHom_dualNumber_
  fst_eq_snd_ne_zero_rigidDataH1Pow.lean`
and
`P2M/Sol/S_ModularCurve_FullLevel_Diamond_exists_algHom_dualNumber_
  fst_eq_snd_ne_zero_rigidDataH1Pow.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source files at commit
`6e837e75355538c7f80bab5b956861e86c4eacc2`.
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
The upstream NOTICE also credits:
Mathlib — https://github.com/leanprover-community/mathlib4
Copyright (c) the respective Mathlib authors, as recorded in the headers of the
Mathlib source files.
Released under the Apache License, Version 2.0.
The source is machine-generated proof code built around a proof-extraction
framework; the statements and proofs are reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.DualNumber
public import Mathlib.RingTheory.Derivation.Basic

import Mathlib.Algebra.TrivSqZeroExt.Ideal
import Mathlib.RingTheory.Derivation.ToSquareZero

/-!
# Lifting a point to the dual numbers along a derivation

An `A`-derivation `D` of `B` into a `B`-algebra `Ω` gives the `A`-algebra map
`b ↦ (algebraMap B Ω b, D b)` from `B` to the dual numbers over `Ω`: Mathlib's
`liftOfDerivationToSquareZero` for the square-zero ideal `TrivSqZeroExt.kerIdeal Ω Ω`. This is
the tangent-space step behind first-order deformations of a point. A point given as
`φ₀ : B →ₐ[A] Ω` makes `Ω` a `B`-algebra through `φ₀.toRingHom.toAlgebra`.
-/

@[expose] public section

namespace Derivation

variable {A B Ω : Type*} [CommRing A] [CommRing B] [CommRing Ω]
  [Algebra A B] [Algebra A Ω] [Algebra B Ω] [IsScalarTower A B Ω]

/-- A nonzero `A`-derivation `D` of `B` into a commutative ring `Ω`, where `Ω` is a `B`-algebra,
lifts the point `algebraMap B Ω` to the dual numbers: some `A`-algebra map `B →ₐ[A] DualNumber Ω`
has first component `algebraMap B Ω` and a second component that is nonzero somewhere. The lift is
`b ↦ (algebraMap B Ω b, D b)`, which `liftOfDerivationToSquareZero` builds from `D` as a derivation
into the square-zero ideal `TrivSqZeroExt.kerIdeal Ω Ω`. -/
theorem exists_algHom_dualNumber_fst_eq_snd_ne_zero (D : Derivation A B Ω)
    (hD : ∃ b : B, D b ≠ 0) :
    ∃ φ : B →ₐ[A] DualNumber Ω,
      (∀ b : B, (φ b).fst = algebraMap B Ω b) ∧ ∃ b : B, (φ b).snd ≠ 0 := by
  -- The scalar actions of `A` and `B` on `DualNumber Ω` agree with their algebra actions only
  -- after unfolding, so the towers that make the square-zero ideal a module are given here.
  have : IsScalarTower A (DualNumber Ω) (DualNumber Ω) :=
    IsScalarTower.right (R := A) (A := DualNumber Ω)
  have : IsScalarTower B (DualNumber Ω) (DualNumber Ω) :=
    IsScalarTower.right (R := B) (A := DualNumber Ω)
  let ι : Ω →ₗ[B] TrivSqZeroExt.kerIdeal Ω Ω :=
    LinearMap.codRestrict ((TrivSqZeroExt.kerIdeal Ω Ω).restrictScalars B)
      ((TrivSqZeroExt.inrHom Ω Ω).restrictScalars B) fun x => by
        simp [TrivSqZeroExt.mem_kerIdeal_iff_inr]
  let φ := liftOfDerivationToSquareZero _ (TrivSqZeroExt.kerIdeal_sq Ω Ω) (ι.compDer D)
  have hφ (b : B) : φ b = TrivSqZeroExt.inr (D b) + algebraMap B (DualNumber Ω) b := rfl
  refine ⟨φ, fun b => by simp [hφ, TrivSqZeroExt.algebraMap_eq_inl'], ?_⟩
  obtain ⟨b, hb⟩ := hD
  exact ⟨b, by simpa [hφ, TrivSqZeroExt.algebraMap_eq_inl'] using hb⟩

end Derivation
