/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.MotivicPowerCycleSourcesModCoefficientSequenceExact
import Mathlib.Algebra.Category.ModuleCat.EpiMono
import Mathlib.Data.Nat.Prime.Basic

/-!
# Tests for short exactness of the mod-ℓ coefficient sequence
-/

namespace MathlibExtTest.AlgebraicGeometry.MotivicPowerCycleSourcesModCoefficientSequenceExact

open MathlibExt.AlgebraicGeometry.MotivicBocksteinModels
open WantedExt.AlgebraicGeometry.MotivicPowerCycleSourcesWanted

/-- The sequence is short exact at the concrete prime `ℓ = 2`. -/
example : (modSequence 2).ShortExact := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact modCoefficientSequenceExact 2

/-- The sequence is short exact at the concrete prime `ℓ = 3`. -/
example : (modSequence 3).ShortExact := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact modCoefficientSequenceExact 3

/-- The first map `n ↦ ℓ * n` is injective. -/
example (ell : ℕ) [Fact ell.Prime] : Function.Injective ⇑(modSequence ell).f :=
  (ModuleCat.mono_iff_injective _).mp (modCoefficientSequenceExact ell).mono_f

/-- Reduction modulo `ℓ` is surjective. -/
example (ell : ℕ) [Fact ell.Prime] : Function.Surjective ⇑(modSequence ell).g :=
  (ModuleCat.epi_iff_surjective _).mp (modCoefficientSequenceExact ell).epi_g

/-- At `ℓ = 3`, the first map is multiplication by `3`: it sends `2` to `6` in `ZMod 9`. -/
example : (modSequence 3).f (ULift.up 2) = ULift.up (6 : ZMod (3 * 3)) := rfl

/-- At `ℓ = 3`, the second map is reduction modulo `3`: it sends `7` in `ZMod 9` to `1`. -/
example : (modSequence 3).g (ULift.up 7) = ULift.up (1 : ZMod 3) := rfl

end MathlibExtTest.AlgebraicGeometry.MotivicPowerCycleSourcesModCoefficientSequenceExact
