/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_FormallyUnramified_nonempty_ringHom_int.lean`
and
`P2M/Sol/S_Algebra_FormallyUnramified_nonempty_ringHom_int.lean`
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

public import Mathlib.NumberTheory.NumberField.ExistsRamified
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Unramified.Basic

@[expose] public section

namespace Algebra.FormallyUnramified

private theorem nonempty_ringEquiv_int_of_isDomain
    (D : Type*) [CommRing D] [IsDomain D] [CharZero D] [Module.Finite ℤ D]
    [Algebra.FormallyUnramified ℤ D] : Nonempty (D ≃+* ℤ) := by
  haveI : Algebra.Unramified ℤ D := ⟨inferInstance, inferInstance⟩
  exact ⟨(RingEquiv.ofBijective (algebraMap ℤ D)
    (bijective_algebraMap_int_of_finite_of_unramified (𝒪 := D))).symm⟩

/-- Every nontrivial finite flat formally unramified `ℤ`-algebra admits a ring
homomorphism to `ℤ`. -/
theorem nonempty_ringHom_int
    (B : Type*) [CommRing B] [Nontrivial B] [Module.Finite ℤ B] [Module.Flat ℤ B]
    [Algebra.FormallyUnramified ℤ B] : Nonempty (B →+* ℤ) := by
  classical
  obtain ⟨Q, -, hQp, hQ⟩ :=
    Ideal.exists_ideal_over_prime_of_isIntegral (R := ℤ) (S := B) (⊥ : Ideal ℤ) (⊥ : Ideal B)
      (by simp)
  haveI : IsDomain (B ⧸ Q) := Ideal.Quotient.isDomain Q
  haveI : Module.Finite ℤ (B ⧸ Q) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ ℤ Q).toLinearMap
      (Ideal.Quotient.mkₐ_surjective ℤ Q)
  haveI : @Algebra.FormallyUnramified ℤ (B ⧸ Q) _ _ (Ring.toIntAlgebra _) :=
    (Subsingleton.elim (Ideal.instAlgebraQuotient ℤ Q : Algebra ℤ (B ⧸ Q))
      (Ring.toIntAlgebra _)) ▸ Algebra.FormallyUnramified.comp ℤ B (B ⧸ Q)
  have hinj : Function.Injective (algebraMap ℤ (B ⧸ Q)) := by
    rw [RingHom.injective_iff_ker_eq_bot, IsScalarTower.algebraMap_eq ℤ B (B ⧸ Q),
      ← RingHom.comap_ker, Ideal.Quotient.algebraMap_eq, Ideal.mk_ker]
    exact hQ
  haveI : CharZero (B ⧸ Q) := charZero_of_injective_algebraMap hinj
  obtain ⟨e⟩ := nonempty_ringEquiv_int_of_isDomain (B ⧸ Q)
  exact ⟨e.toRingHom.comp (Ideal.Quotient.mk Q)⟩

end Algebra.FormallyUnramified
