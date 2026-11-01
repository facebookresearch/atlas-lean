/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_RingHom_exists_comp_algebraMap_eq_and_ker_eq_of_isIntegral_
of_isAlgClosed.lean`
and
`P2M/Sol/S_RingHom_exists_comp_algebraMap_eq_and_ker_eq_of_isIntegral_
of_isAlgClosed.lean`
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

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic

@[expose] public section

namespace RingHom

/-- A homomorphism from `R` to an algebraically closed field extends to an
integral extension `S` with any prescribed prime kernel lying over `ker χ`.

This is the key step for extending points of a scheme along integral
morphisms, for going-up arguments, and for lifting maps through integral
closures: the kernel control `RingHom.ker χ' = Q` says the lifted map has
exactly the prescribed residue behavior. -/
theorem exists_comp_algebraMap_eq_and_ker_eq_of_isIntegral_of_isAlgClosed
    {R S K : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.IsIntegral R S]
    [Field K] [IsAlgClosed K] (χ : R →+* K)
    (Q : Ideal S) [Q.IsPrime] (hQ : Q.comap (algebraMap R S) = RingHom.ker χ) :
    ∃ χ' : S →+* K, χ'.comp (algebraMap R S) = χ ∧ RingHom.ker χ' = Q := by
  classical
  have hP : (Q.comap (algebraMap R S)).IsPrime :=
    Ideal.comap_isPrime (algebraMap R S) Q
  have hle : ∀ a ∈ Q.comap (algebraMap R S), χ a = 0 :=
    fun a ha => RingHom.mem_ker.mp (hQ ▸ ha)
  let ψ : (R ⧸ Q.comap (algebraMap R S)) →+* K := Ideal.Quotient.lift _ χ hle
  have hψinj : Function.Injective ψ :=
    RingHom.lift_injective_of_ker_le_ideal _ hle hQ.ge
  let _ : Algebra (R ⧸ Q.comap (algebraMap R S)) K := ψ.toAlgebra
  have _ : IsDomain (S ⧸ Q) := Ideal.Quotient.isDomain Q
  haveI : IsDomain (R ⧸ Q.comap (algebraMap R S)) := Ideal.Quotient.isDomain _
  haveI : Module.IsTorsionFree (R ⧸ Q.comap (algebraMap R S)) (S ⧸ Q) :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      Ideal.algebraMap_quotient_injective
  haveI : Module.IsTorsionFree (R ⧸ Q.comap (algebraMap R S)) K :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr hψinj
  haveI : Algebra.IsAlgebraic (R ⧸ Q.comap (algebraMap R S)) (S ⧸ Q) :=
    Algebra.IsIntegral.isAlgebraic
  let θ : (S ⧸ Q) →ₐ[R ⧸ Q.comap (algebraMap R S)] K := IsAlgClosed.lift
  refine ⟨θ.toRingHom.comp (Ideal.Quotient.mk Q), ?_, ?_⟩
  · ext a
    change θ (Ideal.Quotient.mk Q (algebraMap R S a)) = χ a
    have h1 : Ideal.Quotient.mk Q (algebraMap R S a)
        = algebraMap (R ⧸ Q.comap (algebraMap R S)) (S ⧸ Q)
            (Ideal.Quotient.mk _ a) := rfl
    rw [h1, θ.commutes]
    exact Ideal.Quotient.lift_mk _ χ _
  · have hker : RingHom.ker θ.toRingHom = ⊥ := by
      apply Ideal.eq_bot_of_under_eq_bot (R := R ⧸ Q.comap (algebraMap R S))
        (S := S ⧸ Q)
      rw [Ideal.under_def, eq_bot_iff]
      intro x hx
      rw [Ideal.mem_comap, RingHom.mem_ker] at hx
      change θ (algebraMap (R ⧸ Q.comap (algebraMap R S)) (S ⧸ Q) x) = 0 at hx
      rw [θ.commutes] at hx
      exact (Ideal.mem_bot).mpr (hψinj (by rw [map_zero]; exact hx))
    rw [← RingHom.comap_ker, hker, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]

end RingHom
