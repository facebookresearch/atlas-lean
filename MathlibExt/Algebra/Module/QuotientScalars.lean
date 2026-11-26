/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/

module

public import Mathlib.Algebra.Module.End
public import Mathlib.Algebra.Module.RingHom
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Descending module scalars through an annihilating ideal

Let I be a two-sided ideal of a ring R annihilating an R-module M. Factoring the scalar action
gives an R/I-module structure on the same additive group, with (r mod I)·m=r·m.

The original and quotient actions form a scalar tower. Finite generation passes to the
quotient scalar ring, and R-linear maps between annihilated modules become R/I-linear with the
same values.
-/

@[expose] public section

namespace Module

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- The action homomorphism factored through the quotient ring.

An annihilating two-sided ideal lets the scalar action factor as R/I → End_add(M). -/
def quotientAction (I : Ideal R) [I.IsTwoSided]
    (hI : ∀ r ∈ I, ∀ m : M, r • m = 0) : R ⧸ I →+* AddMonoid.End M :=
  Ideal.Quotient.lift I (Module.toAddMonoidEnd R M) fun r hr =>
    AddMonoidHom.ext fun m => hI r hr m

/-- The quotient action on a scalar representative.

The class of r acts on m as the original scalar r. -/
@[simp]
theorem quotientAction_mk_apply (I : Ideal R) [I.IsTwoSided]
    (hI : ∀ r ∈ I, ∀ m : M, r • m = 0) (r : R) (m : M) :
    quotientAction I hI (Ideal.Quotient.mk I r) m = r • m := rfl

/-- The descended quotient-ring module structure.

Give M its R/I-action through quotientAction. -/
abbrev quotientScalars (I : Ideal R) [I.IsTwoSided]
    (hI : ∀ r ∈ I, ∀ m : M, r • m = 0) : Module (R ⧸ I) M :=
  { smul := fun r m => quotientAction I hI r m
    one_smul := fun m => by change quotientAction I hI 1 m = m; rw [map_one]; rfl
    mul_smul := fun r s m => by
      change quotientAction I hI (r * s) m = _
      rw [map_mul]
      rfl
    smul_add := fun r m n => (quotientAction I hI r).map_add m n
    smul_zero := fun r => (quotientAction I hI r).map_zero
    add_smul := fun r s m => by
      change quotientAction I hI (r + s) m = _
      rw [map_add]
      rfl
    zero_smul := fun m => by change quotientAction I hI 0 m = 0; rw [map_zero]; rfl }

/-- The descended scalar multiplication formula.

The class of r in R/I sends m to r·m. -/
theorem quotientScalars_mk_smul (I : Ideal R) [I.IsTwoSided]
    (hI : ∀ r ∈ I, ∀ m : M, r • m = 0) (r : R) (m : M) :
    letI := quotientScalars I hI
    Ideal.Quotient.mk I r • m = r • m := rfl

/-- The scalar tower of original and quotient actions.

The two actions satisfy IsScalarTower R (R/I) M. -/
theorem quotientScalarsTower (I : Ideal R) [I.IsTwoSided]
    (hI : ∀ r ∈ I, ∀ m : M, r • m = 0) :
    letI := quotientScalars I hI
    IsScalarTower R (R ⧸ I) M := by
  let := quotientScalars I hI
  constructor
  intro r s m
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective s
  change (quotientAction I hI (r • Ideal.Quotient.mk I a)) m =
    r • quotientAction I hI (Ideal.Quotient.mk I a) m
  change (r * a) • m = r • a • m
  exact mul_smul r a m

/-- Finite generation passes to the quotient scalars.

If M is finite over R and I annihilates it, it is finite over R/I. -/
theorem finite_quotientScalars (I : Ideal R) [I.IsTwoSided]
    (hI : ∀ r ∈ I, ∀ m : M, r • m = 0) [Module.Finite R M] :
    letI := quotientScalars I hI
    Module.Finite (R ⧸ I) M := by
  let := quotientScalars I hI
  let := quotientScalarsTower I hI
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ I) M

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- The quotient-linear form of an original linear map.

An R-linear map between I-annihilated modules is R/I-linear for the descended actions. -/
def quotientScalarsMap (I : Ideal R) [I.IsTwoSided]
    (hM : ∀ r ∈ I, ∀ m : M, r • m = 0)
    (hN : ∀ r ∈ I, ∀ n : N, r • n = 0) (f : M →ₗ[R] N) :
    letI := quotientScalars I hM
    letI := quotientScalars I hN
    M →ₗ[R ⧸ I] N := by
  letI := quotientScalars I hM
  letI := quotientScalars I hN
  exact
    { f.toAddMonoidHom with
      map_smul' := fun r m => by
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective r
        exact f.map_smul a m }

/-- The values of the quotient-linear map are unchanged.

The descended linear map sends m to the original f(m). -/
@[simp]
theorem quotientScalarsMap_apply (I : Ideal R) [I.IsTwoSided]
    (hM : ∀ r ∈ I, ∀ m : M, r • m = 0)
    (hN : ∀ r ∈ I, ∀ n : N, r • n = 0) (f : M →ₗ[R] N) (m : M) :
    quotientScalarsMap I hM hN f m = f m := rfl

end Module
