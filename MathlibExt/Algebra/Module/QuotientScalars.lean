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
# Descending a module action to a quotient ring

An ideal that annihilates a module lies in the kernel of its action on additive
endomorphisms. The quotient action is obtained by factoring that same ring
homomorphism. Its characteristic formula retains the original scalar action.
-/

@[expose] public section

namespace Module

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- Factor the original action through a two-sided ideal that annihilates the module. -/
def quotientAction (I : Ideal R) [I.IsTwoSided]
    (hI : ∀ r ∈ I, ∀ m : M, r • m = 0) : R ⧸ I →+* AddMonoid.End M :=
  Ideal.Quotient.lift I (Module.toAddMonoidEnd R M) fun r hr =>
    AddMonoidHom.ext fun m => hI r hr m

/-- The descended action on a quotient representative is the original action. -/
@[simp]
theorem quotientAction_mk_apply (I : Ideal R) [I.IsTwoSided]
    (hI : ∀ r ∈ I, ∀ m : M, r • m = 0) (r : R) (m : M) :
    quotientAction I hI (Ideal.Quotient.mk I r) m = r • m := rfl

/-- The quotient module structure induced by the original action.
This is a reducible non-instance, so a caller chooses which quotient acts. -/
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

/-- Restricting the descended scalar structure along the quotient map recovers
the original action on every element. -/
theorem quotientScalars_mk_smul (I : Ideal R) [I.IsTwoSided]
    (hI : ∀ r ∈ I, ∀ m : M, r • m = 0) (r : R) (m : M) :
    letI := quotientScalars I hI
    Ideal.Quotient.mk I r • m = r • m := rfl

/-- The quotient scalar action and the original action form the expected scalar tower. -/
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

/-- Finite generation of an annihilated module is retained over the quotient ring. -/
theorem finite_quotientScalars (I : Ideal R) [I.IsTwoSided]
    (hI : ∀ r ∈ I, ∀ m : M, r • m = 0) [Module.Finite R M] :
    letI := quotientScalars I hI
    Module.Finite (R ⧸ I) M := by
  let := quotientScalars I hI
  let := quotientScalarsTower I hI
  exact Module.Finite.of_restrictScalars_finite R (R ⧸ I) M

variable {N : Type*} [AddCommGroup N] [Module R N]

/-- An original linear map between annihilated modules is linear for the
descended quotient actions. Its underlying map is unchanged. -/
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

@[simp]
theorem quotientScalarsMap_apply (I : Ideal R) [I.IsTwoSided]
    (hM : ∀ r ∈ I, ∀ m : M, r • m = 0)
    (hN : ∀ r ∈ I, ∀ n : N, r • n = 0) (f : M →ₗ[R] N) (m : M) :
    quotientScalarsMap I hM hN f m = f m := rfl

end Module
