/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RepresentationTheory.IrreducibleDimension

import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Tactic

namespace MathlibExtTest.RepresentationTheory.IrreducibleDimension

open _root_.CharacterTheory

universe u

/-- Every one-dimensional representation is irreducible: its subrepresentations
are the submodules of a one-dimensional space, hence only `⊥` and `⊤`. -/
theorem one_dim_rep_irreducible {G : Type u} [Group G] [Fintype G]
    {k : Type u} [Field k] (ρ : Representation k G k) :
    ρ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  refine (isSimpleModule_iff _ _).mpr ?_
  have h : Module.finrank k ρ.asModule = 1 := Module.finrank_self k
  exact is_simple_module_of_finrank_eq_one h

/-- The dimension-divides-order theorem applied to a one-dimensional
representation: `1 ∣ |G|`. -/
theorem finrank_one_dvd_card {G : Type u} [Group G] [Fintype G]
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    (ρ : Representation k G k) :
    Module.finrank k k ∣ Fintype.card G := by
  have : ρ.IsIrreducible := one_dim_rep_irreducible ρ
  exact irred_dim_dvd_card ρ

/-- The trivial representation of `S₃` on `ℂ` is one-dimensional, so its
dimension `1` divides `|S₃| = 6`. -/
theorem trivial_rep_s3_dim_dvd_card :
    Module.finrank ℂ ℂ ∣ Fintype.card (Equiv.Perm (Fin 3)) :=
  finrank_one_dvd_card (Representation.trivial ℂ (Equiv.Perm (Fin 3)) ℂ)

/-- The sign representation of `S₃`: a permutation `g` acts on `ℂ` by
multiplication by `sign g`. -/
noncomputable def signRep : Representation ℂ (Equiv.Perm (Fin 3)) ℂ where
  toFun g := ((Equiv.Perm.sign g : ℤ) : ℂ) • LinearMap.id
  map_one' := by
    apply LinearMap.ext
    intro x
    simp
  map_mul' := by
    intro g h
    apply LinearMap.ext
    intro x
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.id_apply,
      smul_eq_mul]
    rw [Equiv.Perm.sign_mul]
    simp only [Units.val_mul, Int.cast_mul]
    ring

/-- The sign representation of `S₃` is one-dimensional, so its dimension `1`
divides `|S₃| = 6`. -/
theorem sign_rep_s3_dim_dvd_card :
    Module.finrank ℂ ℂ ∣ Fintype.card (Equiv.Perm (Fin 3)) :=
  finrank_one_dvd_card signRep

/-- The theorem applies to an arbitrary irreducible representation, with no
one-dimensionality assumption. -/
theorem irred_dim_dvd_card_of_irreducible {G : Type u} [Group G] [Fintype G]
    {k : Type u} [Field k] [IsAlgClosed k] [CharZero k]
    {V : Type u} [AddCommGroup V] [Module k V] [FiniteDimensional k V]
    (ρ : Representation k G V) [ρ.IsIrreducible] :
    Module.finrank k V ∣ Fintype.card G :=
  irred_dim_dvd_card ρ

end MathlibExtTest.RepresentationTheory.IrreducibleDimension
