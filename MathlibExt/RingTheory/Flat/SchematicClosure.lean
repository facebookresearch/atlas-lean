/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_FiniteFlat_SchematicClosure.lean`
(https://github.com/anthropics/fermats-last-theorem):
Compared with the source file at commit
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

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Module.Torsion.Free

@[expose] public section

open scoped TensorProduct

universe u v w

variable {R : Type u} [CommRing R]
variable {F : Type v} [Field F] [Algebra R F]
variable {G : Type w} [CommRing G] [Algebra R G]

instance : IsScalarTower R F (F ⊗[R] G) :=
  IsScalarTower.of_algebraMap_eq fun _ => rfl

/-- The schematic closure of a subalgebra `B` of `F ⊗[R] G` in `G`: the
`R`-subalgebra of elements of `G` whose image `1 ⊗ g` lies in `B`. -/
def flatClosure (B : Subalgebra F (F ⊗[R] G)) : Subalgebra R G where
  carrier := {g : G | (1 : F) ⊗ₜ[R] g ∈ B}
  mul_mem' {a b} ha hb := by
    have h : ((1 : F) ⊗ₜ[R] a) * ((1 : F) ⊗ₜ[R] b) ∈ B := mul_mem ha hb
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul] at h
    exact h
  one_mem' := by
    show (1 : F) ⊗ₜ[R] (1 : G) ∈ B
    rw [← Algebra.TensorProduct.one_def]
    exact one_mem B
  add_mem' {a b} ha hb := by
    have h : ((1 : F) ⊗ₜ[R] a) + ((1 : F) ⊗ₜ[R] b) ∈ B := add_mem ha hb
    rw [← TensorProduct.tmul_add] at h
    exact h
  zero_mem' := by
    show (1 : F) ⊗ₜ[R] (0 : G) ∈ B
    rw [TensorProduct.tmul_zero]
    exact zero_mem B
  algebraMap_mem' r := by
    show (1 : F) ⊗ₜ[R] (algebraMap R G r) ∈ B
    have h1 : (1 : F) ⊗ₜ[R] (algebraMap R G r)
        = (algebraMap R F r) ⊗ₜ[R] (1 : G) := by
      rw [Algebra.algebraMap_eq_smul_one r, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul', ← Algebra.algebraMap_eq_smul_one]
    rw [h1, ← Algebra.TensorProduct.algebraMap_apply]
    exact B.algebraMap_mem _

@[simp]
lemma mem_flatClosure_iff {B : Subalgebra F (F ⊗[R] G)} {g : G} :
    g ∈ flatClosure B ↔ (1 : F) ⊗ₜ[R] g ∈ B :=
  Iff.rfl

lemma flatClosure_mono {B B' : Subalgebra F (F ⊗[R] G)} (h : B ≤ B') :
    flatClosure B ≤ flatClosure B' :=
  fun _ hg => h hg

lemma le_flatClosure_iff {B : Subalgebra F (F ⊗[R] G)} {S : Subalgebra R G} :
    S ≤ flatClosure B ↔ ∀ g ∈ S, (1 : F) ⊗ₜ[R] g ∈ B :=
  Iff.rfl

/-- The schematic closure is finitely generated as an `R`-module when `G`
is, over a Noetherian ring. -/
theorem flatClosure_finite [IsNoetherianRing R] [Module.Finite R G]
    (B : Subalgebra F (F ⊗[R] G)) : Module.Finite R (flatClosure B) := by
  haveI : IsNoetherian R G := isNoetherian_of_isNoetherianRing_of_finite R G
  exact Module.Finite.iff_fg.mpr
    (IsNoetherian.noetherian (Subalgebra.toSubmodule (flatClosure B)))

/-- The schematic closure is torsion-free when `G` is. -/
theorem flatClosure_isTorsionFree [Module.IsTorsionFree R G]
    (B : Subalgebra F (F ⊗[R] G)) : Module.IsTorsionFree R (flatClosure B) :=
  Function.Injective.moduleIsTorsionFree _ Subtype.coe_injective (fun _ _ => rfl)

/-- Over a PID, the schematic closure of a finite torsion-free algebra is
free. -/
theorem flatClosure_free [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [Module.Finite R G] [Module.IsTorsionFree R G]
    (B : Subalgebra F (F ⊗[R] G)) : Module.Free R (flatClosure B) := by
  haveI := flatClosure_finite (R := R) (F := F) (G := G) B
  haveI := flatClosure_isTorsionFree (R := R) (F := F) (G := G) B
  exact Module.free_of_finite_type_torsion_free'

/-- Over a PID, the schematic closure of a finite torsion-free algebra is
flat. -/
theorem flatClosure_flat [IsDomain R] [IsPrincipalIdealRing R] [IsNoetherianRing R]
    [Module.Finite R G] [Module.IsTorsionFree R G]
    (B : Subalgebra F (F ⊗[R] G)) : Module.Flat R (flatClosure B) := by
  haveI := flatClosure_free (R := R) (F := F) (G := G) B
  exact Module.Flat.of_free
