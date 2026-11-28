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
public import Mathlib.Algebra.Algebra.Subalgebra.Tower
public import Mathlib.LinearAlgebra.TensorProduct.Basic
public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.RingTheory.TensorProduct.Basic

@[expose] public section

open scoped TensorProduct

universe u v w

variable {R : Type u} [CommRing R]
variable {F : Type v} [Field F] [Algebra R F]
variable {G : Type w} [CommRing G] [Algebra R G]

/-- **Flat closure of a subalgebra.** The flat closure of an `F`-subalgebra `B` of
`F ⊗[R] G`, for a field `F` that is an `R`-algebra and a commutative `R`-algebra `G`: the
preimage of `B` under `g ↦ 1 ⊗ g`, an `R`-subalgebra of `G`. -/
def flatClosure (B : Subalgebra F (F ⊗[R] G)) : Subalgebra R G :=
  (B.restrictScalars R).comap Algebra.TensorProduct.includeRight

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

/-- **Finiteness of the flat closure.** Over a Noetherian ring `R`, for a field `F` that is an
`R`-algebra and a commutative `R`-algebra `G` that is finitely generated as an `R`-module, the
flat closure of an `F`-subalgebra of `F ⊗[R] G` is finitely generated as an `R`-module. -/
theorem flatClosure_finite [IsNoetherianRing R] [Module.Finite R G]
    (B : Subalgebra F (F ⊗[R] G)) : Module.Finite R (flatClosure B) := by
  have : IsNoetherian R G := isNoetherian_of_isNoetherianRing_of_finite R G
  exact Module.Finite.iff_fg.mpr
    (IsNoetherian.noetherian (Subalgebra.toSubmodule (flatClosure B)))

/-- **Torsion-freeness of the flat closure.** For a field `F` that is an `R`-algebra and a
commutative `R`-algebra `G` that is torsion-free as an `R`-module, the flat closure of an
`F`-subalgebra of `F ⊗[R] G` is torsion-free. -/
theorem flatClosure_isTorsionFree [Module.IsTorsionFree R G]
    (B : Subalgebra F (F ⊗[R] G)) : Module.IsTorsionFree R (flatClosure B) :=
  inferInstance

/-- **Freeness of the flat closure over a principal ideal domain.** Over a principal ideal
domain `R`, for a field `F` that is an `R`-algebra and a commutative `R`-algebra `G` that is
finite and torsion-free as an `R`-module, the flat closure of an `F`-subalgebra of `F ⊗[R] G`
is a free `R`-module. -/
theorem flatClosure_free [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Finite R G] [Module.IsTorsionFree R G]
    (B : Subalgebra F (F ⊗[R] G)) : Module.Free R (flatClosure B) := by
  have := flatClosure_finite (R := R) (F := F) (G := G) B
  have := flatClosure_isTorsionFree (R := R) (F := F) (G := G) B
  exact Module.free_of_finite_type_torsion_free'

/-- **Flatness of the flat closure over a principal ideal domain.** Over a principal ideal
domain `R`, for a field `F` that is an `R`-algebra and a commutative `R`-algebra `G` that is
finite and torsion-free as an `R`-module, the flat closure of an `F`-subalgebra of `F ⊗[R] G`
is a flat `R`-module. -/
theorem flatClosure_flat [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Finite R G] [Module.IsTorsionFree R G]
    (B : Subalgebra F (F ⊗[R] G)) : Module.Flat R (flatClosure B) := by
  have := flatClosure_free (R := R) (F := F) (G := G) B
  exact Module.Flat.of_free
