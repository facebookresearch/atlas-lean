/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Algebra_IsInvariant_moduleFinite_and_finiteType_of_finiteType.lean` and
`P2M/Sol/S_Algebra_IsInvariant_moduleFinite_and_finiteType_of_finiteType.lean`
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
framework; the statement and proof are reused here with that machinery
removed and the name restated in Mathlib style.
-/

module

public import Mathlib.RingTheory.Invariant.Basic
public import Mathlib.RingTheory.Finiteness.Basic

/-!
# Finiteness when the algebra-map image contains the fixed elements

Let `R → A → B` be an algebra tower over a Noetherian ring `R`, with
`algebraMap A B` injective and `B` finite type over `R`. Let a finite
group `G` act on `B` by semiring automorphisms. If every element fixed by `G` lies in the
image of `algebraMap A B`, then `B` is finite as an `A`-module and `A` is
finite type over `R`. This containment is `Algebra.IsInvariant A B G`.
It gives integrality of `B` over `A`; finite generation then descends
along the injective algebra map.
-/

@[expose] public section

/-- Over a Noetherian ring `R`, suppose `B` is finite type over `R` and
the faithful image of `A` in `B` contains every fixed element of a finite
group acting on `B` by semiring automorphisms. Then `B` is finite over `A`
and `A` is finite type over `R`. -/
theorem Algebra.IsInvariant.moduleFinite_and_finiteType_of_finiteType
    (R : Type*) [CommRing R] [IsNoetherianRing R]
    (A : Type*) [CommRing A] [Algebra R A]
    (B : Type*) [CommRing B] [Algebra R B] [Algebra A B] [IsScalarTower R A B]
    [FaithfulSMul A B]
    (G : Type*) [Group G] [Finite G] [MulSemiringAction G B] [Algebra.IsInvariant A B G]
    [Algebra.FiniteType R B] :
    Module.Finite A B ∧ Algebra.FiniteType R A := by
  have hint : Algebra.IsIntegral A B := Algebra.IsInvariant.isIntegral A B G
  have hftAB : Algebra.FiniteType A B := Algebra.FiniteType.of_restrictScalars_finiteType R A B
  have hfin : Module.Finite A B := Algebra.IsIntegral.finite
  refine ⟨hfin, ?_⟩
  have hAC : (⊤ : Subalgebra R B).FG := Algebra.FiniteType.out
  have hBC : (⊤ : Submodule A B).FG := Module.Finite.fg_top
  have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
  exact ⟨fg_of_fg_of_fg R A B hAC hBC hinj⟩
