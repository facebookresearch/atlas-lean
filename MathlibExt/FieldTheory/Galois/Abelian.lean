/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Order
public import Mathlib.FieldTheory.Galois.Abelian

@[expose] public section

/-!
# Intermediate fields of an abelian Galois extension form a modular lattice

For a finite-dimensional abelian Galois extension `L / K`, the lattice
`IntermediateField K L` is modular. The proof transports Mathlib's existing
modular-lattice structure on subgroups of the commutative Galois group across the
Galois correspondence `IsGalois.intermediateFieldEquivSubgroup`.

## ATLAS provenance

This constructor generalizes the cyclotomic prerequisite proved in
`Atlas/NumberTheoryI/code/AnalyticClassNumber.lean` at revision
`e8b31c5cb0bec89b487ce33fe525a2c0b0f8b9c6`, lines 1627--1651
(`cyclotomicSubgroupModular`, `cyclotomicIntermediateFieldModular`), which supports
the N390 development. Source-to-API mapping: `cyclotomicIntermediateFieldModular`
maps to `IsAbelianGalois.isModularLattice_intermediateField`.
Only the intermediate-field modularity prerequisite is
generalized here: the constructor replaces the cyclotomic-specific
`cyclotomicIntermediateFieldModular` argument, not the remainder of N390. The
companion cyclotomic subgroup fact is not ported since it duplicates Mathlib's
existing `IsModularLattice (Subgroup C)` instance for commutative groups.

## Design

The result is a named noncomputable constructor rather than a global instance, so
downstream proofs install it locally with
`letI := IsAbelianGalois.isModularLattice_intermediateField`.
-/

open scoped IsMulCommutative

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [IsAbelianGalois K L]

namespace IsAbelianGalois

/-- **Intermediate fields of an abelian extension form a modular lattice.** If $L/K$ is a
finite-dimensional abelian Galois extension, then the lattice of intermediate fields of $L/K$
is modular.

The proof transports the modular lattice of subgroups of the commutative Galois group across
the Galois correspondence. -/
theorem isModularLattice_intermediateField :
    IsModularLattice (IntermediateField K L) := by
  have e := IsGalois.intermediateFieldEquivSubgroup (F := K) (E := L)
  constructor
  intro x y z hxz
  have h := IsModularLattice.sup_inf_le_assoc_of_le (e y) (e.le_iff_le.mpr hxz)
  rw [← e.map_sup, ← e.map_inf, ← e.map_inf, ← e.map_sup] at h
  exact e.le_iff_le.mp h

end IsAbelianGalois
