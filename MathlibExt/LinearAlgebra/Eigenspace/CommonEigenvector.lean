/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_Module_End_exists_common_eigenvector_of_commute.lean`
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
framework; the statement is reused here with that machinery removed and
the name restated in Mathlib style. The proof is new: it derives the result
from Mathlib's weight theory for Lie modules.
-/

module

public import Mathlib.FieldTheory.IsAlgClosed.Basic

import Mathlib.Algebra.Lie.Weights.Linear

@[expose] public section

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Module.End

/-- **Common eigenvector of commuting endomorphisms.** Let $K$ be an algebraically closed field
and $V$ a nonzero finite-dimensional vector space over $K$. Every family $(T_i)_{i \in \iota}$ of
pairwise commuting endomorphisms of $V$, indexed by an arbitrary type $\iota$, has a common
eigenvector: there are a nonzero $v \in V$ and scalars $\chi_i \in K$ with $T_i v = \chi_i v$ for
every $i$. -/
public theorem exists_common_eigenvector_of_commute
    {K : Type*} [Field K] [IsAlgClosed K] {V : Type*} [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Nontrivial V] {ι : Type*} (T : ι → Module.End K V)
    (hcomm : ∀ i j, Commute (T i) (T j)) :
    ∃ (χ : ι → K) (v : V), v ≠ 0 ∧ ∀ i, T i v = χ i • v := by
  -- The family spans an abelian Lie subalgebra of `Module.End K V`, and a weight of a nilpotent
  -- Lie algebra with linear weights has a simultaneous eigenvector.
  let L := LieSubalgebra.lieSpan K (Module.End K V) (Set.range T)
  have : IsLieAbelian L := LieSubalgebra.isLieAbelian_lieSpan_iff.mpr <| by
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    exact commute_iff_lie_eq.mp (hcomm i j)
  obtain ⟨χ, hχ⟩ := LieModule.exists_nontrivial_weightSpace_of_isNilpotent K L V
  obtain ⟨⟨v, hv⟩, hv0⟩ := exists_ne (0 : LieModule.weightSpace V χ)
  have hT (i : ι) : T i ∈ L := LieSubalgebra.subset_lieSpan ⟨i, rfl⟩
  refine ⟨fun i ↦ χ ⟨T i, hT i⟩, v, fun h ↦ hv0 (by subst h; rfl), fun i ↦ ?_⟩
  rw [LieModule.mem_weightSpace] at hv
  exact hv ⟨T i, hT i⟩

end Module.End
