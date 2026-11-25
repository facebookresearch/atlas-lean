/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_IsFinite_of_comp_of_surjective.lean`
and
`P2M/Sol/S_AlgebraicGeometry_IsFinite_of_comp_of_surjective.lean`
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
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.IsFinite

/-- Finiteness of a composite `f ≫ g` descends to `g` when `f` is
surjective, `g` is locally of finite type and separated: `g` is then
proper with finite fibers, hence finite. -/
public theorem of_comp_of_surjective {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) [Surjective f] [IsFinite (f ≫ g)]
    [LocallyOfFiniteType g] [IsSeparated g] : IsFinite g := by
  haveI : UniversallyClosed g := UniversallyClosed.of_comp_surjective f g
  haveI : IsProper g := IsProper.mk
  haveI : LocallyQuasiFinite g := by
    rw [locallyQuasiFinite_iff_finite_preimage_singleton]
    intro z
    have hfin := (f ≫ g).finite_preimage_singleton z
    have hsub : g.base ⁻¹' {z} ⊆ f.base '' ((f ≫ g).base ⁻¹' {z}) := by
      intro y hy
      obtain ⟨x, rfl⟩ := f.surjective y
      exact ⟨x, by simpa [Scheme.Hom.comp_apply] using hy, rfl⟩
    exact (hfin.image _).subset hsub
  exact IsFinite.of_isProper_of_locallyQuasiFinite g

end AlgebraicGeometry.IsFinite
