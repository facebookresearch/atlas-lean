/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Theorems/Thm_AlgebraicGeometry_exists_over_hom_base_closedPoint_eq_of_isClosed_singleton.lean`
and
`P2M/Sol/S_AlgebraicGeometry_exists_over_hom_base_closedPoint_eq_of_isClosed_singleton.lean`
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

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# Closed points of a scheme over an algebraically closed field

A closed point of a scheme of finite type over an algebraically closed
field is the image of the closed point of the residue field under the
morphism from the spectrum of the residue field.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A closed point of a scheme of finite type over an algebraically
closed field lifts to a point over the base. -/
theorem exists_over_hom_base_closedPoint_eq_of_isClosed_singleton
    (k : Type u) [Field k] [IsAlgClosed k] {X : Scheme.{u}} (t : X ⟶ Spec (CommRingCat.of k))
    [LocallyOfFiniteType t] (x : X) (hx : IsClosed ({x} : Set X)) :
    ∃ z : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ Over.mk t,
      z.left.base (IsLocalRing.closedPoint k) = x := by
  refine ⟨Over.homMk (Spec.map (residueFieldIsoBase t x hx).hom ≫ X.fromSpecResidueField x) ?_, ?_⟩
  · change (Spec.map (residueFieldIsoBase t x hx).hom ≫ X.fromSpecResidueField x) ≫ t = 𝟙 _
    rw [Category.assoc, ← SpecMap_residueFieldIsoBase_inv t x hx, ← Spec.map_comp, Iso.inv_hom_id,
      Spec.map_id]
  · change (Spec.map (residueFieldIsoBase t x hx).hom ≫ X.fromSpecResidueField x).base
        (IsLocalRing.closedPoint k) = x
    have hmem : (Spec.map (residueFieldIsoBase t x hx).hom ≫ X.fromSpecResidueField x).base
        (IsLocalRing.closedPoint k) ∈ Set.range (X.fromSpecResidueField x).base :=
      ⟨(Spec.map (residueFieldIsoBase t x hx).hom).base (IsLocalRing.closedPoint k), rfl⟩
    rw [Scheme.range_fromSpecResidueField] at hmem
    exact hmem

end AlgebraicGeometry
