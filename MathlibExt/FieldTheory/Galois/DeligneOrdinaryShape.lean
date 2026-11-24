/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_GaloisRep_DeligneOrdinaryShape.lean`
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

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

open Matrix

namespace GaloisRep

/-- A local representation has Deligne's ordinary shape when, in some basis,
it is lower-triangular, inertia acts on the lower-right entry trivially and
on the upper-left entry through `χ ^ (k - 1)`, Frobenius has lower-right
entry `ap`, and the two diagonal Frobenius entries multiply, up to `ap`, to
`χ(frob) ^ (k - 1) * εp`. -/
public def DeligneOrdinaryShape {A : Type*} [CommRing A] {H : Type*}
    [Group H] (ρloc : H →* GL (Fin 2) A) (I : Subgroup H) (frob : H)
    (χ : H →* A) (k : ℕ) (ap εp : A) : Prop :=
  ∃ g : GL (Fin 2) A,
    (∀ σ : H, (g * ρloc σ * g⁻¹).val 1 0 = 0) ∧
    (∀ σ ∈ I, (g * ρloc σ * g⁻¹).val 1 1 = 1) ∧
    (g * ρloc frob * g⁻¹).val 1 1 = ap ∧
    (∀ σ ∈ I, (g * ρloc σ * g⁻¹).val 0 0 = χ σ ^ (k - 1)) ∧
    ap * (g * ρloc frob * g⁻¹).val 0 0 = χ frob ^ (k - 1) * εp

namespace DeligneOrdinaryShape

variable {A : Type*} [CommRing A] {H : Type*} [Group H]
  {ρloc : H →* GL (Fin 2) A} {I : Subgroup H} {frob : H}
  {χ : H →* A} {k : ℕ} {ap εp : A}

/-- In the ordinary shape, some conjugate of every group element is
lower-triangular. -/
public theorem exists_conj_apply_one_zero
    (h : DeligneOrdinaryShape ρloc I frob χ k ap εp) (σ : H) :
    ∃ g : GL (Fin 2) A, (g * ρloc σ * g⁻¹).val 1 0 = 0 := by
  obtain ⟨g, hg, -, -, -, -⟩ := h
  exact ⟨g, hg σ⟩

/-- In the ordinary shape, inertia has lower-right entry `1` after the
same conjugation that makes the representation lower-triangular. -/
public theorem exists_conj_inertia_apply_one_one
    (h : DeligneOrdinaryShape ρloc I frob χ k ap εp) {σ : H} (hσ : σ ∈ I) :
    ∃ g : GL (Fin 2) A, (g * ρloc σ * g⁻¹).val 1 1 = 1 := by
  obtain ⟨g, -, hg, -, -, -⟩ := h
  exact ⟨g, hg σ hσ⟩

/-- In the ordinary shape, the conjugated Frobenius has lower-right
entry `ap`. -/
public theorem exists_conj_frob_apply_one_one
    (h : DeligneOrdinaryShape ρloc I frob χ k ap εp) :
    ∃ g : GL (Fin 2) A, (g * ρloc frob * g⁻¹).val 1 1 = ap := by
  obtain ⟨g, -, -, hg, -, -⟩ := h
  exact ⟨g, hg⟩

/-- The upper-left Frobenius entry is constrained by the determinant-type
identity in the shape: `ap` times that entry equals
`χ(frob) ^ (k - 1) * εp` for the witnessing basis. -/
public theorem exists_conj_frob_mul_apply_zero_zero
    (h : DeligneOrdinaryShape ρloc I frob χ k ap εp) :
    ∃ g : GL (Fin 2) A,
      ap * (g * ρloc frob * g⁻¹).val 0 0 = χ frob ^ (k - 1) * εp := by
  obtain ⟨g, -, -, -, -, hg⟩ := h
  exact ⟨g, hg⟩

end DeligneOrdinaryShape

/-- The trivial representation has the ordinary shape with `ap = 1` and
`εp = 1` for the trivial character: every conjugated entry condition is
checked in the identity basis. -/
public theorem deligneOrdinaryShape_one {A : Type*} [CommRing A]
    {H : Type*} [Group H] (I : Subgroup H) (frob : H) (k : ℕ) :
    DeligneOrdinaryShape (1 : H →* GL (Fin 2) A) I frob 1 k 1 1 := by
  refine ⟨1, ?_, ?_, ?_, ?_, ?_⟩ <;> simp

end GaloisRep
