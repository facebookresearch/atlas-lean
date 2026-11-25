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
framework; the statement is reused here with that machinery
removed and the names restated in Mathlib style.
-/

module

public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

@[expose] public section

open Matrix

namespace GaloisRep

/-- A local representation has Deligne's ordinary shape when, in some basis,
it is upper-triangular (the lower-left entry `(1, 0)` vanishes), inertia acts
on the lower-right entry trivially and on the upper-left entry through
`χ ^ (k - 1)`, Frobenius has lower-right entry `ap`, and `ap` times the
upper-left Frobenius entry is `χ(frob) ^ (k - 1) * εp`. -/
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

/-- A change of basis witnessing the ordinary shape. Every accessor below is
stated for this one element, so its clauses can be combined. -/
public noncomputable def conj (h : DeligneOrdinaryShape ρloc I frob χ k ap εp) :
    GL (Fin 2) A :=
  Classical.choose h

/-- Conjugation by `h.conj` makes every group element upper-triangular. -/
public theorem conj_apply_one_zero
    (h : DeligneOrdinaryShape ρloc I frob χ k ap εp) (σ : H) :
    (h.conj * ρloc σ * h.conj⁻¹).val 1 0 = 0 :=
  (Classical.choose_spec h).1 σ

/-- After conjugation by `h.conj`, inertia has lower-right entry `1`. -/
public theorem conj_inertia_apply_one_one
    (h : DeligneOrdinaryShape ρloc I frob χ k ap εp) {σ : H} (hσ : σ ∈ I) :
    (h.conj * ρloc σ * h.conj⁻¹).val 1 1 = 1 :=
  (Classical.choose_spec h).2.1 σ hσ

/-- After conjugation by `h.conj`, Frobenius has lower-right entry `ap`. -/
public theorem conj_frob_apply_one_one
    (h : DeligneOrdinaryShape ρloc I frob χ k ap εp) :
    (h.conj * ρloc frob * h.conj⁻¹).val 1 1 = ap :=
  (Classical.choose_spec h).2.2.1

/-- After conjugation by `h.conj`, inertia acts on the upper-left entry
through `χ ^ (k - 1)`. -/
public theorem conj_inertia_apply_zero_zero
    (h : DeligneOrdinaryShape ρloc I frob χ k ap εp) {σ : H} (hσ : σ ∈ I) :
    (h.conj * ρloc σ * h.conj⁻¹).val 0 0 = χ σ ^ (k - 1) :=
  (Classical.choose_spec h).2.2.2.1 σ hσ

/-- After conjugation by `h.conj`, `ap` times the upper-left Frobenius entry
is `χ(frob) ^ (k - 1) * εp`. -/
public theorem conj_frob_mul_apply_zero_zero
    (h : DeligneOrdinaryShape ρloc I frob χ k ap εp) :
    ap * (h.conj * ρloc frob * h.conj⁻¹).val 0 0 = χ frob ^ (k - 1) * εp :=
  (Classical.choose_spec h).2.2.2.2

end DeligneOrdinaryShape

/-- The trivial representation has the ordinary shape with `ap = 1` and
`εp = 1` for the trivial character: every conjugated entry condition is
checked in the identity basis. -/
public theorem deligneOrdinaryShape_one {A : Type*} [CommRing A]
    {H : Type*} [Group H] (I : Subgroup H) (frob : H) (k : ℕ) :
    DeligneOrdinaryShape (1 : H →* GL (Fin 2) A) I frob 1 k 1 1 := by
  refine ⟨1, ?_, ?_, ?_, ?_, ?_⟩ <;> simp

end GaloisRep
