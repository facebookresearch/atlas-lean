/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`Definitions/Def_AlgebraicGeometry_OrderedAffineCoverCechCup.lean`
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

public import MathlibExt.AlgebraicGeometry.OrderedAffineCover.Cech

/-!
# Cup product of alternating Čech cochains

For an ordered affine cover `K`, the cup product of a cochain `α` of the structure presheaf in
degree `a` with a cochain `β` of `F` in degree `b` is the degree `a + b` cochain whose value on
`s₀ < ⋯ < sₙ` is `α(s₀, …, s_a) • β(s_a, …, sₙ)`, both restricted to the intersection.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace AlgebraicGeometry

open CategoryTheory Opposite TopologicalSpace

namespace Scheme.OrderedAffineCover

variable {V : Scheme.{u}} (K : V.OrderedAffineCover)

/-- The front `a`-face `(s₀, …, s_a)` of a strictly increasing `(n + 1)`-tuple `(s₀, …, sₙ)`,
`a + b = n`. -/
def frontFace (a b n : ℕ) (h : a + b = n) (s : K.Idx n) : K.Idx a :=
  ⟨fun j => s.1 ⟨j.1, by omega⟩, fun _ _ hj => s.2 (Fin.mk_lt_mk.2 (Fin.lt_def.1 hj))⟩

/-- The back `b`-face `(s_a, …, sₙ)` of a strictly increasing `(n + 1)`-tuple `(s₀, …, sₙ)`,
`a + b = n`. -/
def backFace (a b n : ℕ) (h : a + b = n) (s : K.Idx n) : K.Idx b :=
  ⟨fun j => s.1 ⟨a + j.1, by omega⟩,
    fun _ _ hj => s.2 (Fin.mk_lt_mk.2 (by have := Fin.lt_def.1 hj; omega))⟩

theorem frontFace_apply (a b n : ℕ) (h : a + b = n) (s : K.Idx n) (j : Fin (a + 1)) :
    (K.frontFace a b n h s).1 j = s.1 ⟨j.1, by omega⟩ :=
  rfl

theorem backFace_apply (a b n : ℕ) (h : a + b = n) (s : K.Idx n) (j : Fin (b + 1)) :
    (K.backFace a b n h s).1 j = s.1 ⟨a + j.1, by omega⟩ :=
  rfl

theorem inter_le_inter_frontFace (a b n : ℕ) (h : a + b = n) (s : K.Idx n) :
    K.inter s ≤ K.inter (K.frontFace a b n h s) :=
  le_iInf fun _ => iInf_le _ _

theorem inter_le_inter_backFace (a b n : ℕ) (h : a + b = n) (s : K.Idx n) :
    K.inter s ≤ K.inter (K.backFace a b n h s) :=
  le_iInf fun _ => iInf_le _ _

end Scheme.OrderedAffineCover

namespace OModulePresheaf

variable {R : Type u} [CommRing R] {V : Scheme.{u}} {π : V ⟶ Spec (.of R)}
variable (F : OModulePresheaf π) (K : V.OrderedAffineCover)

/-- The Alexander–Whitney cup product of a structure-sheaf cochain of degree `a` with a
cochain of `F` of degree `b`, landing in degree `n = a + b`. -/
def cup (a b n : ℕ) (h : a + b = n) (α : (unit π).cochain K a) (β : F.cochain K b) :
    F.cochain K n :=
  fun s => (V.presheaf.map (homOfLE (K.inter_le_inter_frontFace a b n h s)).op).hom
      (α (K.frontFace a b n h s)) •
    F.res (K.inter_le_inter_backFace a b n h s) (β (K.backFace a b n h s))

theorem cup_apply (a b n : ℕ) (h : a + b = n) (α : (unit π).cochain K a) (β : F.cochain K b)
    (s : K.Idx n) :
    F.cup K a b n h α β s =
      (V.presheaf.map (homOfLE (K.inter_le_inter_frontFace a b n h s)).op).hom
          (α (K.frontFace a b n h s)) •
        F.res (K.inter_le_inter_backFace a b n h s) (β (K.backFace a b n h s)) :=
  rfl

end OModulePresheaf

end AlgebraicGeometry
