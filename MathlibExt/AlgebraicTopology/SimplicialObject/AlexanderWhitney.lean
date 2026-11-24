/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tsutomu Okano
-/
module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic

/-!
# Alexander–Whitney front and back face interface

This file provides the generic, category-level Alexander–Whitney interface for
simplicial objects. It owns the canonical front and back subinterval inclusions
in the simplex category and the induced morphisms of an arbitrary `SimplicialObject C`.

The inclusions are built definitionally from `SimplexCategory.subinterval` and the
simplicial-object morphisms are obtained by applying `X.map` to the opposite of
those inclusions. No preadditive, abelian, monoidal or concrete hypotheses are
required.

This is the first generic layer for the later alternating-chain Alexander–Whitney
construction; it is not an `SSet` element API and not yet a chain map.
-/

@[expose] public section

universe v u

open CategoryTheory Simplicial SimplexCategory

namespace AlgebraicTopology.AlexanderWhitney

variable {C : Type u} [Category.{v} C]

/-- Front subinterval inclusion `⦋p⦌ ⟶ ⦋n⦌` beginning at `0`, for `p + q = n`.

Built definitionally from `SimplexCategory.subinterval 0 p _`. -/
def frontInclusion (p q n : ℕ) (h : p + q = n) : ⦋p⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.subinterval (n := n) 0 p (by omega)

/-- Back subinterval inclusion `⦋q⦌ ⟶ ⦋n⦌` beginning at `p`, for `p + q = n`.

Built definitionally from `SimplexCategory.subinterval p q _`. -/
def backInclusion (p q n : ℕ) (h : p + q = n) : ⦋q⦌ ⟶ ⦋n⦌ :=
  SimplexCategory.subinterval (n := n) p q (by omega)

@[simp]
lemma frontInclusion_toOrderHom (p q n : ℕ) (h : p + q = n) (i : Fin (p + 1)) :
    ((frontInclusion p q n h).toOrderHom i).val = i.val := by
  simp [frontInclusion, SimplexCategory.subinterval]

@[simp]
lemma backInclusion_toOrderHom (p q n : ℕ) (h : p + q = n) (i : Fin (q + 1)) :
    ((backInclusion p q n h).toOrderHom i).val = i.val + p :=
  rfl

/-- Front face of a simplicial object: the morphism induced by `frontInclusion`.

For `X : SimplicialObject C` and `h : p + q = n`, this is
`X.map (frontInclusion p q n h).op : X _⦋n⦌ ⟶ X _⦋p⦌`. -/
def frontFace (X : SimplicialObject C) {p q n : ℕ} (h : p + q = n) :
    X.obj (Opposite.op ⦋n⦌) ⟶ X.obj (Opposite.op ⦋p⦌) :=
  X.map (frontInclusion p q n h).op

/-- Back face of a simplicial object: the morphism induced by `backInclusion`.

For `X : SimplicialObject C` and `h : p + q = n`, this is
`X.map (backInclusion p q n h).op : X _⦋n⦌ ⟶ X _⦋q⦌`. -/
def backFace (X : SimplicialObject C) {p q n : ℕ} (h : p + q = n) :
    X.obj (Opposite.op ⦋n⦌) ⟶ X.obj (Opposite.op ⦋q⦌) :=
  X.map (backInclusion p q n h).op

@[reassoc (attr := simp)]
theorem frontFace_naturality {X Y : SimplicialObject C} (f : X ⟶ Y)
    {p q n : ℕ} (h : p + q = n) :
    frontFace (C := C) X h ≫ f.app (Opposite.op ⦋p⦌) =
      f.app (Opposite.op ⦋n⦌) ≫ frontFace (C := C) Y h :=
  f.naturality _

@[reassoc (attr := simp)]
theorem backFace_naturality {X Y : SimplicialObject C} (f : X ⟶ Y)
    {p q n : ℕ} (h : p + q = n) :
    backFace (C := C) X h ≫ f.app (Opposite.op ⦋q⦌) =
      f.app (Opposite.op ⦋n⦌) ≫ backFace (C := C) Y h :=
  f.naturality _

end AlgebraicTopology.AlexanderWhitney
