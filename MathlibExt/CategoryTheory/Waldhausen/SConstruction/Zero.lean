/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua, Avocado
-/

module

public import MathlibExt.CategoryTheory.Waldhausen.SConstruction.FiniteStage
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Canonical zero finite Waldhausen stage

The constant-zero diagram supplies a distinguished finite stage for every `n`:
every diagonal value is zero and every non-strict triple carries the identity
cofibration sequence on the zero object.

This does not prove categorical contractibility of any stage and does not
define a simplicial basepoint.
-/

@[expose] public section

open CategoryTheory Limits ZeroObject

universe v u

namespace CategoryTheory.Waldhausen.SConstruction

/-- A pointwise-zero diagram is a finite stage in every degree.

Every map between zero objects is an isomorphism, hence a cofibration. The
cofiber square is a pushout because its horizontal source leg and target leg
are isomorphisms. -/
theorem isStage_of_pointwise_zero (C : Type u) [Category.{v} C] [HasZeroObject C]
    [WaldhausenCategoryWithoutGluing C] {n : ℕ} (G : Ar n ⥤ C)
    (hG : ∀ a, IsZero (G.obj a)) : IsStage n G where
  diag_isZero i := hG (diag i)
  cofiber_triple hij hjk := by
    let : HasZeroMorphisms C := (isZero_zero C).hasZeroMorphisms
    have hX : IsZero (G.obj (interval _ _ hij)) := hG _
    have hY : IsZero (G.obj (interval _ _ (hij.trans hjk))) := hG _
    have hZ : IsZero (G.obj (interval _ _ hjk)) := hG _
    let : IsIso (G.map (horiz hij hjk)) := IsZero.isIso hX hY _
    have hCof : IsCofibration (C := C) (G.map (horiz hij hjk)) :=
      (WaldhausenCategoryWithoutGluing.cofibrations (C := C)).of_isIso _
    let : IsIso (0 : G.obj (interval _ _ hij) ⟶ (0 : C)) :=
      IsZero.isIso hX (isZero_zero C) _
    let : IsIso (G.map (vert hij hjk)) := IsZero.isIso hY hZ _
    exact ⟨hCof, 0, 0, IsPushout.of_horiz_isIso ⟨hX.eq_of_src _ _⟩⟩

/-- Canonical constant-zero diagram `Ar n ⥤ C`. -/
noncomputable def zeroDiagram (C : Type u) [Category.{v} C] [HasZeroObject C]
    (n : ℕ) : Ar n ⥤ C :=
  (Functor.const _).obj (0 : C)

/-- The constant-zero diagram is a finite stage by the generic pointwise-zero
stage construction. -/
theorem isStage_zeroDiagram (C : Type u) [Category.{v} C] [HasZeroObject C]
    [WaldhausenCategoryWithoutGluing C] (n : ℕ) : IsStage n (zeroDiagram C n) :=
  isStage_of_pointwise_zero C _ (fun _ => by simpa [zeroDiagram] using isZero_zero C)

end CategoryTheory.Waldhausen.SConstruction
