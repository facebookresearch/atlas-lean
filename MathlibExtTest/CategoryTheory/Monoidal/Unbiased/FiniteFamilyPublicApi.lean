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

public import MathlibExt.CategoryTheory.Monoidal.Unbiased.FiniteFamily

/-!
# Finite-family public-contract packet

Pins the stable downstream-facing contracts of the pure-reindexing
API: the reindexing-iso characteristic lemmas consumed when stating
the O7E general-`V` singleton-insertion coherence class (o12b).
-/

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]

section ReindexIsoPin

/-- Index equivalence of a reindexing iso. -/
example {X Y : FiniteFamily C} {e : X.index ≃ Y.index}
    {hobj : ∀ i : X.index, X.obj i = Y.obj (e i)} :
    (FiniteFamily.isoOfReindex e hobj).hom.equiv = e :=
  by exact FiniteFamily.isoOfReindex_hom_equiv e hobj

/-- Hom components of a reindexing iso. -/
example {X Y : FiniteFamily C} {e : X.index ≃ Y.index}
    {hobj : ∀ i : X.index, X.obj i = Y.obj (e i)} (i : X.index) :
    (FiniteFamily.isoOfReindex e hobj).hom.hom i =
      eqToHom (hobj i) :=
  by exact FiniteFamily.isoOfReindex_hom_hom e hobj i

/-- Composition of reindexing-iso homs. -/
example {X Y Z : FiniteFamily C} {e₁ : X.index ≃ Y.index}
    {e₂ : Y.index ≃ Z.index}
    {h₁ : ∀ i : X.index, X.obj i = Y.obj (e₁ i)}
    {h₂ : ∀ j : Y.index, Y.obj j = Z.obj (e₂ j)} :
    (FiniteFamily.isoOfReindex e₁ h₁).hom ≫
        (FiniteFamily.isoOfReindex e₂ h₂).hom =
      (FiniteFamily.isoOfReindex (e₁.trans e₂)
        (fun i => (h₁ i).trans (h₂ (e₁ i)))).hom :=
  by exact FiniteFamily.isoOfReindex_hom_comp

end ReindexIsoPin
