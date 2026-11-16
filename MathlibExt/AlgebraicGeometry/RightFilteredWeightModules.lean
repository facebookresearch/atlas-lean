/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RightDifferentialModules
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Subobject.Lattice

/-!
# Actual right differential modules with finite weight filtration

The Hodge filtration is the existing actual good filtration of a native
right module. Weight terms are actual right-D subobjects, with finite
bounds. Graded weight pieces are their native cokernels. Morphisms retain
the original module map and preserve both filtrations on all local sections.
Pure/polarizable graded objects, perverse realization, V-filtration and
local admissibility are separate constructions, not assumed by this type.

Source: Saito1307.2140v5, Section1.1 and Definition2.2.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RightFilteredWeightModules

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite TopologicalSpace
open RightDifferentialModules

variable (k : Type) [CommRing k] (M : Type) [TopologicalSpace M]
  (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
  [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
  [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ U : Opens M, HasWeakSheafify ((Opens.grothendieckTopology M).over U) AddCommGrpCat.{0}]
  [∀ U : Opens M, ((Opens.grothendieckTopology M).over U).WEqualsLocallyBijective AddCommGrpCat.{0}]

structure FilteredWeightModule where
  hodge : RightDifferentialModules.GoodFiltration k M O
  weight : ℤ → Subobject hodge.object
  monotone : Monotone weight
  lower : ℤ
  upper : ℤ
  below : ∀ n : ℤ, n<lower → weight n=⊥
  above : ∀ n : ℤ, upper≤n → weight n=⊤

/-- Weight membership uses the actual right-module subobject arrow. -/
def InWeight (F : FilteredWeightModule k M O) (n : ℤ) (U : Opens M)
    (s : F.hodge.object.val.obj (op U)) : Prop :=
  ∃ t : (Subobject.underlying.obj (F.weight n)).val.obj (op U),
    ((F.weight n).arrow.val.app (op U)).hom t=s

/-- The consecutive inclusion is the native subobject inclusion. -/
def weightStep (F : FilteredWeightModule k M O) (n : ℤ) :
    Subobject.underlying.obj (F.weight (n-1)) ⟶ Subobject.underlying.obj (F.weight n) :=
  Subobject.underlying.map (homOfLE (F.monotone (by omega)))

/-- Graded weights retain the actual right-D module action through the native cokernel. -/
def gradedWeight (F : FilteredWeightModule k M O) (n : ℤ) : RightModule k M O :=
  cokernel (weightStep k M O F n)

structure Hom (F G : FilteredWeightModule k M O) where
  map : F.hodge.object ⟶ G.hodge.object
  hodge : ∀ (p : ℤ) (U : Opens M) (s : F.hodge.object.val.obj (op U)),
    RightDifferentialModules.InFiltration k M O F.hodge.object F.hodge.term p U s →
    RightDifferentialModules.InFiltration k M O G.hodge.object G.hodge.term p U
      ((map.val.app (op U)).hom s)
  weight : ∀ (p : ℤ) (U : Opens M) (s : F.hodge.object.val.obj (op U)),
    InWeight k M O F p U s → InWeight k M O G p U ((map.val.app (op U)).hom s)

@[ext] theorem Hom.ext {F G : FilteredWeightModule k M O} (a b : Hom k M O F G)
    (e : a.map=b.map) : a=b := by
  cases a
  cases b
  cases e
  rfl

instance : Category (FilteredWeightModule k M O) where
  Hom := Hom k M O
  id F :=
    { map := 𝟙 F.hodge.object
      hodge := by intro p U s hs; exact hs
      weight := by intro p U s hs; exact hs }
  comp a b :=
    { map := a.map ≫ b.map
      hodge := by intro p U s hs; exact b.hodge p U _ (a.hodge p U s hs)
      weight := by intro p U s hs; exact b.weight p U _ (a.weight p U s hs) }
  id_comp a := by apply Hom.ext; exact Category.id_comp a.map
  comp_id a := by apply Hom.ext; exact Category.comp_id a.map
  assoc a b c := by apply Hom.ext; exact Category.assoc a.map b.map c.map

end MathlibExt.AlgebraicGeometry.RightFilteredWeightModules
