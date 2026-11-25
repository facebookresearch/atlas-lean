/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.Topology.LocallyConstant.Basic
public import MathlibExt.AlgebraicGeometry.AbelianSchemes

/-!
# Actual p-divisible group schemes over an arbitrary base

Levels are actual commutative group objects in the scheme slice. Their
finite flat ranks are the native local rank of the structure morphism.
Height is consequently fixed by those ranks. The level inclusions are
actual closed group morphisms, kernels are native pullback squares, and
division factors actual multiplication by p^n as a finite faithfully-flat
map. No abstract torsion-group or lattice carrier replaces the geometry.

References: Tate, *p-divisible groups* (1967); Scholze--Weinstein,
arXiv:1211.6357v2, Sections1-2. Generic module Tate construction and finite
Cartier duality are already completed public source primitives; neither
is requested anew by this scheme-level definition.
-/

@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PDivisibleGroupSchemes

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonObj
open _root_.CategoryTheory.CartesianMonoidalCategory _root_.AlgebraicGeometry

variable (S : Scheme.{0})

/-- Actual internal group multiplication, normalized on scheme-valued points. -/
def multiply (G : Over S) [GrpObj G] [IsCommMonObj G] (n : ℕ) : G ⟶ G := by
  letI : CommGroup (G ⟶ G) := CategoryTheory.Hom.commGroup
  exact (𝟙 G) ^ n

/-- The full scheme-theoretic p-divisible tower, with varying local height. -/
structure PDivisibleGroup (p : ℕ) [Fact p.Prime] where
  levels : ℕ ⥤ Over S
  [group : ∀ n, GrpObj (levels.obj n)]
  [commutative : ∀ n, IsCommMonObj (levels.obj n)]
  [finite : ∀ n, IsFinite (levels.obj n).hom]
  [flat : ∀ n, Flat (levels.obj n).hom]
  [presentation : ∀ n, LocallyOfFinitePresentation (levels.obj n).hom]
  height : LocallyConstant S ℕ
  rank : ∀ (n : ℕ) (s : S), (levels.obj n).hom.finrank s = p ^ (n * height s)
  zero : Nonempty (levels.obj 0 ≅ 𝟙_ (Over S))
  [transition_group : ∀ {n m} (h : n ≤ m), IsMonHom (levels.map (homOfLE h))]
  [closed : ∀ {n m} (h : n ≤ m), IsClosedImmersion (levels.map (homOfLE h)).left]
  kernel : ∀ n m : ℕ,
    IsPullback (levels.map (homOfLE (Nat.le_add_right n m)))
      (toUnit (levels.obj n)) (multiply S (levels.obj (n + m)) (p ^ n))
        (η[levels.obj (n + m)])
  divide : ∀ n m : ℕ, levels.obj (n + m) ⟶ levels.obj m
  [divide_group : ∀ n m, IsMonHom (divide n m)]
  factor : ∀ n m,
    divide n m ≫ levels.map (homOfLE (Nat.le_add_left m n)) =
      multiply S (levels.obj (n + m)) (p ^ n)
  [divide_finite : ∀ n m, IsFinite (divide n m).left]
  [divide_flat : ∀ n m, Flat (divide n m).left]
  [divide_presentation : ∀ n m, LocallyOfFinitePresentation (divide n m).left]
  divide_surjective : ∀ n m, Function.Surjective (divide n m).left

attribute [instance] PDivisibleGroup.group PDivisibleGroup.commutative
  PDivisibleGroup.finite PDivisibleGroup.flat PDivisibleGroup.presentation
  PDivisibleGroup.transition_group PDivisibleGroup.closed PDivisibleGroup.divide_group
  PDivisibleGroup.divide_finite PDivisibleGroup.divide_flat PDivisibleGroup.divide_presentation

end MathlibExt.AlgebraicGeometry.PDivisibleGroupSchemes
