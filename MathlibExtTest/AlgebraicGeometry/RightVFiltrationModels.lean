/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.RightVFiltrationModels

/-!
# Conventions of the rational V-filtration

The Kashiwara--Malgrange conditions apply at the strict indices of Saito (2.1.3)/(2.1.4):
`t : V^a → V^(a+1)` is bijective for `a > -1` (so at `a = 0`), and `∂` is bijective on grades for
`a < 0` (so at `a = -1`). A filtration all of whose pieces are the whole module would force `t` to
be bijective on sections, so it is excluded wherever `t` is not invertible. The graded pieces are
cokernels of `V^(>a) → V^a`; nearby and vanishing cycles are `grV^0` and `grV^-1`, with
`can : grV^0 → grV^-1` (from `∂`), `var : grV^-1 → grV^0` (from `t`), and the nilpotent
endomorphisms `var ∘ can` of `grV^0` and `can ∘ var` of `grV^-1`.
-/

namespace MathlibExtTest.AlgebraicGeometry.RightVFiltrationModels

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open MathlibExt.AlgebraicGeometry
open DifferentialOperatorSheaves RightDifferentialModules RightCoordinateDifferentials
open MathlibExt.AlgebraicGeometry.RightVFiltrationModels

variable (k : Type) [CommRing k] [Algebra ℚ k] (M : Type) [TopologicalSpace M]
  (O : (Opens M)ᵒᵖ ⥤ CommAlgCat.{0} k)
  [HasSheafify (Opens.grothendieckTopology M) RingCat.{0}]
  (C : CoordinateDerivation k M O) (N : RightModule k M O)
  (V : RationalVFiltration k M O C N)

/-- `t` is injective on `V^0`: the index `0` satisfies the strict bound `-1 < 0` of (2.1.3). -/
example (U : Opens M) (s : N.val.obj (op U)) (hs : s ∈ (V.term 0).toSubmodule.obj (op U))
    (h : rightCoordinate k M O C N U s = 0) : s = 0 :=
  V.coordinateInjective 0 (by norm_num) U s hs h

/-- `∂ : grV^-1 → grV^-2` is injective: the index `-1` satisfies the strict bound `-1 < 0`
of (2.1.4). -/
example (U : Opens M) (s : N.val.obj (op U)) (hs : s ∈ (V.term (-1)).toSubmodule.obj (op U))
    (h : rightPartial k M O C N U s ∈
      (⨆ b : {b : ℚ // -1 - 1 < b}, V.term b.val).toSubmodule.obj (op U)) :
    s ∈ (⨆ b : {b : ℚ // -1 < b}, V.term b.val).toSubmodule.obj (op U) :=
  V.partialGradedInjective (-1) (by norm_num) U s hs h

/-- If every piece of the filtration contains every section, then `t` is injective on sections. -/
theorem coordinate_injective_of_constant
    (hconst : ∀ (a : ℚ) (U : Opens M) (s : N.val.obj (op U)),
      s ∈ (V.term a).toSubmodule.obj (op U))
    (U : Opens M) (s : N.val.obj (op U)) (h : rightCoordinate k M O C N U s = 0) : s = 0 :=
  V.coordinateInjective 0 (by norm_num) U s (hconst 0 U s) h

/-- If every piece of the filtration contains every section, then `t` is locally surjective on
sections. So the constant filtration is excluded wherever `t` is not invertible, for instance on a
coordinate disk around `t = 0`. -/
theorem coordinate_locally_surjective_of_constant
    (hconst : ∀ (a : ℚ) (U : Opens M) (s : N.val.obj (op U)),
      s ∈ (V.term a).toSubmodule.obj (op U))
    (U : Opens M) (s : N.val.obj (op U)) (y : U) :
    ∃ (W : Opens M) (hW : W ≤ U), y.val ∈ W ∧ ∃ s' : N.val.obj (op W),
      rightCoordinate k M O C N W s' = (N.val.map (homOfLE hW).op).hom s := by
  obtain ⟨W, hW, hy, s', -, hs'⟩ :=
    V.coordinateSurjective 0 (by norm_num) U s (hconst (0 + 1) U s) y
  exact ⟨W, hW, hy, s', hs'⟩

/-- Pieces of strictly larger index lie in the positive-index union. -/
example (a b : ℚ) (h : a < b) : V.term b ≤ termAbove k M O C N V a :=
  le_iSup_of_le (⟨b, h⟩ : {b : ℚ // a < b}) le_rfl

/-- The positive-index union lies in the piece. -/
example (a : ℚ) : termAbove k M O C N V a ≤ V.term a :=
  termAbove_le k M O C N V a

section Graded

variable [HasSheafify (Opens.grothendieckTopology M) AddCommGrpCat.{0}]
  [(Opens.grothendieckTopology M).WEqualsLocallyBijective AddCommGrpCat.{0}]
  [∀ U : Opens M, HasWeakSheafify ((Opens.grothendieckTopology M).over U) AddCommGrpCat.{0}]
  [∀ U : Opens M, ((Opens.grothendieckTopology M).over U).WEqualsLocallyBijective
    AddCommGrpCat.{0}]

/-- The graded piece is the cokernel of `V^(>a) → V^a`. -/
example (a : ℚ) : vStep k M O C N V a ≫ gradedProjection k M O C N V a = 0 :=
  cokernel.condition _

example : nearbyUnipotent k M O C N V = gradedV k M O C N V 0 := rfl

example : vanishingUnipotent k M O C N V = gradedV k M O C N V (-1) := rfl

variable (A : GradedVOperators k M O C N V)

/-- `can` goes from the nearby to the vanishing cycles, `var` back. -/
example : nearbyUnipotent k M O C N V ⟶ vanishingUnipotent k M O C N V := can k M O C N V A

example : vanishingUnipotent k M O C N V ⟶ nearbyUnipotent k M O C N V := var k M O C N V A

/-- The nearby nilpotent endomorphism is `var ∘ can`, the vanishing one `can ∘ var`. -/
example : (nearbyNilpotent k M O C N V A).asHom = can k M O C N V A ≫ var k M O C N V A := rfl

example : (vanishingNilpotent k M O C N V A).asHom = var k M O C N V A ≫ can k M O C N V A := rfl

/-- `can` is the graded `∂` out of `grV^0`, and `var` is the graded `t` out of `grV^-1`. -/
example : HEq (can k M O C N V A) (A.partialMap 0) := by
  unfold can
  exact cast_heq _ _

example : HEq (var k M O C N V A) (A.coordinateMap (-1)) := by
  unfold var
  exact cast_heq _ _

end Graded

end MathlibExtTest.AlgebraicGeometry.RightVFiltrationModels
