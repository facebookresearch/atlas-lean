/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.PDivisibleGroupSchemes
public import MathlibExt.AlgebraicGeometry.FrobeniusGeometry
public import Mathlib.CategoryTheory.Monoidal.Cartesian.GrpLimits

/-!
# Original p-divisible group base change and relative Frobenius

Base change has the literal scheme-slice pullback of every original
finite level and its original level maps. The group comparisons and
p-power division maps are normalized through the native pullback.
Relative Frobenius is induced by the source group's actual absolute
Frobenius and its structural map, not by a selected map of points.

Source: Tate, p-divisible groups; Scholze--Weinstein1211.6357v2,
Sections3.1 and4.1. These are normalized construction contracts.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.PDivisibleBaseChangeModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.CartesianMonoidalCategory
open _root_.CategoryTheory.MonObj _root_.AlgebraicGeometry
open PDivisibleGroupSchemes FrobeniusGeometry

variable (p : ℕ) [Fact p.Prime] {S T : Scheme.{0}}
  (G : PDivisibleGroup S p) (f : T ⟶ S)

/-- The native slice pullback is monoidal through its actual finite-product comparisons. -/
@[instance_reducible] def pullbackMonoidal : (Over.pullback f).Monoidal :=
  Functor.Monoidal.ofChosenFiniteProducts (Over.pullback f)

attribute [local instance] pullbackMonoidal
open scoped CategoryTheory.Obj

/-- The native finite-level pullback includes every original scheme map. -/
def pulledLevels : ℕ ⥤ Over T := G.levels ⋙ Over.pullback f

/-- The monoid law is the image under the native monoidal pullback. -/
@[instance_reducible] def pulledMonoid (n : ℕ) : MonObj ((pulledLevels p G f).obj n) :=
  Functor.monObjObj (F := Over.pullback f) (X := G.levels.obj n)

attribute [local instance] pulledMonoid

/-- The group inverse is the image of the original inverse through that same pullback. -/
@[instance_reducible] def pulledGroup (n : ℕ) : GrpObj ((pulledLevels p G f).obj n) :=
  Functor.grpObjObj (F := Over.pullback f) (G := G.levels.obj n)

attribute [local instance] pulledGroup

/-- The original division is pulled by the same native slice functor. -/
def pulledDivision (n m : ℕ) :
    (pulledLevels p G f).obj (n + m) ⟶ (pulledLevels p G f).obj m :=
  (Over.pullback f).map (G.divide n m)

/-- The geometric p-divisible base change is pinned to all native finite levels and divisions. -/
structure BaseChange where
  group : PDivisibleGroup T p
  levels : group.levels ≅ pulledLevels p G f
  groups : ∀ n : ℕ, IsMonHom (levels.hom.app n)
  divisions : ∀ n m : ℕ,
    group.divide n m ≫ levels.hom.app m =
      levels.hom.app (n + m) ≫ pulledDivision p G f n m
  height : ∀ t : T, group.height t = G.height (f t)

variable (S : Over (Spec (.of (ZMod p))))
  (G₀ : PDivisibleGroup S.left p)

/-- The twist uses the actual prime-field absolute Frobenius of the original base. -/
def frobeniusBase : S.left ⟶ S.left := (primeFieldFrobenius p S).left

/-- This is the actual target scheme of each relative Frobenius map. -/
def frobeniusLevel (n : ℕ) : Over S.left :=
  (Over.pullback (frobeniusBase p S)).obj (G₀.levels.obj n)

/-- The original finite-level relative Frobenius, as an actual pullback lift. -/
def relativeFrobenius (n : ℕ) : G₀.levels.obj n ⟶ frobeniusLevel p S G₀ n := by
  let Fbase := frobeniusBase p S
  let X : Over (Spec (.of (ZMod p))) :=
    (Over.map S.hom).obj (G₀.levels.obj n)
  let hX := isInCharacteristic_of_over X
  let hS := isInCharacteristic_of_over S
  have h : absoluteFrobenius (G₀.levels.obj n).left p hX ≫ (G₀.levels.obj n).hom =
      (G₀.levels.obj n).hom ≫ Fbase := by
    exact absoluteFrobenius_naturality p hX hS (G₀.levels.obj n).hom
  exact Over.homMk (pullback.lift (absoluteFrobenius (G₀.levels.obj n).left p hX)
    (G₀.levels.obj n).hom h) (pullback.lift_snd _ _ _)

/-- Source F/V maps keep the same original scheme-level relative Frobenius. -/
structure FrobeniusVerschiebung where
  twist : BaseChange p G₀ (frobeniusBase p S)
  frobenius : ∀ n : ℕ, G₀.levels.obj n ⟶ twist.group.levels.obj n
  frobenius_source : ∀ n : ℕ,
    frobenius n ≫ twist.levels.hom.app n = relativeFrobenius p S G₀ n
  [frobenius_group : ∀ n : ℕ, IsMonHom (frobenius n)]
  verschiebung : ∀ n : ℕ, twist.group.levels.obj n ⟶ G₀.levels.obj n
  [verschiebung_group : ∀ n : ℕ, IsMonHom (verschiebung n)]
  frobenius_naturality : ∀ (n m : ℕ) (h : n ≤ m),
    G₀.levels.map (homOfLE h) ≫ frobenius m =
      frobenius n ≫ twist.group.levels.map (homOfLE h)
  verschiebung_naturality : ∀ (n m : ℕ) (h : n ≤ m),
    twist.group.levels.map (homOfLE h) ≫ verschiebung m =
      verschiebung n ≫ G₀.levels.map (homOfLE h)
  first_product : ∀ n : ℕ,
    frobenius n ≫ verschiebung n = multiply S.left (G₀.levels.obj n) p
  second_product : ∀ n : ℕ,
    verschiebung n ≫ frobenius n = multiply S.left (twist.group.levels.obj n) p

end MathlibExt.AlgebraicGeometry.PDivisibleBaseChangeModels
