/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.LogRootMorphismModels

/-!
# Actual finite-root restriction along a DF arrow

The functor on finite roots is fixed on every root line, section, unit,
tensor, etale restriction and coefficient arrow by the original DF
characteristic map and comparison. The source restriction triangle
uses the actual commuting power-map square. This is the finite-level
normalization for the canonical infinite-root map.

Source: Talpo--Vistoli1410.1164v2, Sections3--5 and Theorem5.24.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.FiniteLogRootArrowModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.AlgebraicGeometry
open DeligneFaltingsSheaves DenominatorRootFamilies FiniteRootTowers

variable {X : Scheme.{0}} {A B : DeligneFaltingsSheaves.MonoidSheaf X}
  (D : Structure A) (E : Structure B) (j : A ⟶ B) (c : ComparisonAlong j D E)

theorem powerSquare (n : ℕ) : powerMap A n ≫ j = j ≫ powerMap B n := by
  ext U a
  exact map_pow (j.hom.app U).hom a n

/-- Actual finite roots in the displayed source DF category. -/
abbrev FiniteFibre (n : Exponent) := RootFibre (powerMap A n.val) D

/-- Full finite restriction, including every root-line coefficient map. -/
structure Restriction (n : Exponent) where
  functor : FiniteFibre E n ⥤ FiniteFibre D n
  lines : ∀ r : FiniteFibre E n,
    ComparisonAlong j (functor.obj r).of.extended r.of.extended
  restriction_square : ∀ (r : FiniteFibre E n) (U : X.Etale) (a : A.obj.obj (op U)),
    ((functor.obj r).of.restriction.comparison U a).hom ≫
      ((lines r).comparison U ((powerMap A n.val).hom.app (op U) a)).hom =
    (c.comparison U a).hom ≫
      (r.of.restriction.comparison U (j.hom.app (op U) a)).hom ≫
        eqToHom (congrArg (r.of.extended.chart U).module
          ((ConcreteCategory.congr_hom
            (congrArg (fun h => h.hom.app (op U)) (powerSquare j n.val)) a).symm))
  arrows : ∀ {r s : FiniteFibre E n} (a : r ⟶ s)
      (U : X.Etale) (v : A.obj.obj (op U)),
    (((functor.map a).iso.hom.hom).comparison U v).hom ≫ ((lines s).comparison U v).hom =
      ((lines r).comparison U v).hom ≫
        (a.iso.hom.hom.comparison U (j.hom.app (op U) v)).hom

end MathlibExt.AlgebraicGeometry.FiniteLogRootArrowModels
