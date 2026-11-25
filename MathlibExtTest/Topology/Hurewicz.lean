/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Hurewicz
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-! # Tests for `MathlibExt.Topology.Hurewicz` -/

namespace MathlibExtTest.Topology.Hurewicz

open CategoryTheory AlgebraicTopology MathlibExt.Topology.HurewiczWanted.Topology.Hurewicz

-- `IntegralHomology n X` unfolds to Mathlib's singular homology with integer coefficients.
example (n : ℕ) (X : Type) [TopologicalSpace X] :
    IntegralHomology n X =
      ((singularHomologyFunctor AddCommGrpCat.{0} n).obj (AddCommGrpCat.of ℤ)).obj
        (TopCat.of X) :=
  rfl

-- The theorem at an arbitrary base point of a path-connected space.
example (X : Type) [TopologicalSpace X] [PathConnectedSpace X] (x : X) :
    Nonempty (Additive (Group.Abelianization (FundamentalGroup X x)) ≃+
      (IntegralHomology 1 X : Type)) :=
  hurewicz_h1_abelianization X x

/-- A simply connected space has trivial first integral homology: its fundamental group is
trivial, hence so is the abelianization, which the theorem identifies with `H₁`. -/
private theorem subsingleton_integralHomology_one (X : Type) [TopologicalSpace X]
    [SimplyConnectedSpace X] : Subsingleton (IntegralHomology 1 X : Type) := by
  obtain ⟨x⟩ := (inferInstance : PathConnectedSpace X).nonempty
  obtain ⟨e⟩ := hurewicz_h1_abelianization X x
  have : Subsingleton (Group.Abelianization (FundamentalGroup X x)) :=
    (Group.Abelianization.surjective_of (G := FundamentalGroup X x)).subsingleton
  have : Subsingleton (Additive (Group.Abelianization (FundamentalGroup X x))) := this
  exact e.toEquiv.symm.subsingleton

-- The real line is contractible, so its first integral homology vanishes.
example : Subsingleton (IntegralHomology 1 ℝ : Type) :=
  subsingleton_integralHomology_one ℝ

-- The same statement as a zero object of `AddCommGrpCat`.
example : Limits.IsZero (IntegralHomology 1 ℝ) := by
  have := subsingleton_integralHomology_one ℝ
  exact AddCommGrpCat.isZero_of_subsingleton _

-- The unit circle is path-connected, so its first integral homology is the abelianized
-- fundamental group at the base point `1`.
example : Nonempty (Additive (Group.Abelianization (FundamentalGroup Circle 1)) ≃+
    (IntegralHomology 1 Circle : Type)) :=
  hurewicz_h1_abelianization Circle 1

end MathlibExtTest.Topology.Hurewicz
