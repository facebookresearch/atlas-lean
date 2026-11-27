/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.RootStacks
import MathlibExt.AlgebraicGeometry.LinearizedLineBundles
import MathlibExt.AlgebraicGeometry.GeneralStackGeometry

/-!
# Root chart boundary checks

The square root of the zero section has a nonzero nilpotent coordinate.
Its nontrivial order-two scaling map is retained, even though it acts
trivially on the single reduced geometric point. Thus the local root
carrier cannot be replaced by a reduced zero locus or by point sets.
-/

noncomputable section

namespace MathlibExtTest.AlgebraicGeometry.RootStacks

open CategoryTheory _root_.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.RootStacks

abbrev DualNumbers := ChartAlgebra ℚ 0 2
abbrev epsilon : DualNumbers := chartCoordinate ℚ 0 2

example : epsilon ^ 2 = 0 := by
  simpa using chartCoordinate_power ℚ 0 2

theorem epsilon_ne_zero : epsilon ≠ 0 := by
  have h : chartPolynomial ℚ 0 2 = Polynomial.X ^ 2 := by simp [chartPolynomial]
  change AdjoinRoot.mk (chartPolynomial ℚ 0 2) Polynomial.X ≠ 0
  rw [h]
  exact AdjoinRoot.mk_ne_zero_of_natDegree_lt
      (Polynomial.monic_X_pow 2 : (Polynomial.X ^ 2 : Polynomial ℚ).Monic)
      (Polynomial.X_ne_zero : (Polynomial.X : Polynomial ℚ) ≠ 0)
      (by simp : (Polynomial.X : Polynomial ℚ).natDegree <
        (Polynomial.X ^ 2 : Polynomial ℚ).natDegree)

def sign : DualNumbers →ₐ[ℚ] DualNumbers := chartScale (0 : ℚ) 2 (-1) (by simp)

theorem sign_epsilon : sign epsilon = -epsilon := by
  rw [sign, chartScale_coordinate]
  simp

example : sign ≠ AlgHom.id ℚ DualNumbers := by
  intro h
  have he : -epsilon = epsilon := by
    rw [← sign_epsilon, h]
    rfl
  have he2 : (2 : ℚ) • epsilon = 0 := by
    have ha : epsilon + epsilon = 0 := neg_eq_iff_add_eq_zero.mp he
    simpa only [two_smul ℚ] using ha
  have hz := congrArg (fun x : DualNumbers => (1 / 2 : ℚ) • x) he2
  have hz' : epsilon = 0 := by
    norm_num [smul_smul] at hz
    exact hz
  exact epsilon_ne_zero hz'

universe u

/-- A paper can bind the shared root data directly to the general relative
Artin/DM interfaces, retaining its actual native pseudofunctor. -/
def relativeRoot {X : Scheme.{u}} {L : X.Modules}
    {s : MathlibExt.AlgebraicGeometry.LineBundleTaskContracts.Section L} {n : ℕ}
    (R : RootStack L s n) : _root_.AlgebraicGeometry.GeneralStackGeometry.RelativeStack X :=
  R.toRelativeStack

example {X : Scheme.{u}} {L : X.Modules}
    {s : MathlibExt.AlgebraicGeometry.LineBundleTaskContracts.Section L} {n : ℕ}
    (R : RootStack L s n) : (relativeRoot R).toPseudofunctor = R.pseudofunctor := rfl

/-- The geometric root-stack conclusion is a well-typed paper goal even
while the shared root and atlas construction proofs remain Wanted. -/
def rootDeligneMumfordGoal {X : Scheme.{u}} {L : X.Modules}
    {s : MathlibExt.AlgebraicGeometry.LineBundleTaskContracts.Section L} {n : ℕ}
    (R : RootStack L s n) : Prop := (relativeRoot R).IsDeligneMumfordStack

/-- The root-stack interface excludes the degenerate exponent zero. -/
example {X : Scheme.{u}} {L : X.Modules}
    {s : MathlibExt.AlgebraicGeometry.LineBundleTaskContracts.Section L}
    (R : RootStack L s 0) : False :=
  (lt_irrefl 0) R.positive

/-- The rooted module of a root stack is a line bundle. -/
example {X : Scheme.{u}} {L : X.Modules}
    {s : MathlibExt.AlgebraicGeometry.LineBundleTaskContracts.Section L} {n : ℕ}
    (R : RootStack L s n) : MathlibExt.AlgebraicGeometry.CoherentCurveLinearSeries.IsLineBundle L :=
  R.line

end MathlibExtTest.AlgebraicGeometry.RootStacks
