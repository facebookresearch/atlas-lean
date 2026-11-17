/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.RegularSingularConnections
public import MathlibExt.AlgebraicGeometry.CompactSupportIndSheaves
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Exact native rational-curve DR/Sol and matrix-map normalizations

The original two-term derivative-minus-A complex is extended natively
to integer cochain degrees, then shifted [1]. Its horizontal source is
the actual solution sheaf for A in degree -1. Ordinary Sol is the actual
solution sheaf for -transpose(A) in degree zero. A horizontal matrix G
acts covariantly on DR; its transpose acts in the reversed Sol direction.
These statements retain the original rational punctured-line scope.

Source: DK1311.2374v2 Section2.5/Definition9.1.1; the already sourced
RegularSingularConnections analytic connection/solution constructions.
Native Q, shape extension, shifts and single functors: Mathlib56a005, Apache2.0.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.NativeRationalCurveRealizations

open _root_.CategoryTheory _root_.Opposite TopologicalSpace
open CompactSupportIndSheaves RegularSingularConnections

variable (S : Finset ℂ)
  [HasSheafify (Opens.grothendieckTopology (puncturedLine S)) (ModuleCat.{0} ℂ)]

local instance nativeCurvePreadditive :
    Preadditive (OrdinarySheaf ℂ (puncturedLine S)) := Abelian.toPreadditive
attribute [local instance] HasDerivedCategory.standard

variable {r : ℕ} (A : Matrix (Fin r) (Fin r) RationalFunctions)

def ordinaryCurveDR (D : AnalyticConnectionDeRhamData S r A) :
    DerivedCategory (OrdinarySheaf ℂ (puncturedLine S)) :=
  (shiftFunctor (DerivedCategory (OrdinarySheaf ℂ (puncturedLine S))) (1 : ℤ)).obj
    (DerivedCategory.Q.obj (((ComplexShape.embeddingUpNat).extendFunctor
      (OrdinarySheaf ℂ (puncturedLine S))).obj (analyticDeRhamComplex D)))

def horizontalDR : DerivedCategory (OrdinarySheaf ℂ (puncturedLine S)) :=
  (shiftFunctor (DerivedCategory (OrdinarySheaf ℂ (puncturedLine S))) (1 : ℤ)).obj
    ((DerivedCategory.singleFunctor (OrdinarySheaf ℂ (puncturedLine S)) 0).obj (solutionSheaf S A))

def ordinaryCurveSol : DerivedCategory (OrdinarySheaf ℂ (puncturedLine S)) :=
  (DerivedCategory.singleFunctor (OrdinarySheaf ℂ (puncturedLine S)) 0).obj
    (solutionSheaf S (-A.transpose))

variable {s : ℕ} (B : Matrix (Fin s) (Fin s) RationalFunctions)
  (G : Matrix (Fin s) (Fin r) RationalFunctions)

theorem horizontal_reversed_transpose (δ : RationalDerivative)
    (h : HorizontalMatrix δ A B G) : HorizontalMatrix δ (-B.transpose) (-A.transpose) G.transpose := by
  intro i j
  have he : -A.transpose * G.transpose - G.transpose * -B.transpose = (B * G - G * A).transpose := by
    simp only [Matrix.neg_mul, Matrix.mul_neg, Matrix.transpose_sub, Matrix.transpose_mul]
    ext a b
    simp [sub_eq_add_neg, add_comm]
  change δ.derivation (G j i) = (-A.transpose * G.transpose - G.transpose * -B.transpose) i j
  rw [he]
  exact h j i

/-- Both original sheaf maps retain their actual matrix section values before sheafification. -/
structure CurveGaugeSource where
  drMap : solutionSheaf S A ⟶ solutionSheaf S B
  drValues : InducedByMatrix S A B drMap G
  solMap : solutionSheaf S (-B.transpose) ⟶ solutionSheaf S (-A.transpose)
  solValues : InducedByMatrix S (-B.transpose) (-A.transpose) solMap G.transpose

def ordinaryCurveDRMap (P : CurveGaugeSource S A B G) : horizontalDR S A ⟶ horizontalDR S B :=
  (shiftFunctor (DerivedCategory (OrdinarySheaf ℂ (puncturedLine S))) (1 : ℤ)).map
    ((DerivedCategory.singleFunctor (OrdinarySheaf ℂ (puncturedLine S)) 0).map P.drMap)

def ordinaryCurveSolMap (P : CurveGaugeSource S A B G) : ordinaryCurveSol S B ⟶ ordinaryCurveSol S A :=
  (DerivedCategory.singleFunctor (OrdinarySheaf ℂ (puncturedLine S)) 0).map P.solMap

end MathlibExt.AlgebraicGeometry.NativeRationalCurveRealizations
