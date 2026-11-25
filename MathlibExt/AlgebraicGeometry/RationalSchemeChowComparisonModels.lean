/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.IntegralChowChernModels
public import MathlibExt.AlgebraicGeometry.FieldChowOperators
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The native rational scheme-Chow comparison

The comparison sends each actual integral generic-point cycle to the
same cycle with rational coefficients. It descends this specific map
and extends scalars; its inverse is the inverse of that computed map.
Only relation descent and bijectivity remain proof dependencies.
No virtual class or independent cycle comparison is supplied.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.RationalSchemeChowComparisonModels

open _root_.CategoryTheory _root_.AlgebraicGeometry
open IntegralChowChernModels FieldChowOperators
open scoped TensorProduct

/-- Every coefficient changes by the literal inclusion Z into Q. -/
def rationalCycle (X : Scheme.{0}) : AlgebraicCycle X ℤ →+ AlgebraicCycle X ℚ where
  toFun c := {
    toFun := fun x => (c x : ℚ)
    supportWithinDomain' := Set.subset_univ _
    supportLocallyFiniteWithinDomain' := by
      intro x _
      obtain ⟨U, hU, hfin⟩ := c.locallyFiniteSupport x
      refine ⟨U, hU, hfin.subset ?_⟩
      intro y hy
      refine ⟨hy.1, ?_⟩
      change c y ≠ 0
      intro h
      apply hy.2
      change (c y : ℚ) = 0
      simp only [h, Int.cast_zero] }
  map_zero' := by ext x; simp
  map_add' a b := by
    ext x
    change ((a x + b x : ℤ) : ℚ) = (a x : ℚ) + (b x : ℚ)
    exact Int.cast_add (a x) (b x)

def dimensionRationalCycle (X : Scheme.{0}) (d : ℕ) :
    IntegerSchemeChow.CycleGroup X (d : ℤ) →+ GeometricChow.CycleGroup X d where
  toFun c := ⟨rationalCycle X c.1, by
    intro x hx
    have hi : c.1 x ≠ 0 := by
      intro h
      exact hx (by change (c.1 x : ℚ) = 0; simp [h])
    obtain ⟨n, hn, hh⟩ := c.2 x hi
    have hnd : n = d := Int.ofNat.inj hn
    simpa only [hnd] using hh⟩
  map_zero' := by ext x; simp [rationalCycle]
  map_add' a b := by ext x; exact Int.cast_add (a.1 x) (b.1 x)

variable (F : SchemeData) (d : ℕ)

def integralCycleToField : IntegerSchemeChow.CycleGroup F.scheme.left (d : ℤ) →+
    RelativeCurveClasses.ChowGroup F.scheme d :=
  ((RelativeCurveClasses.relations F.scheme d).mkQ.toAddMonoidHom).comp
    (dimensionRationalCycle F.scheme.left d)

/-- Descent is about the displayed principal-cycle coefficient map. -/
structure PrincipalDescent : Prop where
  preserves : IntegerSchemeChow.rationalEquivalences F.scheme.left (d : ℤ) ≤
    (integralCycleToField F d).ker

def integralToField (D : PrincipalDescent F d) :
    Chow F (d : ℤ) →+ RelativeCurveClasses.ChowGroup F.scheme d :=
  QuotientAddGroup.lift _ (integralCycleToField F d) D.preserves

/-- Native rational scalar extension of that same quotient map. -/
def rationalToField (D : PrincipalDescent F d) :
    TensorProduct ℤ ℚ (Chow F (d : ℤ)) →ₗ[ℚ] RelativeCurveClasses.ChowGroup F.scheme d :=
  TensorProduct.AlgebraTensorModule.lift {
    toFun := fun q => q • (integralToField F d D).toIntLinearMap
    map_add' := by intro q r; ext a; exact add_smul q r (integralToField F d D a)
    map_smul' := by intro q r; ext a; exact mul_smul q r (integralToField F d D a) }

/-- Availability consists of source-relation proofs and bijectivity of the computed map. -/
structure NativeChowComparison where
  descent : ∀ d : ℕ, PrincipalDescent F d
  bijective : ∀ d : ℕ, Function.Bijective (rationalToField F d (descent d))

def fieldToRational (C : NativeChowComparison F) (d : ℕ) :
    RelativeCurveClasses.ChowGroup F.scheme d →ₗ[ℚ] TensorProduct ℤ ℚ (Chow F (d : ℤ)) :=
  (LinearEquiv.ofBijective (rationalToField F d (C.descent d)) (C.bijective d)).symm.toLinearMap

def rationalGradeCast {d e : ℤ} (h : d=e) :
    TensorProduct ℤ ℚ (Chow F d) →ₗ[ℚ] TensorProduct ℤ ℚ (Chow F e) := by
  cases h
  exact LinearMap.id

/-- The virtual-class coefficient conversion retains the actual signed grading. -/
def gradedFieldToRational (C : NativeChowComparison F) (i : ℤ) :
    gradedChow F.scheme i →ₗ[ℚ] TensorProduct ℤ ℚ (Chow F i) := by
  by_cases hi : 0 ≤ i
  · exact (rationalGradeCast F (show (i.toNat : ℤ)=i by omega)).comp
      ((fieldToRational F C i.toNat).comp (positiveChowIso F.scheme i hi).toLinearEquiv.toLinearMap)
  · exact 0

end MathlibExt.AlgebraicGeometry.RationalSchemeChowComparisonModels
