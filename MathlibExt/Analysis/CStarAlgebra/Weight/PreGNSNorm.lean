/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.CStarAlgebra.Weight.PreInnerProduct
public import Mathlib.Analysis.CStarAlgebra.Basic

/-!
# The actual weight seminorm and faithful pre-GNS norm

The proved scalar-weight pre-inner-product Core supplies the stock
seminormed additive group and complex inner-product structure on the
literal pre-GNS type copy. Its norm is the square root of the original
finite positive-square weight value, with no ambient norm substitution.

The original positive-weight faithfulness law proves definiteness:
a zero diagonal has finite square value zero, hence its original positive
square is zero, and the C-star proper-star law forces the original element
to be zero. The stock definite-Core factory constructs the faithful normed
additive group. The same actual pre-inner-product structure is retained.
No norm/inner/Hilbert certificate or existence theorem is supplied as input.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- The actual weight Core gives its original induced seminorm and distance. -/
instance Weight.preGNSSeminormedAddCommGroup (φ : Weight A) : SeminormedAddCommGroup φ.PreGNS :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := φ.preGNSPreInnerProduct)

/-- The same proved Core gives the actual complex pre-inner-product structure. -/
instance Weight.preGNSInnerProductSpace (φ : Weight A) : InnerProductSpace ℂ φ.PreGNS :=
  InnerProductSpace.ofCore φ.preGNSPreInnerProduct

/-- The induced inner product retains the original scalar-weight polarization values. -/
@[simp]
theorem Weight.preGNS_inner (φ : Weight A) (x y : φ.PreGNS) :
    ⟪x, y⟫_ℂ = φ.finiteSquarePolarInner (φ.preGNSLinearEquiv x) (φ.preGNSLinearEquiv y) :=
  rfl

/-- The induced norm is the square root of the original finite positive-square value. -/
theorem Weight.preGNS_norm (φ : Weight A) (x : φ.PreGNS) :
    ‖x‖ = Real.sqrt (φ.finiteSquareValue (φ.preGNSLinearEquiv x)) := by
  change Real.sqrt (RCLike.re (φ.finiteSquarePolarInner
    (φ.preGNSLinearEquiv x) (φ.preGNSLinearEquiv x))) =
      Real.sqrt (φ.finiteSquareValue (φ.preGNSLinearEquiv x))
  rw [φ.finiteSquarePolarInner_self, RCLike.ofReal_re]

/-- The actual pre-GNS norm square equals the original finite weight value. -/
theorem Weight.preGNS_norm_sq (φ : Weight A) (x : φ.PreGNS) :
    ‖x‖ ^ 2 = φ.finiteSquareValue (φ.preGNSLinearEquiv x) := by
  rw [φ.preGNS_norm]
  exact Real.sq_sqrt (φ.finiteSquareValue_nonneg _)

/-- Original positive-weight faithfulness proves the actual diagonal is definite. -/
theorem Weight.preGNS_definite (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (x : φ.PreGNS) (hx : φ.preGNSPreInnerProduct.inner x x = 0) : x = 0 := by
  let y : φ.finiteSquareSubmodule := φ.preGNSLinearEquiv x
  have hreal := congrArg (fun z : ℂ => RCLike.re z) hx
  change RCLike.re (φ.finiteSquarePolarInner y y) = RCLike.re (0 : ℂ) at hreal
  rw [φ.finiteSquarePolarInner_self, RCLike.ofReal_re, map_zero] at hreal
  have hfinite : φ.value (leftSquare (y : A)) < ⊤ := y.property
  change (φ.value (leftSquare (y : A))).toReal = 0 at hreal
  have hvalue : φ.value (leftSquare (y : A)) = 0 :=
    ((ENNReal.toReal_eq_zero_iff _).1 hreal).resolve_right hfinite.ne
  have hsquare : star (y : A) * (y : A) = 0 := hφ (leftSquare (y : A)) hvalue
  have hy : (y : A) = 0 := star_mul_self_eq_zero.mp hsquare
  apply φ.preGNSLinearEquiv.injective
  rw [map_zero]
  apply Subtype.ext
  exact hy

/-- The genuine faithful Core retains the same weight kernel and proved definite field. -/
@[instance_reducible]
def Weight.faithfulPreGNSCore (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    InnerProductSpace.Core ℂ φ.PreGNS where
  __ := φ.preGNSPreInnerProduct
  definite x hx := φ.preGNS_definite hφ x hx

/-- The stock definite-Core factory gives the actual faithful weight normed group. -/
@[instance_reducible]
def Weight.faithfulPreGNSNormedAddCommGroup (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    NormedAddCommGroup φ.PreGNS :=
  InnerProductSpace.Core.toNormedAddCommGroup (cd := φ.faithfulPreGNSCore hφ)

end

end CStarAlgebra.ScalarWeight
