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

public import MathlibExt.Analysis.CStarAlgebra.Weight.GNSLeftOperator
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Tactic.FunProp

/-!
# The original weight left action and its actual adjoint

The original star-product square differences match the left action at a
with the left action at star a. Finite-positive weight difference equality
therefore proves the real pairing identity. Complex linearity of the
literal finite-square left map proves the imaginary coordinate as well.

This constructs the pre-GNS adjoint pairing and its actual completed
operator adjoint law, needed by the star-representation constructor.
No full finite integration extension, source existence output or operator/
inner/norm certificate is supplied. Representation faithfulness, normality,
normal range and Tomita/modular/polar statements remain separate.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped InnerProductSpace

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- The original star-product difference matches left multiplication and its original star. -/
theorem leftSquare_difference_leftMul (a x y : A) :
    (leftSquare (a * x + y) : A) - (leftSquare (a * x - y) : A) =
      (leftSquare (x + star a * y) : A) - (leftSquare (x - star a * y) : A) := by
  simp only [leftSquare_difference, star_mul, star_star, mul_assoc]

/-- Actual finite-positive value relations give the original real adjoint pairing. -/
theorem Weight.finiteSquarePolarRe_leftMul (φ : Weight A) (a : A)
    (x y : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarRe (φ.finiteSquareLeftMul a x) y =
      φ.finiteSquarePolarRe x (φ.finiteSquareLeftMul (star a) y) := by
  have hraw :
      (leftSquare (((φ.finiteSquareLeftMul a x) + y : φ.finiteSquareSubmodule) : A) : A) -
        (leftSquare (((φ.finiteSquareLeftMul a x) - y : φ.finiteSquareSubmodule) : A) : A) =
      (leftSquare ((x + φ.finiteSquareLeftMul (star a) y : φ.finiteSquareSubmodule) : A) : A) -
        (leftSquare ((x - φ.finiteSquareLeftMul (star a) y : φ.finiteSquareSubmodule) : A) : A) := by
    change (leftSquare (a * (x : A) + (y : A)) : A) -
      (leftSquare (a * (x : A) - (y : A)) : A) =
      (leftSquare ((x : A) + star a * (y : A)) : A) -
      (leftSquare ((x : A) - star a * (y : A)) : A)
    exact leftSquare_difference_leftMul a (x : A) (y : A)
  have h := φ.finite_toReal_sub_eq_sub
    (leftSquare (((φ.finiteSquareLeftMul a x) + y : φ.finiteSquareSubmodule) : A))
    (leftSquare (((φ.finiteSquareLeftMul a x) - y : φ.finiteSquareSubmodule) : A))
    (leftSquare ((x + φ.finiteSquareLeftMul (star a) y : φ.finiteSquareSubmodule) : A))
    (leftSquare ((x - φ.finiteSquareLeftMul (star a) y : φ.finiteSquareSubmodule) : A))
    ((φ.finiteSquareLeftMul a x) + y).property ((φ.finiteSquareLeftMul a x) - y).property
    (x + φ.finiteSquareLeftMul (star a) y).property (x - φ.finiteSquareLeftMul (star a) y).property hraw
  dsimp only [Weight.finiteSquarePolarRe, Weight.finiteSquareValue]
  linarith [h]

/-- The actual complex weight pairing has the original left-star adjoint relation. -/
theorem Weight.finiteSquarePolarInner_leftMul (φ : Weight A) (a : A)
    (x y : φ.finiteSquareSubmodule) :
    φ.finiteSquarePolarInner (φ.finiteSquareLeftMul a x) y =
      φ.finiteSquarePolarInner x (φ.finiteSquareLeftMul (star a) y) := by
  apply Complex.ext
  · change φ.finiteSquarePolarRe (φ.finiteSquareLeftMul a x) y =
      φ.finiteSquarePolarRe x (φ.finiteSquareLeftMul (star a) y)
    exact φ.finiteSquarePolarRe_leftMul a x y
  · change φ.finiteSquarePolarRe (Complex.I • φ.finiteSquareLeftMul a x) y =
      φ.finiteSquarePolarRe (Complex.I • x) (φ.finiteSquareLeftMul (star a) y)
    rw [← (φ.finiteSquareLeftMul a).map_smul Complex.I x]
    exact φ.finiteSquarePolarRe_leftMul a (Complex.I • x) y

/-- The actual weight pre-GNS left operator is paired with left multiplication by star a. -/
theorem Weight.preGNSLeftMul_adjoint_pairing (φ : Weight A) (a : A) (x y : φ.PreGNS) :
    ⟪φ.preGNSLeftMul a x, y⟫_ℂ = ⟪x, φ.preGNSLeftMul (star a) y⟫_ℂ := by
  rw [φ.preGNS_inner, φ.preGNS_inner, φ.preGNSLeftMul_apply, φ.preGNSLeftMulLinear_apply,
    φ.preGNSLeftMul_apply, φ.preGNSLeftMulLinear_apply]
  exact φ.finiteSquarePolarInner_leftMul a (φ.preGNSLinearEquiv x) (φ.preGNSLinearEquiv y)

/-- The completed bounded left operators have the actual original star/adjoint law. -/
theorem Weight.gnsLeftMul_star (φ : Weight A) (a : A) :
    φ.gnsLeftMul (star a) = star (φ.gnsLeftMul a) := by
  rw [ContinuousLinearMap.star_eq_adjoint]
  refine (ContinuousLinearMap.eq_adjoint_iff (φ.gnsLeftMul (star a)) (φ.gnsLeftMul a)).2 ?_
  intro x y
  induction x, y using UniformSpace.Completion.induction_on₂ with
  | hp => apply isClosed_eq <;> fun_prop
  | ih x y =>
      change ⟪φ.gnsLeftMul (star a) (φ.toGNS x), φ.toGNS y⟫_ℂ =
        ⟪φ.toGNS x, φ.gnsLeftMul a (φ.toGNS y)⟫_ℂ
      rw [φ.gnsLeftMul_toGNS, φ.gnsLeftMul_toGNS, φ.toGNS_inner, φ.toGNS_inner]
      simpa only [star_star] using φ.preGNSLeftMul_adjoint_pairing (star a) x y

end

end CStarAlgebra.ScalarWeight
