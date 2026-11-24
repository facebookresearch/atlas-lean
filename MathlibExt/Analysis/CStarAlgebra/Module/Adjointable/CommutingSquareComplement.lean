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

public import MathlibExt.Analysis.CStarAlgebra.Module.Adjointable
public import MathlibExt.Analysis.CStarAlgebra.SquareComplement

/-!
# The actual square complement in a represented commutant

An actual adjointable endomorphism commuting with a star representation has a
square complement in the same commutant. The complement is the positive CFC
square root of the original norm-square scalar minus the adjoint square.

This extra commutation is needed to bound the second-factor map on the actual
balanced internal tensor used by Blackadar, K-Theory for Operator Algebras,
Theorem 10.1.2. A square complement without commutation does not suffice there.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open scoped CStarAlgebra

namespace CStarModule.AdjointableOperator

universe uB uC uE

variable {B : Type uB} [NonUnitalCStarAlgebra B]
  [PartialOrder Bᵐᵒᵖ] [StarOrderedRing Bᵐᵒᵖ]
variable {C : Type uC} [NonUnitalCStarAlgebra C]
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [SMul Bᵐᵒᵖ E] [CStarModule Bᵐᵒᵖ E] [CompleteSpace E]

/-- Construct the norm-square complement in the same actual commutant. -/
theorem exists_commuting_norm_square_complement
    (φ : C →⋆ₙₐ[ℂ] End B E) (T : End B E)
    (hComm : ∀ c : C, Commute T (φ c)) :
    ∃ Q : End B E, (∀ c : C, Commute Q (φ c)) ∧
      ∀ x : E, T.adjoint (T x) + Q.adjoint (Q x) = (‖T‖ ^ 2 : ℝ) • x := by
  let : PartialOrder (End B E) := CStarAlgebra.spectralOrder _
  let : StarOrderedRing (End B E) := CStarAlgebra.spectralOrderedRing _
  have hStar : ∀ c : C, Commute (star T) (φ c) := by
    intro c
    simpa only [map_star, star_star] using (hComm (star c)).star_star
  refine ⟨CStarAlgebra.normSquareComplement T, ?_, ?_⟩
  · intro c
    exact CStarAlgebra.normSquareComplement_commute T (φ c) (hComm c) (hStar c)
  · intro x
    have h := congrArg (fun S : End B E => S x)
      (CStarAlgebra.star_mul_self_add_normSquareComplement T)
    simpa only [add_apply, mul_apply, star_apply,
      IsScalarTower.algebraMap_apply ℝ ℂ (End B E), algebraMap_apply,
      RCLike.real_smul_eq_coe_smul (K := ℂ)] using h

end CStarModule.AdjointableOperator
