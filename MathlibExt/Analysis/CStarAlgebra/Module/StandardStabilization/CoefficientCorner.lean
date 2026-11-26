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

public import MathlibExt.Analysis.CStarAlgebra.Module.StandardStabilization
public import MathlibExt.Analysis.CStarAlgebra.Module.Matrix.StandardCompact
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Initial coefficient corner in standard stabilization

For nonunital C-star `B`, insert its coefficient as a one-by-one C-star matrix and use the
initial coordinate `0` of `H_B = Standard B ℕ`. The resulting nonunital star homomorphism `β : B
→ K_B(H_B)` has action `β(b)x = single 0 (b * coord 0 x)`.

This corner preserves the coefficient norm: `‖β(b)‖ = ‖b‖`, including the zero algebra. It is
constructed from coefficient insertion and evaluation, without a unit-valued basis vector.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarModule.Right

noncomputable section
universe uB
attribute [local instance] standardStabilizationCStarAlgebra

/-- **Initial standard-module coordinate.** The injection `Fin 1 ↪ ℕ` sends its unique index to
`0`. -/
public def standardCoefficientIndex : Fin 1 ↪ ℕ where
  toFun i := i.val
  inj' := Fin.val_injective

/-- **Coefficient as a one-by-one matrix.** For nonunital C-star `B`, the star homomorphism `B →
M₁(B)` sends `b` to the matrix with its unique entry equal to `b`. -/
public def standardCoefficientMatrix (B : Type uB) [NonUnitalCStarAlgebra B] :
    B →⋆ₙₐ[ℂ] CStarMatrix (Fin 1) (Fin 1) B := by
  exact (CStarMatrix.toOneByOne (Fin 1) ℂ B).toNonUnitalStarAlgHom

/-- **Entry of the one-by-one coefficient matrix.** `standardCoefficientMatrix B b i j = b` for
`i,j : Fin 1`. -/
public theorem standardCoefficientMatrix_apply (B : Type uB) [NonUnitalCStarAlgebra B]
    (b : B) (i j : Fin 1) : standardCoefficientMatrix B b i j = b := rfl

/-- **Coefficient corner in the stabilization algebra.** For nonunital C-star `B`, the nonunital
star map `β : B → StandardStabilization B` is the compact operator `x ↦ single 0 (b * coord 0
x)`. -/
public def standardCoefficientCompactHom (B : Type uB) [NonUnitalCStarAlgebra B] :
    B →⋆ₙₐ[ℂ] StandardStabilization B := by
  letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  exact (CStarModule.AdjointableOperator.rightMatrixStandardCompactHom
    (B := B) standardCoefficientIndex).comp (standardCoefficientMatrix B)

/-- **Value of the initial coordinate injection.** `standardCoefficientIndex (0 : Fin 1) = 0`. -/
public theorem standardCoefficientIndex_zero : standardCoefficientIndex (0 : Fin 1) = 0 := rfl

/-- **Vector action of the coefficient corner.** For nonunital C-star `B`, `b : B` and `x :
Standard B ℕ`, `β(b)x = Standard.single 0 (b * Standard.coord 0 x)`, where `β =
standardCoefficientCompactHom B`. -/
public theorem standardCoefficientCompactHom_apply (B : Type uB) [NonUnitalCStarAlgebra B] :
    letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ;
    letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ;
    letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule;
    ∀ (b : B) (x : H B),
      (Subtype.val (show CStarModule.AdjointableOperator.CompactEnd B (H B) from standardCoefficientCompactHom B b)) x =
        Standard.single 0 (b * Standard.coord 0 x) := by
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  exact fun b x => by
    change (Subtype.val (CStarModule.AdjointableOperator.rightMatrixStandardCompactHom
      (B := B) standardCoefficientIndex (standardCoefficientMatrix B b))) x =
        Standard.single 0 (b * Standard.coord 0 x)
    simpa only [Fin.sum_univ_one, standardCoefficientMatrix_apply, standardCoefficientIndex_zero] using
      (CStarModule.AdjointableOperator.rightMatrixStandardCompactHom_apply
        (B := B) standardCoefficientIndex (standardCoefficientMatrix B b) x)

/-- **Norm of the coefficient corner.** For nonunital C-star `B`, `‖standardCoefficientCompactHom
B b‖ = ‖b‖`. -/
public theorem norm_standardCoefficientCompactHom (B : Type uB) [NonUnitalCStarAlgebra B] :
    letI : NonUnitalCStarAlgebra (StandardStabilization B) := standardStabilizationCStarAlgebra B;
    ∀ b : B, ‖standardCoefficientCompactHom B b‖ = ‖b‖ := by
  let : PartialOrder B := CStarAlgebra.spectralOrder B
  let : StarOrderedRing B := CStarAlgebra.spectralOrderedRing B
  let : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  let : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  let : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  let : NonUnitalCStarAlgebra (StandardStabilization B) := standardStabilizationCStarAlgebra B
  exact fun b =>
    (CStarModule.AdjointableOperator.norm_rightMatrixStandardCompactHom_apply
      (B := B) standardCoefficientIndex (standardCoefficientMatrix B b)).trans
        (NonUnitalStarAlgHom.norm_map
          (CStarMatrix.toOneByOne (Fin 1) ℂ B).toNonUnitalStarAlgHom
          (CStarMatrix.toOneByOne (Fin 1) ℂ B).toEquiv.injective b)

end

end CStarModule.Right
