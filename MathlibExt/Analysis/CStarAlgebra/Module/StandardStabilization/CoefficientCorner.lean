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
# The actual coefficient corner into compacts of the genuine standard module

H_B is the existing coefficient-inner completion of finite-support vectors,
with its verified norm-convergent coefficient square-sum realization. The
coefficient goes through the literal 1×1 matrix and the actual finite-coordinate
compact corner. No scalar norm-l2(B), coefficient unit, target model,
stabilization/equivalence output or V/K0 theorem is used to form this DATA.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarModule.Right

noncomputable section
universe uB
attribute [local instance] standardStabilizationCStarAlgebra

/-- The actual initial coefficient coordinate in the genuine standard module. -/
public def standardCoefficientIndex : Fin 1 ↪ ℕ where
  toFun i := i.val
  inj' := Fin.val_injective

/-- The actual source coefficient as its literal 1×1 C-star matrix, with no coefficient unit. -/
public def standardCoefficientMatrix (B : Type uB) [NonUnitalCStarAlgebra B] :
    B →⋆ₙₐ[ℂ] CStarMatrix (Fin 1) (Fin 1) B := by
  exact (CStarMatrix.toOneByOne (Fin 1) ℂ B).toNonUnitalStarAlgHom

/-- Every original 1×1 entry is exactly the supplied coefficient. -/
public theorem standardCoefficientMatrix_apply (B : Type uB) [NonUnitalCStarAlgebra B]
    (b : B) (i j : Fin 1) : standardCoefficientMatrix B b i j = b := rfl

/-- The actual nonunital coefficient corner into K(H_B), using its original compact/inner norm. -/
public def standardCoefficientCompactHom (B : Type uB) [NonUnitalCStarAlgebra B] :
    B →⋆ₙₐ[ℂ] StandardStabilization B := by
  letI : PartialOrder Bᵐᵒᵖ := CStarAlgebra.spectralOrder Bᵐᵒᵖ
  letI : StarOrderedRing Bᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Bᵐᵒᵖ
  letI : CStarModule Bᵐᵒᵖ B := CStarModule.Right.selfModule
  exact (CStarModule.AdjointableOperator.rightMatrixStandardCompactHom
    (B := B) standardCoefficientIndex).comp (standardCoefficientMatrix B)

/-- The literal initial standard coordinate is zero. -/
public theorem standardCoefficientIndex_zero : standardCoefficientIndex (0 : Fin 1) = 0 := rfl

/-- Every whole standard-vector action is the original single(0,b*coord(0,x)). -/
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

/-- The original complete matrix and compact norms give the exact coefficient norm. -/
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
