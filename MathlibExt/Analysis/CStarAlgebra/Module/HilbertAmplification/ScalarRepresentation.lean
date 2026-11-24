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

public import MathlibExt.Analysis.CStarAlgebra.Module.Compact
public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic

/-!
# The scalar representation on a nonunital coefficient self module

Scalar multiplication by c is c times the genuine identity adjointable
endomorphism of A. The coefficient algebra need not have an identity.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra

namespace CStarModule.HilbertAmplification

noncomputable section

universe uA

/-- The original complex scalar action on the coefficient self module,
with its canonical opposite spectral order and Hilbert-module data. -/
def scalarSelfHom (A : Type uA) [NonUnitalCStarAlgebra A] :
    letI : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ;
    letI : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ;
    letI : CStarModule Aᵐᵒᵖ A := CStarModule.Right.selfModule;
    ℂ →⋆ₙₐ[ℂ] AdjointableOperator.End A A := by
  let : PartialOrder Aᵐᵒᵖ := CStarAlgebra.spectralOrder Aᵐᵒᵖ
  let : StarOrderedRing Aᵐᵒᵖ := CStarAlgebra.spectralOrderedRing Aᵐᵒᵖ
  let : CStarModule Aᵐᵒᵖ A := CStarModule.Right.selfModule
  exact
    { toFun := fun c => c • (1 : AdjointableOperator.End A A)
      map_zero' := zero_smul ℂ (1 : AdjointableOperator.End A A)
      map_add' := fun c d => add_smul c d (1 : AdjointableOperator.End A A)
      map_mul' := fun c d => by
        rw [smul_mul_assoc, mul_smul_comm, one_mul, smul_smul]
      map_smul' := fun c d => by
        change (c * d) • (1 : AdjointableOperator.End A A) =
          c • (d • (1 : AdjointableOperator.End A A))
        exact (smul_smul c d (1 : AdjointableOperator.End A A)).symm
      map_star' := fun c => by
        rw [star_smul, star_one] }

end

end CStarModule.HilbertAmplification
