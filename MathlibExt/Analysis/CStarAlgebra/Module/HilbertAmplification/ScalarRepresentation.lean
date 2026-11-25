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
# Complex scalars on a nonunital coefficient module

For a nonunital C-star algebra `A`, regard `A` as a right module over itself with `⟨a,b⟩_A =
star a*b`. The scalar representation is `λ(c) = c • id_A`, acting as `λ(c) a = c • a`. It is a
complex star-algebra homomorphism into adjointable endomorphisms; the identity here is that of
the endomorphism algebra, so `A` may be nonunital.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra

namespace CStarModule.HilbertAmplification

noncomputable section

universe uA

/-- **Scalar representation on the coefficient self-module.** For a nonunital C-star algebra `A`,
`scalarSelfHom A : ℂ → End_A(A)` sends `c` to `c • id_A`, acting as `a ↦ c • a` with adjoint
`a ↦ star c • a`. -/
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
