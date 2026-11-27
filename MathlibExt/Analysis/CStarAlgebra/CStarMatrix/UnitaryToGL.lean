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

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Algebra.Star.Unitary
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import MathlibExt.Analysis.CStarAlgebra.CStarMatrix.Map

/-!
# Actual finite general-linear values of C-star matrix unitaries

Forget the actual matrix norm through the stock ring equivalence, then map
the unitary's actual inverse pair to ordinary matrix units. This is the DATA
needed by the original finite K1 representative class. No K-equivalence,
component quotient, path or matrix-fold output is a premise.
-/

@[expose] public section
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarMatrix

universe uR uI
variable {R : Type uR} {ι : Type uI}
variable [Semiring R] [StarRing R] [Fintype ι] [DecidableEq ι]

/-- Let `R` be a semiring. Let `ι` be a finite index type with decidable equality. The star on `R` is an
additive involution reversing products. The unitary-to-ordinary-GL homomorphism, preserving both
inverse matrix values.
-/
public def unitaryToGL :
    unitary (CStarMatrix ι ι R) →* Matrix.GeneralLinearGroup ι R :=
  (Units.map (CStarMatrix.ofMatrixRingEquiv (n := ι) (A := R)).symm.toMonoidHom).comp
    Unitary.toUnits

/-- Let `R` be a semiring. Let `ι` be a finite index type with decidable equality. The star on `R` is an
additive involution reversing products. For `w : unitary (CStarMatrix ι ι R)`. The whole ordinary
matrix is exactly the C-star matrix unitary's value.
-/
public theorem unitaryToGL_coe_matrix (w : unitary (CStarMatrix ι ι R)) :
    (unitaryToGL w : Matrix ι ι R) =
      (CStarMatrix.ofMatrixRingEquiv (n := ι) (A := R)).symm (w : CStarMatrix ι ι R) := rfl

/-- Let `R` be a semiring. Let `ι` be a finite index type with decidable equality. The star on `R` is an
additive involution reversing products. For `w : unitary (CStarMatrix ι ι R)` and `i` and `j : ι`.
Every ordinary finite matrix coefficient has its unitary value.
-/
public theorem unitaryToGL_apply_entry (w : unitary (CStarMatrix ι ι R)) (i j : ι) :
    (unitaryToGL w : Matrix ι ι R) i j = (w : CStarMatrix ι ι R) i j := rfl

end CStarMatrix
