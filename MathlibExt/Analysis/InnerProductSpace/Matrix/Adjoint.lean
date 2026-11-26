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

public import MathlibExt.Topology.Algebra.Module.Matrix
public import MathlibExt.Analysis.InnerProductSpace.Adjoint.OneSided
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Rectangular adjoints of operator-valued matrices

Let 𝕜 be an RCLike field, E a complete inner product space, F an inner product space and m,n
finite index types. For A_ij:E→F bounded linear, let T_A:E^n→F^m act by (T_A v)_i=∑j
A_ij(v_j), with finite ℓ² product norms. The complete-source adjoint of T_A is T_(A♯), where
(A♯)_ji=(A_ij)†. If F is also complete, this is the usual bounded-operator adjoint.
-/

@[expose] public section

noncomputable section

open scoped BigOperators

universe uScalar uRow uColumn uSource uTarget

variable {𝕜 : Type uScalar} [RCLike 𝕜]
variable {m : Type uRow} {n : Type uColumn}
variable {E : Type uSource} {F : Type uTarget}
variable [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
variable [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace Matrix

/-- **One-sided adjoint of a rectangular Hilbert column action.**

Let 𝕜 be an RCLike field, E a complete inner product space, F an inner product space and m,n
finite index types. For A_ij:E→F bounded linear, let T_A:E^n→F^m act by (T_A v)_i=∑j
A_ij(v_j), with finite ℓ² product norms. For A_ij†:F→E the complete-source adjoint of A_ij,
(T_A)†=T_(A♯), with A♯ the transpose of the entry adjoints. F need not be complete.
-/
@[simp]
theorem toPiLpContinuousLinearMap_adjointOfCompleteSource [Fintype m] [Fintype n]
    (M : Matrix m n (E →L[𝕜] F)) :
    ContinuousLinearMap.adjointOfCompleteSource (toPiLpContinuousLinearMap M) =
      toPiLpContinuousLinearMap
        ((M.map fun T : E →L[𝕜] F =>
          ContinuousLinearMap.adjointOfCompleteSource T).transpose) := by
  apply ContinuousLinearMap.ext
  intro u
  apply ext_inner_right 𝕜
  intro v
  simp only [ContinuousLinearMap.adjointOfCompleteSource_inner_left,
    PiLp.inner_apply, toPiLpContinuousLinearMap_apply,
    transpose_apply, map_apply, sum_inner, inner_sum]
  exact Finset.sum_comm

variable [CompleteSpace F]

/-- **Adjoint matrix of a rectangular operator action.**

Let 𝕜 be an RCLike field, E a complete inner product space, F an inner product space and m,n
finite index types. For A_ij:E→F bounded linear, let T_A:E^n→F^m act by (T_A v)_i=∑j
A_ij(v_j), with finite ℓ² product norms. Assume also F is complete. Then
adjoint(T_A)=T_(transpose(A_ij.adjoint)), between the finite Hilbert products.
-/
@[simp]
theorem toPiLpContinuousLinearMap_adjoint [Fintype m] [Fintype n]
    (M : Matrix m n (E →L[𝕜] F)) :
    ContinuousLinearMap.adjoint (toPiLpContinuousLinearMap M) =
      toPiLpContinuousLinearMap
        ((M.map fun T : E →L[𝕜] F => ContinuousLinearMap.adjoint T).transpose) := by
  simpa only [ContinuousLinearMap.adjointOfCompleteSource_eq_adjoint] using
    (toPiLpContinuousLinearMap_adjointOfCompleteSource M)

end Matrix

end
