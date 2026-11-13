/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierD.SixVertexBetheSymmetricInverseBound









open Finset Matrix

namespace StatMech.FrontierD

noncomputable section

theorem sixVertexBethePositiveHalfScaledJacobianMatrix_mulVec
    {N m : Nat} {c : Real} (hc : 2 < c) (q : Fin m -> Real)
    (v : Fin m -> Real) :
    (sixVertexBethePositiveHalfScaledJacobianMatrix N m c q).mulVec v =
      sixVertexEvenSymmetricBetheRootJacobian N m c q
        (fun k => sixVertexPositiveHalfRootGap q k * v k) := by
  have hmatrix : LinearMap.toMatrix'
      (sixVertexEvenSymmetricBetheRootJacobian N m c q).toLinearMap =
        sixVertexBethePositiveHalfJacobianMatrix N m c q := by
    ext j k
    exact sixVertexEvenSymmetricBetheRootJacobian_toMatrix'_apply hc q j k
  rw [sixVertexBethePositiveHalfScaledJacobianMatrix_eq_mul_diagonal,
    <- Matrix.mulVec_mulVec]
  have haction := LinearMap.toMatrix'_mulVec
    (sixVertexEvenSymmetricBetheRootJacobian N m c q).toLinearMap
    ((Matrix.diagonal (sixVertexPositiveHalfRootGap q)).mulVec v)
  rw [hmatrix] at haction
  exact haction.trans (congrArg
    (sixVertexEvenSymmetricBetheRootJacobian N m c q).toLinearMap (by
      funext k
      exact Matrix.mulVec_diagonal _ _ k))

end

end StatMech.FrontierD
