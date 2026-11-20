/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.Universality.IsingFermionicStoppedAnalytic









namespace StatMech.Universality



theorem isingLeapfrogDiffusiveExitInputs_of_pointwise
    (A : Real) (hA : 0 <= A)
    (hpoint : forall (R rho : Nat) (p p' : IsingLeapfrogBox R),
      0 < rho ->
      IsingLeapfrogInteriorMargin R rho p ->
      IsingLeapfrogInteriorMargin R rho p' ->
      IsingLeapfrogDiagonalAdjacent p p' ->
      forall q, |isingLeapfrogExitKernel R (rho * rho) p q -
          isingLeapfrogExitKernel R (rho * rho + 1) p' q| <=
        A / (rho : Real) ^ 2) :
    IsingLeapfrogDiffusiveExitInputs A 152 := by
  refine ⟨hA, by norm_num, ?_⟩
  intro R rho p p' hrho hp hp' hpp'
  exact ⟨hpoint R rho p p' hrho hp hp' hpp',
    isingLeapfrogStoppedKernel_neighbor_timeOffset_diffusive_l1_le
      R rho p p' hrho hp hp' hpp'⟩

end StatMech.Universality
