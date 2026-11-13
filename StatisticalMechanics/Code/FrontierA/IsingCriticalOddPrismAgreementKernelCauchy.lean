/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FrontierA.IsingCriticalOddPrismLayerCoordinates










namespace StatMech.FrontierA

open StatMech StatMech.Ising
open scoped BigOperators

noncomputable section



theorem oddPrismAgreementEndpointKernel_sq_le_diagonal
    (beta : Real) (n : Nat)
    (a q : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))) :
    oddPrismAgreementEndpointKernel beta n a q ^ 2 <=
      oddPrismAgreementEndpointKernel beta n a a *
        oddPrismAgreementEndpointKernel beta n q q := by
  let f : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1)) -> Real :=
    fun s => oddPrismLayerHalfWeight beta n s *
      oddPrismUpperConditionedVector beta n (ghsLMate a s)
  let g : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1)) -> Real :=
    fun s => oddPrismLayerHalfWeight beta n s *
      oddPrismUpperConditionedVector beta n (ghsLMate q s)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset
      (ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1)))) f g
  have haq : oddPrismAgreementEndpointKernel beta n a q =
      ∑ s, f s * g s := by
    unfold oddPrismAgreementEndpointKernel f g
    apply Finset.sum_congr rfl
    intro s _
    ring
  have haa : oddPrismAgreementEndpointKernel beta n a a =
      ∑ s, f s ^ 2 := by
    unfold oddPrismAgreementEndpointKernel f
    apply Finset.sum_congr rfl
    intro s _
    ring
  have hqq : oddPrismAgreementEndpointKernel beta n q q =
      ∑ s, g s ^ 2 := by
    unfold oddPrismAgreementEndpointKernel g
    apply Finset.sum_congr rfl
    intro s _
    ring
  rw [haq, haa, hqq]
  exact hcs


theorem oddPrismAgreementEndpointKernel_principalMinor_nonneg
    (beta : Real) (n : Nat)
    (a q : ConfigSpace (Fin (2 * n + 1) × Fin (2 * n + 1))) :
    0 <= oddPrismAgreementEndpointKernel beta n a a *
        oddPrismAgreementEndpointKernel beta n q q -
      oddPrismAgreementEndpointKernel beta n a q ^ 2 := by
  exact sub_nonneg.mpr
    (oddPrismAgreementEndpointKernel_sq_le_diagonal beta n a q)

end

end StatMech.FrontierA
