/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electronics.TerminalChargeJacobian

@[expose] public section

open PhyslibExt.Electronics.TerminalChargeJacobian MetaMathlibExt

namespace PhyslibExtTest.Electronics.TerminalChargeJacobian

/-- Pairwise capacitor charges have zero Jacobian column and row sums. -/
example (Cap : Matrix (Fin 3) (Fin 3) ℝ) (hsymm : ∀ i k, Cap i k = Cap k i)
    (v : Fin 3 → ℝ) :
    (∀ j, ∑ i, jacobianMatrix (pairwiseCapacitorCharge 3 Cap) v i j = 0) ∧
      (∀ i, ∑ j, jacobianMatrix (pairwiseCapacitorCharge 3 Cap) v i j = 0) :=
  pairwiseCapacitorCharge_jacobian_sums_eq_zero 3 Cap hsymm v

/-- The leaky example really has column sum `2`. -/
example : ∑ i, jacobianMatrix
    (fun w : Fin 2 → ℝ => ![w 0 - w 1, w 0 - w 1]) 0 i 0 = 2 :=
  leaky_charge_column_sum_ne_zero.2.2

/-- The ground-referenced example really has row sum `1`. -/
example : ∑ j, jacobianMatrix (fun w : Fin 2 → ℝ => ![w 0, -w 0]) 0 0 j = 1 :=
  ground_referenced_row_sum_ne_zero.2.2

/-- And it fails the exact local invariance premise: arbitrarily
small nonzero common-mode shifts move the charge. -/
example : ∃ v : Fin 2 → ℝ, ∀ δ > 0, ∃ c : ℝ, |c| < δ ∧
    (fun w : Fin 2 → ℝ => ![w 0, -w 0]) (v + c • (fun _ => (1 : ℝ))) ≠
      (fun w : Fin 2 → ℝ => ![w 0, -w 0]) v :=
  ground_referenced_row_sum_ne_zero.2.1

end PhyslibExtTest.Electronics.TerminalChargeJacobian
