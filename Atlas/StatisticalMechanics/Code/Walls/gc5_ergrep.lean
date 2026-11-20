/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Mathlib
import Code.Sharpness.RandomCurrent
import Code.Sharpness.CurrentRep
import Code.Ising.CorrelationRatio

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent
open StatMech.Ising

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

















theorem gc5_currentSum_eq_sum_weight (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) :
    Sharpness.currentSum G β J A
      = ∑' m : ↥G.edgeFinset → ℕ,
          (if Sharpness.sources G (Sharpness.ofEdgeFun G m) = A
            then Sharpness.weight G β J (Sharpness.ofEdgeFun G m) else 0) := rfl

















theorem gc5_Z0_pos (β : ℝ) (J : Sym2 V → ℝ) :
    0 < Sharpness.currentSum G β J ∅ :=
  acr_currentSum_empty_pos G β J




theorem gc5_Z0_ne_zero (β : ℝ) (J : Sym2 V → ℝ) :
    Sharpness.currentSum G β J ∅ ≠ 0 :=
  ne_of_gt (gc5_Z0_pos G β J)




























theorem gc5_ergRep (β : ℝ) (A : Finset V) :
    isingExpectation G β 0 (spinProd A)
      = Sharpness.currentSum G β (fun _ => 1) A / Sharpness.currentSum G β (fun _ => 1) ∅ :=
  Sharpness.isingExpectation_eq_currentSum_ratio G β A









theorem gc5_ergRep_J (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V) :
    Sharpness.expectationJ G β J A
      = Sharpness.currentSum G β J A / Sharpness.currentSum G β J ∅ :=
  Sharpness.current_representation G β J A












theorem gc5_ratio_well_defined (β : ℝ) (A : Finset V) :
    isingExpectation G β 0 (spinProd A)
        = Sharpness.currentSum G β (fun _ => 1) A / Sharpness.currentSum G β (fun _ => 1) ∅
      ∧ 0 < Sharpness.currentSum G β (fun _ => 1) ∅ :=
  ⟨gc5_ergRep G β A, gc5_Z0_pos G β (fun _ => 1)⟩









theorem gc5_correlation_times_Z0_eq_numerator (β : ℝ) (A : Finset V) :
    isingExpectation G β 0 (spinProd A) * Sharpness.currentSum G β (fun _ => 1) ∅
      = Sharpness.currentSum G β (fun _ => 1) A := by
  rw [gc5_ergRep, div_mul_cancel₀ _ (gc5_Z0_ne_zero G β (fun _ => 1))]

end StatMech.Walls
