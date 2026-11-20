/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/











import Code.FrontierB.FiniteLocalSwitching

open scoped symmDiff

namespace StatMech.FrontierB

open Finset Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable local instance normalizedSwitchingPropDecidable
    (p : Prop) : Decidable p := Classical.propDecidable p



noncomputable def normalizedGatedSourcePairSum
    (beta : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (P : Current V → Prop) [DecidablePred P] : ℝ :=
  gatedSourcePairSum G beta J A B P /
    (currentSum G beta J A * currentSum G beta J B)



theorem sourcePairNormalization_mul
    (beta : ℝ) (J : Sym2 V → ℝ) (A B : Finset V)
    (P : Current V → Prop) [DecidablePred P]
    (hA : 0 < currentSum G beta J A)
    (hB : 0 < currentSum G beta J B) :
    (currentSum G beta J A * currentSum G beta J B) *
        normalizedGatedSourcePairSum G beta J A B P =
      gatedSourcePairSum G beta J A B P := by
  rw [normalizedGatedSourcePairSum]
  exact mul_div_cancel₀ _ (mul_ne_zero hA.ne' hB.ne')




theorem normalizedGatedSourcePairSum_switching
    (beta : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    {u v : V} (huv : u ≠ v)
    (P : Current V → Prop) [DecidablePred P]
    (hAu : 0 < currentSum G beta J (A ∆ ({u, v} : Finset V)))
    (huvSum : 0 < currentSum G beta J ({u, v} : Finset V))
    (hA : 0 < currentSum G beta J A)
    (hzero : 0 < currentSum G beta J ∅) :
    (currentSum G beta J (A ∆ ({u, v} : Finset V)) *
        currentSum G beta J ({u, v} : Finset V)) *
        normalizedGatedSourcePairSum G beta J
          (A ∆ ({u, v} : Finset V)) {u, v} P =
      (currentSum G beta J A * currentSum G beta J ∅) *
        normalizedGatedSourcePairSum G beta J A ∅
          (fun m => P m ∧ CurrentConnected G m u v) := by
  rw [sourcePairNormalization_mul G beta J
      (A ∆ ({u, v} : Finset V)) {u, v} P hAu huvSum,
    sourcePairNormalization_mul G beta J A ∅
      (fun m => P m ∧ CurrentConnected G m u v) hA hzero]
  exact gatedSourcePairSum_switching G beta J A huv P



theorem normalizedGatedSourcePairSum_switching_local
    (beta : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    {u v : V} (huv : u ≠ v) (S : Finset (Sym2 V))
    (Q : (↑S → ℕ) → Prop) [DecidablePred Q]
    (hAu : 0 < currentSum G beta J (A ∆ ({u, v} : Finset V)))
    (huvSum : 0 < currentSum G beta J ({u, v} : Finset V))
    (hA : 0 < currentSum G beta J A)
    (hzero : 0 < currentSum G beta J ∅) :
    (currentSum G beta J (A ∆ ({u, v} : Finset V)) *
        currentSum G beta J ({u, v} : Finset V)) *
        normalizedGatedSourcePairSum G beta J
          (A ∆ ({u, v} : Finset V)) {u, v}
          (currentLocalPattern S Q) =
      (currentSum G beta J A * currentSum G beta J ∅) *
        normalizedGatedSourcePairSum G beta J A ∅
          (fun m => currentLocalPattern S Q m ∧
            CurrentConnected G m u v) :=
  normalizedGatedSourcePairSum_switching G beta J A huv
    (currentLocalPattern S Q) hAu huvSum hA hzero

end StatMech.FrontierB
