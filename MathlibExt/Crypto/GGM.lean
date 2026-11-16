/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.List.Basic

/-!
# GGM construction: evaluation algebra

The GGM pseudorandom function folds the two halves of a
PRG (coded as a step family `step : Bool → ℕ → ℕ` on
natural-coded seeds) along the input bits. Evaluation
splits over concatenation of the input. The hybrid
security proof is not included here.
-/

@[expose] public section

/-- GGM construction core (QCI-21): from a length-doubling
step family `step : Bool → ℕ → ℕ` (the two halves of a PRG
applied to a seed, seeds coded as naturals), the PRF at
input bits `bs` folds the steps from the seed. -/
def ggmEval (step : Bool → ℕ → ℕ) (seed : ℕ) (bs : List Bool) : ℕ :=
  bs.foldl (fun s b => step b s) seed

/-- Evaluation splits over concatenation of the input. -/
theorem ggmEval_append (step : Bool → ℕ → ℕ) (seed : ℕ)
    (bs₁ bs₂ : List Bool) :
    ggmEval step seed (bs₁ ++ bs₂)
      = ggmEval step (ggmEval step seed bs₁) bs₂ := by
  unfold ggmEval
  exact List.foldl_append

/-- The value at a prefix determines the subtree: evaluating
a longer input through its prefix equals evaluating the
suffix from the prefix value (same statement as append with
roles renamed, kept for the hybrid argument). -/
theorem ggmEval_cons (step : Bool → ℕ → ℕ) (seed : ℕ)
    (b : Bool) (bs : List Bool) :
    ggmEval step seed (b :: bs) = ggmEval step (step b seed) bs := by
  unfold ggmEval
  exact List.foldl_cons

end
