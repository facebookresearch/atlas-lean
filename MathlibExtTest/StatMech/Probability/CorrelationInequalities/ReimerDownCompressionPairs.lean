/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.ReimerDownCompressionPairs

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.ReimerButterflyProve2`

* `dpairsCount_downDown_mono` on `Fin 2` for the families `{{0}}`, `{{1}}`;
* `wdpairs_downDown_mono` for the weight `w x b = if b then 1/3 else 2/3`, whose hypothesis
  `w i true ≤ w i false` is proved;
* `wdpairs_downDown_not_mono_general` (the counterexample when that hypothesis fails).
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerButterflyProve2

open _root_.StatMech


/-- The family `{{0}}` on `Fin 2`. -/
def famA : Finset (Finset (Fin 2)) := {{0}}

/-- The family `{{1}}` on `Fin 2`. -/
def famB : Finset (Finset (Fin 2)) := {{1}}

/-- A weight favoring closed coordinates. -/
noncomputable def wClosed : Fin 2 → Bool → ℝ := fun _ b => if b then 1 / 3 else 2 / 3

-- Down-compression at `0` does not decrease the number of disjoint pairs.
example : dpairsCount famA famB
    ≤ dpairsCount (Down.compression 0 famA) (Down.compression 0 famB) :=
  dpairsCount_downDown_mono famA famB 0

-- The weighted version, with all hypotheses discharged.
example : wdpairs wClosed famA famA
    ≤ wdpairs wClosed (Down.compression 0 famA) (Down.compression 0 famA) :=
  wdpairs_downDown_mono (fun _ b => by cases b <;> norm_num [wClosed]) 0
    (by norm_num [wClosed]) famA famA

-- Without `w i true ≤ w i false` the weighted monotonicity fails.
example : ∃ (w : Fin 1 → Bool → ℝ) (𝒜 ℬ : Finset (Finset (Fin 1))) (i : Fin 1),
    (∀ x b, 0 ≤ w x b) ∧
      ¬ (wdpairs w 𝒜 ℬ ≤ wdpairs w (Down.compression i 𝒜) (Down.compression i ℬ)) :=
  wdpairs_downDown_not_mono_general

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerButterflyProve2
