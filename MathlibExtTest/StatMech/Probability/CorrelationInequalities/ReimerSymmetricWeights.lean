/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.ReimerSymmetricWeights

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.ReimerButterflyProve`

* `wdpairs_symm_le_mul` for the symmetric uniform weight on `Fin 2` and the families
  `famA = {∅, {0}}`, `famB = {∅, {1}}`;
* `wdpairs_symm_compress_invariant` for the same data;
* `wdpairs_not_le_wboxValue_general` (the non-symmetric counterexample).
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerButterflyProve

open _root_.StatMech

/-- The lower family `{∅, {0}}` on `Fin 2`. -/
def famA : Finset (Finset (Fin 2)) := {∅, {0}}

/-- The lower family `{∅, {1}}` on `Fin 2`. -/
def famB : Finset (Finset (Fin 2)) := {∅, {1}}

/-- The uniform coordinate weight. -/
noncomputable def half : Fin 2 → Bool → ℝ := fun _ _ => 1 / 2

-- `wdpairs_symm_le_mul`, symmetric hypothesis discharged.
example : wdpairs half famA famB ≤ fmarg half famA * fmarg half famB :=
  wdpairs_symm_le_mul (fun _ => rfl) famA famB

-- `doubleCompress` preserves the weighted size of `boxDoubled` for a symmetric weight.
example : wboxValue half (doubleCompress 0 (boxDoubled famA famB)) = wdpairs half famA famB :=
  wdpairs_symm_compress_invariant (fun _ => rfl) 0 famA famB

-- Without symmetry the bound fails.
example : ∃ (w : Fin 1 → Bool → ℝ), (∀ x b, 0 ≤ w x b) ∧
    ¬ (wdpairs w ({∅} : Finset (Finset (Fin 1))) {∅}
        ≤ wboxValue w (boxDoubled ({∅} : Finset (Finset (Fin 1))) {∅})) :=
  wdpairs_not_le_wboxValue_general

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerButterflyProve
