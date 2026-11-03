/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.CorrelationInequalities.ReimerWeightedPairs

/-!
# Tests for `MathlibExt.Probability.CorrelationInequalities.ReimerButterflyClose`

* `fwt`, `fmarg`, `wdpairs` computed for the uniform weight `1/2` on `Fin 2` and the families
  `famA = {∅, {0}}`, `famB = {∅, {1}}` (`fwt = 1/4`, `fmarg = 1/2`, `wdpairs = 1/4`);
* `wdpairs_le_mul` instantiated (`1/4 ≤ 1/2 * 1/2`);
* `rby_separate_compression_strictly_decreases` and the counterexample families.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerButterflyClose

open _root_.StatMech

/-- The lower family `{∅, {0}}` on `Fin 2`. -/
def famA : Finset (Finset (Fin 2)) := {∅, {0}}

/-- The lower family `{∅, {1}}` on `Fin 2`. -/
def famB : Finset (Finset (Fin 2)) := {∅, {1}}

/-- The uniform coordinate weight. -/
noncomputable def half : Fin 2 → Bool → ℝ := fun _ _ => 1 / 2

-- `fwt half S = 1/4` for every `S`.
theorem fwt_half (S : Finset (Fin 2)) : fwt half S = 1 / 4 := by
  simp only [fwt, half, Fin.prod_univ_two]
  norm_num

-- `fmarg half famA = 1/2`.
theorem fmarg_famA : fmarg half famA = 1 / 2 := by
  simp only [fmarg, famA, fwt_half]
  rw [Finset.sum_const, Finset.card_insert_of_notMem (by decide), Finset.card_singleton]
  norm_num

-- `wdpairs half famA famB = 1/4`: four disjoint pairs, each of weight `1/16`.
theorem wdpairs_famA_famB : wdpairs half famA famB = 1 / 4 := by
  simp only [wdpairs, fwt_half]
  rw [Finset.sum_const, show ((famA ×ˢ famB).filter (fun p => Disjoint p.1 p.2)).card = 4 by
    decide]
  norm_num

-- `wdpairs_le_mul` instantiated and evaluated: `1/4 ≤ 1/2 * 1/2`.
example : wdpairs half famA famB ≤ fmarg half famA * fmarg half famB :=
  wdpairs_le_mul (fun _ _ => by norm_num [half]) famA famB

-- Separate compressions of the two families can decrease the number of disjoint pairs.
example : ∃ (𝒜 ℬ : Finset (Finset (Fin 2))) (i : Fin 2),
    (boxDoubled (Down.compression i 𝒜) (UV.compression ({i} : Finset (Fin 2)) ∅ ℬ)).card
      < (boxDoubled 𝒜 ℬ).card :=
  rby_separate_compression_strictly_decreases

-- The counterexample families.
example : rbyCexA.card = 2 ∧ rbyCexB.card = 1 := by decide

end MathlibExtTest.StatMech.Probability.CorrelationInequalities.ReimerButterflyClose
