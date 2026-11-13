/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.KKLpBiased
public import CSLibExtTest.Complexity.BooleanFunctions.KKL.KKLEvents

/-!
# Tests for the `p`-biased KKL interface

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.KKLpBiased`:

* `kpb_flipAll` at small inputs and as an involution;
* `kpb_kkl_reflect` applied to the proved `p = 1/2` case `bph_KKL cro2_rhoOptimise`
  (`KKLHypercontractive (1 - 1/2) 2`), and `kpb_residue_c0`;
* `kpb_PBiasedHC q` is proved here for no `q > 1/2`; for `q ≤ 1/2` it holds because `(1/2, q)` is
  empty. Consequently `kpb_sharpThreshold` and `kpb_sharpThreshold_window` can only be
  instantiated at the degenerate parameter `q = 1/2`, which the test records for the dictator
  event.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability

example : kpb_flipAll (fun x : Bool => x) = fun x => !x := by decide
example : kpb_flipAll (kpb_flipAll (fun x : Bool => x)) = fun x => x := by decide
example (ω : ConfigSpace (Fin 3)) : kpb_flipAll (kpb_flipAll ω) = ω := kpb_flipAll_involutive ω

example : KKLHypercontractive (1 - 1 / 2) 2 := kpb_kkl_reflect (bph_KKL cro2_rhoOptimise)

example : ∀ p ∈ Set.Ioo (1 / 2 : ℝ) 1, KKLHypercontractive p 0 := kpb_residue_c0 le_rfl

/-- `kpb_PBiasedHC q` for `q ≤ 1/2` holds vacuously. -/
lemma kpb_PBiasedHC_of_le_half {q : ℝ} (hq : q ≤ 1 / 2) : kpb_PBiasedHC q :=
  fun _ hp => absurd (hp.1.trans hp.2) (not_lt.mpr hq)

/-- `kpb_PBiasedHC q` for `q > 1/2` contains the KKL inequality with constant `2` at some
`p > 1/2`. -/
example {q : ℝ} (hq : 1 / 2 < q) (H : kpb_PBiasedHC q) :
    ∃ p, 1 / 2 < p ∧ KKLHypercontractive p 2 :=
  ⟨(1 / 2 + q) / 2, by linarith, H _ ⟨by linarith, by linarith⟩⟩

example : 1 / 2 + (2 * 1 * 1) * ((1 / 2 : ℝ) - 1 / 2) ≤ StatMech.prob (1 / 2) dictEvent :=
  kpb_sharpThreshold dictEvent dictEvent_isIncreasing le_rfl zero_le_one zero_le_one
    prob_dictEvent (kpb_PBiasedHC_of_le_half le_rfl) (by simp) (by simp)

example : (1 / 2 : ℝ) - 1 / 2 ≤ (1 / 2 - 1 / 2) / (2 * 1 * 1) :=
  kpb_sharpThreshold_window dictEvent dictEvent_isIncreasing le_rfl (by norm_num)
    prob_dictEvent zero_le_one zero_le_one (kpb_PBiasedHC_of_le_half le_rfl) (by simp) (by simp)
    (by rw [prob_dictEvent]; norm_num)

end StatMechTest.BooleanFunctions
