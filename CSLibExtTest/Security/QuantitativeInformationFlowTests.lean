/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Security.QuantitativeInformationFlow
public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import MathlibExt.Probability.ProbabilityMassFunction.Uniform

open scoped BigOperators

namespace Cslib.Security.QuantitativeInformationFlow.Tests

/-!
# Min-entropy leakage tests

Ground instances of the leakage bounds on two-point types.
-/

/-- T1: vulnerability of the two-point uniform prior is one half. -/
public theorem test_uniform_two_vulnerability :
  vulnerability (PMF.uniformFintype Bool) = 1 / 2 := by
  rw [vulnerability_uniformFintype, Fintype.card_bool]
  norm_num

/-- T2: the identity channel on two points has posterior one. -/
public theorem test_identity_posterior :
  posteriorVulnerability (PMF.uniformFintype Bool) (fun x => PMF.pure x) =
  1 := by
  rw [posterior_det_uniform]
  have himg : Finset.card (Finset.image (fun x : Bool => x)
    Finset.univ) = 2 := by
    decide
  rw [himg, Fintype.card_bool]
  norm_num

/-- T3: a constant channel on two points leaks nothing. -/
public theorem test_const_leakage_zero :
  minEntropyLeakage (PMF.uniformFintype Bool) (fun _ : Bool => PMF.pure true) = 0 := by
  have hv : 0 < vulnerability (PMF.uniformFintype Bool) := by
    rw [test_uniform_two_vulnerability]
    norm_num
  exact leakage_const_channel (PMF.uniformFintype Bool) (fun _ : Bool =>
    PMF.pure true) true (fun x => rfl) hv

/-- T4: the range of the constant-`true` map has one element. -/
public theorem test_range_card :
  Finset.card (Finset.image (fun _ : Bool => true) Finset.univ) =
  1 := by
  decide

/-- T4: a non-surjective deterministic channel leaks `log2 1 = 0`. -/
public theorem test_nonsurjective_leakage :
  minEntropyLeakage (PMF.uniformFintype Bool) (fun _ : Bool => PMF.pure true) = 0 := by
  rw [leakage_det_uniform, test_range_card]
  simp

/-- T5: the Q4 bound on the two-point identity channel. -/
public theorem test_posterior_le_numeric :
  posteriorVulnerability (PMF.uniformFintype Bool) (fun x => PMF.pure x) ≤
  (Fintype.card Bool : Real) * vulnerability (PMF.uniformFintype Bool) :=
  posterior_le_card_mul _ _

-- T6: axiom check for the main theorems.
#print axioms posterior_le_card_mul
#print axioms leakage_le_log_card
#print axioms leakage_det_uniform
#print axioms posterior_const_channel
#print axioms leakage_const_channel

end Cslib.Security.QuantitativeInformationFlow.Tests
