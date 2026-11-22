/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Matrix.Freivalds.Counting
public import Cslib.Probability.PMF
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Basic.ENNReal.Inv
import Mathlib.Tactic

set_option autoImplicit false

open scoped ENNReal

@[expose] public section

namespace Cslib.Algorithms.Lean.Matrix

/-- Uniform complete binary seeds, mapped through the actual charged trial.
This law supplies no PRNG implementation or assumed error oracle. -/
noncomputable def freivaldsTrialLaw {n : Nat}
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) n) n) : PMF Bool :=
  (Cslib.Probability.PMF.uniformOfFintype (Fin n → ZMod 2)).map
    fun r => (freivaldsTrial A B C r).ret

/-- Each complete binary assignment has its exact uniform point mass. -/
theorem freivaldsSeed_pointMass {n : Nat} (r : Fin n → ZMod 2) :
    Cslib.Probability.PMF.uniformOfFintype (Fin n → ZMod 2) r = ((2 : ℝ≥0∞) ^ n)⁻¹ := by
  simp [Cslib.Probability.PMF.uniformOfFintype_apply]

/-- Acceptance is the canonical uniform mass of seeds accepted by the actual
executor. Canonical outer-measure pushforward supplies the fiber count. -/
theorem freivaldsTrialLaw_acceptance {n : Nat}
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) n) n) :
    freivaldsTrialLaw A B C true =
      (Fintype.card {r : Fin n → ZMod 2 // (freivaldsTrial A B C r).ret = true} : ℝ≥0∞) /
        Fintype.card (Fin n → ZMod 2) := by
  classical
  calc
    freivaldsTrialLaw A B C true = (freivaldsTrialLaw A B C).toOuterMeasure {true} :=
      (PMF.toOuterMeasure_apply_singleton (freivaldsTrialLaw A B C) true).symm
    _ = (Cslib.Probability.PMF.uniformOfFintype (Fin n → ZMod 2)).toOuterMeasure
        {r | (freivaldsTrial A B C r).ret = true} := by
      rw [freivaldsTrialLaw, PMF.toOuterMeasure_map_apply]
      rfl
    _ = _ := by
      rw [PMF.toOuterMeasure_apply, tsum_fintype]
      simp only [Set.indicator_apply, Set.mem_ofPred_eq,
        Cslib.Probability.PMF.uniformOfFintype_apply]
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul]
      rw [← Fintype.card_subtype]
      rfl

/-- A correct product has acceptance probability one under the same actual
trial law, including empty matrices. -/
theorem freivaldsTrialLaw_complete {n : Nat}
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) n) n)
    (correct : freivaldsMatrix A * freivaldsMatrix B = freivaldsMatrix C) :
    freivaldsTrialLaw A B C true = 1 := by
  classical
  rw [freivaldsTrialLaw_acceptance]
  have accepted :
      Fintype.card {r : Fin n → ZMod 2 // (freivaldsTrial A B C r).ret = true} =
        Fintype.card (Fin n → ZMod 2) := by
    simpa only [Finset.card_univ] using
      Fintype.card_of_subtype (Finset.univ : Finset (Fin n → ZMod 2))
        (fun r => ⟨fun _ => freivaldsTrial_complete A B C correct r,
          fun _ => Finset.mem_univ r⟩)
  rw [accepted]
  exact ENNReal.div_self
    (by exact_mod_cast (Fintype.card_ne_zero (α := Fin n → ZMod 2))) (by simp)

/-- An incorrect product is accepted with probability at most one half.
The bound follows from the executor's finite seed pairing. -/
theorem freivaldsTrialLaw_sound {n : Nat}
    (A B C : _root_.Vector (_root_.Vector (ZMod 2) n) n)
    (wrong : freivaldsMatrix A * freivaldsMatrix B ≠ freivaldsMatrix C) :
    freivaldsTrialLaw A B C true ≤ (1 / 2 : ℝ≥0∞) := by
  rw [freivaldsTrialLaw_acceptance]
  have count := freivaldsTrial_acceptanceCard_bound A B C wrong
  have scaled :
      (Fintype.card {r : Fin n → ZMod 2 // (freivaldsTrial A B C r).ret = true} : ℝ≥0∞) * 2 ≤
        Fintype.card (Fin n → ZMod 2) := by
    exact_mod_cast (show
      Fintype.card {r : Fin n → ZMod 2 // (freivaldsTrial A B C r).ret = true} * 2 ≤
        Fintype.card (Fin n → ZMod 2) by simpa [mul_comm] using count)
  have nonzero : (Fintype.card (Fin n → ZMod 2) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero (α := Fin n → ZMod 2))
  have finite : (Fintype.card (Fin n → ZMod 2) : ℝ≥0∞) ≠ ∞ := by simp
  apply (ENNReal.div_le_iff nonzero finite).mpr
  have half :
      (Fintype.card {r : Fin n → ZMod 2 // (freivaldsTrial A B C r).ret = true} : ℝ≥0∞) ≤
        (Fintype.card (Fin n → ZMod 2) : ℝ≥0∞) / 2 :=
    (ENNReal.le_div_iff_mul_le (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)).mpr scaled
  simpa [div_eq_mul_inv, mul_comm] using half

end Cslib.Algorithms.Lean.Matrix
