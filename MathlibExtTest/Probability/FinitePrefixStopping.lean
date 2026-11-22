/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.FinitePrefixStopping

@[expose] public section

open scoped ENNReal

open MathlibExt.Probability.FinitePrefix

namespace MathlibExtTest.Probability.FinitePrefixStopping

/-! ### Nonvacuity fixtures

Ordinary tokens are `Bool`, so an `Option Bool` step has three
outcomes. All kernels below are constant in the prefix, which makes
the expected masses direct powers; prefix-dependence is not needed to make these numbers
nonvacuous. No test renormalizes: the EOS `= 0` kernel keeps all mass
in survival forever, and the constant `1/4` kernel leaves
`(3/4)^N` un-terminated at every finite horizon `N`. -/

/-- Constant EOS probability `1/4`. At every prefix,
`none` has mass `1/4` and each ordinary `Bool` token has mass `3/8`,
so the total ordinary-token mass per step is `3/4`. -/
noncomputable def constQuarterKernel (_ : List Bool) : PMF (Option Bool) :=
  PMF.ofFintype
    (fun x => if x = Option.none then (1 / 4 : ℝ≥0∞) else (3 / 8 : ℝ≥0∞))
    (by
      rw [Fintype.sum_option, Fintype.sum_bool]
      simp only [Option.some_ne_none, ite_false, ite_true]
      have h1 : ((1/4 : NNReal) : ℝ≥0∞) = (1/4 : ℝ≥0∞) := by
        rw [ENNReal.coe_div (by norm_num)]; simp
      have h2 : ((3/8 : NNReal) : ℝ≥0∞) = (3/8 : ℝ≥0∞) := by
        rw [ENNReal.coe_div (by norm_num)]; simp
      have h3 : ((1 : NNReal) : ℝ≥0∞) = (1 : ℝ≥0∞) := by simp
      rw [← h1, ← h2, ← h3, ← ENNReal.coe_add, ← ENNReal.coe_add]
      norm_cast
      norm_num)

/-- EOS probability `0` at every prefix. -/
noncomputable def zeroEOSKernel (_ : List Bool) : PMF (Option Bool) :=
  PMF.ofFintype
    (fun x => if x = Option.none then (0 : ℝ≥0∞) else (1 / 2 : ℝ≥0∞))
    (by
      rw [Fintype.sum_option, Fintype.sum_bool]
      simp only [Option.some_ne_none, ite_false, ite_true]
      have h1 : ((0 : NNReal) : ℝ≥0∞) = (0 : ℝ≥0∞) := by simp
      have h2 : ((1/2 : NNReal) : ℝ≥0∞) = (1/2 : ℝ≥0∞) := by
        rw [ENNReal.coe_div (by norm_num)]; simp
      have h3 : ((1 : NNReal) : ℝ≥0∞) = (1 : ℝ≥0∞) := by simp
      rw [← h1, ← h2, ← h3, ← ENNReal.coe_add, ← ENNReal.coe_add]
      norm_cast
      norm_num)

/-- EOS probability `1` at every prefix. -/
noncomputable def oneEOSKernel (_ : List Bool) : PMF (Option Bool) :=
  PMF.ofFintype
    (fun x => if x = Option.none then (1 : ℝ≥0∞) else (0 : ℝ≥0∞))
    (by
      rw [Fintype.sum_option, Fintype.sum_bool]
      simp only [Option.some_ne_none, ite_false, ite_true]
      simp)

/-- Empty string under constant EOS `1/4`: terminated mass is
the immediate EOS mass, and survival at horizon `0` is `1`. -/
theorem constQuarter_terminatedMass_nil :
    terminatedMass constQuarterKernel ([] : List Bool)
      = (1 / 4 : ℝ≥0∞) := by
  rw [terminatedMass_nil]
  simp [eosProb, constQuarterKernel]

/-- Empty-string termination at length zero, EOS `1/4`. -/
theorem constQuarter_stopMass_zero :
    stopMass constQuarterKernel 0 = (1 / 4 : ℝ≥0∞) := by
  rw [stopMass_zero]
  simp [eosProb, constQuarterKernel]

/-- EOS `= 0`: the empty string has terminated mass `0`, while
survival through one and two steps stays `1`. -/
theorem zeroEOS_examples :
    terminatedMass zeroEOSKernel ([] : List Bool) = 0
      ∧ survivalMass zeroEOSKernel 1 = 1
      ∧ survivalMass zeroEOSKernel 2 = 1
      ∧ stopMass zeroEOSKernel 0 = 0
      ∧ stopMass zeroEOSKernel 1 = 0 := by
  have hterm : terminatedMass zeroEOSKernel ([] : List Bool) = 0 := by
    rw [terminatedMass_nil]
    simp [eosProb, zeroEOSKernel]
  have hsurv1 : survivalMass zeroEOSKernel 1 = 1 := by
    have h1 : ((1/2 : NNReal) : ℝ≥0∞) = (1/2 : ℝ≥0∞) := by
      rw [ENNReal.coe_div (by norm_num)]; simp
    have h3 : ((1 : NNReal) : ℝ≥0∞) = (1 : ℝ≥0∞) := by simp
    calc survivalMass zeroEOSKernel 1
        = ∑ a : Bool, ((1/2 : ℝ≥0∞) * 1) := by
          simp [survivalMass_succ, survivalMass_zero, zeroEOSKernel]
      _ = (1/2 : ℝ≥0∞) + (1/2 : ℝ≥0∞) := by
          rw [Fintype.sum_bool]; simp [mul_one]
      _ = 1 := by
          rw [← h1, ← h3, ← ENNReal.coe_add]
          norm_cast
          norm_num
  have hsurv2 : survivalMass zeroEOSKernel 2 = 1 := by
    have hshift : ∀ a : Bool, (fun p : List Bool => zeroEOSKernel (a :: p))
        = zeroEOSKernel := fun _ => rfl
    have h1 : ((1/2 : NNReal) : ℝ≥0∞) = (1/2 : ℝ≥0∞) := by
      rw [ENNReal.coe_div (by norm_num)]; simp
    have h3 : ((1 : NNReal) : ℝ≥0∞) = (1 : ℝ≥0∞) := by simp
    calc survivalMass zeroEOSKernel 2
        = ∑ a : Bool, ((1/2 : ℝ≥0∞) * 1) := by
          rw [survivalMass_succ 1]
          apply Finset.sum_congr rfl
          intro a _
          have hs : survivalMass (fun p => zeroEOSKernel (a :: p)) 1 = 1 := by
            rw [hshift a]; exact hsurv1
          rw [hs]
          simp [zeroEOSKernel]
      _ = (1/2 : ℝ≥0∞) + (1/2 : ℝ≥0∞) := by
          rw [Fintype.sum_bool]; simp [mul_one]
      _ = 1 := by
          rw [← h1, ← h3, ← ENNReal.coe_add]
          norm_cast
          norm_num
  have hstop0 : stopMass zeroEOSKernel 0 = 0 := by
    rw [stopMass_zero]
    simp [eosProb, zeroEOSKernel]
  have hstop1 : stopMass zeroEOSKernel 1 = 0 := by
    rw [stopMass_succ 0]
    simp [stopMass_zero, eosProb, zeroEOSKernel]
  exact ⟨hterm, hsurv1, hsurv2, hstop0, hstop1⟩

/-- EOS `= 1`: the empty string carries all mass, termination at
length zero is `1`, and survival past the first step is `0`. -/
theorem oneEOS_examples :
    terminatedMass oneEOSKernel ([] : List Bool) = 1
      ∧ stopMass oneEOSKernel 0 = 1
      ∧ stopMass oneEOSKernel 1 = 0
      ∧ survivalMass oneEOSKernel 1 = 0
      ∧ survivalMass oneEOSKernel 2 = 0 := by
  have hterm : terminatedMass oneEOSKernel ([] : List Bool) = 1 := by
    rw [terminatedMass_nil]
    simp [eosProb, oneEOSKernel]
  have hstop0 : stopMass oneEOSKernel 0 = 1 := by
    rw [stopMass_zero]
    simp [eosProb, oneEOSKernel]
  have hstop1 : stopMass oneEOSKernel 1 = 0 := by
    rw [stopMass_succ 0]
    simp [oneEOSKernel]
  have hsurv1 : survivalMass oneEOSKernel 1 = 0 := by
    simp [survivalMass_succ, survivalMass_zero, oneEOSKernel]
  have hsurv2 : survivalMass oneEOSKernel 2 = 0 := by
    rw [survivalMass_succ 1]
    simp [oneEOSKernel]
  exact ⟨hterm, hstop0, hstop1, hsurv1, hsurv2⟩

/-- Constant EOS `1/4` survival values required by the leaf:
`1, 3/4, 9/16, 27/64` at horizons `0, 1, 2, 3`. -/
theorem constQuarter_survival_values :
    survivalMass constQuarterKernel 0 = 1
      ∧ survivalMass constQuarterKernel 1 = (3 / 4 : ℝ≥0∞)
      ∧ survivalMass constQuarterKernel 2 = (9 / 16 : ℝ≥0∞)
      ∧ survivalMass constQuarterKernel 3 = (27 / 64 : ℝ≥0∞) := by
  have hshift : ∀ a : Bool, (fun p : List Bool => constQuarterKernel (a :: p))
      = constQuarterKernel := fun _ => rfl
  have hs0 : survivalMass constQuarterKernel 0 = 1 := survivalMass_zero _
  have hs1 : survivalMass constQuarterKernel 1 = (3 / 4 : ℝ≥0∞) := by
    have h38 : ((3/8 : NNReal) : ℝ≥0∞) = (3/8 : ℝ≥0∞) := by
      rw [ENNReal.coe_div (by norm_num)]; simp
    have h34 : ((3/4 : NNReal) : ℝ≥0∞) = (3/4 : ℝ≥0∞) := by
      rw [ENNReal.coe_div (by norm_num)]; simp
    calc survivalMass constQuarterKernel 1
        = (3/8 : ℝ≥0∞) + (3/8 : ℝ≥0∞) := by
          rw [survivalMass_succ 0, Fintype.sum_bool]
          simp [survivalMass_zero, constQuarterKernel, mul_one]
      _ = (3/4 : ℝ≥0∞) := by
          rw [← h38, ← h34, ← ENNReal.coe_add]
          norm_cast
          norm_num
  have hs2 : survivalMass constQuarterKernel 2 = (9 / 16 : ℝ≥0∞) := by
    have h38 : ((3/8 : NNReal) : ℝ≥0∞) = (3/8 : ℝ≥0∞) := by
      rw [ENNReal.coe_div (by norm_num)]; simp
    have h34 : ((3/4 : NNReal) : ℝ≥0∞) = (3/4 : ℝ≥0∞) := by
      rw [ENNReal.coe_div (by norm_num)]; simp
    have h916 : ((9/16 : NNReal) : ℝ≥0∞) = (9/16 : ℝ≥0∞) := by
      rw [ENNReal.coe_div (by norm_num)]; simp
    calc survivalMass constQuarterKernel 2
        = ((3/8 : ℝ≥0∞) * (3/4 : ℝ≥0∞))
          + ((3/8 : ℝ≥0∞) * (3/4 : ℝ≥0∞)) := by
          rw [survivalMass_succ 1, Fintype.sum_bool]
          have e1 : survivalMass (fun p => constQuarterKernel (true :: p)) 1
              = (3/4 : ℝ≥0∞) := by rw [hshift true]; exact hs1
          have e2 : survivalMass (fun p => constQuarterKernel (false :: p)) 1
              = (3/4 : ℝ≥0∞) := by rw [hshift false]; exact hs1
          rw [e1, e2]
          simp [constQuarterKernel]
      _ = (9/16 : ℝ≥0∞) := by
          rw [← h38, ← h34, ← h916, ← ENNReal.coe_mul, ← ENNReal.coe_add]
          norm_cast
          norm_num
  have hs3 : survivalMass constQuarterKernel 3 = (27 / 64 : ℝ≥0∞) := by
    have h38 : ((3/8 : NNReal) : ℝ≥0∞) = (3/8 : ℝ≥0∞) := by
      rw [ENNReal.coe_div (by norm_num)]; simp
    have h916 : ((9/16 : NNReal) : ℝ≥0∞) = (9/16 : ℝ≥0∞) := by
      rw [ENNReal.coe_div (by norm_num)]; simp
    have h2764 : ((27/64 : NNReal) : ℝ≥0∞) = (27/64 : ℝ≥0∞) := by
      rw [ENNReal.coe_div (by norm_num)]; simp
    calc survivalMass constQuarterKernel 3
        = ((3/8 : ℝ≥0∞) * (9/16 : ℝ≥0∞))
          + ((3/8 : ℝ≥0∞) * (9/16 : ℝ≥0∞)) := by
          rw [survivalMass_succ 2, Fintype.sum_bool]
          have e1 : survivalMass (fun p => constQuarterKernel (true :: p)) 2
              = (9/16 : ℝ≥0∞) := by rw [hshift true]; exact hs2
          have e2 : survivalMass (fun p => constQuarterKernel (false :: p)) 2
              = (9/16 : ℝ≥0∞) := by rw [hshift false]; exact hs2
          rw [e1, e2]
          simp [constQuarterKernel]
      _ = (27/64 : ℝ≥0∞) := by
          rw [← h38, ← h916, ← h2764, ← ENNReal.coe_mul, ← ENNReal.coe_add]
          norm_cast
          norm_num
  exact ⟨hs0, hs1, hs2, hs3⟩

/-- Constant EOS `1/4` termination masses at lengths `0, 1, 2`:
each is the survival mass at that length times `1/4`. -/
theorem constQuarter_stopMass_values :
    stopMass constQuarterKernel 0 = (1 / 4 : ℝ≥0∞)
      ∧ stopMass constQuarterKernel 1 = (3 / 16 : ℝ≥0∞)
      ∧ stopMass constQuarterKernel 2 = (9 / 64 : ℝ≥0∞) := by
  have hshift : ∀ a : Bool, (fun p : List Bool => constQuarterKernel (a :: p))
      = constQuarterKernel := fun _ => rfl
  have ht0 : stopMass constQuarterKernel 0 = (1 / 4 : ℝ≥0∞) :=
    constQuarter_stopMass_zero
  have ht1 : stopMass constQuarterKernel 1 = (3 / 16 : ℝ≥0∞) := by
    have h38 : ((3/8 : NNReal) : ℝ≥0∞) = (3/8 : ℝ≥0∞) := by
      rw [ENNReal.coe_div (by norm_num)]; simp
    have h14 : ((1/4 : NNReal) : ℝ≥0∞) = (1/4 : ℝ≥0∞) := by
      rw [ENNReal.coe_div (by norm_num)]; simp
    have h316 : ((3/16 : NNReal) : ℝ≥0∞) = (3/16 : ℝ≥0∞) := by
      rw [ENNReal.coe_div (by norm_num)]; simp
    calc stopMass constQuarterKernel 1
        = ((3/8 : ℝ≥0∞) * (1/4 : ℝ≥0∞))
          + ((3/8 : ℝ≥0∞) * (1/4 : ℝ≥0∞)) := by
          rw [stopMass_succ 0, Fintype.sum_bool]
          have e1 : stopMass (fun p => constQuarterKernel (true :: p)) 0
              = (1/4 : ℝ≥0∞) := by rw [hshift true]; exact ht0
          have e2 : stopMass (fun p => constQuarterKernel (false :: p)) 0
              = (1/4 : ℝ≥0∞) := by rw [hshift false]; exact ht0
          rw [e1, e2]
          simp [constQuarterKernel]
      _ = (3/16 : ℝ≥0∞) := by
          rw [← h38, ← h14, ← h316, ← ENNReal.coe_mul, ← ENNReal.coe_add]
          norm_cast
          norm_num
  have ht2 : stopMass constQuarterKernel 2 = (9 / 64 : ℝ≥0∞) := by
    have h38 : ((3/8 : NNReal) : ℝ≥0∞) = (3/8 : ℝ≥0∞) := by
      rw [ENNReal.coe_div (by norm_num)]; simp
    have h316 : ((3/16 : NNReal) : ℝ≥0∞) = (3/16 : ℝ≥0∞) := by
      rw [ENNReal.coe_div (by norm_num)]; simp
    have h964 : ((9/64 : NNReal) : ℝ≥0∞) = (9/64 : ℝ≥0∞) := by
      rw [ENNReal.coe_div (by norm_num)]; simp
    calc stopMass constQuarterKernel 2
        = ((3/8 : ℝ≥0∞) * (3/16 : ℝ≥0∞))
          + ((3/8 : ℝ≥0∞) * (3/16 : ℝ≥0∞)) := by
          rw [stopMass_succ 1, Fintype.sum_bool]
          have e1 : stopMass (fun p => constQuarterKernel (true :: p)) 1
              = (3/16 : ℝ≥0∞) := by rw [hshift true]; exact ht1
          have e2 : stopMass (fun p => constQuarterKernel (false :: p)) 1
              = (3/16 : ℝ≥0∞) := by rw [hshift false]; exact ht1
          rw [e1, e2]
          simp [constQuarterKernel]
      _ = (9/64 : ℝ≥0∞) := by
          rw [← h38, ← h316, ← h964, ← ENNReal.coe_mul, ← ENNReal.coe_add]
          norm_cast
          norm_num
  exact ⟨ht0, ht1, ht2⟩

/-- Constant EOS `1/4`, one concrete terminated word:
`[true]` has ordinary mass `3/8` followed by final EOS `1/4`. -/
theorem constQuarter_terminatedMass_singleton :
    terminatedMass constQuarterKernel ([true] : List Bool)
      = (3 / 32 : ℝ≥0∞) := by
  have hshift : (fun p : List Bool => constQuarterKernel (true :: p))
      = constQuarterKernel := rfl
  have h38 : ((3/8 : NNReal) : ℝ≥0∞) = (3/8 : ℝ≥0∞) := by
    rw [ENNReal.coe_div (by norm_num)]; simp
  have h14 : ((1/4 : NNReal) : ℝ≥0∞) = (1/4 : ℝ≥0∞) := by
    rw [ENNReal.coe_div (by norm_num)]; simp
  have h332 : ((3/32 : NNReal) : ℝ≥0∞) = (3/32 : ℝ≥0∞) := by
    rw [ENNReal.coe_div (by norm_num)]; simp
  calc terminatedMass constQuarterKernel ([true] : List Bool)
      = (3/8 : ℝ≥0∞) * (1/4 : ℝ≥0∞) := by
        rw [terminatedMass_cons]
        have e : terminatedMass (fun p => constQuarterKernel (true :: p)) []
            = (1/4 : ℝ≥0∞) := by
          rw [hshift]; exact constQuarter_terminatedMass_nil
        rw [e]
        simp [constQuarterKernel]
    _ = (3/32 : ℝ≥0∞) := by
        rw [← h38, ← h14, ← h332, ← ENNReal.coe_mul]
        norm_cast
        norm_num

/-- Partial balance made concrete at horizon `3` for constant
EOS `1/4`: `1/4 + 3/16 + 9/64 + 27/64 = 1`, with no renormalization. -/
theorem constQuarter_partial_balance_three :
    Finset.sum (Finset.range 3) (fun k => stopMass constQuarterKernel k)
      + survivalMass constQuarterKernel 3 = 1 := by
  exact partial_mass_balance constQuarterKernel 3


end MathlibExtTest.Probability.FinitePrefixStopping
