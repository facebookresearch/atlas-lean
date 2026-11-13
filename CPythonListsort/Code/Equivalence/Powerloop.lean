/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Transcription.Powerloop
import Mathlib

/-!
# `powerloop` recurrence equivalence

This file projects the reviewed 64-bit transcription to a recurrence over
arbitrary-precision natural numbers.  The explicit safety trace records the
signed-comparison and shift-representability obligations inherited from C.
-/

namespace CPythonListsort

/-- Arbitrary-precision observable state corresponding to `PowerloopState`. -/
structure PowerloopNatState where
  result : Nat
  a : Nat
  b : Nat
  stopped : Bool
  deriving DecidableEq, Repr

/-- Forget the 64-bit representation and retain the unsigned values. -/
def PowerloopState.toNatState (state : PowerloopState) : PowerloopNatState :=
  { result := state.result
    a := state.a.toNat
    b := state.b.toNat
    stopped := state.stopped }

/-- The quotient-bit recurrence from `listsort.txt`, over mathematical naturals. -/
def powerloopNatStep (n : Nat) (state : PowerloopNatState) : PowerloopNatState :=
  if state.stopped then
    state
  else
    let state := { state with result := state.result + 1 }
    let state :=
      if n ≤ state.a then
        { state with a := state.a - n, b := state.b - n }
      else if n ≤ state.b then
        { state with stopped := true }
      else
        state
    if state.stopped then
      state
    else
      { state with a := 2 * state.a, b := 2 * state.b }

/-- Iterate the arbitrary-precision recurrence with the same stopping convention. -/
def powerloopNatLoop : Nat → Nat → PowerloopNatState → PowerloopNatState
  | 0, _, state => state
  | fuel + 1, n, state =>
      if state.stopped then state else powerloopNatLoop fuel n (powerloopNatStep n state)

/-- Premises needed to project one finite-width loop step exactly. -/
def PowerloopStepSafe (n : PySSize) (state : PowerloopState) : Prop :=
  n.Nonnegative ∧
    state.a.Nonnegative ∧
    state.b.Nonnegative ∧
    state.a.toNat ≤ state.b.toNat ∧
    2 * state.a.toNat < 2 ^ 63 ∧
    2 * state.b.toNat < 2 ^ 63

/-- Safety evidence for every non-stopped state visited by a bounded loop. -/
def PowerloopTraceSafe : Nat → PySSize → PowerloopState → Prop
  | 0, _, _ => True
  | fuel + 1, n, state =>
      if state.stopped then True
      else PowerloopStepSafe n state ∧ PowerloopTraceSafe fuel n (powerloopStep n state)

private theorem slt_eq_nat_lt (x y : PySSize)
    (hx : x.Nonnegative) (hy : y.Nonnegative) :
    x.slt y = decide (x.toNat < y.toNat) := by
  rw [BitVec.slt_eq_decide]
  rw [BitVec.toInt_eq_toNat_of_msb hx]
  rw [BitVec.toInt_eq_toNat_of_msb hy]
  norm_cast

private theorem toNat_shiftLeft_one (x : PySSize)
    (hfit : 2 * x.toNat < 2 ^ 63) :
    (x <<< 1).toNat = 2 * x.toNat := by
  rw [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  norm_num
  rw [Nat.mod_eq_of_lt]
  · omega
  · omega

private theorem toNat_two_mul_add (x y : PySSize)
    (hfit : 2 * x.toNat + y.toNat < 2 ^ 63) :
    (2 * x + y).toNat = 2 * x.toNat + y.toNat := by
  have htwo : (2 : PySSize).toNat = 2 := by decide
  have hmul : ((2 : PySSize) * x).toNat = 2 * x.toNat := by
    apply BitVec.toNat_mul_of_lt
    rw [htwo]
    norm_num at hfit ⊢
    omega
  calc
    (2 * x + y).toNat = (2 * x).toNat + y.toNat :=
      BitVec.toNat_add_of_lt (by rw [hmul]; norm_num at hfit ⊢; omega)
    _ = 2 * x.toNat + y.toNat := by rw [hmul]

/-- One transcribed step is exactly the natural-number quotient-bit step. -/
theorem powerloopStep_eq_spec (n : PySSize) (state : PowerloopState)
    (hsafe : PowerloopStepSafe n state) :
    (powerloopStep n state).toNatState =
      powerloopNatStep n.toNat state.toNatState := by
  rcases hsafe with ⟨hn, haNonnegative, hbNonnegative, hab, haFit, hbFit⟩
  have haCmp := slt_eq_nat_lt state.a n haNonnegative hn
  have hbCmp := slt_eq_nat_lt state.b n hbNonnegative hn
  cases hstopped : state.stopped with
  | true =>
      simp [powerloopStep, powerloopNatStep, PowerloopState.toNatState, hstopped]
  | false =>
      by_cases hna : n.toNat ≤ state.a.toNat
      · have hnb : n.toNat ≤ state.b.toNat := le_trans hna hab
        have hnaBits : n ≤ state.a := by simpa [BitVec.le_def] using hna
        have hnbBits : n ≤ state.b := by simpa [BitVec.le_def] using hnb
        have haSubFit : 2 * (state.a - n).toNat < 2 ^ 63 := by
          rw [BitVec.toNat_sub_of_le hnaBits]
          omega
        have hbSubFit : 2 * (state.b - n).toNat < 2 ^ 63 := by
          rw [BitVec.toNat_sub_of_le hnbBits]
          omega
        simp [powerloopStep, powerloopNatStep, PowerloopState.toNatState,
          hstopped, haCmp, hna, BitVec.toNat_sub_of_le hnaBits,
          BitVec.toNat_sub_of_le hnbBits,
          toNat_shiftLeft_one (state.a - n) haSubFit,
          toNat_shiftLeft_one (state.b - n) hbSubFit]
      · by_cases hnb : n.toNat ≤ state.b.toNat
        · simp [powerloopStep, powerloopNatStep, PowerloopState.toNatState,
            hstopped, haCmp, hbCmp, hna, hnb]
        · simp [powerloopStep, powerloopNatStep, PowerloopState.toNatState,
            hstopped, haCmp, hbCmp, hna, hnb,
            toNat_shiftLeft_one state.a haFit,
            toNat_shiftLeft_one state.b hbFit]

/-- The step equivalence lifts through any safely traced finite loop. -/
theorem powerloopLoop_eq_spec (fuel : Nat) (n : PySSize) (state : PowerloopState)
    (hsafe : PowerloopTraceSafe fuel n state) :
    (powerloopLoop fuel n state).toNatState =
      powerloopNatLoop fuel n.toNat state.toNatState := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases hstopped : state.stopped with
      | true =>
          simp [powerloopLoop, powerloopNatLoop, PowerloopState.toNatState, hstopped]
      | false =>
          have hsafePair :
              PowerloopStepSafe n state ∧
                PowerloopTraceSafe fuel n (powerloopStep n state) := by
            simpa [PowerloopTraceSafe, hstopped] using hsafe
          have hsafeStep : PowerloopStepSafe n state := by
            exact hsafePair.1
          have hsafeTail : PowerloopTraceSafe fuel n (powerloopStep n state) := by
            exact hsafePair.2
          simp only [powerloopLoop, powerloopNatLoop, hstopped, Bool.false_eq_true,
            if_false]
          rw [ih (powerloopStep n state) hsafeTail]
          rw [powerloopStep_eq_spec n state hsafeStep]
          simp [PowerloopState.toNatState, hstopped]

/-- Natural-number specification initialized from the exact doubled midpoints. -/
def powerloopNatSpec (s1 n1 n2 n : PySSize) : PowerloopNatState :=
  let a := 2 * s1.toNat + n1.toNat
  let b := a + n1.toNat + n2.toNat
  powerloopNatLoop 64 n.toNat
    { result := 0, a := a, b := b, stopped := false }

/-- The zero-based quotient bit inspected by the natural-number recurrence. -/
def powerloopQuotientBit (a n k : Nat) : Nat :=
  ((2 ^ k * a) / n) % 2

/-- `k` is the first zero-based quotient-bit position at which `a / n` and `b / n` differ. -/
def IsFirstDifferingQuotientBit (a b n k : Nat) : Prop :=
  powerloopQuotientBit a n k = 0 ∧
    powerloopQuotientBit b n k = 1 ∧
    ∀ j < k, powerloopQuotientBit a n j = powerloopQuotientBit b n j

/-- The complete transcription agrees with the exact natural recurrence when initialization is
signed-representable and every visited shift remains signed-representable. -/
theorem powerloopTraced_eq_spec (s1 n1 n2 n : PySSize)
    (haInit : 2 * s1.toNat + n1.toNat < 2 ^ 63)
    (hbInit : 2 * s1.toNat + n1.toNat + n1.toNat + n2.toNat < 2 ^ 63)
    (hsafe :
      let a := 2 * s1 + n1
      let b := a + n1 + n2
      PowerloopTraceSafe 64 n { result := 0, a := a, b := b, stopped := false }) :
    (powerloopTraced s1 n1 n2 n).toNatState = powerloopNatSpec s1 n1 n2 n := by
  have haNat : (2 * s1 + n1).toNat = 2 * s1.toNat + n1.toNat :=
    toNat_two_mul_add s1 n1 haInit
  have habNat : ((2 * s1 + n1) + n1).toNat =
      2 * s1.toNat + n1.toNat + n1.toNat := by
    calc
      ((2 * s1 + n1) + n1).toNat = (2 * s1 + n1).toNat + n1.toNat :=
        BitVec.toNat_add_of_lt (by rw [haNat]; norm_num at hbInit ⊢; omega)
      _ = 2 * s1.toNat + n1.toNat + n1.toNat := by rw [haNat]
  have hbNat : ((2 * s1 + n1) + n1 + n2).toNat =
      2 * s1.toNat + n1.toNat + n1.toNat + n2.toNat := by
    calc
      ((2 * s1 + n1) + n1 + n2).toNat =
          ((2 * s1 + n1) + n1).toNat + n2.toNat :=
        BitVec.toNat_add_of_lt (by rw [habNat]; norm_num at hbInit ⊢; omega)
      _ = 2 * s1.toNat + n1.toNat + n1.toNat + n2.toNat := by rw [habNat]
  unfold powerloopTraced powerloopNatSpec
  rw [powerloopLoop_eq_spec 64 n _ hsafe]
  simp only [PowerloopState.toNatState]
  rw [haNat, hbNat]

end CPythonListsort
