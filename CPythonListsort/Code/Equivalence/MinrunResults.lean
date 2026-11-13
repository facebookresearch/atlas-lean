/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Equivalence.Minrun
import Code.Equivalence.PowerloopResults
import Mathlib

/-!
# Adaptive-minrun sequence results

This file proves the least-exponent characterization and the full-cycle
quotient/remainder properties of CPython's adaptive minrun generator.
-/

namespace CPythonListsort

/-- A bounded exponent search returns the least successful exponent whenever a witness lies
inside its fuel window. -/
theorem minrunExponentSpecLoop_characterization (fuel listSize exponent : Nat)
    (hwitness : ∃ d < fuel, listSize / 2 ^ (exponent + d) < 64) :
    let out := minrunExponentSpecLoop fuel listSize exponent
    out.2 = true ∧
      out.1 < exponent + fuel ∧
      listSize / 2 ^ out.1 < 64 ∧
      ∀ j, exponent ≤ j → j < out.1 → 64 ≤ listSize / 2 ^ j := by
  induction fuel generalizing exponent with
  | zero =>
      rcases hwitness with ⟨d, hd, _⟩
      omega
  | succ fuel ih =>
      simp only [minrunExponentSpecLoop]
      by_cases hcurrent : listSize >>> exponent < 64
      · rw [if_pos hcurrent]
        constructor
        · rfl
        constructor
        · omega
        constructor
        · simpa [Nat.shiftRight_eq_div_pow] using hcurrent
        · intro j _ hj
          omega
      · rw [if_neg hcurrent]
        have hcurrentDiv : 64 ≤ listSize / 2 ^ exponent := by
          rw [Nat.shiftRight_eq_div_pow] at hcurrent
          omega
        rcases hwitness with ⟨d, hdFuel, hd⟩
        have hdPos : 0 < d := by
          by_contra hnot
          have hdZero : d = 0 := by omega
          subst d
          simp only [Nat.add_zero] at hd
          omega
        obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : d ≠ 0)
        have htailWitness : ∃ d' < fuel,
            listSize / 2 ^ (exponent + 1 + d') < 64 := by
          refine ⟨d, by omega, ?_⟩
          have heq : exponent + d.succ = exponent + 1 + d := by omega
          rwa [heq] at hd
        have htail := ih (exponent + 1) htailWitness
        rcases htail with ⟨hstopped, hbound, hsuccess, hleast⟩
        refine ⟨hstopped, ?_, hsuccess, ?_⟩
        · omega
        · intro j hjLower hjUpper
          by_cases hj : j = exponent
          · subst j
            exact hcurrentDiv
          · exact hleast j (by omega) hjUpper

/-- `merge_init` stops and chooses the least exponent whose quotient is below 64. -/
theorem minrunExponentCharacterization (listSize : PySSize)
    (_hlistSize : listSize.Nonnegative)
    (hmax : listSize.toNat ≤ PY_LIST_MAX) :
    let out := minrunExponentSpecLoop 64 listSize.toNat 0
    out.2 = true ∧
      out.1 < 64 ∧
      listSize.toNat / 2 ^ out.1 < 64 ∧
      ∀ j < out.1, 64 ≤ listSize.toNat / 2 ^ j := by
  have hwitness : ∃ d < 64, listSize.toNat / 2 ^ (0 + d) < 64 := by
    refine ⟨63, by omega, ?_⟩
    have hlt : listSize.toNat < 2 ^ 63 := by
      rw [pyListMax_eq] at hmax
      norm_num at hmax ⊢
      omega
    rw [Nat.zero_add, Nat.div_eq_of_lt hlt]
    omega
  have hspec := minrunExponentSpecLoop_characterization 64 listSize.toNat 0 hwitness
  simpa using hspec

/-- Named corollary: the chosen exponent is below the `PySSize` word width. -/
theorem minrunExponent_lt_64 (listSize : PySSize)
    (hlistSize : listSize.Nonnegative)
    (hmax : listSize.toNat ≤ PY_LIST_MAX) :
    (minrunExponentSpecLoop 64 listSize.toNat 0).1 < 64 :=
  (minrunExponentCharacterization listSize hlistSize hmax).2.1

/-- Named corollary: initialization stops and its stored exponent is below 64. -/
theorem minrunInit_stops_and_exponent_lt_64 (listSize : PySSize)
    (hlistSize : listSize.Nonnegative)
    (hmax : listSize.toNat ≤ PY_LIST_MAX) :
    (minrunInitTraced listSize).stopped = true ∧
      (minrunInit listSize).mr_e.toNat < 64 := by
  have hinit := minrunInit_exponent_eq_spec listSize hlistSize
  have hcharacterization := minrunExponentCharacterization listSize hlistSize hmax
  dsimp only at hinit hcharacterization ⊢
  exact ⟨hinit.2.2.trans hcharacterization.1, hinit.1.trans_lt hcharacterization.2.1⟩

/-- The selected exponent is at most 60 on a 64-bit build with 8-byte object pointers. -/
theorem minrunExponent_le_60 (listSize : PySSize)
    (hlistSize : listSize.Nonnegative)
    (hmax : listSize.toNat ≤ PY_LIST_MAX) :
    (minrunExponentSpecLoop 64 listSize.toNat 0).1 ≤ 60 := by
  have hcharacterization := minrunExponentCharacterization listSize hlistSize hmax
  dsimp only at hcharacterization
  by_contra hnot
  have hleast := hcharacterization.2.2.2 60 (by omega)
  have hlt : listSize.toNat < 2 ^ 60 := by
    rw [pyListMax_eq] at hmax
    norm_num at hmax ⊢
    omega
  rw [Nat.div_eq_of_lt hlt] at hleast
  omega

/-! ## Width-independent output range -/

/-- For a positive admitted list, the initialized modulus does not exceed the
list length.  This uses only the exponent search, not the mask. -/
theorem minrunInit_modulus_le_listSize
    (listSize : PySSize) (hNonnegative : listSize.Nonnegative)
    (hMax : listSize.toNat ≤ PY_LIST_MAX) (hPositive : 0 < listSize.toNat) :
    2 ^ (minrunInit listSize).mr_e.toNat ≤ listSize.toNat := by
  let out := minrunExponentSpecLoop 64 listSize.toNat 0
  have hinit := minrunInit_exponent_eq_spec listSize hNonnegative
  have hcharacterization :=
    minrunExponentCharacterization listSize hNonnegative hMax
  change 2 ^ (minrunInit listSize).mr_e.toNat ≤ listSize.toNat
  rw [hinit.1]
  by_cases hzero : out.1 = 0
  · rw [hzero]
    exact hPositive
  · obtain ⟨exponent, hexponent⟩ := Nat.exists_eq_succ_of_ne_zero hzero
    change 2 ^ out.1 ≤ listSize.toNat
    dsimp only at hcharacterization
    rw [hexponent] at hcharacterization ⊢
    have hprevious :
        64 ≤ listSize.toNat / 2 ^ exponent := by
      exact hcharacterization.2.2.2 exponent (by omega)
    have hpowPositive : 0 < 2 ^ exponent := by positivity
    have hscaled : 64 * 2 ^ exponent ≤ listSize.toNat :=
      (Nat.le_div_iff_mul_le hpowPositive).mp hprevious
    rw [pow_succ]
    omega

/-- The initialized 32-bit transcription mask is below the selected mathematical
modulus, including when `mr_e` is too large for exact mask equivalence. -/
theorem minrunInit_mask_lt_modulus
    (listSize : PySSize) (hNonnegative : listSize.Nonnegative)
    (hMax : listSize.toNat ≤ PY_LIST_MAX) :
    (minrunInit listSize).mr_mask.toNat <
      2 ^ (minrunInit listSize).mr_e.toNat := by
  simp only [minrunInit, minrunInitTraced]
  rw [minrunExponentLoop_eq_spec 64 listSize 0 hNonnegative]
  have hbound := minrunExponent_lt_64 listSize hNonnegative hMax
  have hlt : (minrunExponentSpecLoop 64 listSize.toNat 0).1 < 2 ^ 64 := by
    norm_num at hbound ⊢
    omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hlt]
  exact cIntMinrunMask_toNat_lt_pow _

/-- Width-independent facts preserved by every adaptive-minrun call. -/
private structure MinrunRangeInv (state : MinrunState) : Prop where
  listMax : state.listlen.toNat ≤ PY_LIST_MAX
  exponent60 : state.mr_e.toNat ≤ 60
  current : state.mr_current.toNat < 2 ^ state.mr_e.toNat
  mask : state.mr_mask.toNat < 2 ^ state.mr_e.toNat
  modulusLe : 2 ^ state.mr_e.toNat ≤ state.listlen.toNat
  floorLt : state.listlen.toNat / 2 ^ state.mr_e.toNat < 64

/-- One adaptive-minrun call passes its assertion, returns a target in the
public `1 .. MAX_MINRUN` band, and preserves the bounded-current fact. -/
private theorem minrunNext_range (state : MinrunState)
    (h : MinrunRangeInv state) :
    (minrunNext state).assertionPassed = true ∧
      1 ≤ (minrunNext state).result.toNat ∧
      (minrunNext state).result.toNat ≤ MAX_MINRUN.toNat ∧
      (minrunNext state).state.mr_current.toNat < 2 ^ state.mr_e.toNat := by
  let total : PySSize := state.mr_current + state.listlen
  have hpowLe : 2 ^ state.mr_e.toNat ≤ 2 ^ 60 :=
    Nat.pow_le_pow_right (by omega) h.exponent60
  have hcurrent := h.current
  have hmodulusLe := h.modulusLe
  have hfloorLt := h.floorLt
  have hlistMax := h.listMax
  rw [pyListMax_eq] at hlistMax
  have htotal64 : state.mr_current.toNat + state.listlen.toNat < 2 ^ 64 := by
    norm_num at hpowLe hlistMax ⊢
    omega
  have htotal63 : state.mr_current.toNat + state.listlen.toNat < 2 ^ 63 := by
    norm_num at hpowLe hlistMax ⊢
    omega
  have htotalNat : total.toNat =
      state.mr_current.toNat + state.listlen.toNat :=
    BitVec.toNat_add_of_lt htotal64
  have htotalMsb : total.msb = false := by
    rw [BitVec.msb_eq_false_iff_two_mul_lt, htotalNat]
    norm_num at htotal63 ⊢
    omega
  have hresult : (minrunNext state).result.toNat =
      (state.mr_current.toNat + state.listlen.toNat) /
        2 ^ state.mr_e.toNat := by
    simp only [minrunNext, total,
      BitVec.toNat_sshiftRight_of_msb_false htotalMsb,
      htotalNat, Nat.shiftRight_eq_div_pow]
  have hpowPositive : 0 < 2 ^ state.mr_e.toNat := by positivity
  have hpositive : 1 ≤ (minrunNext state).result.toNat := by
    rw [hresult]
    apply (Nat.le_div_iff_mul_le hpowPositive).2
    simp only [one_mul]
    omega
  have hlistLt : state.listlen.toNat < 64 * 2 ^ state.mr_e.toNat :=
    (Nat.div_lt_iff_lt_mul hpowPositive).mp hfloorLt
  have hupper : (minrunNext state).result.toNat ≤ MAX_MINRUN.toNat := by
    have hresultLt : (minrunNext state).result.toNat < 65 := by
      rw [hresult]
      apply (Nat.div_lt_iff_lt_mul hpowPositive).2
      omega
    have hmaxMinrun : MAX_MINRUN.toNat = 64 := by decide
    rw [hmaxMinrun]
    omega
  have hnextCurrent :
      (minrunNext state).state.mr_current.toNat < 2 ^ state.mr_e.toNat := by
    simp only [minrunNext]
    rw [BitVec.toNat_and]
    exact Nat.and_lt_two_pow _ h.mask
  exact ⟨by simp [minrunNext, total, htotalMsb], hpositive, hupper,
    hnextCurrent⟩

private theorem MinrunRangeInv.next
    {state : MinrunState} (h : MinrunRangeInv state) :
    MinrunRangeInv (minrunNext state).state := by
  have hstep := minrunNext_range state h
  constructor
  · simpa [minrunNext] using h.listMax
  · simpa [minrunNext] using h.exponent60
  · simpa [minrunNext] using hstep.2.2.2
  · simpa [minrunNext] using h.mask
  · simpa [minrunNext] using h.modulusLe
  · simpa [minrunNext] using h.floorLt

private theorem minrunInit_rangeInv
    (listSize : PySSize) (hNonnegative : listSize.Nonnegative)
    (hMax : listSize.toNat ≤ PY_LIST_MAX) (hPositive : 0 < listSize.toNat) :
    MinrunRangeInv (minrunInit listSize) := by
  have hinit := minrunInit_exponent_eq_spec listSize hNonnegative
  have hcharacterization :=
    minrunExponentCharacterization listSize hNonnegative hMax
  constructor
  · simpa [minrunInit, minrunInitTraced] using hMax
  · rw [hinit.1]
    exact minrunExponent_le_60 listSize hNonnegative hMax
  · rw [hinit.2.1]
    simp
  · exact minrunInit_mask_lt_modulus listSize hNonnegative hMax
  · exact minrunInit_modulus_le_listSize listSize hNonnegative hMax hPositive
  · rw [hinit.1]
    exact hcharacterization.2.2.1

/-- Iteration preserves the private range invariant and records the band for
every emitted target. -/
private theorem minrunNextN_range
    (calls : Nat) (state : MinrunState) (h : MinrunRangeInv state) :
    let run := minrunNextN calls state
    MinrunRangeInv run.state ∧
      run.assertionsPassed = true ∧
      ∀ target ∈ run.outputs,
        1 ≤ target ∧ target ≤ MAX_MINRUN.toNat := by
  induction calls generalizing state with
  | zero =>
      simp only [minrunNextN]
      exact ⟨h, trivial, by simp⟩
  | succ calls ih =>
      let next := minrunNext state
      have hstep := minrunNext_range state h
      have htail := ih next.state h.next
      dsimp only at htail
      rcases htail with ⟨htailInv, htailAssertions, htailBounds⟩
      simp only [minrunNextN]
      refine ⟨htailInv, ?_, ?_⟩
      · simp [next, hstep.1, htailAssertions]
      · intro target htarget
        simp only [List.mem_cons] at htarget
        rcases htarget with rfl | htarget
        · exact ⟨hstep.2.1, hstep.2.2.1⟩
        · exact htailBounds target htarget

/-- Arbitrarily many calls from `merge_init` pass every signed-overflow
assertion and emit only targets in `1 .. 64`.
This theorem does not use exact quotient/remainder mask equivalence. -/
theorem minrunNextN_output_bounds
    (listSize : PySSize) (hNonnegative : listSize.Nonnegative)
    (hMax : listSize.toNat ≤ PY_LIST_MAX) (hPositive : 0 < listSize.toNat)
    (calls : Nat) :
    let run := minrunNextN calls (minrunInit listSize)
    run.assertionsPassed = true ∧
      ∀ target ∈ run.outputs,
        1 ≤ target ∧ target ≤ MAX_MINRUN.toNat := by
  have hrun := minrunNextN_range calls (minrunInit listSize)
    (minrunInit_rangeInv listSize hNonnegative hMax hPositive)
  exact hrun.2

/-- The next call after any reachable prefix passes its assertion and returns
a target in the unconditional `1 .. MAX_MINRUN` band. -/
theorem minrunNext_after_init_bounds
    (listSize : PySSize) (hNonnegative : listSize.Nonnegative)
    (hMax : listSize.toNat ≤ PY_LIST_MAX) (hPositive : 0 < listSize.toNat)
    (calls : Nat) :
    let state := (minrunNextN calls (minrunInit listSize)).state
    (minrunNext state).assertionPassed = true ∧
      1 ≤ (minrunNext state).result.toNat ∧
      (minrunNext state).result.toNat ≤ MAX_MINRUN.toNat := by
  have hrun := minrunNextN_range calls (minrunInit listSize)
    (minrunInit_rangeInv listSize hNonnegative hMax hPositive)
  dsimp only at hrun ⊢
  have hstep := minrunNext_range
    (minrunNextN calls (minrunInit listSize)).state hrun.1
  exact ⟨hstep.1, hstep.2.1, hstep.2.2.1⟩

/-- Natural-number trace of repeated quotient/remainder generator steps. -/
structure MinrunSpecTrace where
  outputs : List Nat
  residual : Nat
  deriving DecidableEq, Repr

/-- Iterate the exact-arithmetic minrun recurrence. -/
def minrunSpecTrace : Nat → Nat → Nat → Nat → MinrunSpecTrace
  | 0, _, _, current => { outputs := [], residual := current }
  | calls + 1, listlen, exponent, current =>
      let next := minrunNextSpec listlen current exponent
      let tail := minrunSpecTrace calls listlen exponent next.residual
      { outputs := next.result :: tail.outputs, residual := tail.residual }

/-- At exponent 33 the selected 32-bit transcription mask no longer agrees with the
ideal full-width mask: the second actual target is 63 rather than 64.  This is
kernel-checked executable evidence that the width restriction on exact
equivalence is substantive. -/
theorem minrun_cIntMask_truncation_regression :
    let listSize : PySSize := BitVec.ofNat 64 (2 ^ 39 - 2 ^ 32)
    (minrunInit listSize).mr_e.toNat = 33 ∧
      (minrunInit listSize).mr_mask.toNat = 2 ^ 32 - 1 ∧
      (minrunNextN 2 (minrunInit listSize)).outputs = [63, 63] ∧
      (minrunSpecTrace 2 listSize.toNat 33 0).outputs = [63, 64] := by
  decide

/-- Prefix sums telescope through the quotient/remainder recurrence. -/
theorem minrunSpecTrace_prefix (calls listlen exponent current : Nat)
    (hcurrent : current < 2 ^ exponent) :
    let trace := minrunSpecTrace calls listlen exponent current
    trace.outputs.sum = (current + calls * listlen) / 2 ^ exponent ∧
      trace.residual = (current + calls * listlen) % 2 ^ exponent ∧
      trace.residual < 2 ^ exponent := by
  induction calls generalizing current with
  | zero =>
      have hpow : 0 < 2 ^ exponent := pow_pos (by omega) _
      simp [minrunSpecTrace, Nat.div_eq_of_lt hcurrent,
        Nat.mod_eq_of_lt hcurrent, hcurrent]
  | succ calls ih =>
      let modulus := 2 ^ exponent
      let total := current + listlen
      let quotient := total / modulus
      let residual := total % modulus
      have hmodulus : 0 < modulus := by
        simp [modulus]
      have hresidual : residual < modulus := Nat.mod_lt _ hmodulus
      have htail := ih residual hresidual
      change
        quotient + (minrunSpecTrace calls listlen exponent residual).outputs.sum =
            (current + (calls + 1) * listlen) / modulus ∧
          (minrunSpecTrace calls listlen exponent residual).residual =
            (current + (calls + 1) * listlen) % modulus ∧
          (minrunSpecTrace calls listlen exponent residual).residual < modulus
      rcases htail with ⟨htailSum, htailResidual, htailBound⟩
      rw [htailSum, htailResidual]
      have hdecompose : residual + modulus * quotient = total := by
        exact Nat.mod_add_div total modulus
      have htotalEq : modulus * quotient + (residual + calls * listlen) =
          current + (calls + 1) * listlen := by
        calc
          modulus * quotient + (residual + calls * listlen) =
              (residual + modulus * quotient) + calls * listlen := by ring
          _ = total + calls * listlen := by rw [hdecompose]
          _ = current + (calls + 1) * listlen := by
            simp only [total]
            ring
      constructor
      · calc
          quotient + (residual + calls * listlen) / modulus =
              (modulus * quotient + (residual + calls * listlen)) / modulus := by
                rw [Nat.mul_add_div hmodulus]
          _ = (current + (calls + 1) * listlen) / modulus := by rw [htotalEq]
      constructor
      · calc
          (residual + calls * listlen) % modulus =
              (modulus * quotient + (residual + calls * listlen)) % modulus := by
                rw [Nat.mul_add_mod_self_left]
          _ = (current + (calls + 1) * listlen) % modulus := by rw [htotalEq]
      · exact Nat.mod_lt _ hmodulus

/-- Repeated finite-width calls agree with the exact trace while preserving the C assertion. -/
theorem minrunNextN_eq_spec (calls : Nat) (state : MinrunState)
    (hexponent : state.mr_e.toNat < 32)
    (hexponent60 : state.mr_e.toNat ≤ 60)
    (hmask : state.mr_mask = ((1 : PySSize) <<< state.mr_e.toNat) - 1)
    (hcurrent : state.mr_current.toNat < 2 ^ state.mr_e.toNat)
    (hlistMax : state.listlen.toNat ≤ PY_LIST_MAX) :
    let trace := minrunSpecTrace calls state.listlen.toNat
      state.mr_e.toNat state.mr_current.toNat
    (minrunNextN calls state).outputs = trace.outputs ∧
      (minrunNextN calls state).state.mr_current.toNat = trace.residual ∧
      (minrunNextN calls state).assertionsPassed = true := by
  induction calls generalizing state with
  | zero => simp [minrunNextN, minrunSpecTrace]
  | succ calls ih =>
      have hpowLe : 2 ^ state.mr_e.toNat ≤ 2 ^ 60 :=
        Nat.pow_le_pow_right (by omega) hexponent60
      have hnoOverflow : state.mr_current.toNat + state.listlen.toNat < 2 ^ 63 := by
        rw [pyListMax_eq] at hlistMax
        norm_num at hpowLe hlistMax ⊢
        omega
      have hstep := minrunNext_eq_spec state hexponent hmask hnoOverflow
      let next := minrunNext state
      let specified := minrunNextSpec state.listlen.toNat state.mr_current.toNat
        state.mr_e.toNat
      change next.result.toNat = specified.result ∧
        next.state.mr_current.toNat = specified.residual ∧
        next.assertionPassed = true at hstep
      rcases hstep with ⟨hresult, hresidual, hassertion⟩
      have hnextExponent : next.state.mr_e.toNat = state.mr_e.toNat := by
        simp [next, minrunNext]
      have hnextMask :
          next.state.mr_mask = ((1 : PySSize) <<< next.state.mr_e.toNat) - 1 := by
        simp [next, minrunNext, hmask]
      have hnextList : next.state.listlen.toNat = state.listlen.toNat := by
        simp [next, minrunNext]
      have hnextCurrent : next.state.mr_current.toNat < 2 ^ next.state.mr_e.toNat := by
        rw [hnextExponent, hresidual]
        exact Nat.mod_lt _ (pow_pos (by omega) _)
      have htail := ih next.state
        (by rwa [hnextExponent])
        (by rwa [hnextExponent])
        hnextMask hnextCurrent (by rwa [hnextList])
      change
        next.result.toNat :: (minrunNextN calls next.state).outputs =
            specified.result ::
              (minrunSpecTrace calls state.listlen.toNat state.mr_e.toNat
                specified.residual).outputs ∧
          (minrunNextN calls next.state).state.mr_current.toNat =
            (minrunSpecTrace calls state.listlen.toNat state.mr_e.toNat
              specified.residual).residual ∧
          (next.assertionPassed && (minrunNextN calls next.state).assertionsPassed) = true
      rw [hresult]
      have htail' :
          (minrunNextN calls next.state).outputs =
              (minrunSpecTrace calls state.listlen.toNat state.mr_e.toNat
                specified.residual).outputs ∧
            (minrunNextN calls next.state).state.mr_current.toNat =
              (minrunSpecTrace calls state.listlen.toNat state.mr_e.toNat
                specified.residual).residual ∧
            (minrunNextN calls next.state).assertionsPassed = true := by
        simpa [hnextExponent, hnextList, hresidual] using htail
      rcases htail' with ⟨houtputs, htailResidual, htailAssertions⟩
      simp [houtputs, htailResidual, hassertion, htailAssertions]

/-- Exact prefix-sum and residual invariant for repeated transcribed calls from `merge_init`. -/
theorem minrunPrefixSum (listSize : PySSize)
    (hlistSize : listSize.Nonnegative)
    (hmax : listSize.toNat ≤ PY_LIST_MAX)
    (hexponent32 : (minrunInit listSize).mr_e.toNat < 32)
    (calls : Nat)
    (_hcalls : calls ≤ 2 ^ (minrunInit listSize).mr_e.toNat) :
    let state := minrunInit listSize
    let run := minrunNextN calls state
    let modulus := 2 ^ state.mr_e.toNat
    run.outputs.sum = (calls * listSize.toNat) / modulus ∧
      run.state.mr_current.toNat = (calls * listSize.toNat) % modulus ∧
      run.state.mr_current.toNat < modulus ∧
      run.state.mr_current.toNat + listSize.toNat < 2 ^ 63 ∧
      run.assertionsPassed = true := by
  let state := minrunInit listSize
  let exponentResult := minrunExponentSpecLoop 64 listSize.toNat 0
  have hinitExponent := minrunInit_exponent_eq_spec listSize hlistSize
  have hspecified32 : exponentResult.1 < 32 := by
    rw [← hinitExponent.1]
    exact hexponent32
  have hinit := minrunInit_eq_spec listSize hlistSize hspecified32
  change state.mr_e.toNat = exponentResult.1 ∧
      state.mr_mask = ((1 : PySSize) <<< exponentResult.1) - 1 ∧
      state.mr_current = 0 ∧ (minrunInitTraced listSize).stopped = exponentResult.2 at hinit
  have hexponent : state.mr_e.toNat < 32 := by
    exact hexponent32
  have hexponent60 : state.mr_e.toNat ≤ 60 := by
    rw [hinit.1]
    exact minrunExponent_le_60 listSize hlistSize hmax
  have hmask : state.mr_mask = ((1 : PySSize) <<< state.mr_e.toNat) - 1 := by
    rw [hinit.1]
    exact hinit.2.1
  have hcurrent : state.mr_current.toNat < 2 ^ state.mr_e.toNat := by
    rw [hinit.2.2.1]
    simp
  have hstateList : state.listlen.toNat = listSize.toNat := by
    simp [state, minrunInit, minrunInitTraced]
  have hrun := minrunNextN_eq_spec calls state hexponent hexponent60 hmask hcurrent
    (by rwa [hstateList])
  have hpure := minrunSpecTrace_prefix calls state.listlen.toNat
    state.mr_e.toNat state.mr_current.toNat hcurrent
  change
    (minrunNextN calls state).outputs.sum =
        (calls * listSize.toNat) / 2 ^ state.mr_e.toNat ∧
      (minrunNextN calls state).state.mr_current.toNat =
        (calls * listSize.toNat) % 2 ^ state.mr_e.toNat ∧
      (minrunNextN calls state).state.mr_current.toNat < 2 ^ state.mr_e.toNat ∧
      (minrunNextN calls state).state.mr_current.toNat + listSize.toNat < 2 ^ 63 ∧
      (minrunNextN calls state).assertionsPassed = true
  dsimp only at hrun hpure
  rcases hrun with ⟨houtputs, hresidual, hassertions⟩
  rcases hpure with ⟨hsum, hpureResidual, hresidualBound⟩
  have hcurrentNat : state.mr_current.toNat = 0 := by
    rw [hinit.2.2.1]
    rfl
  have hsumFinal : (minrunNextN calls state).outputs.sum =
      (calls * listSize.toNat) / 2 ^ state.mr_e.toNat := by
    calc
      (minrunNextN calls state).outputs.sum =
          (minrunSpecTrace calls state.listlen.toNat state.mr_e.toNat
            state.mr_current.toNat).outputs.sum := congrArg List.sum houtputs
      _ = (state.mr_current.toNat + calls * state.listlen.toNat) /
          2 ^ state.mr_e.toNat := hsum
      _ = (calls * listSize.toNat) / 2 ^ state.mr_e.toNat := by
        rw [hcurrentNat, hstateList, Nat.zero_add]
  have hresidualFinal : (minrunNextN calls state).state.mr_current.toNat =
      (calls * listSize.toNat) % 2 ^ state.mr_e.toNat := by
    calc
      (minrunNextN calls state).state.mr_current.toNat =
          (minrunSpecTrace calls state.listlen.toNat state.mr_e.toNat
            state.mr_current.toNat).residual := hresidual
      _ = (state.mr_current.toNat + calls * state.listlen.toNat) %
          2 ^ state.mr_e.toNat := hpureResidual
      _ = (calls * listSize.toNat) % 2 ^ state.mr_e.toNat := by
        rw [hcurrentNat, hstateList, Nat.zero_add]
  have hresidualFinalBound :
      (minrunNextN calls state).state.mr_current.toNat < 2 ^ state.mr_e.toNat := by
    rw [hresidualFinal]
    exact Nat.mod_lt _ (pow_pos (by omega) _)
  have hpowLe : 2 ^ state.mr_e.toNat ≤ 2 ^ 60 :=
    Nat.pow_le_pow_right (by omega) hexponent60
  have haddition :
      (minrunNextN calls state).state.mr_current.toNat + listSize.toNat < 2 ^ 63 := by
    rw [pyListMax_eq] at hmax
    norm_num at hpowLe hmax
    omega
  exact ⟨hsumFinal, hresidualFinal, hresidualFinalBound, haddition, hassertions⟩

/-- Ceiling division used to state the balanced-sequence result without rationals. -/
def minrunCeilDiv (x modulus : Nat) : Nat :=
  (x + modulus - 1) / modulus

private theorem minrunCeilDiv_eq_succ (x modulus : Nat)
    (hmodulus : 0 < modulus)
    (hremainder : 0 < x % modulus) :
    minrunCeilDiv x modulus = x / modulus + 1 := by
  let quotient := x / modulus
  let residual := x % modulus
  have hresidual : residual < modulus := Nat.mod_lt _ hmodulus
  have hdecompose : modulus * quotient + residual = x := Nat.div_add_mod x modulus
  have htailDiv : (residual + modulus - 1) / modulus = 1 := by
    exact Nat.div_eq_of_lt_le (by omega) (by omega)
  unfold minrunCeilDiv
  have htotal : x + modulus - 1 = modulus * quotient + (residual + modulus - 1) := by
    omega
  rw [htotal, Nat.mul_add_div hmodulus, htailDiv]

private theorem minrunNextSpec_balanced (listlen exponent current : Nat)
    (hcurrent : current < 2 ^ exponent) :
    let next := minrunNextSpec listlen current exponent
    next.result = listlen / 2 ^ exponent ∨
      next.result = minrunCeilDiv listlen (2 ^ exponent) := by
  let modulus := 2 ^ exponent
  let quotient := listlen / modulus
  let residual := listlen % modulus
  have hmodulus : 0 < modulus := by simp [modulus]
  have hresidual : residual < modulus := Nat.mod_lt _ hmodulus
  have hdecompose : modulus * quotient + residual = listlen := Nat.div_add_mod listlen modulus
  have htotal : current + listlen = modulus * quotient + (current + residual) := by
    omega
  have hresult : (current + listlen) / modulus =
      quotient + (current + residual) / modulus := by
    rw [htotal, Nat.mul_add_div hmodulus]
  dsimp only [minrunNextSpec]
  rw [hresult]
  by_cases hcarry : current + residual < modulus
  · left
    rw [Nat.div_eq_of_lt hcarry]
    simp [quotient, modulus]
  · right
    have hcarryDiv : (current + residual) / modulus = 1 := by
      exact Nat.div_eq_of_lt_le (by omega) (by omega)
    rw [hcarryDiv]
    have hremainder : 0 < listlen % modulus := by
      change 0 < residual
      by_contra hzero
      have : residual = 0 := by omega
      omega
    rw [minrunCeilDiv_eq_succ listlen modulus hmodulus hremainder]

/-- Every exact-arithmetic output is either the floor or ceiling target, provided a divisible
list length starts with zero residual. -/
theorem minrunSpecTrace_balanced (calls listlen exponent current : Nat)
    (hcurrent : current < 2 ^ exponent)
    (hzero : listlen % 2 ^ exponent = 0 → current = 0) :
    ∀ x ∈ (minrunSpecTrace calls listlen exponent current).outputs,
      x = listlen / 2 ^ exponent ∨
        x = minrunCeilDiv listlen (2 ^ exponent) := by
  induction calls generalizing current with
  | zero => simp [minrunSpecTrace]
  | succ calls ih =>
      let next := minrunNextSpec listlen current exponent
      have hnextCurrent : next.residual < 2 ^ exponent := by
        exact Nat.mod_lt _ (pow_pos (by omega) _)
      have hnextZero : listlen % 2 ^ exponent = 0 → next.residual = 0 := by
        intro hdivisible
        have hcurrentZero := hzero hdivisible
        simp [next, minrunNextSpec, hcurrentZero, hdivisible]
      have hhead := minrunNextSpec_balanced listlen exponent current hcurrent
      have htail := ih next.residual hnextCurrent hnextZero
      simp only [minrunSpecTrace, List.mem_cons]
      intro x hx
      rcases hx with rfl | hx
      · exact hhead
      · exact htail x hx

theorem minrunSpecTrace_length (calls listlen exponent current : Nat) :
    (minrunSpecTrace calls listlen exponent current).outputs.length = calls := by
  induction calls generalizing current with
  | zero => simp [minrunSpecTrace]
  | succ calls ih => simp [minrunSpecTrace, ih]

/-- A complete generator cycle is the balanced floor/ceiling partition of the list length. -/
theorem minrunSequence (listSize : PySSize)
    (hlistSize : listSize.Nonnegative)
    (hmax : listSize.toNat ≤ PY_LIST_MAX)
    (hexponent32 : (minrunInit listSize).mr_e.toNat < 32) :
    let state := minrunInit listSize
    let modulus := 2 ^ state.mr_e.toNat
    let run := minrunNextN modulus state
    run.outputs.length = modulus ∧
      (∀ x ∈ run.outputs,
        x = listSize.toNat / modulus ∨
          x = minrunCeilDiv listSize.toNat modulus) ∧
      run.outputs.sum = listSize.toNat ∧
      run.state.mr_current.toNat = 0 ∧
      run.assertionsPassed = true := by
  let state := minrunInit listSize
  let modulus := 2 ^ state.mr_e.toNat
  let run := minrunNextN modulus state
  have hpref := minrunPrefixSum listSize hlistSize hmax hexponent32 modulus (by rfl)
  change
    run.outputs.sum = (modulus * listSize.toNat) / modulus ∧
      run.state.mr_current.toNat = (modulus * listSize.toNat) % modulus ∧
      run.state.mr_current.toNat < modulus ∧
      run.state.mr_current.toNat + listSize.toNat < 2 ^ 63 ∧
      run.assertionsPassed = true at hpref
  let exponentResult := minrunExponentSpecLoop 64 listSize.toNat 0
  have hinitExponent := minrunInit_exponent_eq_spec listSize hlistSize
  have hspecified32 : exponentResult.1 < 32 := by
    rw [← hinitExponent.1]
    exact hexponent32
  have hinit := minrunInit_eq_spec listSize hlistSize hspecified32
  change state.mr_e.toNat = exponentResult.1 ∧
      state.mr_mask = ((1 : PySSize) <<< exponentResult.1) - 1 ∧
      state.mr_current = 0 ∧ (minrunInitTraced listSize).stopped = exponentResult.2 at hinit
  have hexponent : state.mr_e.toNat < 32 := by
    exact hexponent32
  have hexponent60 : state.mr_e.toNat ≤ 60 := by
    rw [hinit.1]
    exact minrunExponent_le_60 listSize hlistSize hmax
  have hmask : state.mr_mask = ((1 : PySSize) <<< state.mr_e.toNat) - 1 := by
    rw [hinit.1]
    exact hinit.2.1
  have hcurrentNat : state.mr_current.toNat = 0 := by
    rw [hinit.2.2.1]
    rfl
  have hcurrent : state.mr_current.toNat < 2 ^ state.mr_e.toNat := by
    rw [hcurrentNat]
    simp
  have hstateList : state.listlen.toNat = listSize.toNat := by
    simp [state, minrunInit, minrunInitTraced]
  have hrun := minrunNextN_eq_spec modulus state hexponent hexponent60 hmask hcurrent
    (by rwa [hstateList])
  dsimp only at hrun
  rcases hrun with ⟨houtputs, _, _⟩
  have hlength : run.outputs.length = modulus := by
    change (minrunNextN modulus state).outputs.length = modulus
    rw [houtputs, minrunSpecTrace_length]
  have hbalancedSpec := minrunSpecTrace_balanced modulus state.listlen.toNat
    state.mr_e.toNat state.mr_current.toNat hcurrent (by
      intro _
      exact hcurrentNat)
  have hbalanced : ∀ x ∈ run.outputs,
      x = listSize.toNat / modulus ∨ x = minrunCeilDiv listSize.toNat modulus := by
    intro x hx
    have hxSpec : x ∈ (minrunSpecTrace modulus state.listlen.toNat state.mr_e.toNat
        state.mr_current.toNat).outputs := by
      rw [← houtputs]
      exact hx
    have hxBalanced := hbalancedSpec x hxSpec
    simpa [modulus, hstateList] using hxBalanced
  have hmodulus : 0 < modulus := by simp [modulus]
  have hsum : run.outputs.sum = listSize.toNat := by
    calc
      run.outputs.sum = (modulus * listSize.toNat) / modulus := hpref.1
      _ = listSize.toNat := Nat.mul_div_right _ hmodulus
  have hresidual : run.state.mr_current.toNat = 0 := by
    calc
      run.state.mr_current.toNat = (modulus * listSize.toNat) % modulus := hpref.2.1
      _ = 0 := by simp
  exact ⟨hlength, hbalanced, hsum, hresidual, hpref.2.2.2.2⟩

end CPythonListsort
