/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.ReverseSliceSafety
import Code.Transcription.CountRun

/-!
# `count_run` safety

The evaluator below mirrors the reviewed `count_run` transcription while
producing its trace compositionally.  The Lean instrumentation reads the
previous entry and then the next entry; its comparator orientation and control
branch match CPython's `IF_NEXT_SMALLER`, without making a claim about C operand
evaluation order.  Every operational-equivalence-block, prefix, and whole-run
reversal delegates to the traced `sortslice_reverse` evaluator proved safe in
`ReverseSliceSafety`.

As in the v1 transcription, `BoolComparator` is total.  CPython's comparator
error/failure return path is therefore outside this model; the safety theorem is
for every total Boolean comparator, including inconsistent ones.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

private def ascendingScanResult (length : Nat) (fuelExhausted : Bool) :
    AscendingScanResult :=
  { length := length, fuelExhausted := fuelExhausted }

/-- Traced ascending scan.  The instrumentation chooses a predecessor-first
read order, while the comparison itself has CPython's `next < previous`
orientation. -/
def ascendingScanTraced? :
    Nat → BoolComparator κ → SortSlice κ ν → Int → Nat → Nat →
      TraceResult AscendingScanResult
  | 0, _, _, _, nremaining, n =>
      let result := ascendingScanResult n (decide (n < nremaining))
      if n < nremaining then
        (TraceResult.pure result).markFuelExhausted
      else
        TraceResult.pure result
  | fuel + 1, lt, slice, base, nremaining, n =>
      if n < nremaining then
        (TraceResult.sortSliceKeysRead? slice
          (base + Int.ofNat (n - 1))).bind fun previous =>
            (TraceResult.sortSliceKeysRead? slice
              (base + Int.ofNat n)).bind fun next =>
                if iflt lt next.key previous.key then
                  TraceResult.pure (ascendingScanResult n false)
                else
                  ascendingScanTraced? fuel lt slice base nremaining (n + 1)
      else
        TraceResult.pure (ascendingScanResult n false)

/-- Traced `REVERSE_LAST_NEQ`. -/
def reverseLastEqualTraced? (valuesPresent : Bool)
    (slice : SortSlice κ ν) (base : Int) (n neq : Nat) :
    TraceResult (ReverseEqualResult κ ν) :=
  if neq = 0 then
    TraceResult.pure { slice := slice, fuelExhausted := false }
  else
    let count := neq + 1
    let start := base + Int.ofNat n - Int.ofNat count
    (sortsliceReverseTraced? valuesPresent slice start count).map fun reversed =>
      { slice := reversed.slice, fuelExhausted := reversed.fuelExhausted }

private def descendingScanResult (slice : SortSlice κ ν) (length equalTail : Nat)
    (fuelExhausted : Bool) : DescendingScanResult κ ν :=
  { slice := slice
    length := length
    equalTail := equalTail
    fuelExhausted := fuelExhausted }

/-- Traced descending scan.  It probes `next < previous` first, then
`previous < next`, and delegates every completed equality block to
`reverseLastEqualTraced?`. -/
def descendingScanTraced? :
    Nat → Bool → BoolComparator κ → SortSlice κ ν → Int → Nat → Nat → Nat →
      TraceResult (DescendingScanResult κ ν)
  | 0, _, _, slice, _, nremaining, n, neq =>
      let result := descendingScanResult slice n neq (decide (n < nremaining))
      if n < nremaining then
        (TraceResult.pure result).markFuelExhausted
      else
        TraceResult.pure result
  | fuel + 1, valuesPresent, lt, slice, base, nremaining, n, neq =>
      if n < nremaining then
        (TraceResult.sortSliceKeysRead? slice
          (base + Int.ofNat (n - 1))).bind fun previous =>
            (TraceResult.sortSliceKeysRead? slice
              (base + Int.ofNat n)).bind fun next =>
                if iflt lt next.key previous.key then
                  (reverseLastEqualTraced? valuesPresent slice base n neq).bind
                    fun reversed =>
                      if reversed.fuelExhausted then
                        TraceResult.pure
                          (descendingScanResult reversed.slice n 0 true)
                      else
                        descendingScanTraced? fuel valuesPresent lt reversed.slice
                          base nremaining (n + 1) 0
                else if iflt lt previous.key next.key then
                  TraceResult.pure
                    (descendingScanResult slice n neq false)
                else
                  descendingScanTraced? fuel valuesPresent lt slice base
                    nremaining (n + 1) (neq + 1)
      else
        TraceResult.pure (descendingScanResult slice n neq false)

/-- Traced completion of the descending case, including final
operational-equivalence-block reversal, whole-prefix reversal, and ascending
suffix extension. -/
def finishDescendingTraced? (state : MergeState κ ν)
    (slice : SortSlice κ ν) (base : Int) (nremaining n : Nat) :
    TraceResult (CountRunResult κ ν) :=
  (descendingScanTraced? nremaining state.a.hasValues state.key_compare slice
    base nremaining n 0).bind fun descending =>
      if descending.fuelExhausted then
        TraceResult.pure
          { slice := descending.slice
            length := descending.length
            fuelExhausted := true }
      else
        (reverseLastEqualTraced? state.a.hasValues descending.slice base
          descending.length descending.equalTail).bind fun equalTailReversed =>
            if equalTailReversed.fuelExhausted then
              TraceResult.pure
                { slice := equalTailReversed.slice
                  length := descending.length
                  fuelExhausted := true }
            else
              (sortsliceReverseTraced? state.a.hasValues equalTailReversed.slice
                base descending.length).bind fun wholeReversed =>
                  if wholeReversed.fuelExhausted then
                    TraceResult.pure
                      { slice := wholeReversed.slice
                        length := descending.length
                        fuelExhausted := true }
                  else
                    (ascendingScanTraced? nremaining state.key_compare
                      wholeReversed.slice base nremaining descending.length).map
                        fun extended =>
                          { slice := wholeReversed.slice
                            length := extended.length
                            fuelExhausted := extended.fuelExhausted }

/-- Fully traced `count_run` evaluator. -/
def countRunTraced? (state : MergeState κ ν) (slice : SortSlice κ ν)
    (base : Int) (nremaining : Nat) : TraceResult (CountRunResult κ ν) :=
  if 0 < nremaining ∧ nremaining ≤ PY_SSIZE_T_MAX then
    (ascendingScanTraced? nremaining state.key_compare slice base nremaining 1).bind
      fun ascending =>
        if ascending.fuelExhausted then
          TraceResult.pure
            { slice := slice
              length := ascending.length
              fuelExhausted := true }
        else if ascending.length = nremaining then
          TraceResult.pure
            { slice := slice
              length := ascending.length
              fuelExhausted := false }
        else if 1 < ascending.length then
          (TraceResult.sortSliceKeysRead? slice base).bind fun first =>
            (TraceResult.sortSliceKeysRead? slice
              (base + Int.ofNat (ascending.length - 1))).bind fun last =>
                if iflt state.key_compare first.key last.key then
                  TraceResult.pure
                    { slice := slice
                      length := ascending.length
                      fuelExhausted := false }
                else
                  (sortsliceReverseTraced? state.a.hasValues slice base
                    ascending.length).bind fun reversed =>
                      if reversed.fuelExhausted then
                        TraceResult.pure
                          { slice := reversed.slice
                            length := ascending.length + 1
                            fuelExhausted := true }
                      else
                        finishDescendingTraced? state reversed.slice base nremaining
                          (ascending.length + 1)
        else
          finishDescendingTraced? state slice base nremaining
            (ascending.length + 1)
  else
    TraceResult.failure

/-! ## Merge-memory event freedom -/

private theorem ascendingScanTraced_memoryEvents_eq_nil
    (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν)
    (base : Int) (nremaining n : Nat) :
    (ascendingScanTraced? fuel lt slice base nremaining n).trace.memoryEvents =
      [] := by
  induction fuel generalizing n with
  | zero =>
      by_cases hactive : n < nremaining
      · simp [ascendingScanTraced?, hactive, TraceResult.markFuelExhausted,
          TraceResult.pure, AccessTrace.empty, AccessTrace.compose,
          AccessTrace.exhausted]
      · simp [ascendingScanTraced?, hactive, TraceResult.pure,
          AccessTrace.empty]
  | succ fuel ih =>
      rw [ascendingScanTraced?]
      by_cases hactive : n < nremaining
      · rw [if_pos hactive]
        apply TraceResult.memoryEvents_bind_eq_nil
        · rfl
        · intro previous
          apply TraceResult.memoryEvents_bind_eq_nil
          · rfl
          · intro next
            by_cases hcomparison : iflt lt next.key previous.key = true
            · rw [if_pos hcomparison]
              rfl
            · rw [if_neg hcomparison]
              exact ih (n + 1)
      · rw [if_neg hactive]
        rfl

private theorem reverseLastEqualTraced_memoryEvents_eq_nil
    (valuesPresent : Bool) (slice : SortSlice κ ν) (base : Int)
    (n neq : Nat) :
    (reverseLastEqualTraced? valuesPresent slice base n neq).trace.memoryEvents =
      [] := by
  unfold reverseLastEqualTraced?
  by_cases hzero : neq = 0
  · rw [if_pos hzero]
    rfl
  · rw [if_neg hzero]
    simpa only [TraceResult.memoryEvents_map] using
      (sortsliceReverseTraced_memoryEvents_eq_nil valuesPresent slice
        (base + Int.ofNat n - Int.ofNat (neq + 1)) (neq + 1))

private theorem descendingScanTraced_memoryEvents_eq_nil
    (fuel : Nat) (valuesPresent : Bool) (lt : BoolComparator κ)
    (slice : SortSlice κ ν) (base : Int) (nremaining n neq : Nat) :
    (descendingScanTraced? fuel valuesPresent lt slice base nremaining n
      neq).trace.memoryEvents = [] := by
  induction fuel generalizing slice n neq with
  | zero =>
      by_cases hactive : n < nremaining
      · simp [descendingScanTraced?, hactive, TraceResult.markFuelExhausted,
          TraceResult.pure, AccessTrace.empty, AccessTrace.compose,
          AccessTrace.exhausted]
      · simp [descendingScanTraced?, hactive, TraceResult.pure,
          AccessTrace.empty]
  | succ fuel ih =>
      rw [descendingScanTraced?]
      by_cases hactive : n < nremaining
      · rw [if_pos hactive]
        apply TraceResult.memoryEvents_bind_eq_nil
        · rfl
        · intro previous
          apply TraceResult.memoryEvents_bind_eq_nil
          · rfl
          · intro next
            by_cases hnextSmaller :
                iflt lt next.key previous.key = true
            · rw [if_pos hnextSmaller]
              apply TraceResult.memoryEvents_bind_eq_nil
              · exact reverseLastEqualTraced_memoryEvents_eq_nil _ _ _ _ _
              · intro reversed
                by_cases hexhausted : reversed.fuelExhausted = true
                · rw [if_pos hexhausted]
                  rfl
                · rw [if_neg hexhausted]
                  exact ih reversed.slice (n + 1) 0
            · rw [if_neg hnextSmaller]
              by_cases hpreviousSmaller :
                  iflt lt previous.key next.key = true
              · rw [if_pos hpreviousSmaller]
                rfl
              · rw [if_neg hpreviousSmaller]
                exact ih slice (n + 1) (neq + 1)
      · rw [if_neg hactive]
        rfl

private theorem finishDescendingTraced_memoryEvents_eq_nil
    (state : MergeState κ ν) (slice : SortSlice κ ν) (base : Int)
    (nremaining n : Nat) :
    (finishDescendingTraced? state slice base nremaining n).trace.memoryEvents =
      [] := by
  unfold finishDescendingTraced?
  apply TraceResult.memoryEvents_bind_eq_nil
  · exact descendingScanTraced_memoryEvents_eq_nil _ _ _ _ _ _ _ _
  · intro descending
    by_cases hdescendingFuel : descending.fuelExhausted = true
    · rw [if_pos hdescendingFuel]
      rfl
    · rw [if_neg hdescendingFuel]
      apply TraceResult.memoryEvents_bind_eq_nil
      · exact reverseLastEqualTraced_memoryEvents_eq_nil _ _ _ _ _
      · intro equalTailReversed
        by_cases hequalFuel : equalTailReversed.fuelExhausted = true
        · rw [if_pos hequalFuel]
          rfl
        · rw [if_neg hequalFuel]
          apply TraceResult.memoryEvents_bind_eq_nil
          · exact sortsliceReverseTraced_memoryEvents_eq_nil _ _ _ _
          · intro wholeReversed
            by_cases hwholeFuel : wholeReversed.fuelExhausted = true
            · rw [if_pos hwholeFuel]
              rfl
            · rw [if_neg hwholeFuel]
              simpa only [TraceResult.memoryEvents_map] using
                (ascendingScanTraced_memoryEvents_eq_nil nremaining
                  state.key_compare wholeReversed.slice base nremaining
                  descending.length)

/-- The complete `count_run` wrapper cannot emit a merge-memory boundary on
any admitted, rejected, comparator-selected, or fuel-exhaustion path. -/
theorem countRunTraced_memoryEvents_eq_nil
    (state : MergeState κ ν) (slice : SortSlice κ ν) (base : Int)
    (nremaining : Nat) :
    (countRunTraced? state slice base nremaining).trace.memoryEvents = [] := by
  unfold countRunTraced?
  by_cases hguard : 0 < nremaining ∧ nremaining ≤ PY_SSIZE_T_MAX
  · rw [if_pos hguard]
    apply TraceResult.memoryEvents_bind_eq_nil
    · exact ascendingScanTraced_memoryEvents_eq_nil _ _ _ _ _ _
    · intro ascending
      by_cases hascendingFuel : ascending.fuelExhausted = true
      · rw [if_pos hascendingFuel]
        rfl
      · rw [if_neg hascendingFuel]
        by_cases hcomplete : ascending.length = nremaining
        · rw [if_pos hcomplete]
          rfl
        · rw [if_neg hcomplete]
          by_cases hlong : 1 < ascending.length
          · rw [if_pos hlong]
            apply TraceResult.memoryEvents_bind_eq_nil
            · rfl
            · intro first
              apply TraceResult.memoryEvents_bind_eq_nil
              · rfl
              · intro last
                by_cases hcomparison :
                    iflt state.key_compare first.key last.key = true
                · rw [if_pos hcomparison]
                  rfl
                · rw [if_neg hcomparison]
                  apply TraceResult.memoryEvents_bind_eq_nil
                  · exact sortsliceReverseTraced_memoryEvents_eq_nil _ _ _ _
                  · intro reversed
                    by_cases hreverseFuel : reversed.fuelExhausted = true
                    · rw [if_pos hreverseFuel]
                      rfl
                    · rw [if_neg hreverseFuel]
                      exact finishDescendingTraced_memoryEvents_eq_nil _ _ _ _ _
          · rw [if_neg hlong]
            exact finishDescendingTraced_memoryEvents_eq_nil _ _ _ _ _
  · rw [if_neg hguard]
    rfl

/-! ## Logical-policy event freedom -/

private theorem ascendingScanTraced_policyEvents_eq_nil
    (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν)
    (base : Int) (nremaining n : Nat) :
    (ascendingScanTraced? fuel lt slice base nremaining n).trace.policyEvents =
      [] := by
  induction fuel generalizing n with
  | zero =>
      by_cases hactive : n < nremaining
      · simp [ascendingScanTraced?, hactive, TraceResult.markFuelExhausted,
          TraceResult.pure, AccessTrace.empty, AccessTrace.compose,
          AccessTrace.exhausted]
      · simp [ascendingScanTraced?, hactive, TraceResult.pure,
          AccessTrace.empty]
  | succ fuel ih =>
      rw [ascendingScanTraced?]
      by_cases hactive : n < nremaining
      · rw [if_pos hactive]
        apply TraceResult.policyEvents_bind_eq_nil
        · rfl
        · intro previous
          apply TraceResult.policyEvents_bind_eq_nil
          · rfl
          · intro next
            by_cases hcomparison : iflt lt next.key previous.key = true
            · rw [if_pos hcomparison]
              rfl
            · rw [if_neg hcomparison]
              exact ih (n + 1)
      · rw [if_neg hactive]
        rfl

private theorem reverseLastEqualTraced_policyEvents_eq_nil
    (valuesPresent : Bool) (slice : SortSlice κ ν) (base : Int)
    (n neq : Nat) :
    (reverseLastEqualTraced? valuesPresent slice base n neq).trace.policyEvents =
      [] := by
  unfold reverseLastEqualTraced?
  by_cases hzero : neq = 0
  · rw [if_pos hzero]
    rfl
  · rw [if_neg hzero]
    simpa only [TraceResult.policyEvents_map] using
      (sortsliceReverseTraced_policyEvents_eq_nil valuesPresent slice
        (base + Int.ofNat n - Int.ofNat (neq + 1)) (neq + 1))

private theorem descendingScanTraced_policyEvents_eq_nil
    (fuel : Nat) (valuesPresent : Bool) (lt : BoolComparator κ)
    (slice : SortSlice κ ν) (base : Int) (nremaining n neq : Nat) :
    (descendingScanTraced? fuel valuesPresent lt slice base nremaining n
      neq).trace.policyEvents = [] := by
  induction fuel generalizing slice n neq with
  | zero =>
      by_cases hactive : n < nremaining
      · simp [descendingScanTraced?, hactive, TraceResult.markFuelExhausted,
          TraceResult.pure, AccessTrace.empty, AccessTrace.compose,
          AccessTrace.exhausted]
      · simp [descendingScanTraced?, hactive, TraceResult.pure,
          AccessTrace.empty]
  | succ fuel ih =>
      rw [descendingScanTraced?]
      by_cases hactive : n < nremaining
      · rw [if_pos hactive]
        apply TraceResult.policyEvents_bind_eq_nil
        · rfl
        · intro previous
          apply TraceResult.policyEvents_bind_eq_nil
          · rfl
          · intro next
            by_cases hnextSmaller : iflt lt next.key previous.key = true
            · rw [if_pos hnextSmaller]
              apply TraceResult.policyEvents_bind_eq_nil
              · exact reverseLastEqualTraced_policyEvents_eq_nil _ _ _ _ _
              · intro reversed
                by_cases hexhausted : reversed.fuelExhausted = true
                · rw [if_pos hexhausted]
                  rfl
                · rw [if_neg hexhausted]
                  exact ih reversed.slice (n + 1) 0
            · rw [if_neg hnextSmaller]
              by_cases hpreviousSmaller :
                  iflt lt previous.key next.key = true
              · rw [if_pos hpreviousSmaller]
                rfl
              · rw [if_neg hpreviousSmaller]
                exact ih slice (n + 1) (neq + 1)
      · rw [if_neg hactive]
        rfl

private theorem finishDescendingTraced_policyEvents_eq_nil
    (state : MergeState κ ν) (slice : SortSlice κ ν) (base : Int)
    (nremaining n : Nat) :
    (finishDescendingTraced? state slice base nremaining n).trace.policyEvents =
      [] := by
  unfold finishDescendingTraced?
  apply TraceResult.policyEvents_bind_eq_nil
  · exact descendingScanTraced_policyEvents_eq_nil _ _ _ _ _ _ _ _
  · intro descending
    by_cases hdescendingFuel : descending.fuelExhausted = true
    · rw [if_pos hdescendingFuel]
      rfl
    · rw [if_neg hdescendingFuel]
      apply TraceResult.policyEvents_bind_eq_nil
      · exact reverseLastEqualTraced_policyEvents_eq_nil _ _ _ _ _
      · intro equalTailReversed
        by_cases hequalFuel : equalTailReversed.fuelExhausted = true
        · rw [if_pos hequalFuel]
          rfl
        · rw [if_neg hequalFuel]
          apply TraceResult.policyEvents_bind_eq_nil
          · exact sortsliceReverseTraced_policyEvents_eq_nil _ _ _ _
          · intro wholeReversed
            by_cases hwholeFuel : wholeReversed.fuelExhausted = true
            · rw [if_pos hwholeFuel]
              rfl
            · rw [if_neg hwholeFuel]
              simpa only [TraceResult.policyEvents_map] using
                (ascendingScanTraced_policyEvents_eq_nil nremaining
                  state.key_compare wholeReversed.slice base nremaining
                  descending.length)

/-- The complete `count_run` helper cannot emit a formed-run or logical-merge
event on any branch. -/
theorem countRunTraced_policyEvents_eq_nil
    (state : MergeState κ ν) (slice : SortSlice κ ν) (base : Int)
    (nremaining : Nat) :
    (countRunTraced? state slice base nremaining).trace.policyEvents = [] := by
  unfold countRunTraced?
  by_cases hguard : 0 < nremaining ∧ nremaining ≤ PY_SSIZE_T_MAX
  · rw [if_pos hguard]
    apply TraceResult.policyEvents_bind_eq_nil
    · exact ascendingScanTraced_policyEvents_eq_nil _ _ _ _ _ _
    · intro ascending
      by_cases hascendingFuel : ascending.fuelExhausted = true
      · rw [if_pos hascendingFuel]
        rfl
      · rw [if_neg hascendingFuel]
        by_cases hcomplete : ascending.length = nremaining
        · rw [if_pos hcomplete]
          rfl
        · rw [if_neg hcomplete]
          by_cases hlong : 1 < ascending.length
          · rw [if_pos hlong]
            apply TraceResult.policyEvents_bind_eq_nil
            · rfl
            · intro first
              apply TraceResult.policyEvents_bind_eq_nil
              · rfl
              · intro last
                by_cases hcomparison :
                    iflt state.key_compare first.key last.key = true
                · rw [if_pos hcomparison]
                  rfl
                · rw [if_neg hcomparison]
                  apply TraceResult.policyEvents_bind_eq_nil
                  · exact sortsliceReverseTraced_policyEvents_eq_nil _ _ _ _
                  · intro reversed
                    by_cases hreverseFuel : reversed.fuelExhausted = true
                    · rw [if_pos hreverseFuel]
                      rfl
                    · rw [if_neg hreverseFuel]
                      exact finishDescendingTraced_policyEvents_eq_nil _ _ _ _ _
          · rw [if_neg hlong]
            exact finishDescendingTraced_policyEvents_eq_nil _ _ _ _ _
  · rw [if_neg hguard]
    rfl

@[simp]
theorem erase_ascendingScanTraced (fuel : Nat) (lt : BoolComparator κ)
    (slice : SortSlice κ ν) (base : Int) (nremaining n : Nat) :
    (ascendingScanTraced? fuel lt slice base nremaining n).erase =
      ascendingScan? fuel lt slice base nremaining n := by
  induction fuel generalizing n with
  | zero =>
      by_cases h : n < nremaining <;>
        simp [ascendingScanTraced?, ascendingScan?, ascendingScanResult, h]
  | succ fuel ih =>
      by_cases h : n < nremaining
      · simp only [ascendingScanTraced?, ascendingScan?, h, if_true,
          TraceResult.erase_bind, TraceResult.erase_sortSliceKeysRead]
        unfold countRunBindOptionAcross
        cases hprevious : slice.read? (base + Int.ofNat (n - 1)) with
        | none => simp
        | some previous =>
            simp only [Option.bind_some]
            cases hnext : slice.read? (base + Int.ofNat n) with
            | none => simp
            | some next =>
                simp only [Option.bind_some]
                by_cases hcomparison : iflt lt next.key previous.key = true
                · change lt next.key previous.key = true at hcomparison
                  simp [hcomparison, ascendingScanResult]
                · have hcomparison' : ¬lt next.key previous.key = true := by
                    simpa [iflt] using hcomparison
                  simp [hcomparison', ih]
      · simp [ascendingScanTraced?, ascendingScan?, h, ascendingScanResult]

@[simp]
theorem erase_reverseLastEqualTraced (valuesPresent : Bool)
    (slice : SortSlice κ ν) (base : Int) (n neq : Nat) :
    (reverseLastEqualTraced? valuesPresent slice base n neq).erase =
      reverseLastEqual? slice base n neq := by
  by_cases hzero : neq = 0
  · simp [reverseLastEqualTraced?, reverseLastEqual?, hzero]
  · simp only [reverseLastEqualTraced?, reverseLastEqual?, hzero, if_false,
      TraceResult.erase_map, erase_sortsliceReverseTraced]
    cases hreverse : sortsliceReverse? slice
        (base + Int.ofNat n - Int.ofNat (neq + 1)) (neq + 1) <;>
      simp

@[simp]
theorem erase_descendingScanTraced (fuel : Nat) (valuesPresent : Bool)
    (lt : BoolComparator κ) (slice : SortSlice κ ν) (base : Int)
    (nremaining n neq : Nat) :
    (descendingScanTraced? fuel valuesPresent lt slice base nremaining n neq).erase =
      descendingScan? fuel lt slice base nremaining n neq := by
  induction fuel generalizing slice n neq with
  | zero =>
      by_cases h : n < nremaining <;>
        simp [descendingScanTraced?, descendingScan?, descendingScanResult, h]
  | succ fuel ih =>
      by_cases hactive : n < nremaining
      · simp only [descendingScanTraced?, descendingScan?, hactive, if_true,
          TraceResult.erase_bind, TraceResult.erase_sortSliceKeysRead,
          bind, Option.bind]
        cases hprevious : slice.read? (base + Int.ofNat (n - 1)) with
        | none => simp
        | some previous =>
            simp only
            cases hnext : slice.read? (base + Int.ofNat n) with
            | none => simp
            | some next =>
                simp only
                by_cases hsmaller : iflt lt next.key previous.key = true
                · rw [if_pos hsmaller]
                  simp only [hsmaller, if_true]
                  simp only [TraceResult.erase_bind,
                    erase_reverseLastEqualTraced]
                  cases hreverse : reverseLastEqual? slice base n neq with
                  | none => rfl
                  | some reversed =>
                      by_cases hfuel : reversed.fuelExhausted = true
                      · simp [hfuel, descendingScanResult]
                      · simp [hfuel, ih]
                · rw [if_neg hsmaller]
                  simp only [hsmaller]
                  by_cases hlarger : iflt lt previous.key next.key = true
                  · rw [if_pos hlarger]
                    simp only [hlarger, if_true]
                    rfl
                  · rw [if_neg hlarger]
                    simp only [hlarger]
                    exact ih _ _ _
      · simp [descendingScanTraced?, descendingScan?, hactive,
          descendingScanResult]

@[simp]
theorem erase_finishDescendingTraced (state : MergeState κ ν)
    (slice : SortSlice κ ν) (base : Int) (nremaining n : Nat) :
    (finishDescendingTraced? state slice base nremaining n).erase =
      finishDescending? state slice base nremaining n := by
  unfold finishDescendingTraced? finishDescending?
  rw [TraceResult.erase_bind, erase_descendingScanTraced]
  cases hdescending : descendingScan? nremaining state.key_compare slice base
      nremaining n 0 with
  | none => rfl
  | some descending =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases hdescendingFuel : descending.fuelExhausted with
      | true => simp only [if_true, TraceResult.erase_pure]
      | false =>
        simp only [Bool.false_eq_true, if_false, TraceResult.erase_bind,
          erase_reverseLastEqualTraced]
        cases hequal : reverseLastEqual? descending.slice base descending.length
            descending.equalTail with
        | none => simp only [Option.bind_none]
        | some equalTailReversed =>
            simp only [Option.bind_some]
            cases hequalFuel : equalTailReversed.fuelExhausted with
            | true =>
                simp only [if_true, TraceResult.erase_pure]
            | false =>
              simp only [Bool.false_eq_true, if_false,
                TraceResult.erase_bind, erase_sortsliceReverseTraced]
              cases hwhole : sortsliceReverse? equalTailReversed.slice base
                  descending.length with
              | none => simp only [Option.bind_none]
              | some wholeReversed =>
                  simp only [Option.bind_some]
                  cases hwholeFuel : wholeReversed.fuelExhausted with
                  | true =>
                      simp only [if_true, TraceResult.erase_pure]
                  | false =>
                    simp only [Bool.false_eq_true, if_false,
                      TraceResult.erase_map, erase_ascendingScanTraced]
                    unfold countRunBindOptionAcross
                    cases ascendingScan? nremaining state.key_compare
                        wholeReversed.slice base nremaining descending.length <;>
                      rfl

@[simp]
theorem erase_countRunTraced (state : MergeState κ ν)
    (slice : SortSlice κ ν) (base : Int) (nremaining : Nat) :
    (countRunTraced? state slice base nremaining).erase =
      countRun? state slice base nremaining := by
  unfold countRunTraced? countRun?
  by_cases hguard : 0 < nremaining ∧ nremaining ≤ PY_SSIZE_T_MAX
  · rw [if_pos hguard, if_pos hguard, TraceResult.erase_bind,
      erase_ascendingScanTraced]
    unfold countRunBindOptionAcross
    cases hascending : ascendingScan? nremaining state.key_compare slice base
        nremaining 1 with
    | none => simp
    | some ascending =>
        simp only [Option.bind_some]
        cases hascendingFuel : ascending.fuelExhausted with
        | true => simp
        | false =>
          simp only [Bool.false_eq_true, if_false]
          by_cases hcomplete : ascending.length = nremaining
          · simp [hcomplete]
          · simp only [hcomplete, if_false]
            by_cases hlong : 1 < ascending.length
            · rw [if_pos hlong, if_pos hlong]
              simp only [TraceResult.erase_bind,
                TraceResult.erase_sortSliceKeysRead]
              cases hfirst : slice.read? base with
              | none => simp
              | some first =>
                  cases hlast : slice.read?
                      (base + Int.ofNat (ascending.length - 1)) with
                  | none => simp
                  | some last =>
                      simp only [bind, Option.bind]
                      cases hcomparison :
                          iflt state.key_compare first.key last.key with
                      | true => simp
                      | false =>
                        simp only [Bool.false_eq_true, if_false,
                          TraceResult.erase_bind,
                          erase_sortsliceReverseTraced]
                        cases hreverse : sortsliceReverse? slice base
                            ascending.length with
                        | none => simp
                        | some reversed =>
                            cases hreverseFuel : reversed.fuelExhausted with
                            | true => simp [hreverseFuel]
                            | false =>
                              simp [hreverseFuel,
                                erase_finishDescendingTraced]
            · rw [if_neg hlong, if_neg hlong]
              exact erase_finishDescendingTraced _ _ _ _ _
  · simp [hguard]

private structure CountTraceSafe (execution : TraceResult α) : Prop where
  fuel : execution.trace.fuelExhausted = false
  noPushes : execution.trace.pushDepths = []
  bounds : execution.trace.allAccessesInBounds
  tempLive : execution.trace.tempPayloadAccessesLive

namespace CountTraceSafe

private theorem pure (value : α) :
    CountTraceSafe (TraceResult.pure value) := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · exact AccessTrace.allAccessesInBounds_empty
  · exact AccessTrace.tempPayloadAccessesLive_empty

private theorem bind (current : TraceResult α) (next : α → TraceResult β)
    (value : α) (hresult : current.result = some value)
    (hcurrent : CountTraceSafe current)
    (hnext : CountTraceSafe (next value)) :
    CountTraceSafe (current.bind next) := by
  constructor
  · simp [TraceResult.trace_bind, hresult, hcurrent.fuel, hnext.fuel]
  · simp [TraceResult.trace_bind, hresult, AccessTrace.compose,
      hcurrent.noPushes, hnext.noPushes]
  · rw [TraceResult.trace_bind, hresult,
      AccessTrace.allAccessesInBounds_compose]
    exact ⟨hcurrent.bounds, hnext.bounds⟩
  · rw [TraceResult.trace_bind, hresult,
      AccessTrace.tempPayloadAccessesLive_compose]
    exact ⟨hcurrent.tempLive, hnext.tempLive⟩

private theorem map (current : TraceResult α) (transform : α → β)
    (hcurrent : CountTraceSafe current) :
    CountTraceSafe (current.map transform) := by
  constructor
  · simpa [TraceResult.map] using hcurrent.fuel
  · simpa [TraceResult.map] using hcurrent.noPushes
  · simpa [TraceResult.map] using hcurrent.bounds
  · simpa [TraceResult.map] using hcurrent.tempLive

end CountTraceSafe

private theorem countKeyRead_safe (slice : SortSlice κ ν) (index : Int)
    (hindex : SortSlice.IndexInBounds slice index) :
    CountTraceSafe (TraceResult.sortSliceKeysRead? slice index) := by
  constructor
  all_goals
    simp [AccessTrace.singletonAccess, AccessTrace.allAccessesInBounds,
      AccessTrace.tempPayloadAccessesLive, AccessEvent.InBounds,
      AccessEvent.TempPayloadLive, SortSlice.IndexInBounds] at hindex ⊢
  all_goals aesop

private def ascendingScanResult' (length : Nat) : AscendingScanResult :=
  { length := length, fuelExhausted := false }

private structure AscendingScanSafetyPost
    (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν)
    (base : Int) (nremaining n : Nat)
    (result : AscendingScanResult) : Prop where
  resultEq :
    (ascendingScanTraced? fuel lt slice base nremaining n).result = some result
  resultFuel : result.fuelExhausted = false
  traceSafe :
    CountTraceSafe (ascendingScanTraced? fuel lt slice base nremaining n)
  exactErasure :
    (ascendingScanTraced? fuel lt slice base nremaining n).erase =
      ascendingScan? fuel lt slice base nremaining n
  lengthBounds : n ≤ result.length ∧ result.length ≤ nremaining

private theorem ascendingScanTraced_safe
    (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν)
    (base : Int) (nremaining n : Nat)
    (hrange : SortSlice.RangeInBounds slice base nremaining)
    (hnPositive : 1 ≤ n) (hnUpper : n ≤ nremaining)
    (hfuel : nremaining ≤ n + fuel) :
    ∃ result,
      AscendingScanSafetyPost fuel lt slice base nremaining n result := by
  induction fuel generalizing n with
  | zero =>
      have hstop : ¬n < nremaining := by omega
      let result := ascendingScanResult' n
      refine ⟨result, ?_⟩
      exact
        { resultEq := by
            simp only [ascendingScanTraced?, hstop, if_false]
            rfl
          resultFuel := rfl
          traceSafe := by
            simpa [ascendingScanTraced?, hstop, result,
              ascendingScanResult', ascendingScanResult] using
              (CountTraceSafe.pure result)
          exactErasure := erase_ascendingScanTraced _ _ _ _ _ _
          lengthBounds := ⟨le_rfl, hnUpper⟩ }
  | succ fuel ih =>
      by_cases hactive : n < nremaining
      · have hpreviousIndex : SortSlice.IndexInBounds slice
            (base + Int.ofNat (n - 1)) := by
          rcases hrange with ⟨hbase, hend⟩
          constructor
          · exact add_nonneg hbase (Int.natCast_nonneg _)
          · simp only [Int.ofNat_eq_natCast] at hend ⊢
            omega
        have hnextIndex : SortSlice.IndexInBounds slice
            (base + Int.ofNat n) := by
          rcases hrange with ⟨hbase, hend⟩
          constructor
          · exact add_nonneg hbase (Int.natCast_nonneg _)
          · simp only [Int.ofNat_eq_natCast] at hend ⊢
            omega
        rcases SortSlice.read_eq_some_of_indexInBounds slice _ hpreviousIndex with
          ⟨previous, hpreviousRaw⟩
        rcases SortSlice.read_eq_some_of_indexInBounds slice _ hnextIndex with
          ⟨next, hnextRaw⟩
        have hprevious :
            (TraceResult.sortSliceKeysRead? slice
              (base + Int.ofNat (n - 1))).result = some previous := by
          exact hpreviousRaw
        have hnext :
            (TraceResult.sortSliceKeysRead? slice
              (base + Int.ofNat n)).result = some next := by
          exact hnextRaw
        have hpreviousSafe := countKeyRead_safe slice _ hpreviousIndex
        have hnextSafe := countKeyRead_safe slice _ hnextIndex
        by_cases hsmaller : iflt lt next.key previous.key = true
        · let result := ascendingScanResult' n
          have htailSafe : CountTraceSafe
              ((TraceResult.sortSliceKeysRead? slice
                (base + Int.ofNat n)).bind fun next =>
                  if iflt lt next.key previous.key then
                    TraceResult.pure (ascendingScanResult n false)
                  else
                    ascendingScanTraced? fuel lt slice base nremaining
                      (n + 1)) := by
            apply CountTraceSafe.bind _ _ next hnext hnextSafe
            simpa only [hsmaller, if_true] using
              (CountTraceSafe.pure (ascendingScanResult n false))
          refine ⟨result, ?_⟩
          exact
            { resultEq := by
                simp only [ascendingScanTraced?, hactive, if_true,
                  TraceResult.bind, hprevious, hnext, hsmaller]
                rfl
              resultFuel := rfl
              traceSafe := by
                simp only [ascendingScanTraced?, hactive, if_true]
                exact CountTraceSafe.bind _ _ previous hprevious
                  hpreviousSafe htailSafe
              exactErasure := erase_ascendingScanTraced _ _ _ _ _ _
              lengthBounds := ⟨le_rfl, hnUpper⟩ }
        · have hnextFuel : nremaining ≤ n + 1 + fuel := by omega
          change ¬lt next.key previous.key = true at hsmaller
          rcases ih (n + 1) (by omega) (by omega) hnextFuel with
            ⟨result, hresult⟩
          have htailSafe : CountTraceSafe
              ((TraceResult.sortSliceKeysRead? slice
                (base + Int.ofNat n)).bind fun next =>
                  if iflt lt next.key previous.key then
                    TraceResult.pure (ascendingScanResult n false)
                  else
                    ascendingScanTraced? fuel lt slice base nremaining
                      (n + 1)) := by
            apply CountTraceSafe.bind _ _ next hnext hnextSafe
            simpa only [iflt, hsmaller, Bool.false_eq_true, if_false] using
              hresult.traceSafe
          refine ⟨result, ?_⟩
          exact
            { resultEq := by
                simpa only [ascendingScanTraced?, hactive, if_true,
                  TraceResult.bind, hprevious, hnext, iflt, hsmaller,
                  Bool.false_eq_true, if_false]
                  using hresult.resultEq
              resultFuel := hresult.resultFuel
              traceSafe := by
                simp only [ascendingScanTraced?, hactive, if_true]
                exact CountTraceSafe.bind _ _ previous hprevious
                  hpreviousSafe htailSafe
              exactErasure := erase_ascendingScanTraced _ _ _ _ _ _
              lengthBounds :=
                ⟨le_trans (by omega) hresult.lengthBounds.1,
                  hresult.lengthBounds.2⟩ }
      · let result := ascendingScanResult' n
        refine ⟨result, ?_⟩
        exact
          { resultEq := by
              simp only [ascendingScanTraced?, hactive, if_false]
              rfl
            resultFuel := rfl
            traceSafe := by
              simpa [ascendingScanTraced?, hactive, result,
                ascendingScanResult', ascendingScanResult] using
                (CountTraceSafe.pure result)
            exactErasure := erase_ascendingScanTraced _ _ _ _ _ _
            lengthBounds := ⟨le_rfl, hnUpper⟩ }

private theorem countTraceSafe_of_reverse
    (valuesPresent : Bool) (slice : SortSlice κ ν) (base : Int) (n : Nat)
    (result : ReverseSliceResult κ ν)
    (hpost : ReverseSliceSafetyPost slice valuesPresent base n result) :
    CountTraceSafe (sortsliceReverseTraced? valuesPresent slice base n) :=
  ⟨hpost.traceFuel, hpost.noPushes, hpost.accessesInBounds,
    hpost.tempAccessesLive⟩

private structure ReverseEqualSafetyPost
    (valuesPresent : Bool) (before : SortSlice κ ν) (base : Int)
    (n neq : Nat) (result : ReverseEqualResult κ ν) : Prop where
  resultEq :
    (reverseLastEqualTraced? valuesPresent before base n neq).result = some result
  resultFuel : result.fuelExhausted = false
  traceSafe :
    CountTraceSafe (reverseLastEqualTraced? valuesPresent before base n neq)
  exactErasure :
    (reverseLastEqualTraced? valuesPresent before base n neq).erase =
      reverseLastEqual? before base n neq
  valuesMode : SortSlice.ValuesModeInvariant valuesPresent result.slice
  sizeEq : result.slice.entries.size = before.entries.size

private theorem reverseLastEqualTraced_safe
    (valuesPresent : Bool) (slice : SortSlice κ ν) (base : Int)
    (nremaining n neq : Nat)
    (hrange : SortSlice.RangeInBounds slice base nremaining)
    (hnUpper : n ≤ nremaining) (hneq : neq < n)
    (hMode : SortSlice.ValuesModeInvariant valuesPresent slice) :
    ∃ result,
      ReverseEqualSafetyPost valuesPresent slice base n neq result := by
  by_cases hzero : neq = 0
  · let result : ReverseEqualResult κ ν :=
      { slice := slice, fuelExhausted := false }
    refine ⟨result, ?_⟩
    exact
      { resultEq := by
          simp only [reverseLastEqualTraced?, hzero, if_true]
          rfl
        resultFuel := rfl
        traceSafe := by
          simpa [reverseLastEqualTraced?, hzero, result] using
            (CountTraceSafe.pure result)
        exactErasure := erase_reverseLastEqualTraced _ _ _ _ _
        valuesMode := hMode
        sizeEq := rfl }
  · let count := neq + 1
    let start := base + Int.ofNat n - Int.ofNat count
    have hcountLe : count ≤ n := by
      dsimp [count]
      omega
    have hsubrange : SortSlice.RangeInBounds slice start count := by
      rcases hrange with ⟨hbase, hend⟩
      constructor
      · dsimp [start, count]
        omega
      · dsimp [start, count]
        simp only [Int.ofNat_eq_natCast] at hend ⊢
        omega
    rcases sortsliceReverse_safe valuesPresent slice start count hsubrange hMode with
      ⟨reversed, hreverse⟩
    let result : ReverseEqualResult κ ν :=
      { slice := reversed.slice, fuelExhausted := reversed.fuelExhausted }
    refine ⟨result, ?_⟩
    exact
      { resultEq := by
          simp only [reverseLastEqualTraced?, hzero, if_false]
          change
            ((sortsliceReverseTraced? valuesPresent slice start count).map
              (fun reversed =>
                { slice := reversed.slice
                  fuelExhausted := reversed.fuelExhausted })).result =
              some result
          simp [TraceResult.map, hreverse.resultEq, result]
        resultFuel := by
          exact hreverse.resultFuel
        traceSafe := by
          simp only [reverseLastEqualTraced?, hzero, if_false]
          exact CountTraceSafe.map _ _
            (countTraceSafe_of_reverse _ _ _ _ _ hreverse)
        exactErasure := erase_reverseLastEqualTraced _ _ _ _ _
        valuesMode := hreverse.valuesMode
        sizeEq := hreverse.sizeEq }

private structure DescendingScanSafetyPost
    (fuel : Nat) (valuesPresent : Bool) (lt : BoolComparator κ)
    (before : SortSlice κ ν) (base : Int) (nremaining n neq : Nat)
    (result : DescendingScanResult κ ν) : Prop where
  resultEq :
    (descendingScanTraced? fuel valuesPresent lt before base nremaining n neq).result =
      some result
  resultFuel : result.fuelExhausted = false
  traceSafe : CountTraceSafe
    (descendingScanTraced? fuel valuesPresent lt before base nremaining n neq)
  exactErasure :
    (descendingScanTraced? fuel valuesPresent lt before base nremaining n neq).erase =
      descendingScan? fuel lt before base nremaining n neq
  lengthBounds : n ≤ result.length ∧ result.length ≤ nremaining
  equalTailLt : result.equalTail < result.length
  valuesMode : SortSlice.ValuesModeInvariant valuesPresent result.slice
  sizeEq : result.slice.entries.size = before.entries.size

private theorem descendingScanTraced_safe
    (fuel : Nat) (valuesPresent : Bool) (lt : BoolComparator κ)
    (slice : SortSlice κ ν) (base : Int) (nremaining n neq : Nat)
    (hrange : SortSlice.RangeInBounds slice base nremaining)
    (hnPositive : 1 ≤ n) (hnUpper : n ≤ nremaining)
    (hneq : neq < n) (hfuel : nremaining ≤ n + fuel)
    (hMode : SortSlice.ValuesModeInvariant valuesPresent slice) :
    ∃ result,
      DescendingScanSafetyPost fuel valuesPresent lt slice base nremaining n neq
        result := by
  induction fuel generalizing slice n neq with
  | zero =>
      have hstop : ¬n < nremaining := by omega
      let result := descendingScanResult slice n neq false
      refine ⟨result, ?_⟩
      exact
        { resultEq := by
            simp only [descendingScanTraced?, hstop, if_false]
            rfl
          resultFuel := rfl
          traceSafe := by
            simpa [descendingScanTraced?, hstop, result] using
              (CountTraceSafe.pure result)
          exactErasure := erase_descendingScanTraced _ _ _ _ _ _ _ _
          lengthBounds := ⟨le_rfl, hnUpper⟩
          equalTailLt := hneq
          valuesMode := hMode
          sizeEq := rfl }
  | succ fuel ih =>
      by_cases hactive : n < nremaining
      · have hpreviousIndex : SortSlice.IndexInBounds slice
            (base + Int.ofNat (n - 1)) := by
          rcases hrange with ⟨hbase, hend⟩
          constructor
          · exact add_nonneg hbase (Int.natCast_nonneg _)
          · simp only [Int.ofNat_eq_natCast] at hend ⊢
            omega
        have hnextIndex : SortSlice.IndexInBounds slice
            (base + Int.ofNat n) := by
          rcases hrange with ⟨hbase, hend⟩
          constructor
          · exact add_nonneg hbase (Int.natCast_nonneg _)
          · simp only [Int.ofNat_eq_natCast] at hend ⊢
            omega
        rcases SortSlice.read_eq_some_of_indexInBounds slice _ hpreviousIndex with
          ⟨previous, hpreviousRaw⟩
        rcases SortSlice.read_eq_some_of_indexInBounds slice _ hnextIndex with
          ⟨next, hnextRaw⟩
        have hprevious :
            (TraceResult.sortSliceKeysRead? slice
              (base + Int.ofNat (n - 1))).result = some previous :=
          hpreviousRaw
        have hnext :
            (TraceResult.sortSliceKeysRead? slice
              (base + Int.ofNat n)).result = some next :=
          hnextRaw
        have hpreviousSafe := countKeyRead_safe slice _ hpreviousIndex
        have hnextSafe := countKeyRead_safe slice _ hnextIndex
        by_cases hsmaller : iflt lt next.key previous.key = true
        · rcases reverseLastEqualTraced_safe valuesPresent slice base
              nremaining n neq hrange hnUpper hneq hMode with
            ⟨reversed, hreverse⟩
          have hrangeReversed :
              SortSlice.RangeInBounds reversed.slice base nremaining :=
            hrange.of_size_eq hreverse.sizeEq
          have hnextFuel : nremaining ≤ n + 1 + fuel := by omega
          rcases ih reversed.slice (n + 1) 0 hrangeReversed (by omega)
              (by omega) (by omega) hnextFuel hreverse.valuesMode with
            ⟨result, hresult⟩
          have hbranchSafe : CountTraceSafe
              ((reverseLastEqualTraced? valuesPresent slice base n neq).bind
                fun reversed =>
                  if reversed.fuelExhausted then
                    TraceResult.pure
                      (descendingScanResult reversed.slice n 0 true)
                  else
                    descendingScanTraced? fuel valuesPresent lt reversed.slice
                      base nremaining (n + 1) 0) := by
            apply CountTraceSafe.bind _ _ reversed hreverse.resultEq
              hreverse.traceSafe
            simpa [hreverse.resultFuel] using hresult.traceSafe
          have hafterNextSafe : CountTraceSafe
              ((TraceResult.sortSliceKeysRead? slice
                (base + Int.ofNat n)).bind fun next =>
                  if iflt lt next.key previous.key then
                    (reverseLastEqualTraced? valuesPresent slice base n neq).bind
                      fun reversed =>
                        if reversed.fuelExhausted then
                          TraceResult.pure
                            (descendingScanResult reversed.slice n 0 true)
                        else
                          descendingScanTraced? fuel valuesPresent lt
                            reversed.slice base nremaining (n + 1) 0
                  else if iflt lt previous.key next.key then
                    TraceResult.pure (descendingScanResult slice n neq false)
                  else
                    descendingScanTraced? fuel valuesPresent lt slice base
                      nremaining (n + 1) (neq + 1)) := by
            apply CountTraceSafe.bind _ _ next hnext hnextSafe
            simpa only [hsmaller, if_true] using hbranchSafe
          refine ⟨result, ?_⟩
          exact
            { resultEq := by
                simpa only [descendingScanTraced?, hactive, if_true,
                  TraceResult.bind, hprevious, hnext, hsmaller,
                  hreverse.resultEq, hreverse.resultFuel,
                  Bool.false_eq_true, if_false] using hresult.resultEq
              resultFuel := hresult.resultFuel
              traceSafe := by
                simp only [descendingScanTraced?, hactive, if_true]
                exact CountTraceSafe.bind _ _ previous hprevious
                  hpreviousSafe hafterNextSafe
              exactErasure := erase_descendingScanTraced _ _ _ _ _ _ _ _
              lengthBounds :=
                ⟨le_trans (by omega) hresult.lengthBounds.1,
                  hresult.lengthBounds.2⟩
              equalTailLt := hresult.equalTailLt
              valuesMode := hresult.valuesMode
              sizeEq := hresult.sizeEq.trans hreverse.sizeEq }
        · change ¬lt next.key previous.key = true at hsmaller
          by_cases hlarger : iflt lt previous.key next.key = true
          · change lt previous.key next.key = true at hlarger
            let result := descendingScanResult slice n neq false
            have hbranchSafe : CountTraceSafe
                (if iflt lt next.key previous.key then
                  (reverseLastEqualTraced? valuesPresent slice base n neq).bind
                    fun reversed =>
                      if reversed.fuelExhausted then
                        TraceResult.pure
                          (descendingScanResult reversed.slice n 0 true)
                      else
                        descendingScanTraced? fuel valuesPresent lt
                          reversed.slice base nremaining (n + 1) 0
                else if iflt lt previous.key next.key then
                  TraceResult.pure (descendingScanResult slice n neq false)
                else
                  descendingScanTraced? fuel valuesPresent lt slice base
                    nremaining (n + 1) (neq + 1)) := by
              simpa only [iflt, hsmaller, Bool.false_eq_true, if_false,
                hlarger, if_true] using
                (CountTraceSafe.pure (descendingScanResult slice n neq false))
            have hafterNextSafe : CountTraceSafe
                ((TraceResult.sortSliceKeysRead? slice
                  (base + Int.ofNat n)).bind fun next =>
                    if iflt lt next.key previous.key then
                      (reverseLastEqualTraced? valuesPresent slice base n neq).bind
                        fun reversed =>
                          if reversed.fuelExhausted then
                            TraceResult.pure
                              (descendingScanResult reversed.slice n 0 true)
                          else
                            descendingScanTraced? fuel valuesPresent lt
                              reversed.slice base nremaining (n + 1) 0
                    else if iflt lt previous.key next.key then
                      TraceResult.pure (descendingScanResult slice n neq false)
                    else
                      descendingScanTraced? fuel valuesPresent lt slice base
                        nremaining (n + 1) (neq + 1)) :=
              CountTraceSafe.bind _ _ next hnext hnextSafe hbranchSafe
            refine ⟨result, ?_⟩
            exact
              { resultEq := by
                  simp only [descendingScanTraced?, hactive, if_true,
                    TraceResult.bind, hprevious, hnext, iflt, hsmaller,
                    Bool.false_eq_true, if_false, hlarger, result]
                  rfl
                resultFuel := rfl
                traceSafe := by
                  simp only [descendingScanTraced?, hactive, if_true]
                  exact CountTraceSafe.bind _ _ previous hprevious
                    hpreviousSafe hafterNextSafe
                exactErasure := erase_descendingScanTraced _ _ _ _ _ _ _ _
                lengthBounds := ⟨le_rfl, hnUpper⟩
                equalTailLt := hneq
                valuesMode := hMode
                sizeEq := rfl }
          · change ¬lt previous.key next.key = true at hlarger
            have hnextFuel : nremaining ≤ n + 1 + fuel := by omega
            rcases ih slice (n + 1) (neq + 1) hrange (by omega) (by omega)
                (by omega) hnextFuel hMode with ⟨result, hresult⟩
            have hbranchSafe : CountTraceSafe
                (if iflt lt next.key previous.key then
                  (reverseLastEqualTraced? valuesPresent slice base n neq).bind
                    fun reversed =>
                      if reversed.fuelExhausted then
                        TraceResult.pure
                          (descendingScanResult reversed.slice n 0 true)
                      else
                        descendingScanTraced? fuel valuesPresent lt
                          reversed.slice base nremaining (n + 1) 0
                else if iflt lt previous.key next.key then
                  TraceResult.pure (descendingScanResult slice n neq false)
                else
                  descendingScanTraced? fuel valuesPresent lt slice base
                    nremaining (n + 1) (neq + 1)) := by
              simpa only [iflt, hsmaller, hlarger, Bool.false_eq_true,
                if_false] using hresult.traceSafe
            have hafterNextSafe : CountTraceSafe
                ((TraceResult.sortSliceKeysRead? slice
                  (base + Int.ofNat n)).bind fun next =>
                    if iflt lt next.key previous.key then
                      (reverseLastEqualTraced? valuesPresent slice base n neq).bind
                        fun reversed =>
                          if reversed.fuelExhausted then
                            TraceResult.pure
                              (descendingScanResult reversed.slice n 0 true)
                          else
                            descendingScanTraced? fuel valuesPresent lt
                              reversed.slice base nremaining (n + 1) 0
                    else if iflt lt previous.key next.key then
                      TraceResult.pure (descendingScanResult slice n neq false)
                    else
                      descendingScanTraced? fuel valuesPresent lt slice base
                        nremaining (n + 1) (neq + 1)) :=
              CountTraceSafe.bind _ _ next hnext hnextSafe hbranchSafe
            refine ⟨result, ?_⟩
            exact
              { resultEq := by
                  simpa only [descendingScanTraced?, hactive, if_true,
                    TraceResult.bind, hprevious, hnext, iflt, hsmaller,
                    hlarger, Bool.false_eq_true, if_false] using
                    hresult.resultEq
                resultFuel := hresult.resultFuel
                traceSafe := by
                  simp only [descendingScanTraced?, hactive, if_true]
                  exact CountTraceSafe.bind _ _ previous hprevious
                    hpreviousSafe hafterNextSafe
                exactErasure := erase_descendingScanTraced _ _ _ _ _ _ _ _
                lengthBounds :=
                  ⟨le_trans (by omega) hresult.lengthBounds.1,
                    hresult.lengthBounds.2⟩
                equalTailLt := hresult.equalTailLt
                valuesMode := hresult.valuesMode
                sizeEq := hresult.sizeEq }
      · let result := descendingScanResult slice n neq false
        refine ⟨result, ?_⟩
        exact
          { resultEq := by
              simp only [descendingScanTraced?, hactive, if_false]
              rfl
            resultFuel := rfl
            traceSafe := by
              simpa [descendingScanTraced?, hactive, result] using
                (CountTraceSafe.pure result)
            exactErasure := erase_descendingScanTraced _ _ _ _ _ _ _ _
            lengthBounds := ⟨le_rfl, hnUpper⟩
            equalTailLt := hneq
            valuesMode := hMode
            sizeEq := rfl }

private structure FinishDescendingSafetyPost
    (state : MergeState κ ν) (before : SortSlice κ ν) (base : Int)
    (nremaining n : Nat) (result : CountRunResult κ ν) : Prop where
  resultEq :
    (finishDescendingTraced? state before base nremaining n).result = some result
  resultFuel : result.fuelExhausted = false
  traceSafe :
    CountTraceSafe (finishDescendingTraced? state before base nremaining n)
  exactErasure :
    (finishDescendingTraced? state before base nremaining n).erase =
      finishDescending? state before base nremaining n
  lengthBounds : n ≤ result.length ∧ result.length ≤ nremaining
  valuesMode :
    SortSlice.ValuesModeInvariant state.a.hasValues result.slice
  sizeEq : result.slice.entries.size = before.entries.size

private theorem finishDescendingTraced_safe
    (state : MergeState κ ν) (slice : SortSlice κ ν) (base : Int)
    (nremaining n : Nat)
    (hrange : SortSlice.RangeInBounds slice base nremaining)
    (hnPositive : 1 ≤ n) (hnUpper : n ≤ nremaining)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues slice) :
    ∃ result,
      FinishDescendingSafetyPost state slice base nremaining n result := by
  rcases descendingScanTraced_safe nremaining state.a.hasValues
      state.key_compare slice base nremaining n 0 hrange hnPositive hnUpper
      (by omega) (by omega) hMode with ⟨descending, hdescending⟩
  have hrangeDescending :
      SortSlice.RangeInBounds descending.slice base nremaining :=
    hrange.of_size_eq hdescending.sizeEq
  rcases reverseLastEqualTraced_safe state.a.hasValues descending.slice base
      nremaining descending.length descending.equalTail hrangeDescending
      hdescending.lengthBounds.2 hdescending.equalTailLt
      hdescending.valuesMode with ⟨equalTailReversed, hequalTail⟩
  have hrangeEqualTail :
      SortSlice.RangeInBounds equalTailReversed.slice base nremaining :=
    hrangeDescending.of_size_eq hequalTail.sizeEq
  have hwholeRange : SortSlice.RangeInBounds equalTailReversed.slice base
      descending.length := by
    rcases hrangeEqualTail with ⟨hbase, hend⟩
    constructor
    · exact hbase
    · have hlengthCast :
        Int.ofNat descending.length ≤ Int.ofNat nremaining := by
        exact Int.ofNat_le.mpr hdescending.lengthBounds.2
      exact le_trans (by simpa [add_comm] using
        (add_le_add_left hlengthCast base)) hend
  rcases sortsliceReverse_safe state.a.hasValues equalTailReversed.slice base
      descending.length hwholeRange hequalTail.valuesMode with
    ⟨wholeReversed, hwhole⟩
  have hrangeWhole : SortSlice.RangeInBounds wholeReversed.slice base
      nremaining := hrangeEqualTail.of_size_eq hwhole.sizeEq
  rcases ascendingScanTraced_safe nremaining state.key_compare
      wholeReversed.slice base nremaining descending.length hrangeWhole
      (le_trans hnPositive hdescending.lengthBounds.1)
      hdescending.lengthBounds.2 (by omega) with ⟨extended, hextended⟩
  let result : CountRunResult κ ν :=
    { slice := wholeReversed.slice
      length := extended.length
      fuelExhausted := extended.fuelExhausted }
  have hdescendingSafe : CountTraceSafe
      (descendingScanTraced? nremaining state.a.hasValues state.key_compare
        slice base nremaining n 0) := hdescending.traceSafe
  have hequalSafe : CountTraceSafe
      (reverseLastEqualTraced? state.a.hasValues descending.slice base
        descending.length descending.equalTail) := hequalTail.traceSafe
  have hwholeSafe : CountTraceSafe
      (sortsliceReverseTraced? state.a.hasValues equalTailReversed.slice base
        descending.length) :=
    countTraceSafe_of_reverse _ _ _ _ _ hwhole
  have hextendedMapSafe : CountTraceSafe
      ((ascendingScanTraced? nremaining state.key_compare wholeReversed.slice
        base nremaining descending.length).map fun extended =>
          ({ slice := wholeReversed.slice
             length := extended.length
             fuelExhausted := extended.fuelExhausted } : CountRunResult κ ν)) :=
    CountTraceSafe.map _ _ hextended.traceSafe
  have hwholeContinuationSafe : CountTraceSafe
      ((sortsliceReverseTraced? state.a.hasValues equalTailReversed.slice base
        descending.length).bind fun wholeReversed =>
          if wholeReversed.fuelExhausted then
            TraceResult.pure
              ({ slice := wholeReversed.slice
                 length := descending.length
                 fuelExhausted := true } : CountRunResult κ ν)
          else
            (ascendingScanTraced? nremaining state.key_compare
              wholeReversed.slice base nremaining descending.length).map
                fun extended =>
                  ({ slice := wholeReversed.slice
                     length := extended.length
                     fuelExhausted := extended.fuelExhausted } :
                    CountRunResult κ ν)) := by
    apply CountTraceSafe.bind _ _ wholeReversed hwhole.resultEq hwholeSafe
    simpa [hwhole.resultFuel] using hextendedMapSafe
  have hequalContinuationSafe : CountTraceSafe
      ((reverseLastEqualTraced? state.a.hasValues descending.slice base
        descending.length descending.equalTail).bind fun equalTailReversed =>
          if equalTailReversed.fuelExhausted then
            TraceResult.pure
              ({ slice := equalTailReversed.slice
                 length := descending.length
                 fuelExhausted := true } : CountRunResult κ ν)
          else
            (sortsliceReverseTraced? state.a.hasValues equalTailReversed.slice
              base descending.length).bind fun wholeReversed =>
                if wholeReversed.fuelExhausted then
                  TraceResult.pure
                    ({ slice := wholeReversed.slice
                       length := descending.length
                       fuelExhausted := true } : CountRunResult κ ν)
                else
                  (ascendingScanTraced? nremaining state.key_compare
                    wholeReversed.slice base nremaining descending.length).map
                      fun extended =>
                        ({ slice := wholeReversed.slice
                           length := extended.length
                           fuelExhausted := extended.fuelExhausted } :
                          CountRunResult κ ν)) := by
    apply CountTraceSafe.bind _ _ equalTailReversed hequalTail.resultEq hequalSafe
    simpa [hequalTail.resultFuel] using hwholeContinuationSafe
  refine ⟨result, ?_⟩
  exact
    { resultEq := by
        simp only [finishDescendingTraced?, TraceResult.bind,
          hdescending.resultEq, hdescending.resultFuel, Bool.false_eq_true,
          if_false, hequalTail.resultEq, hequalTail.resultFuel,
          hwhole.resultEq, hwhole.resultFuel, TraceResult.map,
          hextended.resultEq]
        rfl
      resultFuel := hextended.resultFuel
      traceSafe := by
        simp only [finishDescendingTraced?]
        apply CountTraceSafe.bind _ _ descending hdescending.resultEq
          hdescendingSafe
        simpa [hdescending.resultFuel] using hequalContinuationSafe
      exactErasure := erase_finishDescendingTraced _ _ _ _ _
      lengthBounds :=
        ⟨le_trans hdescending.lengthBounds.1 hextended.lengthBounds.1,
          hextended.lengthBounds.2⟩
      valuesMode := hwhole.valuesMode
      sizeEq := hwhole.sizeEq.trans
        (hequalTail.sizeEq.trans hdescending.sizeEq) }

/-- Public safety certificate for natural-run detection. -/
structure CountRunSafetyPost
    (state : MergeState κ ν) (before : SortSlice κ ν) (base : Int)
    (nremaining : Nat) (result : CountRunResult κ ν) : Prop where
  resultEq :
    (countRunTraced? state before base nremaining).result = some result
  resultFuel : result.fuelExhausted = false
  traceFuel :
    (countRunTraced? state before base nremaining).trace.fuelExhausted = false
  accessesInBounds :
    (countRunTraced? state before base nremaining).trace.allAccessesInBounds
  tempAccessesLive :
    (countRunTraced? state before base nremaining).trace.tempPayloadAccessesLive
  noPushes :
    (countRunTraced? state before base nremaining).trace.pushDepths = []
  exactErasure :
    (countRunTraced? state before base nremaining).erase =
      countRun? state before base nremaining
  valuesMode :
    SortSlice.ValuesModeInvariant state.a.hasValues result.slice
  sizeEq : result.slice.entries.size = before.entries.size
  lengthBounds : 1 ≤ result.length ∧ result.length ≤ nremaining

private theorem countRunSafetyPost_of
    (state : MergeState κ ν) (slice : SortSlice κ ν) (base : Int)
    (nremaining : Nat) (result : CountRunResult κ ν)
    (hresult : (countRunTraced? state slice base nremaining).result = some result)
    (hresultFuel : result.fuelExhausted = false)
    (htrace : CountTraceSafe (countRunTraced? state slice base nremaining))
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues result.slice)
    (hsize : result.slice.entries.size = slice.entries.size)
    (hlength : 1 ≤ result.length ∧ result.length ≤ nremaining) :
    CountRunSafetyPost state slice base nremaining result :=
  { resultEq := hresult
    resultFuel := hresultFuel
    traceFuel := htrace.fuel
    accessesInBounds := htrace.bounds
    tempAccessesLive := htrace.tempLive
    noPushes := htrace.noPushes
    exactErasure := erase_countRunTraced _ _ _ _
    valuesMode := hMode
    sizeEq := hsize
    lengthBounds := hlength }

/-- Internal branch proof behind the compact public `countRun_safe` contract. -/
private theorem countRun_safe_core (state : MergeState κ ν)
    (slice : SortSlice κ ν)
    (base : Int) (nremaining : Nat)
    (hrange : SortSlice.RangeInBounds slice base nremaining)
    (hpositive : 0 < nremaining)
    (hsizeRepresentable : nremaining ≤ PY_SSIZE_T_MAX)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues slice) :
    ∃ result, CountRunSafetyPost state slice base nremaining result := by
  have hguard : 0 < nremaining ∧ nremaining ≤ PY_SSIZE_T_MAX :=
    ⟨hpositive, hsizeRepresentable⟩
  rcases ascendingScanTraced_safe nremaining state.key_compare slice base
      nremaining 1 hrange (by omega) (by omega) (by omega) with
    ⟨ascending, hascending⟩
  by_cases hcomplete : ascending.length = nremaining
  · let result : CountRunResult κ ν :=
      { slice := slice
        length := ascending.length
        fuelExhausted := false }
    have hcontinuationSafe : CountTraceSafe
        (if ascending.fuelExhausted then
          TraceResult.pure
            ({ slice := slice
               length := ascending.length
               fuelExhausted := true } : CountRunResult κ ν)
        else if ascending.length = nremaining then
          TraceResult.pure result
        else if 1 < ascending.length then
          (TraceResult.sortSliceKeysRead? slice base).bind fun first =>
            (TraceResult.sortSliceKeysRead? slice
              (base + Int.ofNat (ascending.length - 1))).bind fun last =>
                if iflt state.key_compare first.key last.key then
                  TraceResult.pure
                    { slice := slice
                      length := ascending.length
                      fuelExhausted := false }
                else
                  (sortsliceReverseTraced? state.a.hasValues slice base
                    ascending.length).bind fun reversed =>
                      if reversed.fuelExhausted then
                        TraceResult.pure
                          { slice := reversed.slice
                            length := ascending.length + 1
                            fuelExhausted := true }
                      else
                        finishDescendingTraced? state reversed.slice base
                          nremaining (ascending.length + 1)
        else
          finishDescendingTraced? state slice base nremaining
            (ascending.length + 1)) := by
      simpa [hascending.resultFuel, hcomplete] using
        (CountTraceSafe.pure result)
    have htrace : CountTraceSafe
        (countRunTraced? state slice base nremaining) := by
      simp only [countRunTraced?, hguard]
      exact CountTraceSafe.bind _ _ ascending hascending.resultEq
        hascending.traceSafe hcontinuationSafe
    refine ⟨result, ?_⟩
    apply countRunSafetyPost_of state slice base nremaining result
    · simp only [countRunTraced?]
      rw [if_pos hguard]
      simp only [TraceResult.bind, hascending.resultEq,
        hascending.resultFuel, Bool.false_eq_true, if_false, hcomplete,
        if_true]
      simp [TraceResult.pure, result, hcomplete]
    · rfl
    · exact htrace
    · exact hMode
    · rfl
    · exact
        ⟨by simpa [result, hcomplete] using hascending.lengthBounds.1,
          by simp [result, hcomplete]⟩
  · by_cases hlong : 1 < ascending.length
    · have hlengthUpper := hascending.lengthBounds.2
      have hlengthLt : ascending.length < nremaining := by omega
      have hfirstIndex : SortSlice.IndexInBounds slice base := by
        rcases hrange with ⟨hbase, hend⟩
        constructor
        · exact hbase
        · simp only [Int.ofNat_eq_natCast] at hend ⊢
          omega
      have hlastIndex : SortSlice.IndexInBounds slice
          (base + Int.ofNat (ascending.length - 1)) := by
        rcases hrange with ⟨hbase, hend⟩
        constructor
        · exact add_nonneg hbase (Int.natCast_nonneg _)
        · simp only [Int.ofNat_eq_natCast] at hend ⊢
          omega
      rcases SortSlice.read_eq_some_of_indexInBounds slice base hfirstIndex with
        ⟨first, hfirstRaw⟩
      rcases SortSlice.read_eq_some_of_indexInBounds slice
          (base + Int.ofNat (ascending.length - 1)) hlastIndex with
        ⟨last, hlastRaw⟩
      have hfirst :
          (TraceResult.sortSliceKeysRead? slice base).result = some first :=
        hfirstRaw
      have hlast :
          (TraceResult.sortSliceKeysRead? slice
            (base + Int.ofNat (ascending.length - 1))).result = some last :=
        hlastRaw
      have hfirstSafe := countKeyRead_safe slice base hfirstIndex
      have hlastSafe := countKeyRead_safe slice _ hlastIndex
      by_cases hincreasing :
          iflt state.key_compare first.key last.key = true
      · let result : CountRunResult κ ν :=
          { slice := slice
            length := ascending.length
            fuelExhausted := false }
        have htrace : CountTraceSafe
            (countRunTraced? state slice base nremaining) := by
          simp only [countRunTraced?, hguard]
          apply CountTraceSafe.bind _ _ ascending hascending.resultEq
            hascending.traceSafe
          simp only [hascending.resultFuel, Bool.false_eq_true, if_false,
            hcomplete, hlong, if_true]
          apply CountTraceSafe.bind _ _ first hfirst hfirstSafe
          apply CountTraceSafe.bind _ _ last hlast hlastSafe
          simpa only [hincreasing, if_true] using
            (CountTraceSafe.pure result)
        refine ⟨result, ?_⟩
        apply countRunSafetyPost_of state slice base nremaining result
        · simp only [countRunTraced?]
          rw [if_pos hguard]
          simp only [TraceResult.bind, hascending.resultEq,
            hascending.resultFuel, Bool.false_eq_true, if_false, hcomplete,
            hlong, if_true, hfirst, hlast, hincreasing]
          rfl
        · rfl
        · exact htrace
        · exact hMode
        · rfl
        · exact ⟨hascending.lengthBounds.1, hascending.lengthBounds.2⟩
      · have hprefixRange : SortSlice.RangeInBounds slice base
            ascending.length := by
          rcases hrange with ⟨hbase, hend⟩
          constructor
          · exact hbase
          · have hlengthCast :
                Int.ofNat ascending.length ≤ Int.ofNat nremaining :=
                Int.ofNat_le.mpr hascending.lengthBounds.2
            exact le_trans (by simpa [add_comm] using
              (add_le_add_left hlengthCast base)) hend
        rcases sortsliceReverse_safe state.a.hasValues slice base
            ascending.length hprefixRange hMode with ⟨reversed, hreverse⟩
        have hrangeReversed :
            SortSlice.RangeInBounds reversed.slice base nremaining :=
          hrange.of_size_eq hreverse.sizeEq
        rcases finishDescendingTraced_safe state reversed.slice base nremaining
            (ascending.length + 1) hrangeReversed (by omega) (by omega)
            hreverse.valuesMode with ⟨result, hfinish⟩
        have hreverseSafe :=
          countTraceSafe_of_reverse _ _ _ _ _ hreverse
        have hincreasing' :
            ¬state.key_compare first.key last.key = true := by
          simpa [iflt] using hincreasing
        have htrace : CountTraceSafe
            (countRunTraced? state slice base nremaining) := by
          simp only [countRunTraced?, hguard]
          apply CountTraceSafe.bind _ _ ascending hascending.resultEq
            hascending.traceSafe
          simp only [hascending.resultFuel, Bool.false_eq_true, if_false,
            hcomplete, hlong, if_true]
          apply CountTraceSafe.bind _ _ first hfirst hfirstSafe
          apply CountTraceSafe.bind _ _ last hlast hlastSafe
          simp only [iflt, hincreasing', Bool.false_eq_true, if_false]
          apply CountTraceSafe.bind _ _ reversed hreverse.resultEq hreverseSafe
          simpa [hreverse.resultFuel] using hfinish.traceSafe
        refine ⟨result, ?_⟩
        apply countRunSafetyPost_of state slice base nremaining result
        · simp only [countRunTraced?]
          rw [if_pos hguard]
          simp only [TraceResult.bind, hascending.resultEq,
            hascending.resultFuel, Bool.false_eq_true, if_false, hcomplete,
            hlong, if_true, hfirst, hlast, iflt, hincreasing',
            hreverse.resultEq, hreverse.resultFuel, hfinish.resultEq]
        · exact hfinish.resultFuel
        · exact htrace
        · exact hfinish.valuesMode
        · exact hfinish.sizeEq.trans hreverse.sizeEq
        · exact
            ⟨le_trans (by omega) hfinish.lengthBounds.1,
              hfinish.lengthBounds.2⟩
    · have hascendingLower := hascending.lengthBounds.1
      have hascendingUpper := hascending.lengthBounds.2
      have hascendingOne : ascending.length = 1 := by omega
      have honeNotComplete : ¬1 = nremaining := by
        simpa [hascendingOne] using hcomplete
      have hnremainingTwo : 2 ≤ nremaining := by omega
      rcases finishDescendingTraced_safe state slice base nremaining 2 hrange
          (by omega) hnremainingTwo hMode with ⟨result, hfinish⟩
      have htrace : CountTraceSafe
          (countRunTraced? state slice base nremaining) := by
        simp only [countRunTraced?, hguard]
        apply CountTraceSafe.bind _ _ ascending hascending.resultEq
          hascending.traceSafe
        simpa [hascending.resultFuel, hascendingOne, honeNotComplete,
          hlong] using hfinish.traceSafe
      refine ⟨result, ?_⟩
      apply countRunSafetyPost_of state slice base nremaining result
      · simp only [countRunTraced?]
        rw [if_pos hguard]
        simpa [TraceResult.bind, hascending.resultEq,
          hascending.resultFuel, hascendingOne, honeNotComplete, hlong]
          using hfinish.resultEq
      · exact hfinish.resultFuel
      · exact htrace
      · exact hfinish.valuesMode
      · exact hfinish.sizeEq
      · exact ⟨le_trans (by omega) hfinish.lengthBounds.1,
          hfinish.lengthBounds.2⟩

/-- On a nonempty, signed-size-representable in-bounds suffix, `count_run`
succeeds for an arbitrary Boolean comparator, uses no exhausted helper path,
preserves the explicit values mode and backing extent, and returns a run length
inside `[1, nremaining]`. -/
theorem countRun_safe (state : MergeState κ ν) (slice : SortSlice κ ν)
    (base : Int) (nremaining : Nat)
    (hrange : SortSlice.RangeInBounds slice base nremaining)
    (hpositive : 0 < nremaining)
    (hsizeRepresentable : nremaining ≤ PY_SSIZE_T_MAX)
    (hMode : SortSlice.ValuesModeInvariant state.a.hasValues slice) :
    ∃ result, CountRunSafetyPost state slice base nremaining result :=
  countRun_safe_core state slice base nremaining hrange hpositive
    hsizeRepresentable hMode

/-- Installing the returned slice changes no `MergeState` field other than
`data`; in particular pending runs, comparator, temporary storage, and all
adaptive counters remain frame-stable. -/
theorem countRun_install_frame (state : MergeState κ ν)
    (result : CountRunResult κ ν) :
    let after : MergeState κ ν := { state with data := result.slice }
    after.min_gallop = state.min_gallop ∧
    after.listlen = state.listlen ∧
    after.basekeys = state.basekeys ∧
    after.a = state.a ∧
    after.alloced = state.alloced ∧
    after.pending = state.pending ∧
    after.key_compare = state.key_compare ∧
    after.mr_current = state.mr_current ∧
    after.mr_e = state.mr_e ∧
    after.mr_mask = state.mr_mask := by
  simp

/-! ## Exact helper-order pins -/

/-- One active ascending step records the chosen Lean-model predecessor read,
then the next read, and only then the selected comparison branch.  The access
order is a property of this instrumentation; the comparator orientation is the
source-matching `next < previous`. -/
theorem ascendingScanTraced_step_trace_order
    (fuel : Nat) (lt : BoolComparator κ) (slice : SortSlice κ ν)
    (base : Int) (nremaining n : Nat)
    (previous next : SortSliceEntry κ ν)
    (hactive : n < nremaining)
    (hprevious :
      (TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat (n - 1))).result = some previous)
    (hnext :
      (TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat n)).result = some next) :
    (ascendingScanTraced? (fuel + 1) lt slice base nremaining n).trace =
      (TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat (n - 1))).trace.compose
      ((TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat n)).trace.compose
        (if iflt lt next.key previous.key then
          TraceResult.pure (ascendingScanResult n false)
        else
          ascendingScanTraced? fuel lt slice base nremaining (n + 1)).trace) := by
  simp only [ascendingScanTraced?, hactive, if_true]
  rw [TraceResult.trace_bind, hprevious]
  simp only
  rw [TraceResult.trace_bind, hnext]

/-- One active descending step has the same two-read instrumentation order;
after those reads the `next < previous` arm is selected before the reverse
comparison can control the branch. -/
theorem descendingScanTraced_step_trace_order
    (fuel : Nat) (valuesPresent : Bool) (lt : BoolComparator κ)
    (slice : SortSlice κ ν) (base : Int) (nremaining n neq : Nat)
    (previous next : SortSliceEntry κ ν)
    (hactive : n < nremaining)
    (hprevious :
      (TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat (n - 1))).result = some previous)
    (hnext :
      (TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat n)).result = some next) :
    (descendingScanTraced? (fuel + 1) valuesPresent lt slice base nremaining
      n neq).trace =
      (TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat (n - 1))).trace.compose
      ((TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat n)).trace.compose
        (if iflt lt next.key previous.key then
          (reverseLastEqualTraced? valuesPresent slice base n neq).bind
            fun reversed =>
              if reversed.fuelExhausted then
                TraceResult.pure
                  (descendingScanResult reversed.slice n 0 true)
              else
                descendingScanTraced? fuel valuesPresent lt reversed.slice
                  base nremaining (n + 1) 0
        else if iflt lt previous.key next.key then
          TraceResult.pure (descendingScanResult slice n neq false)
        else
          descendingScanTraced? fuel valuesPresent lt slice base nremaining
            (n + 1) (neq + 1)).trace) := by
  simp only [descendingScanTraced?, hactive, if_true]
  rw [TraceResult.trace_bind, hprevious]
  simp only
  rw [TraceResult.trace_bind, hnext]

/-- Conditioned equation pinning comparator priority: a true
`next < previous` answer selects the equality-block reversal/recursive arm,
independently of the reverse comparison's value.  Comparator calls are not
access-trace events, so this is a branch equation rather than a trace claim. -/
theorem descendingScanTraced_next_smaller_priority
    (fuel : Nat) (valuesPresent : Bool) (lt : BoolComparator κ)
    (slice : SortSlice κ ν) (base : Int) (nremaining n neq : Nat)
    (previous next : SortSliceEntry κ ν)
    (hactive : n < nremaining)
    (hprevious :
      (TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat (n - 1))).result = some previous)
    (hnext :
      (TraceResult.sortSliceKeysRead? slice
        (base + Int.ofNat n)).result = some next)
    (hsmaller : iflt lt next.key previous.key = true) :
    (descendingScanTraced? (fuel + 1) valuesPresent lt slice base nremaining
      n neq).result =
      ((reverseLastEqualTraced? valuesPresent slice base n neq).bind
        fun reversed =>
          if reversed.fuelExhausted then
            TraceResult.pure (descendingScanResult reversed.slice n 0 true)
          else
            descendingScanTraced? fuel valuesPresent lt reversed.slice base
              nremaining (n + 1) 0).result := by
  simp only [descendingScanTraced?, hactive, if_true, TraceResult.bind,
    hprevious, hnext, hsmaller]

/-- Successful descending completion appends traces in source-phase order:
descending scan, trailing operational-equivalence-block reversal, whole-prefix
reversal, then ascending extension. -/
theorem finishDescendingTraced_trace_order
    (state : MergeState κ ν) (slice : SortSlice κ ν) (base : Int)
    (nremaining n : Nat) (descending : DescendingScanResult κ ν)
    (equalTail : ReverseEqualResult κ ν)
    (whole : ReverseSliceResult κ ν)
    (hdescending :
      (descendingScanTraced? nremaining state.a.hasValues state.key_compare
        slice base nremaining n 0).result = some descending)
    (hdescendingFuel : descending.fuelExhausted = false)
    (hequal :
      (reverseLastEqualTraced? state.a.hasValues descending.slice base
        descending.length descending.equalTail).result = some equalTail)
    (hequalFuel : equalTail.fuelExhausted = false)
    (hwhole :
      (sortsliceReverseTraced? state.a.hasValues equalTail.slice base
        descending.length).result = some whole)
    (hwholeFuel : whole.fuelExhausted = false) :
    (finishDescendingTraced? state slice base nremaining n).trace =
      (descendingScanTraced? nremaining state.a.hasValues state.key_compare
        slice base nremaining n 0).trace.compose
      ((reverseLastEqualTraced? state.a.hasValues descending.slice base
        descending.length descending.equalTail).trace.compose
      ((sortsliceReverseTraced? state.a.hasValues equalTail.slice base
        descending.length).trace.compose
      (ascendingScanTraced? nremaining state.key_compare whole.slice base
        nremaining descending.length).trace)) := by
  simp [finishDescendingTraced?, TraceResult.trace_bind, hdescending,
    hdescendingFuel, hequal, hequalFuel, hwhole, hwholeFuel, TraceResult.map]

/-! ## Branch and failure anti-vacuity regressions -/

private def countRunRegressionState (slice : SortSlice Nat Nat) :
    MergeState Nat Nat :=
  { min_gallop := MIN_GALLOP
    listlen := slice.entries.size
    basekeys := 0
    data := slice
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending := #[]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

private def countRunSingletonSlice : SortSlice Nat Nat :=
  { entries := #[{ key := 7, value := none }] }

private def countRunAscendingSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 1, value := none }, { key := 2, value := none },
        { key := 3, value := none }, { key := 4, value := none }] }

private def countRunDescendingSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 4, value := none }, { key := 3, value := none },
        { key := 2, value := none }, { key := 1, value := none }] }

private def countRunGateSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 1, value := none }, { key := 3, value := none },
        { key := 2, value := none }] }

private def countRunTaggedEqualSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 3, value := some 30 }, { key := 2, value := some 20 },
        { key := 2, value := some 21 }, { key := 1, value := some 10 }] }

private def countRunValuesRegressionState (slice : SortSlice Nat Nat) :
    MergeState Nat Nat :=
  { countRunRegressionState slice with
    a := { cells := #[], backing := .inline, hasValues := true } }

private def countRunExtensionSlice : SortSlice Nat Nat :=
  { entries :=
      #[{ key := 3, value := none }, { key := 2, value := none },
        { key := 1, value := none }, { key := 3, value := none },
        { key := 4, value := none }, { key := 5, value := none },
        { key := 0, value := none }] }

private def countRunConstantTrueState (slice : SortSlice Nat Nat) :
    MergeState Nat Nat :=
  { countRunRegressionState slice with key_compare := fun _ _ => true }

/-- A singleton reaches the no-probe completion arm with length one. -/
theorem countRunTraced_singleton_regression :
    (countRunTraced? (countRunRegressionState countRunSingletonSlice)
      countRunSingletonSlice 0 1).result.map
        (fun result => (result.length, result.fuelExhausted,
          result.slice.entries.toList)) =
      some (1, false, countRunSingletonSlice.entries.toList) ∧
    (countRunTraced? (countRunRegressionState countRunSingletonSlice)
      countRunSingletonSlice 0 1).trace = AccessTrace.empty := by
  decide

/-- A full ascending run performs exactly the adjacent scan probes and does
not reread the endpoints in the post-scan direction check. -/
theorem countRunTraced_full_ascending_no_reread_regression :
    (countRunTraced? (countRunRegressionState countRunAscendingSlice)
      countRunAscendingSlice 0 4).result.map
        (fun result => (result.length, result.fuelExhausted,
          result.slice.entries.toList)) =
      some (4, false, countRunAscendingSlice.entries.toList) ∧
    (countRunTraced? (countRunRegressionState countRunAscendingSlice)
      countRunAscendingSlice 0 4).trace.accesses.map
        (fun event => (event.kind, event.region, event.index)) =
      [(.read, .inputKeys, 0), (.read, .inputKeys, 1),
       (.read, .inputKeys, 1), (.read, .inputKeys, 2),
       (.read, .inputKeys, 2), (.read, .inputKeys, 3)] := by
  decide

/-- A strict descending run reaches completion, reverses the whole prefix,
and returns the ascending sequence without exhausting fuel. -/
theorem countRunTraced_descending_regression :
    (countRunTraced? (countRunRegressionState countRunDescendingSlice)
      countRunDescendingSlice 0 4).result.map
        (fun result => (result.length, result.fuelExhausted,
          result.slice.entries.toList)) =
      some
        (4, false,
          [{ key := 1, value := none }, { key := 2, value := none },
           { key := 3, value := none }, { key := 4, value := none }]) ∧
    (countRunTraced? (countRunRegressionState countRunDescendingSlice)
      countRunDescendingSlice 0 4).trace.fuelExhausted = false := by
  decide

/-- The post-scan first/last gate is reachable: `[1,3,2]` discovers length
two, rereads indices zero and one, takes the true endpoint branch, and performs
no write. -/
theorem countRunTraced_first_last_gate_regression :
    (countRunTraced? (countRunRegressionState countRunGateSlice)
      countRunGateSlice 0 3).result.map
        (fun result => (result.length, result.fuelExhausted,
          result.slice.entries.toList)) =
      some (2, false, countRunGateSlice.entries.toList) ∧
    (countRunTraced? (countRunRegressionState countRunGateSlice)
      countRunGateSlice 0 3).trace.accesses.map
        (fun event => (event.kind, event.region, event.index)) =
      [(.read, .inputKeys, 0), (.read, .inputKeys, 1),
       (.read, .inputKeys, 1), (.read, .inputKeys, 2),
       (.read, .inputKeys, 0), (.read, .inputKeys, 1)] := by
  decide

/-- A tagged equal block is reversed locally before the whole descending
prefix.  The exact trace pins the local keys phase, local synchronized-values
phase, whole keys phase, and whole synchronized-values phase in that order;
the final equal keys retain payload order `20,21`. -/
theorem countRunTraced_tagged_equal_block_order_regression :
    (countRunTraced? (countRunValuesRegressionState countRunTaggedEqualSlice)
      countRunTaggedEqualSlice 0 4).result.map
        (fun result => (result.length, result.fuelExhausted,
          result.slice.entries.toList)) =
      some
        (4, false,
          [{ key := 1, value := some 10 },
           { key := 2, value := some 20 },
           { key := 2, value := some 21 },
           { key := 3, value := some 30 }]) ∧
    (countRunTraced? (countRunValuesRegressionState countRunTaggedEqualSlice)
      countRunTaggedEqualSlice 0 4).trace.accesses.map
        (fun event => (event.kind, event.region, event.index)) =
      [(.read, .inputKeys, 0), (.read, .inputKeys, 1),
       (.read, .inputKeys, 1), (.read, .inputKeys, 2),
       (.read, .inputKeys, 2), (.read, .inputKeys, 3),
       (.read, .inputKeys, 1), (.read, .inputKeys, 2),
       (.write, .inputKeys, 1), (.write, .inputKeys, 2),
       (.read, .synchronizedValues, 1),
       (.read, .synchronizedValues, 2),
       (.write, .synchronizedValues, 1),
       (.write, .synchronizedValues, 2),
       (.read, .inputKeys, 0), (.read, .inputKeys, 3),
       (.write, .inputKeys, 0), (.write, .inputKeys, 3),
       (.read, .inputKeys, 1), (.read, .inputKeys, 2),
       (.write, .inputKeys, 1), (.write, .inputKeys, 2),
       (.read, .synchronizedValues, 0),
       (.read, .synchronizedValues, 3),
       (.write, .synchronizedValues, 0),
       (.write, .synchronizedValues, 3),
       (.read, .synchronizedValues, 1),
       (.read, .synchronizedValues, 2),
       (.write, .synchronizedValues, 1),
       (.write, .synchronizedValues, 2)] := by
  decide

/-- After reversing the descending prefix `3,2,1`, the final ascending scan
extends through `3,4,5` and stops before the trailing zero. -/
theorem countRunTraced_descending_then_ascending_extension_regression :
    (countRunTraced? (countRunRegressionState countRunExtensionSlice)
      countRunExtensionSlice 0 7).result.map
        (fun result => (result.length, result.fuelExhausted,
          result.slice.entries.toList)) =
      some
        (6, false,
          [{ key := 1, value := none }, { key := 2, value := none },
           { key := 3, value := none }, { key := 3, value := none },
           { key := 4, value := none }, { key := 5, value := none },
           { key := 0, value := none }]) := by
  decide

/-- With a deliberately inconsistent constant-true comparator, the first
`next < previous` answer wins: the descending scan advances through the third
entry and returns length three.  This is an observable control-flow witness,
not a claim that comparator calls appear in `AccessTrace`. -/
theorem countRunTraced_constant_true_priority_regression :
    (countRunTraced? (countRunConstantTrueState countRunGateSlice)
      countRunGateSlice 0 3).result.map
        (fun result => (result.length, result.fuelExhausted)) =
      some (3, false) ∧
    (countRunTraced? (countRunConstantTrueState countRunGateSlice)
      countRunGateSlice 0 3).trace.accesses.map
        (fun event => event.index) = [0, 1, 1, 2, 0, 2, 0, 2] := by
  decide

/-- The active zero-fuel ascending arm exposes exhaustion in both the returned
helper result and trace. -/
theorem ascendingScanTraced_zero_fuel_active_regression :
    (ascendingScanTraced? 0 (fun (left right : Nat) => decide (left < right))
      countRunAscendingSlice 0 4 1).result.map
        (fun result => result.fuelExhausted) = some true ∧
    (ascendingScanTraced? 0 (fun (left right : Nat) => decide (left < right))
      countRunAscendingSlice 0 4 1).trace.fuelExhausted = true := by
  decide

/-- The analogous active zero-fuel descending arm is independently
observable. -/
theorem descendingScanTraced_zero_fuel_active_regression :
    (descendingScanTraced? 0 false
      (fun (left right : Nat) => decide (left < right))
      countRunDescendingSlice 0 4 2 0).result.map
        (fun result => result.fuelExhausted) = some true ∧
    (descendingScanTraced? 0 false
      (fun (left right : Nat) => decide (left < right))
      countRunDescendingSlice 0 4 2 0).trace.fuelExhausted = true := by
  decide

/-- The public assertion guard's zero-length failure arm is concrete and has
no fabricated accesses. -/
theorem countRunTraced_zero_remaining_failure_regression :
    (countRunTraced? (countRunRegressionState countRunSingletonSlice)
      countRunSingletonSlice 0 0).result = none ∧
    (countRunTraced? (countRunRegressionState countRunSingletonSlice)
      countRunSingletonSlice 0 0).trace = AccessTrace.empty := by
  decide

/-- An overstated remaining length preserves the successful first probe and
the rejected one-past probe, making the access-failure path non-vacuous. -/
theorem countRunTraced_oob_failure_regression :
    (countRunTraced? (countRunRegressionState countRunSingletonSlice)
      countRunSingletonSlice 0 2).result = none ∧
    (countRunTraced? (countRunRegressionState countRunSingletonSlice)
      countRunSingletonSlice 0 2).trace.accesses =
      [{ kind := .read, region := .inputKeys, index := 0, extent := 1 },
       { kind := .read, region := .inputKeys, index := 1, extent := 1 }] ∧
    ¬(countRunTraced? (countRunRegressionState countRunSingletonSlice)
      countRunSingletonSlice 0 2).trace.allAccessesInBounds := by
  decide

end CPythonListsort
