/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.ReverseSliceSafety

/-!
# Exact correctness of slice reversal

This file connects the executable `reverse_slice` transcription to a reusable
mathematical operation on half-open array ranges.  The specification retains
the prefix and suffix verbatim and reverses exactly the selected middle.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

namespace ReverseRangeSpec

/-- Replace the half-open range `[start, stop)` by its reversal. -/
def reverseRangeEntries (xs : Array α) (start stop : Nat) : Array α :=
  (xs.extract 0 start ++ (xs.extract start stop).reverse) ++
    xs.extract stop xs.size

/-- The reusable prefix/middle/suffix view of `reverseRange`. -/
theorem toList_reverseRange (xs : Array α) (start stop : Nat) :
    (reverseRangeEntries xs start stop).toList =
      xs.toList.take start ++
        (xs.toList.drop start |>.take (stop - start)).reverse ++
          xs.toList.drop stop := by
  simp [reverseRangeEntries, List.extract_eq_take_drop]

theorem size_reverseRange (xs : Array α) (start stop : Nat)
    (hstart : start ≤ stop) (hstop : stop ≤ xs.size) :
    (reverseRangeEntries xs start stop).size = xs.size := by
  simp [reverseRangeEntries]
  omega

theorem getElem?_reverseRange_before (xs : Array α) (start stop k : Nat)
    (hstart : start ≤ stop) (hstop : stop ≤ xs.size) (hk : k < start) :
    (reverseRangeEntries xs start stop)[k]? = xs[k]? := by
  have hstartSize : start ≤ xs.size := hstart.trans hstop
  have hprefixSize : (xs.extract 0 start).size = start := by
    simp
    omega
  have hmiddleSize : (xs.extract start stop).size = stop - start := by
    simp
    omega
  have hleftSize :
      (xs.extract 0 start ++ (xs.extract start stop).reverse).size = stop := by
    simp [hprefixSize, hmiddleSize]
    omega
  rw [reverseRangeEntries, Array.getElem?_append, hleftSize,
    if_pos (hk.trans_le hstart), Array.getElem?_append, hprefixSize,
    if_pos hk,
    Array.getElem?_extract]
  rw [if_pos (by simpa [hstartSize] using hk)]
  simp

theorem getElem?_reverseRange_inside (xs : Array α) (start stop k : Nat)
    (hstart : start ≤ stop) (hstop : stop ≤ xs.size)
    (hklo : start ≤ k) (hkhi : k < stop) :
    (reverseRangeEntries xs start stop)[k]? = xs[start + stop - 1 - k]? := by
  have hstartSize : start ≤ xs.size := hstart.trans hstop
  have hprefixSize : (xs.extract 0 start).size = start := by
    simp
    omega
  have hmiddleSize : (xs.extract start stop).size = stop - start := by
    simp
    omega
  have hleftSize :
      (xs.extract 0 start ++ (xs.extract start stop).reverse).size = stop := by
    simp [hprefixSize, hmiddleSize]
    omega
  have hoff : k - start < (xs.extract start stop).size := by
    simp [hmiddleSize]
    omega
  rw [reverseRangeEntries, Array.getElem?_append, hleftSize, if_pos hkhi,
    Array.getElem?_append, hprefixSize, if_neg (not_lt_of_ge hklo),
    Array.getElem?_reverse hoff, Array.getElem?_extract]
  rw [min_eq_left hstop, hmiddleSize]
  have hreverseIndex : stop - start - 1 - (k - start) < stop - start := by
    omega
  rw [if_pos hreverseIndex]
  congr 1
  omega

theorem getElem?_reverseRange_after (xs : Array α) (start stop k : Nat)
    (hstart : start ≤ stop) (hstop : stop ≤ xs.size) (hk : stop ≤ k) :
    (reverseRangeEntries xs start stop)[k]? = xs[k]? := by
  have hstartSize : start ≤ xs.size := hstart.trans hstop
  have hprefixSize : (xs.extract 0 start).size = start := by
    simp
    omega
  have hmiddleSize : (xs.extract start stop).size = stop - start := by
    simp
    omega
  have hleftSize :
      (xs.extract 0 start ++ (xs.extract start stop).reverse).size = stop := by
    simp [hprefixSize, hmiddleSize]
    omega
  rw [reverseRangeEntries, Array.getElem?_append, hleftSize,
    if_neg (not_lt_of_ge hk), Array.getElem?_extract]
  simp only [min_self]
  have hkIndex : stop + (k - stop) = k := Nat.add_sub_of_le hk
  by_cases hkSize : k < xs.size
  · have hoff : k - stop < xs.size - stop := by omega
    rw [if_pos hoff, hkIndex]
  · have hoff : ¬k - stop < xs.size - stop := by omega
    rw [if_neg hoff, Array.getElem?_eq_none (Nat.le_of_not_gt hkSize)]

/-- Reversing a valid range twice is the identity. -/
theorem reverseRange_involutive (xs : Array α) (start stop : Nat)
    (hstart : start ≤ stop) (hstop : stop ≤ xs.size) :
    reverseRangeEntries (reverseRangeEntries xs start stop) start stop = xs := by
  apply Array.ext_getElem?
  intro k
  have hsize := size_reverseRange xs start stop hstart hstop
  by_cases hkBefore : k < start
  · rw [getElem?_reverseRange_before _ _ _ _ hstart (by simpa [hsize]) hkBefore,
      getElem?_reverseRange_before _ _ _ _ hstart hstop hkBefore]
  by_cases hkInside : k < stop
  · have hklo : start ≤ k := Nat.le_of_not_gt hkBefore
    rw [getElem?_reverseRange_inside _ _ _ _ hstart (by simpa [hsize]) hklo hkInside]
    have hmirrorLo : start ≤ start + stop - 1 - k := by omega
    have hmirrorHi : start + stop - 1 - k < stop := by omega
    rw [getElem?_reverseRange_inside _ _ _ _ hstart hstop hmirrorLo hmirrorHi]
    congr 1
    omega
  · have hkAfter : stop ≤ k := Nat.le_of_not_gt hkInside
    rw [getElem?_reverseRange_after _ _ _ _ hstart (by simpa [hsize]) hkAfter,
      getElem?_reverseRange_after _ _ _ _ hstart hstop hkAfter]

theorem reverseRange_empty (xs : Array α) (start : Nat)
    (hstart : start ≤ xs.size) :
    reverseRangeEntries xs start start = xs := by
  apply Array.ext_getElem?
  intro k
  by_cases hk : k < start
  · exact getElem?_reverseRange_before xs start start k le_rfl hstart hk
  · exact getElem?_reverseRange_after xs start start k le_rfl hstart
      (Nat.le_of_not_gt hk)

/-- Reversing a range preserves the multiset of whole array entries. -/
theorem reverseRange_perm (xs : Array α) (start stop : Nat)
    (hstart : start ≤ stop) (_hstop : stop ≤ xs.size) :
    (reverseRangeEntries xs start stop).toList.Perm xs.toList := by
  rw [toList_reverseRange]
  have hsplit :
      xs.toList.take start ++ (xs.toList.drop start).take (stop - start) ++
          xs.toList.drop stop = xs.toList := by
    have hinner := List.take_append_drop (stop - start) (xs.toList.drop start)
    rw [List.drop_drop, Nat.add_sub_of_le hstart] at hinner
    rw [← List.take_append_drop start xs.toList]
    simpa [List.append_assoc] using congrArg (xs.toList.take start ++ ·) hinner
  calc
    xs.toList.take start ++
          ((xs.toList.drop start).take (stop - start)).reverse ++
            xs.toList.drop stop
        |>.Perm
      (xs.toList.take start ++
          (xs.toList.drop start).take (stop - start) ++
            xs.toList.drop stop) :=
      ((List.Perm.refl _).append (List.reverse_perm _)).append
        (List.Perm.refl _)
    _ = xs.toList := hsplit

end ReverseRangeSpec

private theorem reverseSliceLoop_succ_nat
    (fuel : Nat) (xs : Array (SortSliceEntry κ ν)) (i j : Nat)
    (hi : i < xs.size) (hj : j < xs.size) (hij : i < j) :
    reverseSliceLoop? (fuel + 1) ({ entries := xs } : SortSlice κ ν)
        (Int.ofNat i) (Int.ofNat j) =
      reverseSliceLoop? fuel
        ({ entries := xs.swap i j hi hj } : SortSlice κ ν)
        (Int.ofNat (i + 1)) (Int.ofNat (j - 1)) := by
  simp only [reverseSliceLoop?]
  have hijInt : Int.ofNat i < Int.ofNat j := Int.ofNat_lt.mpr hij
  rw [if_pos hijInt]
  simp [SortSlice.read?, SortSlice.write?, hi, hj, Array.swap]
  congr
  all_goals omega

private def ReverseRangeLoopInvariant
    (original current : Array α) (start stop i j : Nat) : Prop :=
  current.size = original.size ∧
    start ≤ i ∧ i ≤ stop ∧ start ≤ j ∧ j < stop ∧
    i + j + 1 = start + stop ∧
    ∀ k, current[k]? =
      if i ≤ k ∧ k ≤ j then original[k]?
      else (ReverseRangeSpec.reverseRangeEntries original start stop)[k]?

private theorem ReverseRangeLoopInvariant.terminal
    {original current : Array α} {start stop i j : Nat}
    (hstart : start < stop) (hstop : stop ≤ original.size)
    (hinv : ReverseRangeLoopInvariant original current start stop i j)
    (hterminal : ¬i < j) :
    current = ReverseRangeSpec.reverseRangeEntries original start stop := by
  rcases hinv with ⟨hsize, histart, _histop, hjstart, hjstop, hsum, hpoint⟩
  apply Array.ext_getElem?
  intro k
  rw [hpoint]
  split
  · rename_i hinside
    have hik : i = k := by omega
    have hjk : j = k := by omega
    subst i
    subst j
    rw [ReverseRangeSpec.getElem?_reverseRange_inside original start stop k
      hstart.le hstop (by omega) (by omega)]
    congr 1
    omega
  · rfl

private theorem ReverseRangeLoopInvariant.swap_shrink
    {original current : Array α} {start stop i j : Nat}
    (hstart : start < stop) (hstop : stop ≤ original.size)
    (hinv : ReverseRangeLoopInvariant original current start stop i j)
    (hactive : i < j) :
    ReverseRangeLoopInvariant original
      (current.swap i j (by rcases hinv with ⟨hsize, _, _, _, _hjstop, _⟩; omega)
        (by rcases hinv with ⟨hsize, _, _, _, _hjstop, _⟩; omega))
      start stop (i + 1) (j - 1) := by
  rcases hinv with ⟨hsize, histart, histop, hjstart, hjstop, hsum, hpoint⟩
  have hi : i < current.size := by omega
  have hj : j < current.size := by omega
  have hjpos : 0 < j := by omega
  refine ⟨by simp [hsize], by omega, by omega, by omega, by omega, by omega, ?_⟩
  intro k
  rw [Array.getElem?_swap hi hj]
  by_cases hkj : k = j
  · subst k
    rw [if_pos rfl, ← Array.getElem?_eq_getElem hi, hpoint]
    have hold : i ≤ i ∧ i ≤ j := ⟨le_rfl, hactive.le⟩
    rw [if_pos hold]
    have hnew : ¬(i + 1 ≤ j ∧ j ≤ j - 1) := by omega
    rw [if_neg hnew]
    symm
    rw [ReverseRangeSpec.getElem?_reverseRange_inside original start stop j
      hstart.le hstop (by omega) hjstop]
    congr 1
    omega
  · by_cases hki : k = i
    · subst k
      rw [if_neg (by exact Ne.symm (ne_of_lt hactive)), if_pos rfl,
        ← Array.getElem?_eq_getElem hj, hpoint]
      have hold : i ≤ j ∧ j ≤ j := ⟨hactive.le, le_rfl⟩
      rw [if_pos hold]
      have hnew : ¬(i + 1 ≤ i ∧ i ≤ j - 1) := by omega
      rw [if_neg hnew]
      symm
      rw [ReverseRangeSpec.getElem?_reverseRange_inside original start stop i
        hstart.le hstop histart (by omega)]
      congr 1
      omega
    · rw [if_neg (Ne.symm hkj), if_neg (Ne.symm hki), hpoint]
      by_cases hold : i ≤ k ∧ k ≤ j
      · have hnew : i + 1 ≤ k ∧ k ≤ j - 1 := by omega
        rw [if_pos hold, if_pos hnew]
      · have hnew : ¬(i + 1 ≤ k ∧ k ≤ j - 1) := by omega
        rw [if_neg hold, if_neg hnew]

private theorem reverseSliceLoop_correct_of_invariant
    (fuel : Nat) (original current : Array (SortSliceEntry κ ν))
    (start stop i j : Nat)
    (hstart : start < stop) (hstop : stop ≤ original.size)
    (hinv : ReverseRangeLoopInvariant original current start stop i j)
    (hfuel : j - i ≤ fuel) :
    ∃ result,
      reverseSliceLoop? fuel ({ entries := current } : SortSlice κ ν)
          (Int.ofNat i) (Int.ofNat j) = some result ∧
        result.fuelExhausted = false ∧
        result.slice.entries =
          ReverseRangeSpec.reverseRangeEntries original start stop := by
  induction fuel generalizing current i j with
  | zero =>
      have hterminal : ¬i < j := by omega
      have hentries := hinv.terminal hstart hstop hterminal
      refine ⟨{ slice := { entries := current }, fuelExhausted := false }, ?_⟩
      simp [reverseSliceLoop?, hentries,
        Nat.le_of_not_gt hterminal]
  | succ fuel ih =>
      by_cases hactive : i < j
      · have hinv' :=
          ReverseRangeLoopInvariant.swap_shrink hstart hstop hinv hactive
        rcases hinv with ⟨hsize, _histart, _histop, _hjstart, hjstop,
          _hsum, _hpoint⟩
        have hi : i < current.size := by omega
        have hj : j < current.size := by omega
        have hfuel' : j - 1 - (i + 1) ≤ fuel := by omega
        rw [reverseSliceLoop_succ_nat fuel current i j hi hj hactive]
        exact ih _ _ _ hinv' hfuel'
      · have hentries := hinv.terminal hstart hstop hactive
        refine ⟨{ slice := { entries := current }, fuelExhausted := false }, ?_⟩
        simp [reverseSliceLoop?, hentries,
          Nat.le_of_not_gt hactive]

private theorem reverseSliceLoop_nat_correct
    (slice : SortSlice κ ν) (start stop : Nat)
    (hstart : start < stop) (hstop : stop ≤ slice.entries.size) :
    ∃ result,
      reverseSliceLoop? (stop - start) slice (Int.ofNat start)
          (Int.ofNat (stop - 1)) = some result ∧
        result.fuelExhausted = false ∧
        result.slice.entries =
          ReverseRangeSpec.reverseRangeEntries slice.entries start stop := by
  have hinv : ReverseRangeLoopInvariant slice.entries slice.entries start stop
      start (stop - 1) := by
    refine ⟨rfl, le_rfl, hstart.le, ?_, by omega, by omega, ?_⟩
    · omega
    · intro k
      split
      · rfl
      · rename_i houtside
        by_cases hk : k < start
        · exact (ReverseRangeSpec.getElem?_reverseRange_before
            slice.entries start stop k hstart.le hstop hk).symm
        · have hk : stop ≤ k := by omega
          exact (ReverseRangeSpec.getElem?_reverseRange_after
            slice.entries start stop k hstart.le hstop hk).symm
  exact reverseSliceLoop_correct_of_invariant (stop - start) slice.entries
    slice.entries start stop start (stop - 1) hstart hstop hinv (by omega)

/-- On a valid natural-number half-open range, the executable transcription
returns exactly the prefix, reversed middle, and suffix specification. -/
theorem reverseSlice_nat_correct
    (slice : SortSlice κ ν) (start count : Nat)
    (hrange : start + count ≤ slice.entries.size) :
    ∃ result,
      reverseSlice? slice (Int.ofNat start) (Int.ofNat (start + count)) =
          some result ∧
        result.fuelExhausted = false ∧
        result.slice.entries =
          ReverseRangeSpec.reverseRangeEntries slice.entries start
            (start + count) := by
  cases count with
  | zero =>
      have hempty := ReverseRangeSpec.reverseRange_empty slice.entries start
        (by simpa using hrange)
      refine ⟨{ slice := slice, fuelExhausted := false }, ?_, rfl, hempty.symm⟩
      simp [reverseSlice?]
  | succ count =>
      have hactive : start < start + (count + 1) := by omega
      have hordered : Int.ofNat start ≤ Int.ofNat (start + (count + 1)) :=
        Int.ofNat_le.mpr hactive.le
      have hactiveInt : Int.ofNat start < Int.ofNat (start + (count + 1)) :=
        Int.ofNat_lt.mpr hactive
      rcases reverseSliceLoop_nat_correct slice start (start + (count + 1))
          hactive hrange with ⟨result, hresult, hfuel, hexact⟩
      refine ⟨result, ?_, hfuel, hexact⟩
      simp only [reverseSlice?, hordered, if_true, hactiveInt]
      have hfuelArg :
          (Int.ofNat (start + (count + 1)) - Int.ofNat start).toNat =
            start + (count + 1) - start := by simp
      have hlastArg :
          Int.ofNat (start + (count + 1)) - 1 =
            Int.ofNat (start + (count + 1) - 1) := by
        simp
        omega
      rw [hfuelArg, hlastArg]
      exact hresult

private theorem rangeInBounds_toNat_add_le
    (slice : SortSlice κ ν) (base : Int) (n : Nat)
    (hrange : SortSlice.RangeInBounds slice base n) :
    base.toNat + n ≤ slice.entries.size := by
  have hbaseEq : Int.ofNat base.toNat = base :=
    Int.toNat_of_nonneg hrange.1
  apply Int.ofNat_le.mp
  calc
    Int.ofNat (base.toNat + n) =
        Int.ofNat base.toNat + Int.ofNat n := by simp
    _ = base + Int.ofNat n := by rw [hbaseEq]
    _ ≤ Int.ofNat slice.entries.size := hrange.2

/-- Exact correctness at the signed-pointer public boundary used by
`sortslice_reverse`.  The range premise is precisely the existing safety
premise; no ordering property or element-level assumption is introduced. -/
theorem sortsliceReverse_correct
    (slice : SortSlice κ ν) (base : Int) (n : Nat)
    (hrange : SortSlice.RangeInBounds slice base n) :
    ∃ result,
      sortsliceReverse? slice base n = some result ∧
        result.fuelExhausted = false ∧
        result.slice.entries =
          ReverseRangeSpec.reverseRangeEntries slice.entries base.toNat
            (base.toNat + n) := by
  have hbase : 0 ≤ base := hrange.1
  have hbaseEq : Int.ofNat base.toNat = base := Int.toNat_of_nonneg hbase
  have hrangeNat := rangeInBounds_toNat_add_le slice base n hrange
  rcases reverseSlice_nat_correct slice base.toNat n hrangeNat with
    ⟨result, hresult, hfuel, hexact⟩
  refine ⟨result, ?_, hfuel, hexact⟩
  unfold sortsliceReverse?
  rw [← hbaseEq]
  simpa using hresult

private theorem sortsliceReverse_involutive_from_result
    (slice : SortSlice κ ν) (base : Int) (n : Nat)
    (hrange : SortSlice.RangeInBounds slice base n)
    (first : ReverseSliceResult κ ν)
    (hfirst : sortsliceReverse? slice base n = some first) :
    ∃ second,
      sortsliceReverse? first.slice base n = some second ∧
        second.fuelExhausted = false ∧
        second.slice = slice := by
  rcases sortsliceReverse_correct slice base n hrange with
    ⟨certifiedFirst, hcertifiedFirst, _hfirstFuel, hfirstEntries⟩
  rw [hfirst] at hcertifiedFirst
  injection hcertifiedFirst with heq
  subst certifiedFirst
  have hbaseStop := rangeInBounds_toNat_add_le slice base n hrange
  have hfirstSize : first.slice.entries.size = slice.entries.size := by
    rw [hfirstEntries]
    exact ReverseRangeSpec.size_reverseRange slice.entries base.toNat
      (base.toNat + n) (by omega) hbaseStop
  have hfirstRange : SortSlice.RangeInBounds first.slice base n := by
    simpa [SortSlice.RangeInBounds, hfirstSize] using hrange
  rcases sortsliceReverse_correct first.slice base n hfirstRange with
    ⟨second, hsecond, hsecondFuel, hsecondEntries⟩
  refine ⟨second, hsecond, hsecondFuel, ?_⟩
  apply congrArg SortSlice.mk
  rw [hsecondEntries, hfirstEntries]
  exact ReverseRangeSpec.reverseRange_involutive slice.entries base.toNat
    (base.toNat + n) (by omega) hbaseStop

/-- Public exactness packet for the genuinely traced two-physical-phase
execution.  `safety` is the existing reviewed safety/erasure certificate;
the remaining fields identify its result with the mathematical reversal. -/
structure SortsliceReverseCorrectnessPost
    (before : SortSlice κ ν) (valuesPresent : Bool) (base : Int) (n : Nat)
    (result : ReverseSliceResult κ ν) : Prop where
  safety : ReverseSliceSafetyPost before valuesPresent base n result
  entriesEq :
    result.slice.entries =
      ReverseRangeSpec.reverseRangeEntries before.entries base.toNat
        (base.toNat + n)
  prefixMiddleSuffix :
    result.slice.entries.toList =
      before.entries.toList.take base.toNat ++
        (before.entries.toList.drop base.toNat |>.take n).reverse ++
          before.entries.toList.drop (base.toNat + n)
  wholeEntries : result.slice.entries.toList.Perm before.entries.toList
  beforeFrame :
    ∀ k, k < base.toNat → result.slice.entries[k]? = before.entries[k]?
  afterFrame :
    ∀ k, base.toNat + n ≤ k →
      result.slice.entries[k]? = before.entries[k]?
  involutiveExecution :
    ∃ second,
      sortsliceReverse? result.slice base n = some second ∧
        second.fuelExhausted = false ∧
        second.slice = before

/-- The synchronized traced evaluator returns the exact range reversal while
retaining every safety, erasure, fuel, extent, and values-mode guarantee from
`sortsliceReverse_safe`.  The proof deliberately recovers the untraced result
through `ReverseSliceSafetyPost.exactErasure`, so correctness is about the same
execution whose accesses were checked. -/
theorem sortsliceReverseTraced_correct
    (valuesPresent : Bool) (slice : SortSlice κ ν) (base : Int) (n : Nat)
    (hrange : SortSlice.RangeInBounds slice base n)
    (hMode : SortSlice.ValuesModeInvariant valuesPresent slice) :
    ∃ result,
      SortsliceReverseCorrectnessPost slice valuesPresent base n result := by
  rcases sortsliceReverse_safe valuesPresent slice base n hrange hMode with
    ⟨result, hsafety⟩
  have hraw : sortsliceReverse? slice base n = some result := by
    have hresult := hsafety.resultEq
    change (sortsliceReverseTraced? valuesPresent slice base n).erase =
      some result at hresult
    rw [hsafety.exactErasure] at hresult
    exact hresult
  rcases sortsliceReverse_correct slice base n hrange with
    ⟨rawResult, hrawResult, _hrawFuel, hentries⟩
  rw [hraw] at hrawResult
  injection hrawResult with heq
  subst rawResult
  have hbaseStop := rangeInBounds_toNat_add_le slice base n hrange
  refine ⟨result, hsafety, hentries, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hentries, ReverseRangeSpec.toList_reverseRange]
    simp
  · rw [hentries]
    exact ReverseRangeSpec.reverseRange_perm slice.entries base.toNat
      (base.toNat + n) (by omega) hbaseStop
  · intro k hk
    rw [hentries]
    exact ReverseRangeSpec.getElem?_reverseRange_before slice.entries
      base.toNat (base.toNat + n) k (by omega) hbaseStop hk
  · intro k hk
    rw [hentries]
    exact ReverseRangeSpec.getElem?_reverseRange_after slice.entries
      base.toNat (base.toNat + n) k (by omega) hbaseStop hk
  · exact sortsliceReverse_involutive_from_result slice base n hrange result hraw

/-- Executing a valid reversal twice succeeds both times and restores every
whole key/payload entry. -/
theorem sortsliceReverse_involutive
    (slice : SortSlice κ ν) (base : Int) (n : Nat)
    (hrange : SortSlice.RangeInBounds slice base n) :
    ∃ first second,
      sortsliceReverse? slice base n = some first ∧
        sortsliceReverse? first.slice base n = some second ∧
        second.fuelExhausted = false ∧
        second.slice = slice := by
  rcases sortsliceReverse_correct slice base n hrange with
    ⟨first, hfirst, _hfirstFuel, _hfirstEntries⟩
  rcases sortsliceReverse_involutive_from_result slice base n hrange first hfirst with
    ⟨second, hsecond, hsecondFuel, hrestored⟩
  exact ⟨first, second, hfirst, hsecond, hsecondFuel, hrestored⟩

end CPythonListsort
