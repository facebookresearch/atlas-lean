/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Assembly.GallopLeftSafety
import Code.Assembly.GallopRightSafety
import Code.Assembly.Order

/-!
# Correctness of the two biased gallops

This module proves the partition contracts of the actual `gallopLeft?` and
`gallopRight?` transcriptions.  The search proof is factored through the direct
key-source evaluator used by the safety development; the public theorems erase
that evaluator back to the reviewed `SortSlice` functions.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- The key at logical source index `i` compares strictly before `key`. -/
def GallopBefore (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (i : Nat) : Prop :=
  ∃ entry, source.read? (Int.ofNat i) = some entry ∧ lt entry.key key = true

/-- The key compares strictly before the key at logical source index `i`. -/
def GallopAfter (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (i : Nat) : Prop :=
  ∃ entry, source.read? (Int.ofNat i) = some entry ∧ lt key entry.key = true

/-- A Boolean search predicate is a prefix on the searched range. -/
def GallopPrefix (predicate : Nat → Prop) (n : Nat) : Prop :=
  ∀ i j, i < j → j < n → predicate j → predicate i

/-- Exact boundary contract for a prefix predicate. -/
def GallopPartition (predicate : Nat → Prop) (n k : Nat) : Prop :=
  k ≤ n ∧
    (∀ i, i < k → predicate i) ∧
    (∀ i, k ≤ i → i < n → ¬predicate i)

/-- Pointwise sortedness of the physical run searched by a gallop.  This is
the index-facing form of the project's `Sorted` specification: no later key
strictly precedes an earlier key. -/
def GallopSortedRange (lt : BoolComparator κ)
    (source : GallopKeySource κ ν) (n : Nat) : Prop :=
  ∀ i j (_hi : i < n) (_hj : j < n), i < j →
    ∀ earlier later,
      source.read? (Int.ofNat i) = some earlier →
      source.read? (Int.ofNat j) = some later →
      lt later.key earlier.key = false

/-- A mathematical key array is exactly the `n` logical keys exposed by a
gallop source.  The size equality prevents a caller from padding or truncating
the array, and the pointwise clause identifies both the successful physical
read and its key. -/
def GallopKeyArrayAgreement (source : GallopKeySource κ ν) (n : Nat)
    (keys : Array κ) : Prop :=
  keys.size = n ∧
    ∀ i, i < n → ∃ entry,
      source.read? (Int.ofNat i) = some entry ∧
        keys[i]? = some entry.key

/-- The project's shared `Sorted` predicate, together with exact pointwise
source/key-array agreement, supplies the index-facing sorted-range premise
used by the algorithmic gallop theorems. -/
theorem gallopSortedRange_of_sorted (lt : BoolComparator κ)
    (source : GallopKeySource κ ν) (n : Nat) (keys : Array κ)
    (hagrees : GallopKeyArrayAgreement source n keys)
    (hsorted : Sorted lt keys) :
    GallopSortedRange lt source n := by
  rcases hagrees with ⟨hsize, hagrees⟩
  intro i j hi hj hij earlier later heariler hlater
  rcases hagrees i hi with ⟨sourceEarlier, hsourceEarlier, hkeyEarlier⟩
  rcases hagrees j hj with ⟨sourceLater, hsourceLater, hkeyLater⟩
  have hsourceEarlierEq : sourceEarlier = earlier :=
    Option.some.inj (hsourceEarlier.symm.trans heariler)
  have hsourceLaterEq : sourceLater = later :=
    Option.some.inj (hsourceLater.symm.trans hlater)
  subst sourceEarlier
  subst sourceLater
  have hiKeys : i < keys.size := by omega
  have hjKeys : j < keys.size := by omega
  have hgetEarlier : keys[i]? = some keys[i] := by simp [hiKeys]
  have hgetLater : keys[j]? = some keys[j] := by simp [hjKeys]
  have hearlierKey : earlier.key = keys[i] :=
    Option.some.inj (hkeyEarlier.symm.trans hgetEarlier)
  have hlaterKey : later.key = keys[j] :=
    Option.some.inj (hkeyLater.symm.trans hgetLater)
  have hnot := (sorted_iff_no_later_precedes lt keys).1 hsorted
    i j hiKeys hjKeys hij
  apply Bool.eq_false_of_not_eq_true
  intro hcompare
  apply hnot
  simpa [hearlierKey, hlaterKey] using hcompare

private theorem read_false_of_not_before
    (lt : BoolComparator κ) (source : GallopKeySource κ ν) (key : κ)
    {i : Nat} {entry : SortSliceEntry κ ν}
    (hread : source.read? (Int.ofNat i) = some entry)
    (hcompare : ¬lt entry.key key = true) :
    ¬GallopBefore lt source key i := by
  rintro ⟨other, hother, hotherCompare⟩
  have : other = entry := Option.some.inj (hother.symm.trans hread)
  subst other
  exact hcompare hotherCompare

private theorem read_not_after_of_dual_true
    (lt : BoolComparator κ) (source : GallopKeySource κ ν) (key : κ)
    {i : Nat} {entry : SortSliceEntry κ ν}
    (hread : source.read? (Int.ofNat i) = some entry)
    (hcompare : gallopComparatorDual lt entry.key key = true) :
    ¬GallopAfter lt source key i := by
  have hfalse : lt key entry.key = false := by
    simpa [gallopComparatorDual] using hcompare
  rintro ⟨other, hother, hotherCompare⟩
  have : other = entry := Option.some.inj (hother.symm.trans hread)
  subst other
  simp [hfalse] at hotherCompare

private theorem read_after_of_dual_false
    (lt : BoolComparator κ) (source : GallopKeySource κ ν) (key : κ)
    {i : Nat} {entry : SortSliceEntry κ ν}
    (hread : source.read? (Int.ofNat i) = some entry)
    (hcompare : ¬gallopComparatorDual lt entry.key key = true) :
    GallopAfter lt source key i := by
  refine ⟨entry, hread, ?_⟩
  cases hvalue : lt key entry.key <;>
    simp [gallopComparatorDual, hvalue] at hcompare ⊢

/-! ## Generic lower-bound search -/

private theorem gallopLeftBinaryFromSource_partition
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (lower upper n : Nat)
    (hvalid : source.ValidRange n)
    (hprefix : GallopPrefix (GallopBefore lt source key) n)
    (hlowerUpper : lower ≤ upper) (hupper : upper ≤ n)
    (hbefore : ∀ i, i < lower → GallopBefore lt source key i)
    (hafter : ∀ i, upper ≤ i → i < n → ¬GallopBefore lt source key i)
    (hbudget : upper - lower ≤ fuel) :
    ∃ result,
      gallopLeftBinaryFromSource? fuel lt source key lower upper = some result ∧
      result.fuelExhausted = false ∧
      GallopPartition (GallopBefore lt source key) n result.index := by
  induction fuel generalizing lower upper with
  | zero =>
      have heq : lower = upper := by omega
      subst upper
      refine ⟨⟨lower, false⟩, ?_, rfl, hupper, hbefore, hafter⟩
      simp [gallopLeftBinaryFromSource?]
  | succ fuel ih =>
      by_cases hsearch : lower < upper
      · let middle := lower + (upper - lower) / 2
        have hlowerMiddle : lower ≤ middle := by
          dsimp [middle]
          omega
        have hmiddleUpper : middle < upper := by
          dsimp [middle]
          omega
        have hmiddleN : middle < n := by omega
        rcases source.read_eq_some hvalid hmiddleN with ⟨entry, hread⟩
        have hread' :
            source.read? (Int.ofNat (lower + (upper - lower) / 2)) =
              some entry := by
          simpa only [middle] using hread
        by_cases hcompare : iflt lt entry.key key = true
        · have hcompareRaw : lt entry.key key = true := by
            simpa only [iflt] using hcompare
          have hmiddleBefore : GallopBefore lt source key middle :=
            ⟨entry, hread, hcompareRaw⟩
          have hbefore' :
              ∀ i, i < middle + 1 → GallopBefore lt source key i := by
            intro i hi
            by_cases him : i = middle
            · simpa [him] using hmiddleBefore
            · exact hprefix i middle (by omega) hmiddleN hmiddleBefore
          have hbudget' : upper - (middle + 1) ≤ fuel := by
            dsimp [middle]
            omega
          rcases ih (middle + 1) upper (by omega) hupper hbefore' hafter
              hbudget' with ⟨result, hresult, hfuel, hpartition⟩
          refine ⟨result, ?_, hfuel, hpartition⟩
          rw [gallopLeftBinaryFromSource?, if_pos hsearch]
          simp only [gallopBindOptionAcross]
          rw [hread']
          simp only [if_pos hcompare]
          simpa only [middle] using hresult
        · have hcompareRaw : ¬lt entry.key key = true := by
            simpa only [iflt] using hcompare
          have hmiddleNot : ¬GallopBefore lt source key middle :=
            read_false_of_not_before lt source key hread hcompareRaw
          have hafter' :
              ∀ i, middle ≤ i → i < n → ¬GallopBefore lt source key i := by
            intro i hmi hin hpred
            by_cases him : i = middle
            · exact hmiddleNot (him ▸ hpred)
            · exact hmiddleNot (hprefix middle i (by omega) hin hpred)
          have hbudget' : middle - lower ≤ fuel := by
            dsimp [middle]
            omega
          rcases ih lower middle hlowerMiddle (by omega) hbefore hafter'
              hbudget' with ⟨result, hresult, hfuel, hpartition⟩
          refine ⟨result, ?_, hfuel, hpartition⟩
          rw [gallopLeftBinaryFromSource?, if_pos hsearch]
          simp only [gallopBindOptionAcross]
          rw [hread']
          simp only [if_neg hcompare]
          simpa only [middle] using hresult
      · have heq : lower = upper := by omega
        subst upper
        refine ⟨⟨lower, false⟩, ?_, rfl, hupper, hbefore, hafter⟩
        simp [gallopLeftBinaryFromSource?]

/-! ## Exponential bracketing -/

private theorem gallopLeftRightExponential_partition
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (hint maxOffset lastOffset offset n : Nat)
    (hvalid : source.ValidRange n)
    (hprefix : GallopPrefix (GallopBefore lt source key) n)
    (hwindow : hint + maxOffset = n) (hnmax : n ≤ PY_LIST_MAX)
    (hoffsetPositive : 0 < offset) (hlastOffset : lastOffset < offset)
    (hlastMax : lastOffset < maxOffset)
    (hbudget : maxOffset ≤ fuel + offset)
    (hbefore : ∀ i, i < hint + lastOffset + 1 →
      GallopBefore lt source key i) :
    ∃ result,
      gallopLeftRightExponentialFromSource? fuel lt source key hint maxOffset
          lastOffset offset = some result ∧
      result.fuelExhausted = false ∧
      result.lastOffset < result.offset ∧
      result.lastOffset < maxOffset ∧
      (∀ i, i < hint + result.lastOffset + 1 →
        GallopBefore lt source key i) ∧
      (∀ i, hint + min result.offset maxOffset ≤ i → i < n →
        ¬GallopBefore lt source key i) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
      have hstop : ¬offset < maxOffset := by omega
      refine ⟨⟨lastOffset, offset, false⟩, ?_, rfl, hlastOffset, hlastMax,
        hbefore, ?_⟩
      · simp [gallopLeftRightExponentialFromSource?, hstop]
      · intro i hi hin
        change hint + min offset maxOffset ≤ i at hi
        have : hint + min offset maxOffset = n := by
          rw [Nat.min_eq_right (by omega)]
          exact hwindow
        omega
  | succ fuel ih =>
      by_cases hprobe : offset < maxOffset
      · have hindex : hint + offset < n := by omega
        rcases source.read_eq_some hvalid hindex with ⟨entry, hread⟩
        have hread' :
            source.read? (Int.ofNat hint + Int.ofNat offset) = some entry := by
          simpa using hread
        by_cases hcompare : iflt lt entry.key key = true
        · have hguard := gallop_doubling_guard hprobe (by omega : maxOffset ≤ n)
            hnmax
          have hcompareRaw : lt entry.key key = true := by
            simpa only [iflt] using hcompare
          have hpoint : GallopBefore lt source key (hint + offset) :=
            ⟨entry, hread, hcompareRaw⟩
          have hbefore' : ∀ i, i < hint + offset + 1 →
              GallopBefore lt source key i := by
            intro i hi
            by_cases hieq : i = hint + offset
            · simpa [hieq] using hpoint
            · exact hprefix i (hint + offset) (by omega) hindex hpoint
          rcases ih offset (2 * offset + 1) (by omega) (by omega) hprobe
              (by omega) hbefore' with
            ⟨result, hresult, hfuel, horder, hlast, hbeforeResult,
              hafterResult⟩
          refine ⟨result, ?_, hfuel, horder, hlast, hbeforeResult,
            hafterResult⟩
          rw [gallopLeftRightExponentialFromSource?, if_pos hprobe]
          simp only [gallopBindOptionAcross]
          rw [hread]
          simp only [if_pos hcompare, if_pos hguard]
          exact hresult
        · have hcompareRaw : ¬lt entry.key key = true := by
            simpa only [iflt] using hcompare
          have hnot : ¬GallopBefore lt source key (hint + offset) :=
            read_false_of_not_before lt source key hread hcompareRaw
          refine ⟨⟨lastOffset, offset, false⟩, ?_, rfl, hlastOffset,
            hlastMax, hbefore, ?_⟩
          · rw [gallopLeftRightExponentialFromSource?, if_pos hprobe]
            simp only [gallopBindOptionAcross]
            rw [hread]
            simp only [if_neg hcompare]
          · intro i hi hin hpred
            have hcap : min offset maxOffset = offset := Nat.min_eq_left (Nat.le_of_lt hprobe)
            rw [hcap] at hi
            by_cases hieq : i = hint + offset
            · exact hnot (hieq ▸ hpred)
            · exact hnot (hprefix (hint + offset) i (by omega) hin hpred)
      · refine ⟨⟨lastOffset, offset, false⟩, ?_, rfl, hlastOffset,
          hlastMax, hbefore, ?_⟩
        · simp [gallopLeftRightExponentialFromSource?, hprobe]
        · intro i hi hin
          have hcap : min offset maxOffset = maxOffset := Nat.min_eq_right (by omega)
          rw [hcap, hwindow] at hi
          omega

private theorem gallopLeftLeftExponential_partition
    (fuel : Nat) (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (key : κ) (hint maxOffset lastOffset offset n : Nat)
    (hvalid : source.ValidRange n)
    (hprefix : GallopPrefix (GallopBefore lt source key) n)
    (hmax : maxOffset = hint + 1) (hnmax : n ≤ PY_LIST_MAX)
    (hhint : hint < n)
    (hoffsetPositive : 0 < offset) (hlastOffset : lastOffset < offset)
    (hlastMax : lastOffset < maxOffset)
    (hbudget : maxOffset ≤ fuel + offset)
    (hafter : ∀ i, hint - lastOffset ≤ i → i < n →
      ¬GallopBefore lt source key i) :
    ∃ result,
      gallopLeftLeftExponentialFromSource? fuel lt source key hint maxOffset
          lastOffset offset = some result ∧
      result.fuelExhausted = false ∧
      result.lastOffset < result.offset ∧
      result.lastOffset < maxOffset ∧
      (∀ i, i < hint + 1 - min result.offset maxOffset →
        GallopBefore lt source key i) ∧
      (∀ i, hint - result.lastOffset ≤ i → i < n →
        ¬GallopBefore lt source key i) := by
  induction fuel generalizing lastOffset offset with
  | zero =>
      have hstop : ¬offset < maxOffset := by omega
      refine ⟨⟨lastOffset, offset, false⟩, ?_, rfl, hlastOffset, hlastMax,
        ?_, hafter⟩
      · simp [gallopLeftLeftExponentialFromSource?, hstop]
      · intro i hi
        have hcap : min offset maxOffset = maxOffset := Nat.min_eq_right (by omega)
        rw [hcap, hmax] at hi
        omega
  | succ fuel ih =>
      by_cases hprobe : offset < maxOffset
      · have hoffsetHint : offset ≤ hint := by omega
        have hindex : hint - offset < n := by omega
        have hindexEq :
            Int.ofNat hint - Int.ofNat offset = Int.ofNat (hint - offset) := by
          exact (Int.ofNat_sub hoffsetHint).symm
        rcases source.read_eq_some hvalid hindex with ⟨entry, hreadNat⟩
        have hread : source.read? (Int.ofNat hint - Int.ofNat offset) =
            some entry := by rw [hindexEq]; exact hreadNat
        by_cases hcompare : iflt lt entry.key key = true
        · have hcompareRaw : lt entry.key key = true := by
            simpa only [iflt] using hcompare
          have hpoint : GallopBefore lt source key (hint - offset) :=
            ⟨entry, hreadNat, hcompareRaw⟩
          have hcap : min offset maxOffset = offset := Nat.min_eq_left (by omega)
          refine ⟨⟨lastOffset, offset, false⟩, ?_, rfl, hlastOffset,
            hlastMax, ?_, hafter⟩
          · rw [gallopLeftLeftExponentialFromSource?, if_pos hprobe]
            simp only [gallopBindOptionAcross]
            rw [hread]
            simp only [if_pos hcompare]
          · intro i hi
            rw [hcap] at hi
            by_cases hieq : i = hint - offset
            · simpa [hieq] using hpoint
            · exact hprefix i (hint - offset) (by omega) hindex hpoint
        · have hguard := gallop_doubling_guard hprobe (by omega : maxOffset ≤ n)
            hnmax
          have hcompareRaw : ¬lt entry.key key = true := by
            simpa only [iflt] using hcompare
          have hnot : ¬GallopBefore lt source key (hint - offset) :=
            read_false_of_not_before lt source key hreadNat hcompareRaw
          have hafter' : ∀ i, hint - offset ≤ i → i < n →
              ¬GallopBefore lt source key i := by
            intro i hii hin hpred
            by_cases hieq : i = hint - offset
            · exact hnot (hieq ▸ hpred)
            · exact hnot (hprefix (hint - offset) i (by omega) hin hpred)
          rcases ih offset (2 * offset + 1) (by omega) (by omega) hprobe
              (by omega) hafter' with
            ⟨result, hresult, hfuel, horder, hlast, hbeforeResult,
              hafterResult⟩
          refine ⟨result, ?_, hfuel, horder, hlast, hbeforeResult,
            hafterResult⟩
          rw [gallopLeftLeftExponentialFromSource?, if_pos hprobe]
          simp only [gallopBindOptionAcross]
          rw [hread]
          simp only [if_neg hcompare, if_pos hguard]
          exact hresult
      · refine ⟨⟨lastOffset, offset, false⟩, ?_, rfl, hlastOffset,
          hlastMax, ?_, hafter⟩
        · simp [gallopLeftLeftExponentialFromSource?, hprobe]
        · intro i hi
          have hcap : min offset maxOffset = maxOffset := Nat.min_eq_right (by omega)
          rw [hcap, hmax] at hi
          omega

/-! ## Complete direct-source lower bound -/

private theorem gallopLeftFromSource_partition
    (state : MergeState κ ν) (source : GallopKeySource κ ν)
    (key : κ) (n hint : Nat)
    (hvalid : source.ValidRange n)
    (hprefix : GallopPrefix (GallopBefore state.key_compare source key) n)
    (hn : 0 < n) (hhint : hint < n) (hnmax : n ≤ PY_LIST_MAX) :
    ∃ result,
      gallopLeftFromSource? state source key n hint = some result ∧
      result.fuelExhausted = false ∧
      GallopPartition (GallopBefore state.key_compare source key) n result.index := by
  have hnSsize : n ≤ PY_SSIZE_T_MAX := by
    norm_num [PY_LIST_MAX, PY_SSIZE_T_MAX, PY_OBJECT_PTR_BYTES] at hnmax ⊢
    omega
  have hinput : 0 < n ∧ hint < n ∧ n ≤ PY_SSIZE_T_MAX :=
    ⟨hn, hhint, hnSsize⟩
  rcases source.read_eq_some hvalid hhint with ⟨hinted, hhinted⟩
  by_cases hcompare : iflt state.key_compare hinted.key key = true
  · have hcompareRaw : state.key_compare hinted.key key = true := by
      simpa only [iflt] using hcompare
    have hhintedBefore :
        GallopBefore state.key_compare source key hint :=
      ⟨hinted, hhinted, hcompareRaw⟩
    have hbefore : ∀ i, i < hint + 1 →
        GallopBefore state.key_compare source key i := by
      intro i hi
      by_cases hieq : i = hint
      · simpa [hieq] using hhintedBefore
      · exact hprefix i hint (by omega) hhint hhintedBefore
    rcases gallopLeftRightExponential_partition (n + 1) state.key_compare
        source key hint (n - hint) 0 1 n hvalid hprefix (by omega) hnmax
        (by omega) (by omega) (by omega) (by omega) hbefore with
      ⟨exponential, hexponential, hexponentialFuel, hexponentialOrder,
        hexponentialMax, hbeforeWindow, hafterWindow⟩
    let capped := min exponential.offset (n - hint)
    let lower := hint + exponential.lastOffset + 1
    let upper := hint + capped
    have hlowerUpper : lower ≤ upper := by
      dsimp [lower, upper, capped]
      omega
    have hupper : upper ≤ n := by
      dsimp [upper, capped]
      omega
    have hbudget : upper - lower ≤ n + 1 := by omega
    rcases gallopLeftBinaryFromSource_partition (n + 1) state.key_compare
        source key lower upper n hvalid hprefix hlowerUpper hupper
        (by simpa [lower, Nat.add_assoc] using hbeforeWindow)
        (by simpa [upper, capped] using hafterWindow) hbudget with
      ⟨result, hbinary, hresultFuel, hpartition⟩
    have hfinish :
        finishGallopLeftFromSource? (n + 1) state.key_compare source key n
            (Int.ofNat exponential.lastOffset + Int.ofNat hint)
            (Int.ofNat capped + Int.ofNat hint) false =
          gallopLeftBinaryFromSource? (n + 1) state.key_compare source key
            lower upper := by
      unfold finishGallopLeftFromSource?
      have houter :
          (-1 : Int) ≤ Int.ofNat exponential.lastOffset + Int.ofNat hint ∧
          Int.ofNat exponential.lastOffset + Int.ofNat hint <
            Int.ofNat capped + Int.ofNat hint ∧
          Int.ofNat capped + Int.ofNat hint ≤ Int.ofNat n := by
        simp only [Int.ofNat_eq_natCast]
        dsimp [capped]
        omega
      rw [if_pos houter]
      have hinner :
          0 ≤ Int.ofNat exponential.lastOffset + Int.ofNat hint + 1 ∧
          0 ≤ Int.ofNat capped + Int.ofNat hint := by
        constructor <;> omega
      rw [if_pos hinner]
      have hlowerInt :
          (Int.ofNat exponential.lastOffset + Int.ofNat hint + 1).toNat =
            lower := by
        simp only [Int.ofNat_eq_natCast]
        dsimp [lower]
        omega
      have hupperInt :
          (Int.ofNat capped + Int.ofNat hint).toNat = upper := by
        simp only [Int.ofNat_eq_natCast]
        dsimp [upper]
        omega
      simp
      have hlowerInt' :
          (((exponential.lastOffset : Int) + (hint : Int) + 1).toNat) =
            lower := by simpa only [Int.ofNat_eq_natCast] using hlowerInt
      have hupperInt' :
          (((capped : Int) + (hint : Int)).toNat) = upper := by
        simpa only [Int.ofNat_eq_natCast] using hupperInt
      congr 2
    refine ⟨result, ?_, hresultFuel, hpartition⟩
    rw [gallopLeftFromSource?, if_pos hinput]
    simp only [gallopBindOptionAcross, hhinted, if_pos hcompare,
      hexponential]
    rw [Option.bind_eq_bind, Option.bind_some]
    rw [hexponentialFuel]
    change finishGallopLeftFromSource? (n + 1) state.key_compare source key n
        (Int.ofNat exponential.lastOffset + Int.ofNat hint)
        (Int.ofNat capped + Int.ofNat hint) false = some result
    rw [hfinish]
    exact hbinary
  · have hcompareRaw : ¬state.key_compare hinted.key key = true := by
      simpa only [iflt] using hcompare
    have hhintedNot :
        ¬GallopBefore state.key_compare source key hint :=
      read_false_of_not_before state.key_compare source key hhinted hcompareRaw
    have hafter : ∀ i, hint ≤ i → i < n →
        ¬GallopBefore state.key_compare source key i := by
      intro i hii hin hpred
      by_cases hieq : i = hint
      · exact hhintedNot (hieq ▸ hpred)
      · exact hhintedNot (hprefix hint i (by omega) hin hpred)
    rcases gallopLeftLeftExponential_partition (n + 1) state.key_compare
        source key hint (hint + 1) 0 1 n hvalid hprefix rfl hnmax hhint
        (by omega) (by omega) (by omega) (by omega) hafter with
      ⟨exponential, hexponential, hexponentialFuel, hexponentialOrder,
        hexponentialMax, hbeforeWindow, hafterWindow⟩
    let capped := min exponential.offset (hint + 1)
    let lower := hint + 1 - capped
    let upper := hint - exponential.lastOffset
    have hlowerUpper : lower ≤ upper := by
      dsimp [lower, upper, capped]
      omega
    have hupper : upper ≤ n := by
      dsimp [upper]
      omega
    have hbudget : upper - lower ≤ n + 1 := by omega
    rcases gallopLeftBinaryFromSource_partition (n + 1) state.key_compare
        source key lower upper n hvalid hprefix hlowerUpper hupper
        (by simpa [lower] using hbeforeWindow)
        (by simpa [upper] using hafterWindow) hbudget with
      ⟨result, hbinary, hresultFuel, hpartition⟩
    have hcapped : capped ≤ hint + 1 := by
      exact Nat.min_le_right _ _
    have hlast : exponential.lastOffset ≤ hint := by omega
    have hlowerInt :
        (Int.ofNat hint - Int.ofNat capped + 1).toNat = lower := by
      simp only [Int.ofNat_eq_natCast]
      dsimp [lower]
      omega
    have hupperInt :
        (Int.ofNat hint - Int.ofNat exponential.lastOffset).toNat = upper := by
      simp only [Int.ofNat_eq_natCast]
      dsimp [upper]
      omega
    have hfinish :
        finishGallopLeftFromSource? (n + 1) state.key_compare source key n
            (Int.ofNat hint - Int.ofNat capped)
            (Int.ofNat hint - Int.ofNat exponential.lastOffset) false =
          gallopLeftBinaryFromSource? (n + 1) state.key_compare source key
            lower upper := by
      unfold finishGallopLeftFromSource?
      have houter :
          (-1 : Int) ≤ Int.ofNat hint - Int.ofNat capped ∧
          Int.ofNat hint - Int.ofNat capped <
            Int.ofNat hint - Int.ofNat exponential.lastOffset ∧
          Int.ofNat hint - Int.ofNat exponential.lastOffset ≤ Int.ofNat n := by
        simp only [Int.ofNat_eq_natCast]
        omega
      rw [if_pos houter]
      have hinner :
          0 ≤ Int.ofNat hint - Int.ofNat capped + 1 ∧
          0 ≤ Int.ofNat hint - Int.ofNat exponential.lastOffset := by
        simp only [Int.ofNat_eq_natCast]
        omega
      rw [if_pos hinner]
      simp
      have hlowerInt' :
          (((hint : Int) - (capped : Int) + 1).toNat) = lower := by
        simpa only [Int.ofNat_eq_natCast] using hlowerInt
      have hupperInt' :
          (((hint : Int) - (exponential.lastOffset : Int)).toNat) = upper := by
        simpa only [Int.ofNat_eq_natCast] using hupperInt
      congr 2
    refine ⟨result, ?_, hresultFuel, hpartition⟩
    rw [gallopLeftFromSource?, if_pos hinput]
    simp only [gallopBindOptionAcross, hhinted, if_neg hcompare,
      hexponential]
    rw [Option.bind_eq_bind, Option.bind_some]
    rw [hexponentialFuel]
    change finishGallopLeftFromSource? (n + 1) state.key_compare source key n
        (Int.ofNat hint - Int.ofNat capped)
        (Int.ofNat hint - Int.ofNat exponential.lastOffset) false = some result
    rw [hfinish]
    exact hbinary

/-! ## Sortedness supplies the two monotone search predicates -/

private theorem gallopBefore_prefix_of_sorted
    (lt : BoolComparator κ) (source : GallopKeySource κ ν) (key : κ) (n : Nat)
    (hvalid : source.ValidRange n) (horder : BoolStrictWeakOrder lt)
    (hsorted : GallopSortedRange lt source n) :
    GallopPrefix (GallopBefore lt source key) n := by
  intro i j hij hj hjBefore
  rcases hjBefore with ⟨later, hlater, hlaterKey⟩
  rcases source.read_eq_some hvalid (by omega : i < n) with ⟨earlier, heariler⟩
  have hlaterEarlierFalse :=
    hsorted i j (by omega) hj hij earlier later heariler hlater
  have hlaterEarlier : ¬lt later.key earlier.key = true := by
    simp [hlaterEarlierFalse]
  by_cases hearilerKey : lt earlier.key key = true
  · exact ⟨earlier, heariler, hearilerKey⟩
  · by_cases hearilerLater : lt earlier.key later.key = true
    · exact False.elim (hearilerKey
        (horder.trans earlier.key later.key key hearilerLater hlaterKey))
    · by_cases hkeyEarlier : lt key earlier.key = true
      · exact False.elim (hlaterEarlier
          (horder.trans later.key key earlier.key hlaterKey hkeyEarlier))
      · have hkeyEarlierIncomp :
            ¬lt key earlier.key = true ∧ ¬lt earlier.key key = true :=
          ⟨hkeyEarlier, hearilerKey⟩
        have hearilerLaterIncomp :
            ¬lt earlier.key later.key = true ∧
              ¬lt later.key earlier.key = true :=
          ⟨hearilerLater, hlaterEarlier⟩
        have hkeyLaterIncomp := horder.incomp_trans key earlier.key later.key
          hkeyEarlierIncomp hearilerLaterIncomp
        exact False.elim (hkeyLaterIncomp.2 hlaterKey)

private theorem gallopAfter_suffix_of_sorted
    (lt : BoolComparator κ) (source : GallopKeySource κ ν) (key : κ) (n : Nat)
    (hvalid : source.ValidRange n) (horder : BoolStrictWeakOrder lt)
    (hsorted : GallopSortedRange lt source n) :
    ∀ i j, i < j → j < n → GallopAfter lt source key i →
      GallopAfter lt source key j := by
  intro i j hij hj hiAfter
  rcases hiAfter with ⟨earlier, heariler, hkeyEarlier⟩
  rcases source.read_eq_some hvalid hj with ⟨later, hlater⟩
  have hlaterEarlierFalse :=
    hsorted i j (by omega) hj hij earlier later heariler hlater
  have hlaterEarlier : ¬lt later.key earlier.key = true := by
    simp [hlaterEarlierFalse]
  by_cases hkeyLater : lt key later.key = true
  · exact ⟨later, hlater, hkeyLater⟩
  · by_cases hearilerLater : lt earlier.key later.key = true
    · exact False.elim (hkeyLater
        (horder.trans key earlier.key later.key hkeyEarlier hearilerLater))
    · by_cases hlaterKey : lt later.key key = true
      · exact False.elim (hlaterEarlier
          (horder.trans later.key key earlier.key hlaterKey hkeyEarlier))
      · have hearilerLaterIncomp :
            ¬lt earlier.key later.key = true ∧
              ¬lt later.key earlier.key = true :=
          ⟨hearilerLater, hlaterEarlier⟩
        have hlaterKeyIncomp :
            ¬lt later.key key = true ∧ ¬lt key later.key = true :=
          ⟨hlaterKey, hkeyLater⟩
        have hearilerKeyIncomp := horder.incomp_trans earlier.key later.key key
          hearilerLaterIncomp hlaterKeyIncomp
        exact False.elim (hearilerKeyIncomp.2 hkeyEarlier)

private theorem gallopDualBefore_prefix_of_sorted
    (lt : BoolComparator κ) (source : GallopKeySource κ ν) (key : κ) (n : Nat)
    (hvalid : source.ValidRange n) (horder : BoolStrictWeakOrder lt)
    (hsorted : GallopSortedRange lt source n) :
    GallopPrefix (GallopBefore (gallopComparatorDual lt) source key) n := by
  have hsuffix := gallopAfter_suffix_of_sorted lt source key n hvalid horder hsorted
  intro i j hij hj hjBefore
  rcases hjBefore with ⟨later, hlater, hdualLater⟩
  have hlaterNotAfter : ¬GallopAfter lt source key j :=
    read_not_after_of_dual_true lt source key hlater hdualLater
  rcases source.read_eq_some hvalid (by omega : i < n) with ⟨earlier, heariler⟩
  by_cases hafter : lt key earlier.key = true
  · exact False.elim (hlaterNotAfter
      (hsuffix i j hij hj ⟨earlier, heariler, hafter⟩))
  · refine ⟨earlier, heariler, ?_⟩
    have hfalse : lt key earlier.key = false :=
      Bool.eq_false_of_not_eq_true hafter
    simp [gallopComparatorDual, hfalse]

/-! ## Public exact partition contracts -/

/-- Exact left-biased partition on the reviewed materialized slice. -/
def GallopLeftPartition (lt : BoolComparator κ) (slice : SortSlice κ ν)
    (base : Int) (key : κ) (n k : Nat) : Prop :=
  k ≤ n ∧
    (∀ i, i < k → ∃ entry,
      slice.read? (base + Int.ofNat i) = some entry ∧
        lt entry.key key = true) ∧
    (∀ i, k ≤ i → i < n → ∃ entry,
      slice.read? (base + Int.ofNat i) = some entry ∧
        lt entry.key key = false)

/-- Exact right-biased partition on the reviewed materialized slice. -/
def GallopRightPartition (lt : BoolComparator κ) (slice : SortSlice κ ν)
    (base : Int) (key : κ) (n k : Nat) : Prop :=
  k ≤ n ∧
    (∀ i, i < k → ∃ entry,
      slice.read? (base + Int.ofNat i) = some entry ∧
        lt key entry.key = false) ∧
    (∀ i, k ≤ i → i < n → ∃ entry,
      slice.read? (base + Int.ofNat i) = some entry ∧
        lt key entry.key = true)

private theorem leftPartition_to_slice
    (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (slice : SortSlice κ ν) (base : Int) (key : κ) (n k : Nat)
    (hvalid : source.ValidRange n)
    (hagrees : source.AgreesWithSlice slice base n)
    (hpartition : GallopPartition (GallopBefore lt source key) n k) :
    GallopLeftPartition lt slice base key n k := by
  rcases hpartition with ⟨hk, hbefore, hafter⟩
  refine ⟨hk, ?_, ?_⟩
  · intro i hi
    rcases hbefore i hi with ⟨entry, hread, hcompare⟩
    have hin : i < n := by omega
    have hagree := hagrees (Int.ofNat i) (Int.natCast_nonneg i)
      (Int.ofNat_lt.mpr hin)
    exact ⟨entry, hagree.symm.trans hread, hcompare⟩
  · intro i hki hin
    rcases source.read_eq_some hvalid hin with ⟨entry, hread⟩
    have hagree := hagrees (Int.ofNat i) (Int.natCast_nonneg i)
      (Int.ofNat_lt.mpr hin)
    have hnot := hafter i hki hin
    have hcompare : lt entry.key key = false := by
      apply Bool.eq_false_of_not_eq_true
      intro htrue
      exact hnot ⟨entry, hread, htrue⟩
    exact ⟨entry, hagree.symm.trans hread, hcompare⟩

private theorem dualPartition_to_right_slice
    (lt : BoolComparator κ) (source : GallopKeySource κ ν)
    (slice : SortSlice κ ν) (base : Int) (key : κ) (n k : Nat)
    (hvalid : source.ValidRange n)
    (hagrees : source.AgreesWithSlice slice base n)
    (hpartition : GallopPartition
      (GallopBefore (gallopComparatorDual lt) source key) n k) :
    GallopRightPartition lt slice base key n k := by
  rcases hpartition with ⟨hk, hbefore, hafter⟩
  refine ⟨hk, ?_, ?_⟩
  · intro i hi
    rcases hbefore i hi with ⟨entry, hread, hdual⟩
    have hin : i < n := by omega
    have hagree := hagrees (Int.ofNat i) (Int.natCast_nonneg i)
      (Int.ofNat_lt.mpr hin)
    have hcompare : lt key entry.key = false := by
      simpa [gallopComparatorDual] using hdual
    exact ⟨entry, hagree.symm.trans hread, hcompare⟩
  · intro i hki hin
    rcases source.read_eq_some hvalid hin with ⟨entry, hread⟩
    have hagree := hagrees (Int.ofNat i) (Int.natCast_nonneg i)
      (Int.ofNat_lt.mpr hin)
    have hnot := hafter i hki hin
    have hcompare : lt key entry.key = true := by
      by_contra hfalse
      have hrawFalse : lt key entry.key = false :=
        Bool.eq_false_of_not_eq_true hfalse
      apply hnot
      refine ⟨entry, hread, ?_⟩
      simp [gallopComparatorDual, hrawFalse]
    exact ⟨entry, hagree.symm.trans hread, hcompare⟩

/-- Correctness of the actual left-biased transcription.  The result is the
lower bound: strict predecessors lie before it, and no strict predecessor lies
at or after it. -/
theorem gallopLeft_correct (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (slice : SortSlice κ ν)
    (base : Int) (key : κ) (n hint : Nat)
    (hvalid : source.ValidRange n)
    (hagrees : source.AgreesWithSlice slice base n)
    (horder : BoolStrictWeakOrder state.key_compare)
    (hsorted : GallopSortedRange state.key_compare source n)
    (hn : 0 < n) (hhint : hint < n) (hnmax : n ≤ PY_LIST_MAX) :
    ∃ result,
      gallopLeft? state slice base key n hint = some result ∧
      result.fuelExhausted = false ∧
      GallopLeftPartition state.key_compare slice base key n result.index := by
  have hprefix := gallopBefore_prefix_of_sorted state.key_compare source key n
    hvalid horder hsorted
  rcases gallopLeftFromSource_partition state source key n hint hvalid hprefix
      hn hhint hnmax with ⟨result, hresult, hfuel, hpartition⟩
  refine ⟨result, ?_, hfuel,
    leftPartition_to_slice state.key_compare source slice base key n
      result.index hvalid hagrees hpartition⟩
  rw [← gallopLeftFromSource_eq_slice state source slice base key n hint
    hvalid hagrees hn hhint hnmax]
  exact hresult

/-- Correctness of the actual right-biased transcription.  The result is the
upper bound: keys not strictly after `key` lie before it, while every key from
the result onward is strictly after `key`. -/
theorem gallopRight_correct (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (slice : SortSlice κ ν)
    (base : Int) (key : κ) (n hint : Nat)
    (hvalid : source.ValidRange n)
    (hagrees : source.AgreesWithSlice slice base n)
    (horder : BoolStrictWeakOrder state.key_compare)
    (hsorted : GallopSortedRange state.key_compare source n)
    (hn : 0 < n) (hhint : hint < n) (hnmax : n ≤ PY_LIST_MAX) :
    ∃ result,
      gallopRight? state slice base key n hint = some result ∧
      result.fuelExhausted = false ∧
      GallopRightPartition state.key_compare slice base key n result.index := by
  have hprefix := gallopDualBefore_prefix_of_sorted state.key_compare source key
    n hvalid horder hsorted
  rcases gallopLeftFromSource_partition (gallopDualState state) source key n hint
      hvalid (by simpa using hprefix) hn hhint hnmax with
    ⟨result, hleftResult, hfuel, hpartition⟩
  have hsourceDual :
      gallopRightFromSource? state source key n hint =
        gallopLeftFromSource? (gallopDualState state) source key n hint := by
    have htrace := congrArg TraceResult.erase
      (gallopRight_eq_left_dual state source key n hint)
    simpa using htrace
  have hrightResult :
      gallopRightFromSource? state source key n hint = some result := by
    rw [hsourceDual]
    exact hleftResult
  refine ⟨result, ?_, hfuel,
    dualPartition_to_right_slice state.key_compare source slice base key n
      result.index hvalid hagrees (by simpa using hpartition)⟩
  rw [← gallopRightFromSource_eq_slice state source slice base key n hint
    hvalid hagrees hn hhint hnmax]
  exact hrightResult

/-- `gallopLeft_correct` with its sorted-range premise discharged from the
project-wide `Sorted` predicate on an exactly agreeing key array.  This is the
entry point intended for pending-run correctness proofs. -/
theorem gallopLeft_correct_of_sorted (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (slice : SortSlice κ ν)
    (base : Int) (key : κ) (n hint : Nat) (keys : Array κ)
    (hvalid : source.ValidRange n)
    (hslice : source.AgreesWithSlice slice base n)
    (hkeys : GallopKeyArrayAgreement source n keys)
    (horder : BoolStrictWeakOrder state.key_compare)
    (hsorted : Sorted state.key_compare keys)
    (hn : 0 < n) (hhint : hint < n) (hnmax : n ≤ PY_LIST_MAX) :
    ∃ result,
      gallopLeft? state slice base key n hint = some result ∧
      result.fuelExhausted = false ∧
      GallopLeftPartition state.key_compare slice base key n result.index := by
  exact gallopLeft_correct state source slice base key n hint hvalid hslice
    horder (gallopSortedRange_of_sorted state.key_compare source n keys hkeys
      hsorted) hn hhint hnmax

/-- `gallopRight_correct` with its sorted-range premise discharged from the
same shared `Sorted`/exact-key-array interface. -/
theorem gallopRight_correct_of_sorted (state : MergeState κ ν)
    (source : GallopKeySource κ ν) (slice : SortSlice κ ν)
    (base : Int) (key : κ) (n hint : Nat) (keys : Array κ)
    (hvalid : source.ValidRange n)
    (hslice : source.AgreesWithSlice slice base n)
    (hkeys : GallopKeyArrayAgreement source n keys)
    (horder : BoolStrictWeakOrder state.key_compare)
    (hsorted : Sorted state.key_compare keys)
    (hn : 0 < n) (hhint : hint < n) (hnmax : n ≤ PY_LIST_MAX) :
    ∃ result,
      gallopRight? state slice base key n hint = some result ∧
      result.fuelExhausted = false ∧
      GallopRightPartition state.key_compare slice base key n result.index := by
  exact gallopRight_correct state source slice base key n hint hvalid hslice
    horder (gallopSortedRange_of_sorted state.key_compare source n keys hkeys
      hsorted) hn hhint hnmax

/-! ## Equality-bias regressions -/

private def gallopDuplicateRegressionSlice : SortSlice Nat PUnit :=
  { entries := #[
      { key := 1, value := none },
      { key := 2, value := none },
      { key := 2, value := none },
      { key := 3, value := none }] }

private def gallopDuplicateRegressionState : MergeState Nat PUnit :=
  { min_gallop := 7
    listlen := 4
    basekeys := 0
    data := gallopDuplicateRegressionSlice
    a := { cells := #[], backing := .inline, hasValues := false }
    alloced := 0
    pending := #[]
    key_compare := fun left right => decide (left < right)
    mr_current := 0
    mr_e := 0
    mr_mask := 0 }

/-- On `[1, 2, 2, 3]`, left galloping for `2` returns the first equal key. -/
theorem gallopLeft_duplicate_boundary_regression :
    gallopLeft? gallopDuplicateRegressionState gallopDuplicateRegressionSlice
      0 2 4 2 = some { index := 1, fuelExhausted := false } := by
  decide

/-- On `[1, 2, 2, 3]`, right galloping for `2` returns after the last equal key. -/
theorem gallopRight_duplicate_boundary_regression :
    gallopRight? gallopDuplicateRegressionState gallopDuplicateRegressionSlice
      0 2 4 2 = some { index := 3, fuelExhausted := false } := by
  decide

end CPythonListsort
