/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Policy.BoundaryPowerGeometry
import Code.Policy.MergeAtPreservation
import Code.Policy.StackPowers
import Mathlib

/-!
# Power preservation across a top-stack merge

This file connects the natural three-run geometry theorem to pending runs and
proves the loop invariant used by `found_new_run`: merging the top two pending
runs preserves the powered prefix and the fixed candidate power against the
prospective run.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- Three consecutive pending-run records inherit the complete boundary-power
geometry theorem.  The hypotheses deliberately expose the ordinary-natural
layout facts that callers obtain from `PendingLayout`. -/
theorem pendingBoundaryPower_geometry
    (basekeys : Nat) (listlen : PySSize)
    (left middle right : PendingRun)
    (hlistNonnegative : listlen.Nonnegative)
    (hlistMax : listlen.toNat ≤ PY_LIST_MAX)
    (hbase : basekeys ≤ left.base)
    (hleftMiddle : left.endIndex = middle.base)
    (hmiddleRight : middle.endIndex = right.base)
    (hleftPositive : 0 < left.len.toNat)
    (hmiddlePositive : 0 < middle.len.toNat)
    (hrightPositive : 0 < right.len.toNat)
    (hrightFits : right.endIndex ≤ basekeys + listlen.toNat) :
    let pLM := pendingBoundaryPower basekeys listlen left middle
    let pMR := pendingBoundaryPower basekeys listlen middle right
    pLM ≠ pMR ∧
      (pLM < pMR →
        pendingBoundaryPower basekeys listlen left
          { middle with len := middle.len + right.len } = pLM) ∧
      (pMR < pLM →
        pendingBoundaryPower basekeys listlen
          { left with len := left.len + middle.len } right = pMR) := by
  dsimp only
  let s := left.base - basekeys
  let a := left.len.toNat
  let b := middle.len.toNat
  let c := right.len.toNat
  let n := listlen.toNat
  have hleftBase : left.base = basekeys + s := by
    dsimp [s]
    omega
  have hmiddleBase : middle.base = basekeys + s + a := by
    rw [← hleftMiddle]
    simp only [PendingRun.endIndex]
    dsimp [a]
    omega
  have hmiddleOffset : middle.base - basekeys = s + a := by
    rw [hmiddleBase]
    omega
  have hrightBase : right.base = basekeys + s + a + b := by
    rw [← hmiddleRight]
    simp only [PendingRun.endIndex]
    dsimp [b]
    omega
  have hfits : s + a + b + c ≤ n := by
    simp only [PendingRun.endIndex] at hrightFits
    dsimp [s, a, b, c, n]
    omega
  have hgeometry := boundaryPowerGeometry s a b c n
    (by simpa [a] using hleftPositive)
    (by simpa [b] using hmiddlePositive)
    (by simpa [c] using hrightPositive)
    hfits (by simpa [n] using hlistMax)
  have hleftLen : BitVec.ofNat 64 a = left.len := by
    apply BitVec.toNat_injective
    simp [a]
  have hmiddleLen : BitVec.ofNat 64 b = middle.len := by
    apply BitVec.toNat_injective
    simp [b]
  have hrightLen : BitVec.ofNat 64 c = right.len := by
    apply BitVec.toNat_injective
    simp [c]
  have hlistlen : BitVec.ofNat 64 n = listlen := by
    apply BitVec.toNat_injective
    simp [n]
  have hmiddleRightSum :
      BitVec.ofNat 64 (b + c) = middle.len + right.len := by
    apply BitVec.toNat_injective
    have hsumLt : middle.len.toNat + right.len.toNat < 2 ^ 64 := by
      have hlistLt : listlen.toNat < 2 ^ 63 := by
        rw [PySSize.Nonnegative, BitVec.msb_eq_false_iff_two_mul_lt]
          at hlistNonnegative
        norm_num at hlistNonnegative ⊢
        omega
      dsimp [b, c]
      omega
    have hsumLt' :
        middle.len.toNat + right.len.toNat < 18446744073709551616 := by
      norm_num at hsumLt ⊢
      exact hsumLt
    rw [BitVec.toNat_add_of_lt (w := 64) (x := middle.len)
      (y := right.len) hsumLt']
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by simpa [b, c] using hsumLt)]
  have hleftMiddleSum :
      BitVec.ofNat 64 (a + b) = left.len + middle.len := by
    apply BitVec.toNat_injective
    have hsumLt : left.len.toNat + middle.len.toNat < 2 ^ 64 := by
      have hlistLt : listlen.toNat < 2 ^ 63 := by
        rw [PySSize.Nonnegative, BitVec.msb_eq_false_iff_two_mul_lt]
          at hlistNonnegative
        norm_num at hlistNonnegative ⊢
        omega
      dsimp [a, b]
      omega
    have hsumLt' :
        left.len.toNat + middle.len.toNat < 18446744073709551616 := by
      norm_num at hsumLt ⊢
      exact hsumLt
    rw [BitVec.toNat_add_of_lt (w := 64) (x := left.len)
      (y := middle.len) hsumLt']
    rw [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by simpa [a, b] using hsumLt)]
  simpa [pendingBoundaryPower, s, a, b, c, n, hleftLen, hmiddleLen,
    hrightLen, hlistlen, hmiddleRightSum, hleftMiddleSum, hmiddleOffset,
    hrightBase]
    using hgeometry

/-- Restricting an initialized increasing-power list to an initial segment
preserves initialization, the concrete range, and strict increase. -/
theorem IncreasingPendingPowers.prefix {runs suffix : List PendingRun}
    (h : IncreasingPendingPowers (runs ++ suffix)) :
    IncreasingPendingPowers runs := by
  rcases h with ⟨powers, hmap, hrange, hstrict⟩
  let prefixPowers := powers.take runs.length
  refine ⟨prefixPowers, ?_, ?_, ?_⟩
  · have htake := congrArg (List.take runs.length) hmap
    simpa [prefixPowers] using htake
  · intro power hpower
    exact hrange power (List.take_subset runs.length powers hpower)
  · exact List.Pairwise.sublist (List.take_sublist runs.length powers) hstrict

/-- Expose the increasing powered part for any displayed snoc decomposition
of a nonempty steady-state stack. -/
theorem PoweredPrefix.increasing_of_eq_snoc {state : MergeState κ ν}
    (h : PoweredPrefix state) {older : List PendingRun} {newest : PendingRun}
    (hsplit : state.pending.toList = older ++ [newest]) :
    IncreasingPendingPowers older := by
  rcases h with hempty | ⟨actualOlder, actualNewest, hactual, hpowers, _⟩
  · rw [hempty] at hsplit
    have : (older ++ [newest]).length = 0 := by simpa using congrArg List.length hsplit.symm
    simp at this
  · have heq : older ++ [newest] = actualOlder ++ [actualNewest] :=
      hsplit.symm.trans hactual
    have hlength : older.length = actualOlder.length := by
      have := congrArg List.length heq
      simp only [List.length_append, List.length_singleton] at this
      omega
    have hparts := List.append_inj heq hlength
    simpa [hparts.1] using hpowers

private theorem increasingPowers_lt_last_aux
    (runs : List PendingRun) (last : PendingRun) (powers : List Nat)
    (p : Nat)
    (hmap : (runs ++ [last]).map PendingRun.power = powers.map some)
    (hstrict : powers.Pairwise (fun x y => x < y))
    (hlast : last.power = some p) :
    ∀ run ∈ runs, ∀ q, run.power = some q → q < p := by
  induction runs generalizing powers with
  | nil => simp
  | cons head runs ih =>
      cases powers with
      | nil => simp at hmap
      | cons headPower tailPowers =>
          simp only [List.cons_append, List.map_cons, List.cons.injEq] at hmap
          rcases hmap with ⟨hhead, htail⟩
          simp only [List.pairwise_cons] at hstrict
          rcases hstrict with ⟨hheadLt, htailStrict⟩
          intro run hrun q hrunPower
          simp only [List.mem_cons] at hrun
          rcases hrun with rfl | hrun
          · have hq : q = headPower := by
              rw [hrunPower] at hhead
              exact Option.some.inj hhead
            subst q
            have hpMem : p ∈ tailPowers := by
              have hsomeMem : some p ∈ tailPowers.map some := by
                rw [← htail]
                simp [hlast]
              simpa using hsomeMem
            exact hheadLt p hpMem
          · exact ih tailPowers htail htailStrict run hrun q hrunPower

/-- Every stored power before the final run is strictly below the final
power in an increasing initialized snoc list. -/
theorem IncreasingPendingPowers.power_lt_last
    {runs : List PendingRun} {last run : PendingRun} {p q : Nat}
    (h : IncreasingPendingPowers (runs ++ [last]))
    (hrun : run ∈ runs) (hrunPower : run.power = some q)
    (hlastPower : last.power = some p) : q < p := by
  rcases h with ⟨powers, hmap, _, hstrict⟩
  exact increasingPowers_lt_last_aux runs last powers p hmap hstrict hlastPower
    run hrun q hrunPower

/-- If only the last boundary changes, exact labels on the untouched prefix
can be transported by supplying that one new boundary equality. -/
theorem ExactBoundaryPowers.replace_last_boundary
    {basekeys : Nat} {listlen : PySSize}
    {before : List PendingRun} {previous left right : PendingRun}
    (h : ExactBoundaryPowers basekeys listlen
      (before ++ [previous, left, right]))
    (hnew : previous.power = some
      (pendingBoundaryPower basekeys listlen previous
        { left with len := left.len + right.len })) :
    ExactBoundaryPowers basekeys listlen
      (before ++ [previous, { left with len := left.len + right.len }]) := by
  induction before with
  | nil => simpa [ExactBoundaryPowers] using hnew
  | cons head before ih =>
      cases before <;>
        simp only [List.cons_append, List.nil_append, ExactBoundaryPowers] at h ⊢
      all_goals exact ⟨h.1, ih h.2⟩

/-- A covered run begins at or after the cover cursor and ends no later than
the cover limit; in particular its signed length is positive. -/
theorem PendingRunsCover.member_spec
    {cursor limit : Nat} {runs : List PendingRun} {run : PendingRun}
    (h : PendingRunsCover cursor limit runs) (hrun : run ∈ runs) :
    cursor ≤ run.base ∧ run.len.Nonnegative ∧ 0 < run.len.toNat ∧
      run.endIndex ≤ limit := by
  induction runs generalizing cursor with
  | nil => simp at hrun
  | cons head runs ih =>
      simp only [PendingRunsCover] at h
      rcases h with ⟨hbase, hnonnegative, hpositive, hend, htail⟩
      simp only [List.mem_cons] at hrun
      rcases hrun with rfl | hrun
      · exact ⟨by omega, hnonnegative, hpositive, hend⟩
      · rcases ih htail hrun with ⟨hlower, hrnn, hrpos, hrend⟩
        have hheadEnd : cursor < head.endIndex := by
          simp only [PendingRun.endIndex]
          omega
        exact ⟨by omega, hrnn, hrpos, hrend⟩

/-- The final run in an exact interval cover ends exactly at the cover limit. -/
theorem PendingRunsCover.last_end_eq
    {cursor limit : Nat} {before : List PendingRun} {last : PendingRun}
    (h : PendingRunsCover cursor limit (before ++ [last])) :
    last.endIndex = limit := by
  induction before generalizing cursor with
  | nil =>
      simpa [PendingRunsCover] using h.2.2.2.2
  | cons head before ih =>
      simp only [List.cons_append, PendingRunsCover] at h
      exact ih h.2.2.2.2

/-- A top merge taken under the strict PowerSort guard preserves both the
steady-state powered prefix and the fixed prospective boundary power. -/
theorem mergeTop_preserves_poweredPrefix
    (state : MergeState κ ν) (scanned : Nat)
    (before : List PendingRun) (left right newRun : PendingRun)
    (pInternal q : Nat) (result : MergeAtResult κ ν)
    (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
    (hlayout : PendingLayout state scanned)
    (hpowered : PoweredPrefix state)
    (hsplit : state.pending.toList = before ++ [left, right])
    (hnewBase : newRun.base = state.basekeys + scanned)
    (_hnewNonnegative : newRun.len.Nonnegative)
    (hnewPositive : 0 < newRun.len.toNat)
    (hnewWithin : scanned + newRun.len.toNat ≤ state.listlen.toNat)
    (_hnewOutside : newRun ∉ state.pending.toList)
    (hleftPower : left.power = some pInternal)
    (hpInternal : pInternal =
      pendingBoundaryPower state.basekeys state.listlen left right)
    (hq : q = pendingBoundaryPower state.basekeys state.listlen right newRun)
    (hguard : q < pInternal)
    (hmerge : mergeAt? state (state.pending.size - 2) = some result)
    (_hcode : result.returnCode = 0)
    (_hfuel : result.fuelExhausted = false) :
    let merged : PendingRun := { left with len := left.len + right.len }
    result.state.pending.toList = before ++ [merged] ∧
      merged.power = some pInternal ∧
      PendingLayout result.state scanned ∧
      PoweredPrefix result.state ∧
      q = pendingBoundaryPower result.state.basekeys result.state.listlen
        merged newRun := by
  dsimp only
  let merged : PendingRun := { left with len := left.len + right.len }
  have hindex : state.pending.size - 2 = before.length := by
    have hsize := congrArg List.length hsplit
    simp only [Array.length_toList, List.length_append, List.length_cons,
      List.length_nil] at hsize
    omega
  rcases mergeAt_pending_frame_of_eq_some state (state.pending.size - 2)
      result hmerge with
    ⟨actualLeft, actualRight, hactualLeft, hactualRight,
      hlistlen, hbasekeys, _hdataSize, hpending⟩
  have hleftLookup :
      state.pending[state.pending.size - 2]? = some left := by
    rw [← Array.getElem?_toList, hsplit, hindex]
    simp
  have hrightLookup :
      state.pending[state.pending.size - 2 + 1]? = some right := by
    rw [← Array.getElem?_toList, hsplit, hindex]
    simp
  have hactualLeftEq : actualLeft = left := by
    rw [hleftLookup] at hactualLeft
    exact Option.some.inj hactualLeft.symm
  have hactualRightEq : actualRight = right := by
    rw [hrightLookup] at hactualRight
    exact Option.some.inj hactualRight.symm
  subst actualLeft
  subst actualRight
  have hresultPending : result.state.pending.toList = before ++ [merged] := by
    calc
      result.state.pending.toList =
          ((state.pending.setIfInBounds (state.pending.size - 2) merged)
            |>.eraseIdxIfInBounds (state.pending.size - 2 + 1)).toList := by
              exact congrArg Array.toList hpending
      _ = before ++ [merged] := by
        simpa [merged] using
          Array.toList_set_eraseIdx_adjacent hsplit hindex.symm
  have hresultLayout : PendingLayout result.state scanned := by
    rcases mergeAt_preserves_pendingLayout state scanned
        (state.pending.size - 2) result hlayout hmerge with
      ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, hresultLayout⟩
    exact hresultLayout
  have hcover : PendingRunsCover state.basekeys (state.basekeys + scanned)
      (before ++ [left, right]) := by
    simpa [hsplit] using hlayout.2.2.2
  have hleftSpec := hcover.member_spec
    (run := left) (by simp)
  have hrightSpec := hcover.member_spec
    (run := right) (by simp)
  have hpair := hcover.pair_spec
    (before := before) (after := []) (left := left) (right := right)
  rcases hpair with
    ⟨hleftNonnegative, hleftPositive, hrightNonnegative,
      hrightPositive, hleftRight⟩
  have hrightEnd : right.endIndex = state.basekeys + scanned := by
    apply PendingRunsCover.last_end_eq
      (before := before ++ [left]) (last := right)
    simpa [List.append_assoc] using hcover
  have hnewAdjacency : right.endIndex = newRun.base := by
    rw [hnewBase, hrightEnd]
  have hnewEndFits :
      newRun.endIndex ≤ state.basekeys + state.listlen.toNat := by
    simp only [PendingRun.endIndex, hnewBase]
    omega
  have hgeometryNew := pendingBoundaryPower_geometry
    state.basekeys state.listlen left right newRun hlayout.1 hmax
    hleftSpec.1 hleftRight hnewAdjacency hleftPositive hrightPositive
    hnewPositive hnewEndFits
  have hghostState :
      q = pendingBoundaryPower state.basekeys state.listlen merged newRun := by
    rw [hq]
    exact (hgeometryNew.2.2 (by simpa [hpInternal, hq] using hguard)).symm
  have hghostResult :
      q = pendingBoundaryPower result.state.basekeys result.state.listlen
        merged newRun := by
    simpa only [hbasekeys, hlistlen] using hghostState
  have hmergedPower : merged.power = some pInternal := by
    simpa [merged] using hleftPower
  have hincreasingWithLeft :
      IncreasingPendingPowers (before ++ [left]) := by
    apply hpowered.increasing_of_eq_snoc
    simpa [List.append_assoc] using hsplit
  have hincreasingBefore : IncreasingPendingPowers before := by
    exact hincreasingWithLeft.prefix
  have hresultPowered : PoweredPrefix result.state := by
    rw [PoweredPrefix]
    right
    refine ⟨before, merged, hresultPending, hincreasingBefore, ?_⟩
    rcases List.eq_nil_or_concat' before with hbefore | ⟨older, previous, hbefore⟩
    · subst before
      rw [hresultPending, hbasekeys, hlistlen]
      simp
    · subst before
      have hpreviousLabel : previous.power = some
            (pendingBoundaryPower state.basekeys state.listlen previous left) := by
        apply hpowered.boundary_power
        simpa [List.append_assoc] using hsplit
      have hpreviousLt :
          pendingBoundaryPower state.basekeys state.listlen previous left <
            pInternal := by
        exact IncreasingPendingPowers.power_lt_last
          (runs := older ++ [previous]) (last := left) (run := previous)
          (p := pInternal)
          (q := pendingBoundaryPower state.basekeys state.listlen previous left)
          hincreasingWithLeft (by simp) hpreviousLabel hleftPower
      have hcoverTriple : PendingRunsCover state.basekeys
          (state.basekeys + scanned)
          (older ++ [previous, left, right]) := by
        simpa [List.append_assoc] using hcover
      have hpreviousSpec := hcoverTriple.member_spec
        (run := previous) (by simp)
      have hpreviousLeft := PendingRunsCover.pair_spec
        (before := older) (after := [right])
        (left := previous) (right := left)
        (by simpa [List.append_assoc] using hcoverTriple)
      have hleftRight' := PendingRunsCover.pair_spec
        (before := older ++ [previous]) (after := [])
        (left := left) (right := right)
        (by simpa [List.append_assoc] using hcoverTriple)
      have hrightWithinList :
          right.endIndex ≤ state.basekeys + state.listlen.toNat := by
        exact hrightSpec.2.2.2.trans
          (Nat.add_le_add_left hlayout.2.2.1 state.basekeys)
      have hgeometryPrevious := pendingBoundaryPower_geometry
        state.basekeys state.listlen previous left right hlayout.1 hmax
        hpreviousSpec.1 hpreviousLeft.2.2.2.2 hleftRight'.2.2.2.2
        hpreviousLeft.2.1 hleftRight'.2.1 hleftRight'.2.2.2.1
        hrightWithinList
      have hnewPrevious : previous.power = some
          (pendingBoundaryPower state.basekeys state.listlen previous merged) := by
        rw [hpreviousLabel]
        exact congrArg some (hgeometryPrevious.2.1
          (by simpa [hpInternal] using hpreviousLt)).symm
      have hexactState := hpowered.exact_boundary_powers
      rw [hsplit] at hexactState
      have hexactState' : ExactBoundaryPowers state.basekeys state.listlen
          (older ++ [previous, left, right]) := by
        simpa [List.append_assoc] using hexactState
      have hexactResultState : ExactBoundaryPowers state.basekeys state.listlen
          (older ++ [previous, merged]) := by
        exact hexactState'.replace_last_boundary hnewPrevious
      rw [hresultPending, hbasekeys, hlistlen]
      simpa [List.append_assoc] using hexactResultState
  exact ⟨hresultPending, hmergedPower, hresultLayout, hresultPowered,
    hghostResult⟩

end CPythonListsort
