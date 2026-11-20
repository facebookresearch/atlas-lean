/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.Policy.BoundaryPowerGeometry
import Code.Policy.MergeTopPowerPreservation
import Code.Equivalence.PowerloopResults
import Code.Transcription.FoundNewRun
import Mathlib

/-!
# Policy preservation across `found_new_run`

The theorem in this file is intentionally conditional on a successful,
non-fuel-exhausted transcription result.  Fuel adequacy and the safety of the
delegated merges belong to the separate assembly theorem.
-/

namespace CPythonListsort

universe u v

variable {κ : Type u} {ν : Type v}

/-- `setTopPower?` changes only the final pending-run record. -/
private theorem setTopPower_pending_frame
    (state state' : MergeState κ ν) (power : Nat)
    (before : List PendingRun) (top : PendingRun)
    (hsplit : state.pending.toList = before ++ [top])
    (hset : setTopPower? state power = some state') :
    state'.pending.toList =
        before ++ [{ top with power := some power }] ∧
      state'.listlen = state.listlen ∧
      state'.basekeys = state.basekeys ∧
      state'.data.entries.size = state.data.entries.size := by
  unfold setTopPower? at hset
  have hnonempty : state.pending.isEmpty = false := by
    apply Bool.eq_false_of_not_eq_true
    intro hempty
    rw [Array.isEmpty_iff] at hempty
    have hlen := congrArg List.length hsplit
    rw [hempty] at hlen
    simp at hlen
  simp only [hnonempty, Bool.false_eq_true, if_false] at hset
  have hsize : state.pending.size = before.length + 1 := by
    have hlen := congrArg List.length hsplit
    simpa using hlen
  have hlookup : state.pending[state.pending.size - 1]? = some top := by
    rw [← Array.getElem?_toList, hsplit, hsize]
    simp
  rw [hlookup] at hset
  injection hset with hstate'
  subst state'
  refine ⟨?_, rfl, rfl, rfl⟩
  rw [Array.toList_setIfInBounds, hsplit, hsize]
  simp

/-- Changing only the stored power of the final run does not disturb an exact
interval cover. -/
private theorem PendingRunsCover.replace_last_power
    {cursor limit : Nat} {before : List PendingRun} {top : PendingRun}
    {power : Nat}
    (h : PendingRunsCover cursor limit (before ++ [top])) :
    PendingRunsCover cursor limit
      (before ++ [{ top with power := some power }]) := by
  induction before generalizing cursor with
  | nil => simpa [PendingRunsCover, PendingRun.endIndex] using h
  | cons head before ih =>
      simp only [List.cons_append, PendingRunsCover] at h ⊢
      exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, ih h.2.2.2.2⟩

/-- Replacing the last physical run's stored power by its boundary against a
prospective run establishes exact labels on the virtual post-push list. -/
private theorem ExactBoundaryPowers.set_last_and_append
    {basekeys : Nat} {listlen : PySSize}
    {before : List PendingRun} {top newRun : PendingRun} {power : Nat}
    (hexact : ExactBoundaryPowers basekeys listlen (before ++ [top]))
    (hpower : power = pendingBoundaryPower basekeys listlen top newRun) :
    ExactBoundaryPowers basekeys listlen
      (before ++ [{ top with power := some power }, newRun]) := by
  induction before with
  | nil =>
      simp only [List.nil_append, ExactBoundaryPowers]
      refine ⟨?_, trivial⟩
      simp [hpower, pendingBoundaryPower]
  | cons head before ih =>
      cases before with
      | nil =>
          simp only [List.nil_append, List.cons_append, ExactBoundaryPowers]
            at hexact ⊢
          refine ⟨?_, ?_⟩
          · simpa [pendingBoundaryPower] using hexact.1
          · refine ⟨?_, trivial⟩
            simp [hpower, pendingBoundaryPower]
      | cons next rest =>
          simp only [List.cons_append, ExactBoundaryPowers] at hexact ⊢
          exact ⟨hexact.1, ih hexact.2⟩

/-- Append a newly initialized greatest label to an increasing initialized
power list. -/
private theorem IncreasingPendingPowers.append_of_upper
    {runs : List PendingRun} {top : PendingRun} {power : Nat}
    (h : IncreasingPendingPowers runs)
    (hrange : 1 ≤ power ∧ power ≤ 60)
    (hupper : ∀ run ∈ runs, ∀ candidate,
      run.power = some candidate → candidate < power) :
    IncreasingPendingPowers
      (runs ++ [{ top with power := some power }]) := by
  rcases h with ⟨powers, hmap, hpowersRange, hstrict⟩
  refine ⟨powers ++ [power], ?_, ?_, ?_⟩
  · simp only [List.map_append, List.map_singleton]
    rw [hmap]
  · intro candidate hcandidate
    simp only [List.mem_append, List.mem_singleton] at hcandidate
    rcases hcandidate with hcandidate | rfl
    · exact hpowersRange candidate hcandidate
    · exact hrange
  · rw [List.pairwise_append]
    refine ⟨hstrict, by simp, ?_⟩
    intro candidate hcandidate last hlast
    simp only [List.mem_singleton] at hlast
    subst last
    have hsomeMem : some candidate ∈ runs.map PendingRun.power := by
      rw [hmap]
      exact List.mem_map.mpr ⟨candidate, hcandidate, rfl⟩
    rcases List.mem_map.mp hsomeMem with ⟨run, hrun, hrunPower⟩
    exact hupper run hrun candidate hrunPower

/-- Every run in a valid pending cover starts strictly before its limit. -/
private theorem PendingRunsCover.member_base_lt_limit
    {cursor limit : Nat} {runs : List PendingRun} {run : PendingRun}
    (hcover : PendingRunsCover cursor limit runs) (hrun : run ∈ runs) :
    run.base < limit := by
  rcases hcover.member_spec hrun with ⟨_, _, hpositive, hend⟩
  simp only [PendingRun.endIndex] at hend
  omega

/-- A prospective adjacent run cannot already occur in the covered pending
prefix.  This remains true after power-only updates. -/
private theorem newRun_not_mem_of_layout
    {state : MergeState κ ν} {scanned : Nat} {newRun : PendingRun}
    (hlayout : PendingLayout state scanned)
    (hnewBase : newRun.base = state.basekeys + scanned) :
    newRun ∉ state.pending.toList := by
  intro hmem
  have hlt := hlayout.2.2.2.member_base_lt_limit hmem
  rw [hnewBase] at hlt
  omega

/-- Once the strict merge guard is false, writing the fixed prospective
boundary power on the surviving top establishes the complete pre-push policy
postcondition. -/
private theorem setTopPower_establishes_ready
    (state state' : MergeState κ ν) (scanned : Nat)
    (before : List PendingRun) (top newRun : PendingRun) (power : Nat)
    (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
    (hlayout : PendingLayout state scanned)
    (hpowered : PoweredPrefix state)
    (hsplit : state.pending.toList = before ++ [top])
    (hnewBase : newRun.base = state.basekeys + scanned)
    (hnewNonnegative : newRun.len.Nonnegative)
    (hnewPositive : 0 < newRun.len.toNat)
    (hnewWithin : scanned + newRun.len.toNat ≤ state.listlen.toNat)
    (hpower : power =
      pendingBoundaryPower state.basekeys state.listlen top newRun)
    (hpowerRange : 1 ≤ power ∧ power ≤ 60)
    (hstop : before = [] ∨
      ∃ older preceding precedingPower,
        before = older ++ [preceding] ∧
          preceding.power = some precedingPower ∧
          ¬ power < precedingPower)
    (hset : setTopPower? state power = some state') :
    ReadyToPush state' scanned newRun := by
  rcases setTopPower_pending_frame state state' power before top hsplit hset with
    ⟨hresultPending, hlistlen, hbasekeys, hdataSize⟩
  have hresultLayout : PendingLayout state' scanned := by
    rcases hlayout with
      ⟨hlistNonnegative, hdataBound, hscanned, hcover⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [hlistlen] using hlistNonnegative
    · rw [hbasekeys, hlistlen, hdataSize]
      exact hdataBound
    · simpa [hlistlen] using hscanned
    · rw [hresultPending, hbasekeys]
      rw [hsplit] at hcover
      exact hcover.replace_last_power
  have hincreasingBefore : IncreasingPendingPowers before :=
    hpowered.increasing_of_eq_snoc hsplit
  have hupper : ∀ run ∈ before, ∀ candidate,
      run.power = some candidate → candidate < power := by
    rcases hstop with hbeforeEmpty |
        ⟨older, preceding, precedingPower, hbefore, hprecedingPower,
          hnotGuard⟩
    · subst before
      simp
    · have hcover : PendingRunsCover state.basekeys
          (state.basekeys + scanned) (older ++ [preceding, top]) := by
        have := hlayout.2.2.2
        rw [hsplit, hbefore] at this
        simpa [List.append_assoc] using this
      have hprecedingSpec := hcover.member_spec
        (run := preceding) (by simp)
      have hprecedingTop := hcover.pair_spec
        (before := older) (after := [])
        (left := preceding) (right := top)
      have htopEnd : top.endIndex = state.basekeys + scanned := by
        apply PendingRunsCover.last_end_eq
          (before := older ++ [preceding]) (last := top)
        simpa [List.append_assoc] using hcover
      have htopNew : top.endIndex = newRun.base := by
        rw [hnewBase, htopEnd]
      have hnewEndFits :
          newRun.endIndex ≤ state.basekeys + state.listlen.toNat := by
        simp only [PendingRun.endIndex, hnewBase]
        omega
      have hgeometry := pendingBoundaryPower_geometry
        state.basekeys state.listlen preceding top newRun hlayout.1 hmax
        hprecedingSpec.1 hprecedingTop.2.2.2.2 htopNew
        hprecedingTop.2.1 hprecedingTop.2.2.2.1 hnewPositive
        hnewEndFits
      have hstoredExact : preceding.power = some
          (pendingBoundaryPower state.basekeys state.listlen preceding top) := by
        apply hpowered.boundary_power (before := older) (after := [])
        simpa [hbefore, List.append_assoc] using hsplit
      have hprecedingPowerEq : precedingPower =
          pendingBoundaryPower state.basekeys state.listlen preceding top := by
        rw [hprecedingPower] at hstoredExact
        exact Option.some.inj hstoredExact
      have hpqNe : precedingPower ≠ power := by
        simpa [hprecedingPowerEq, hpower] using hgeometry.1
      have hpq : precedingPower < power := by omega
      intro run hrun candidate hcandidate
      rw [hbefore] at hrun
      simp only [List.mem_append, List.mem_singleton] at hrun
      rcases hrun with hrun | rfl
      · have hbeforeIncreasing :
            IncreasingPendingPowers (older ++ [preceding]) := by
          simpa [hbefore] using hincreasingBefore
        exact (hbeforeIncreasing.power_lt_last hrun hcandidate
          hprecedingPower).trans hpq
      · rw [hcandidate] at hprecedingPower
        have : candidate = precedingPower := Option.some.inj hprecedingPower
        omega
  have hresultIncreasing :
      IncreasingPendingPowers state'.pending.toList := by
    rw [hresultPending]
    exact hincreasingBefore.append_of_upper hpowerRange hupper
  have hstateExact : ExactBoundaryPowers state.basekeys state.listlen
      (before ++ [top]) := by
    rw [← hsplit]
    exact hpowered.exact_boundary_powers
  have hresultExact : ExactBoundaryPowers state'.basekeys state'.listlen
      (state'.pending.toList ++ [newRun]) := by
    rw [hresultPending, hbasekeys, hlistlen]
    simpa [List.append_assoc] using
      hstateExact.set_last_and_append hpower
  have hresultNewBase : newRun.base = state'.basekeys + scanned := by
    simpa [hbasekeys] using hnewBase
  refine ⟨hresultLayout, hresultIncreasing, hresultExact,
    hresultNewBase, hnewNonnegative, hnewPositive, ?_, ?_⟩
  · simpa [hlistlen] using hnewWithin
  · exact newRun_not_mem_of_layout hresultLayout hresultNewBase

/-- Loop invariant for the transcribed collapse loop.  The `power` argument is
a fixed ghost boundary against `newRun`; after every strict top merge the
geometry theorem re-establishes that same equality for the merged top. -/
private theorem foundNewRunLoop_preserves_ready
    (fuel : Nat) (state : MergeState κ ν) (scanned : Nat)
    (before : List PendingRun) (top newRun : PendingRun) (power : Nat)
    (result : FoundNewRunResult κ ν)
    (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
    (hlayout : PendingLayout state scanned)
    (hpowered : PoweredPrefix state)
    (hsplit : state.pending.toList = before ++ [top])
    (hnewBase : newRun.base = state.basekeys + scanned)
    (hnewNonnegative : newRun.len.Nonnegative)
    (hnewPositive : 0 < newRun.len.toNat)
    (hnewWithin : scanned + newRun.len.toNat ≤ state.listlen.toNat)
    (hpower : power =
      pendingBoundaryPower state.basekeys state.listlen top newRun)
    (hpowerRange : 1 ≤ power ∧ power ≤ 60)
    (hloop : foundNewRunLoop? fuel state power = some result)
    (hcode : result.returnCode = 0)
    (hfuel : result.fuelExhausted = false) :
    ReadyToPush result.state scanned newRun := by
  induction fuel generalizing state before top result with
  | zero =>
      simp only [foundNewRunLoop?] at hloop
      injection hloop with hresult
      subst result
      change true = false at hfuel
      contradiction
  | succ remaining ih =>
      have hsize : state.pending.size = before.length + 1 := by
        have := congrArg List.length hsplit
        simpa using this
      by_cases hmany : 1 < state.pending.size
      · rcases List.eq_nil_or_concat' before with hbeforeEmpty |
          ⟨older, preceding, hbefore⟩
        · subst before
          simp at hsize
          omega
        · have hlookup :
              state.pending[state.pending.size - 2]? = some preceding := by
            rw [← Array.getElem?_toList, hsplit, hbefore, hsize]
            simp [hbefore]
          have hprecedingPower : preceding.power = some
              (pendingBoundaryPower state.basekeys state.listlen preceding top) := by
            apply hpowered.boundary_power (before := older) (after := [])
            simpa [hbefore, List.append_assoc] using hsplit
          let precedingPower :=
            pendingBoundaryPower state.basekeys state.listlen preceding top
          by_cases hguard : power < precedingPower
          · have hloop' := hloop
            dsimp only [precedingPower] at hguard
            simp only [foundNewRunLoop?, hmany, if_pos, hlookup,
              hprecedingPower] at hloop'
            rw [if_pos hguard] at hloop'
            cases hmergeOpt : mergeAt? state (state.pending.size - 2) with
            | none => simp [hmergeOpt] at hloop'
            | some merged =>
              simp only [hmergeOpt] at hloop'
              by_cases hmergeSuccess :
                  merged.returnCode = 0 ∧ !merged.fuelExhausted
              · rw [if_pos hmergeSuccess] at hloop'
                have hmergedFuel : merged.fuelExhausted = false := by
                  simpa using hmergeSuccess.2
                have houtside : newRun ∉ state.pending.toList :=
                  newRun_not_mem_of_layout hlayout hnewBase
                have hpolicy := mergeTop_preserves_poweredPrefix
                  state scanned older preceding top newRun precedingPower power
                  merged hmax hlayout hpowered
                  (by simpa [hbefore, List.append_assoc] using hsplit)
                  hnewBase hnewNonnegative hnewPositive hnewWithin houtside
                  hprecedingPower rfl hpower hguard hmergeOpt
                  hmergeSuccess.1 hmergedFuel
                let mergedTop : PendingRun :=
                  { preceding with len := preceding.len + top.len }
                have hmergedSplit : merged.state.pending.toList =
                    older ++ [mergedTop] := by
                  simpa [mergedTop] using hpolicy.1
                have hmergedLayout : PendingLayout merged.state scanned :=
                  hpolicy.2.2.1
                have hmergedPowered : PoweredPrefix merged.state :=
                  hpolicy.2.2.2.1
                have hmergedPower : power = pendingBoundaryPower
                    merged.state.basekeys merged.state.listlen mergedTop newRun := by
                  simpa [mergedTop] using hpolicy.2.2.2.2
                rcases mergeAt_pending_frame_of_eq_some state
                    (state.pending.size - 2) merged hmergeOpt with
                  ⟨_, _, _, _, hmergedListlen, hmergedBasekeys, _, _⟩
                have hmergedMax :
                    merged.state.listlen.toNat ≤ PY_LIST_MAX := by
                  simpa [hmergedListlen] using hmax
                have hmergedNewBase :
                    newRun.base = merged.state.basekeys + scanned := by
                  simpa [hmergedBasekeys] using hnewBase
                have hmergedNewWithin :
                    scanned + newRun.len.toNat ≤
                      merged.state.listlen.toNat := by
                  simpa [hmergedListlen] using hnewWithin
                exact ih merged.state older mergedTop result hmergedMax
                  hmergedLayout hmergedPowered hmergedSplit hmergedNewBase
                  hmergedNewWithin hmergedPower hloop' hcode hfuel
              · rw [if_neg hmergeSuccess] at hloop'
                injection hloop' with hresult
                subst result
                change merged.returnCode = 0 at hcode
                change merged.fuelExhausted = false at hfuel
                exfalso
                apply hmergeSuccess
                constructor
                · exact hcode
                · simp [hfuel]
          · have hloop' := hloop
            dsimp only [precedingPower] at hguard
            simp only [foundNewRunLoop?, hmany, if_pos, hlookup,
              hprecedingPower] at hloop'
            rw [if_neg hguard] at hloop'
            cases hsetOpt : setTopPower? state power with
            | none => simp [hsetOpt] at hloop'
            | some state' =>
              rw [hsetOpt] at hloop'
              injection hloop' with hresult
              subst result
              change ReadyToPush state' scanned newRun
              apply setTopPower_establishes_ready state state' scanned before
                top newRun power hmax hlayout hpowered hsplit hnewBase
                hnewNonnegative hnewPositive hnewWithin hpower hpowerRange
              · right
                exact ⟨older, preceding, precedingPower, hbefore,
                  hprecedingPower, hguard⟩
              · exact hsetOpt
      · have hbeforeEmpty : before = [] := by
          have hlength : before.length = 0 := by omega
          exact List.eq_nil_of_length_eq_zero hlength
        have hloop' := hloop
        simp only [foundNewRunLoop?, hmany, if_false] at hloop'
        cases hsetOpt : setTopPower? state power with
        | none => simp [hsetOpt] at hloop'
        | some state' =>
          rw [hsetOpt] at hloop'
          injection hloop' with hresult
          subst result
          change ReadyToPush state' scanned newRun
          apply setTopPower_establishes_ready state state' scanned before top
            newRun power hmax hlayout hpowered hsplit hnewBase
            hnewNonnegative hnewPositive hnewWithin hpower hpowerRange
          · exact Or.inl hbeforeEmpty
          · exact hsetOpt

/-- A successful, non-fuel-exhausted execution of the transcribed
`found_new_run` establishes exactly the policy facts needed by the caller's
unconditional push.  This theorem deliberately does not prove that such a
result exists; that fuel/safety obligation belongs to the assembly layer. -/
theorem foundNewRun_preserves_readyToPush
    (state : MergeState κ ν) (scanned : Nat) (newRun : PendingRun)
    (result : FoundNewRunResult κ ν)
    (hmax : state.listlen.toNat ≤ PY_LIST_MAX)
    (hlayout : PendingLayout state scanned)
    (hpowered : PoweredPrefix state)
    (hnewBase : newRun.base = state.basekeys + scanned)
    (hnewNonnegative : newRun.len.Nonnegative)
    (hnewPositive : 0 < newRun.len.toNat)
    (hnewWithin : scanned + newRun.len.toNat ≤ state.listlen.toNat)
    (_hnewOutside : newRun ∉ state.pending.toList)
    (hfound : foundNewRun? state newRun.len.toNat = some result)
    (hcode : result.returnCode = 0)
    (hfuel : result.fuelExhausted = false) :
    ReadyToPush result.state scanned newRun := by
  by_cases hempty : state.pending.isEmpty = true
  · unfold foundNewRun? at hfound
    simp only [hempty, if_pos] at hfound
    injection hfound with hresult
    subst result
    change ReadyToPush state scanned newRun
    have hpending : state.pending.toList = [] := by
      rw [Array.isEmpty_iff] at hempty
      simp [hempty]
    refine ⟨hlayout, ?_, ?_, hnewBase, hnewNonnegative, hnewPositive,
      hnewWithin, ?_⟩
    · rw [hpending]
      exact increasingPendingPowers_nil
    · simp [hpending]
    · simp [hpending]
  · have hnonempty : state.pending.toList ≠ [] := by
      intro hpending
      apply hempty
      rw [Array.isEmpty_iff_size_eq_zero]
      have hlength := congrArg List.length hpending
      simpa using hlength
    rcases List.eq_nil_or_concat' state.pending.toList with hpending |
        ⟨before, top, hsplit⟩
    · exact (hnonempty hpending).elim
    · have htopLookup :
          state.pending[state.pending.size - 1]? = some top := by
        have hsize : state.pending.size = before.length + 1 := by
          have := congrArg List.length hsplit
          simpa using this
        rw [← Array.getElem?_toList, hsplit, hsize]
        simp
      have hcover : PendingRunsCover state.basekeys
          (state.basekeys + scanned) (before ++ [top]) := by
        simpa [hsplit] using hlayout.2.2.2
      have htopSpec := hcover.member_spec (run := top) (by simp)
      have htopEnd : top.endIndex = state.basekeys + scanned := by
        exact PendingRunsCover.last_end_eq hcover
      have hfits : top.base - state.basekeys + top.len.toNat +
          newRun.len.toNat ≤ state.listlen.toNat := by
        simp only [PendingRun.endIndex] at htopEnd
        omega
      have hvalidNat := validPowerloopInput_ofNat
        (s := top.base - state.basekeys) (u := top.len.toNat)
        (v := newRun.len.toNat) (n := state.listlen.toNat)
        htopSpec.2.2.1 hnewPositive hfits hmax
      have htopLen : BitVec.ofNat 64 top.len.toNat = top.len := by
        simp
      have hnewLen : BitVec.ofNat 64 newRun.len.toNat = newRun.len := by
        simp
      have hlistlen : BitVec.ofNat 64 state.listlen.toNat = state.listlen := by
        simp
      have hvalid : ValidPowerloopInput
          (BitVec.ofNat 64 (top.base - state.basekeys)) top.len newRun.len
          state.listlen := by
        simpa [htopLen, hnewLen, hlistlen] using hvalidNat
      let prospectivePower :=
        (powerloopTraced
          (BitVec.ofNat 64 (top.base - state.basekeys)) top.len
          newRun.len state.listlen).result
      have hprospectivePower : prospectivePower =
          pendingBoundaryPower state.basekeys state.listlen top newRun := by
        rfl
      have hpowerRangeRaw := powerRange
        (BitVec.ofNat 64 (top.base - state.basekeys)) top.len newRun.len
        state.listlen hvalid
      have hpowerRange :
          1 ≤ prospectivePower ∧ prospectivePower ≤ 60 := by
        simpa [prospectivePower, powerloop, POWER_BOUND, hnewLen] using
          ⟨hpowerRangeRaw.1, hpowerRangeRaw.2.1⟩
      have hstopped := (powerloopTraceSafety
        (BitVec.ofNat 64 (top.base - state.basekeys)) top.len newRun.len
        state.listlen hvalid).2
      unfold foundNewRun? at hfound
      have hnotEmptyBool : state.pending.isEmpty = false :=
        Bool.eq_false_of_not_eq_true hempty
      simp only [hnotEmptyBool, Bool.false_eq_true, if_false, htopLookup]
        at hfound
      split at hfound
      next hguard =>
        simp only [hnewLen, hstopped, Bool.not_true, Bool.false_eq_true,
          if_false] at hfound
        apply foundNewRunLoop_preserves_ready state.pending.size state scanned
          before top newRun prospectivePower result hmax hlayout hpowered hsplit
          hnewBase hnewNonnegative hnewPositive hnewWithin hprospectivePower
          hpowerRange
        · simpa [prospectivePower] using hfound
        · exact hcode
        · exact hfuel
      next hguard => simp at hfound

end CPythonListsort
