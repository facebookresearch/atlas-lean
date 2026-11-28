/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.NPComplete.FlowShopSchedulingDefs
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.Complexity
import CSLibExt.Computability.CookLevin
import CSLibExt.Computability.Complexity.Basic
import CSLibExt.Computability.Complexity.Host
import CSLibExt.Computability.Complexity.Karp.FlowShop
import CSLibExt.Computability.Complexity.Karp.FlowShop.Basic
import CSLibExt.Computability.Complexity.PolynomialEncoding.ListNat
import MathlibExt.Computability.TuringMachine.BitOps
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.List.GetD
import Mathlib.Data.Num.Lemmas
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# FLOW-SHOP SCHEDULING is NP-hard

3-machine flow shop reduces to FLOW-SHOP SCHEDULING with `m` part of the instance. The reduction
prepends the framed number of processors `3` and keeps the rest of the input. A 3-machine
instance with deadline `0` is feasible exactly when every job is all zero, while FLOW-SHOP
SCHEDULING requires a positive deadline; so the deadline `1` is appended exactly when the input
encodes a list of jobs `[0, 0, 0]` with an empty deadline. These inputs form a regular language
(repeated copies of one fixed frame and a terminator), so a finite-state transducer computes the
reduction. Other inputs with an empty deadline are rejected on both sides.

Source: M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), [SS15];
M. R. Garey, D. S. Johnson and R. Sethi, "The complexity of flowshop and jobshop scheduling",
Mathematics of Operations Research 1 (1976), 117-129.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling

open MetaMathlibExt.BitstringEncoding

/-- Well-formedness transfers between `m = 3` scheduling and 3-machine flow shop. -/
private theorem sched_wellFormed_mk3 {jobs : List (List ℕ)} {D : ℕ} (hD : 0 < D) :
    MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling.WellFormed (3, jobs, D) ↔
      MetaMathlibExt.Complexity.NPComplete.FlowShop.WellFormed (jobs, D) := by
  constructor
  · intro h job hj
    exact (h.2.1 job hj)
  · intro h
    refine ⟨?_, h, hD⟩
    change (0 : ℕ) < 3
    decide

/-- Feasibility transfers from 3-machine flow shop to `m = 3` scheduling. -/
private theorem feasible_of_flowShop {jobs : List (List ℕ)} {D : ℕ}
    (h : MetaMathlibExt.Complexity.NPComplete.FlowShop.FlowShopFeasible (jobs, D)) :
    MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling.FlowShopSchedulingFeasible
      (3, jobs, D) := by
  obtain ⟨start, hlen, hrows, hjob, hmach⟩ := h
  refine ⟨fun p j => (start.getD j.val []).getD p.val 0, ?_, ?_, ?_⟩
  · intro p j
    dsimp only
    unfold MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling.len
    dsimp only
    have hj := hjob j.val j.isLt
    dsimp only at hj
    fin_cases p <;> dsimp only at hj ⊢ <;> omega
  · intro p j k hne
    dsimp only
    unfold MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling.len
    dsimp only
    have hne' : j.val ≠ k.val := fun he => hne (Fin.ext he)
    rcases lt_or_gt_of_ne hne' with hlt | hgt
    · exact hmach p.val p.isLt j.val j.isLt k.val k.isLt hlt
    · exact (hmach p.val p.isLt k.val k.isLt j.val j.isLt hgt).symm
  · intro p hp j
    dsimp only
    unfold MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling.len
    dsimp only
    have hj := hjob j.val j.isLt
    dsimp only at hj
    fin_cases p
    · simpa using hj.1
    · simpa using hj.2.1
    · dsimp only at hp; omega

/-- Feasibility transfers from `m = 3` scheduling to 3-machine flow shop. -/
private theorem feasible_of_sched {jobs : List (List ℕ)} {D : ℕ}
    (h : MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling.FlowShopSchedulingFeasible
      (3, jobs, D)) :
    MetaMathlibExt.Complexity.NPComplete.FlowShop.FlowShopFeasible (jobs, D) := by
  obtain ⟨σ, hdead, hsep, hord⟩ := h
  have lt0 : (0 : ℕ) < (3, jobs, D).1 := by change (0 : ℕ) < 3; decide
  have lt1 : (1 : ℕ) < (3, jobs, D).1 := by change (1 : ℕ) < 3; decide
  have lt2 : (2 : ℕ) < (3, jobs, D).1 := by change (2 : ℕ) < 3; decide
  have hp0 : (⟨0, lt0⟩ : Fin (3, jobs, D).1).val + 1 < (3, jobs, D).1 := by
    change (1 : ℕ) < 3; decide
  have hp1 : (⟨1, lt1⟩ : Fin (3, jobs, D).1).val + 1 < (3, jobs, D).1 := by
    change (2 : ℕ) < 3; decide
  have hget : ∀ (j : ℕ) (hj : j < jobs.length) (k : ℕ) (hk : k < 3),
      List.getD (List.getD (List.ofFn (fun j : Fin jobs.length =>
        [σ ⟨0, lt0⟩ j, σ ⟨1, lt1⟩ j, σ ⟨2, lt2⟩ j])) j [])
        k 0 = σ ⟨k, hk⟩ ⟨j, hj⟩ := by
    intro j hj k hk
    have hj' : j < (List.ofFn (fun j : Fin jobs.length =>
        [σ ⟨0, lt0⟩ j, σ ⟨1, lt1⟩ j, σ ⟨2, lt2⟩ j])).length := by
      simpa using hj
    rw [List.getD_eq_getElem _ _ hj', List.getElem_ofFn hj']
    interval_cases k <;> rfl
  refine ⟨List.ofFn (fun j : Fin jobs.length =>
    [σ ⟨0, lt0⟩ j, σ ⟨1, lt1⟩ j, σ ⟨2, lt2⟩ j]), ?_, ?_, ?_, ?_⟩
  · simp
  · intro row hr
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
    rw [List.getElem_ofFn hi]
    rfl
  · intro j hj
    dsimp only
    rw [hget j hj 0 (by decide), hget j hj 1 (by decide), hget j hj 2 (by decide)]
    have hjJ : j < (3, jobs, D).2.1.length := hj
    have h0 := hord ⟨0, lt0⟩ hp0 ⟨j, hjJ⟩
    have h1 := hord ⟨1, lt1⟩ hp1 ⟨j, hjJ⟩
    have h2 := hdead ⟨2, lt2⟩ ⟨j, hjJ⟩
    exact ⟨h0, h1, h2⟩
  · intro k hk a ha b hb hab
    dsimp only
    rw [hget a ha k hk, hget b hb k hk]
    have haJ : a < (3, jobs, D).2.1.length := ha
    have hbJ : b < (3, jobs, D).2.1.length := hb
    have hk3 : k < (3, jobs, D).1 := hk
    have hne : (⟨a, haJ⟩ : Fin (3, jobs, D).2.1.length) ≠ ⟨b, hbJ⟩ := by
      intro he
      have hav : a = b := by simpa using he
      omega
    exact hsep ⟨k, hk3⟩ ⟨a, haJ⟩ ⟨b, hbJ⟩ hne

/-- A feasible 3-machine flow-shop instance with deadline `0` has all-zero entries. -/
private theorem flowShop_D0_allZero {jobs : List (List ℕ)}
    (h : MetaMathlibExt.Complexity.NPComplete.FlowShop.FlowShopFeasible (jobs, 0)) :
    ∀ j < jobs.length, ∀ k < 3, (jobs.getD j []).getD k 0 = 0 := by
  obtain ⟨start, hlen, hrows, hjob, hmach⟩ := h
  intro j hj k hk
  have hj3 := hjob j hj
  dsimp only at hj3
  interval_cases k
  · omega
  · omega
  · omega

/-- An all-zero 3-machine flow-shop instance with deadline `0` is feasible. -/
private theorem flowShop_feasible_D0_of_allZero {jobs : List (List ℕ)}
    (hall : ∀ j < jobs.length, ∀ k < 3, (jobs.getD j []).getD k 0 = 0) :
    MetaMathlibExt.Complexity.NPComplete.FlowShop.FlowShopFeasible (jobs, 0) := by
  have hs : ∀ (j : ℕ) (hj : j < jobs.length) (k : ℕ) (hk : k < 3),
      List.getD (List.getD (List.ofFn (fun _ : Fin jobs.length => [0, 0, 0])) j [])
        k 0 = 0 := by
    intro j hj k hk
    have hj' : j < (List.ofFn (fun _ : Fin jobs.length => [0, 0, 0])).length := by
      simpa using hj
    rw [List.getD_eq_getElem _ _ hj', List.getElem_ofFn hj']
    interval_cases k <;> rfl
  refine ⟨List.ofFn (fun _ : Fin jobs.length => [0, 0, 0]), ?_, ?_, ?_, ?_⟩
  · simp
  · intro row hr
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hr
    rw [List.getElem_ofFn hi]
    rfl
  · intro j hj
    dsimp only
    rw [hs j hj 0 (by decide), hs j hj 1 (by decide), hs j hj 2 (by decide),
      hall j hj 0 (by decide), hall j hj 1 (by decide), hall j hj 2 (by decide)]
    exact ⟨le_rfl, le_rfl, le_rfl⟩
  · intro k hk a ha b hb hab
    dsimp only
    rw [hs a ha k hk, hs b hb k hk, hall a ha k hk, hall b hb k hk]
    exact Or.inl le_rfl

/-- An all-zero `m = 3` scheduling instance with deadline `1` is feasible. -/
private theorem sched_feasible_mk3_D1_of_allZero {jobs : List (List ℕ)}
    (hall : ∀ j < jobs.length, ∀ k < 3, (jobs.getD j []).getD k 0 = 0) :
    MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling.FlowShopSchedulingFeasible
      (3, jobs, 1) := by
  refine ⟨fun _ _ => 0, ?_, ?_, ?_⟩
  · intro p j
    have hl : MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling.len (3, jobs, 1) p j = 0 :=
      hall j.val j.isLt p.val p.isLt
    dsimp only
    rw [hl]
    change (0 : ℕ) + 0 ≤ 1
    decide
  · intro p j k hne
    have hlj : MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling.len (3, jobs, 1) p j = 0 :=
      hall j.val j.isLt p.val p.isLt
    have hlk : MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling.len (3, jobs, 1) p k = 0 :=
      hall k.val k.isLt p.val p.isLt
    dsimp only
    rw [hlj, hlk]
    exact Or.inl le_rfl
  · intro p hp j
    have hl : MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling.len (3, jobs, 1) p j = 0 :=
      hall j.val j.isLt p.val p.isLt
    dsimp only
    rw [hl]

private theorem bitDecode_nat_eq (e : List Bool) :
    bitDecode (α := ℕ) e = some (Computability.decodeNat e) := rfl

private theorem bitDecode_pair_eq {β γ : Type} [MetaMathlibExt.BitstringEncoding β]
    [MetaMathlibExt.BitstringEncoding γ] (x : List Bool) :
    bitDecode (α := β × γ) x =
      match undelimit x with
      | none => none
      | some (block, rest) =>
        match bitDecode block, bitDecode rest with
        | some a, some b => some (a, b)
        | _, _ => none := rfl

private theorem bitDecode_list_eq {β : Type} [MetaMathlibExt.BitstringEncoding β]
    (x : List Bool) :
    bitDecode (α := List β) x = (undelimitBlocks x).bind (·.mapM bitDecode) := rfl

private theorem decodeNat_nil : Computability.decodeNat ([] : List Bool) = 0 := rfl

private theorem decodeNat_eq_zero_iff (E : List Bool) :
    Computability.decodeNat E = 0 ↔ E = [] := by
  constructor
  · intro h
    by_contra hne
    have hdecode : Computability.decodeNum E = ↑(Computability.decodePosNum E) := by
      unfold Computability.decodeNum
      simp [hne]
    have hne0 : (Computability.decodeNum E : ℕ) ≠ 0 := by
      rw [hdecode]
      have hq := PosNum.to_nat_pos (Computability.decodePosNum E)
      have hcoe : (((Computability.decodePosNum E : PosNum) : Num) : ℕ) =
          ((Computability.decodePosNum E : PosNum) : ℕ) := by simp
      rw [hcoe]
      exact ne_of_gt hq
    simp only [Computability.decodeNat] at h
    exact hne0 h
  · intro h
    rw [h]
    rfl

private theorem mapM_some_length {α β : Type} {f : α → Option β} {xs : List α}
    {ys : List β} (h : xs.mapM f = some ys) : ys.length = xs.length := by
  induction xs generalizing ys with
  | nil => simpa using h.symm
  | cons a xs ih =>
    simp only [List.mapM_cons, Bind.bind, Option.bind] at h
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases hb : xs.mapM f with
      | none => simp [ha, hb] at h
      | some bs =>
        have he : b :: bs = ys := by simpa [ha, hb] using h
        subst ys
        simp [ih hb]

private theorem mapM_some_getD {α β : Type} {f : α → Option β} {xs : List α}
    {ys : List β} {d : α} {d' : β} (h : xs.mapM f = some ys) (j : ℕ)
    (hj : j < xs.length) :
    f (xs.getD j d) = some (ys.getD j d') := by
  induction xs generalizing ys j with
  | nil => simp at hj
  | cons a xs ih =>
    cases j with
    | zero =>
      simp only [List.mapM_cons, Bind.bind, Option.bind] at h
      cases ha : f a with
      | none => simp [ha] at h
      | some b =>
        cases hb : xs.mapM f with
        | none => simp [ha, hb] at h
        | some bs =>
          have he : b :: bs = ys := by simpa [ha, hb] using h
          subst ys
          simp [ha]
    | succ j =>
      simp only [List.mapM_cons, Bind.bind, Option.bind] at h
      cases ha : f a with
      | none => simp [ha] at h
      | some b =>
        cases hb : xs.mapM f with
        | none => simp [ha, hb] at h
        | some bs =>
          have he : b :: bs = ys := by simpa [ha, hb] using h
          subst ys
          exact ih hb j (Nat.lt_of_succ_lt_succ hj)

/-- Bit-level all-zero test on a jobs payload: every job block parses and its first three
number blocks are empty. -/
private def allZeroBits (Jp : List Bool) : Bool :=
  match undelimitBlocks Jp with
  | none => false
  | some jobss => jobss.all fun job =>
      match undelimitBlocks job with
      | none => false
      | some nums => (nums.getD 0 [] == []) && (nums.getD 1 [] == []) && (nums.getD 2 [] == [])

/-- The framed encoding of `3` prepended by the reduction. -/
private def redConst : List Bool := delimit (Computability.encodeNat 3)

/-- Bitstring reduction from 3-machine flow shop to general flow-shop scheduling. -/
private def redFun (x : List Bool) : List Bool :=
  match undelimit x with
  | none => redConst ++ x
  | some (Jp, E) =>
      let E' := if E == [] && allZeroBits Jp then Computability.encodeNat 1 else E
      redConst ++ delimit Jp ++ E'

open Classical in
private theorem flowShopDec_eq (x : List Bool) :
    MetaMathlibExt.Complexity.NPComplete.FlowShop.flowShopDec x =
    match undelimit x with
    | none => false
    | some (Jp, E) =>
        match bitDecode (α := List (List ℕ)) Jp with
        | none => false
        | some jobsL =>
            decide (MetaMathlibExt.Complexity.NPComplete.FlowShop.WellFormed
                (jobsL, Computability.decodeNat E) ∧
              MetaMathlibExt.Complexity.NPComplete.FlowShop.FlowShopFeasible
                (jobsL, Computability.decodeNat E)) := by
  unfold MetaMathlibExt.Complexity.NPComplete.FlowShop.flowShopDec
  rw [bitDecode_pair_eq]
  cases hux : undelimit x with
  | none => rfl
  | some q =>
    obtain ⟨Jp, E⟩ := q
    cases hj : bitDecode (α := List (List ℕ)) Jp with
    | none => simp [hj, bitDecode_nat_eq]
    | some jobsL => simp [hj, bitDecode_nat_eq]

private theorem allZeroBits_imp_allZero {Jp : List Bool} {jobsL : List (List ℕ)}
    (hdec : bitDecode (α := List (List ℕ)) Jp = some jobsL)
    (haz : allZeroBits Jp = true) :
    ∀ j < jobsL.length, ∀ k < 3, (jobsL.getD j []).getD k 0 = 0 := by
  unfold allZeroBits at haz
  rw [bitDecode_list_eq] at hdec
  obtain ⟨jobss, hblocks, hmap⟩ := Option.bind_eq_some_iff.mp hdec
  rw [hblocks] at haz
  simp only at haz
  rw [List.all_eq_true] at haz
  intro j hj k hk
  have hlen : jobsL.length = jobss.length := mapM_some_length hmap
  have hj' : j < jobss.length := hlen ▸ hj
  have hjob := mapM_some_getD (d := ([] : List Bool)) (d' := ([] : List ℕ)) hmap j hj'
  have hmem : jobss.getD j [] ∈ jobss := by
    rw [List.getD_eq_getElem _ _ hj']
    exact List.getElem_mem hj'
  have hcheck := haz _ hmem
  rw [bitDecode_list_eq] at hjob
  obtain ⟨nums, hnums, hmapN⟩ := Option.bind_eq_some_iff.mp hjob
  rw [hnums] at hcheck
  simp only at hcheck
  simp only [Bool.and_eq_true, beq_iff_eq] at hcheck
  obtain ⟨⟨h0, h1⟩, h2⟩ := hcheck
  have hjobEq : jobsL.getD j [] = nums.map Computability.decodeNat := by
    have hmm := Cslib.Complexity.PolynomialEncoding.mapM_decode_nat nums
    rw [hmapN] at hmm
    simpa using hmm
  rw [hjobEq, List.getD_eq_getElem?_getD, List.getElem?_map]
  by_cases hkq : nums[k]? = none
  · simp [hkq]
  · obtain ⟨e, he⟩ := Option.ne_none_iff_exists.mp hkq
    rw [← he]
    simp only [Option.map_some, Option.getD_some]
    have hge : nums.getD k [] = e := by
      rw [List.getD_eq_getElem?_getD, ← he, Option.getD_some]
    rw [← hge]
    interval_cases k
    · rw [h0]; exact decodeNat_nil
    · rw [h1]; exact decodeNat_nil
    · rw [h2]; exact decodeNat_nil

private theorem allZeroBits_of_allZero {Jp : List Bool} {jobsL : List (List ℕ)}
    (hdec : bitDecode (α := List (List ℕ)) Jp = some jobsL)
    (hall : ∀ j < jobsL.length, ∀ k < 3, (jobsL.getD j []).getD k 0 = 0) :
    allZeroBits Jp = true := by
  unfold allZeroBits
  rw [bitDecode_list_eq] at hdec
  obtain ⟨jobss, hblocks, hmap⟩ := Option.bind_eq_some_iff.mp hdec
  rw [hblocks]
  simp only
  rw [List.all_eq_true]
  intro job hjobmem
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hjobmem
  rw [List.getElem_eq_getD ([] : List Bool)]
  have hlen : jobsL.length = jobss.length := mapM_some_length hmap
  have hjL : j < jobsL.length := hlen ▸ hj
  have hjob := mapM_some_getD (d := ([] : List Bool)) (d' := ([] : List ℕ)) hmap j hj
  rw [bitDecode_list_eq] at hjob
  obtain ⟨nums, hnums, hmapN⟩ := Option.bind_eq_some_iff.mp hjob
  rw [hnums]
  simp only
  have hjobEq : jobsL.getD j [] = nums.map Computability.decodeNat := by
    have hmm := Cslib.Complexity.PolynomialEncoding.mapM_decode_nat nums
    rw [hmapN] at hmm
    simpa using hmm
  have hentry : ∀ k < 3, nums.getD k [] = [] := by
    intro k hk
    have hallk := hall j hjL k hk
    rw [hjobEq] at hallk
    by_cases hkq : nums[k]? = none
    · simp [List.getD_eq_getElem?_getD, hkq]
    · obtain ⟨e, he⟩ := Option.ne_none_iff_exists.mp hkq
      have hge : nums.getD k [] = e := by
        rw [List.getD_eq_getElem?_getD, ← he, Option.getD_some]
      rw [hge]
      have hmapk : (nums.map Computability.decodeNat).getD k 0 =
          Computability.decodeNat e := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_map, ← he,
          Option.map_some, Option.getD_some]
      rw [hmapk] at hallk
      exact (decodeNat_eq_zero_iff e).mp hallk
  have h0 := hentry 0 (by decide)
  have h1 := hentry 1 (by decide)
  have h2 := hentry 2 (by decide)
  rw [h0, h1, h2]
  decide

open Classical in
private theorem schedDec_eq (y : List Bool) : flowShopSchedulingDec y =
    match undelimit y with
    | none => false
    | some (M, R1) =>
        match undelimit R1 with
        | none => false
        | some (Jp, E) =>
            match bitDecode (α := List (List ℕ)) Jp with
            | none => false
            | some jobsL =>
                decide (MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling.WellFormed
                    (Computability.decodeNat M, jobsL, Computability.decodeNat E) ∧
                  MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling.FlowShopSchedulingFeasible
                    (Computability.decodeNat M, jobsL, Computability.decodeNat E)) := by
  unfold flowShopSchedulingDec
  simp only [bitDecode_pair_eq, bitDecode_nat_eq]
  cases hux : undelimit y with
  | none => simp
  | some q =>
    obtain ⟨M, R1⟩ := q
    cases hu2 : undelimit R1 with
    | none =>
      simp [hu2]
    | some q2 =>
      obtain ⟨Jp, E⟩ := q2
      cases hj : bitDecode (α := List (List ℕ)) Jp with
      | none => simp [hu2, hj]
      | some jobsL => simp [hu2, hj]

private theorem decodeNat_pos_of_ne_nil {E : List Bool} (h : E ≠ []) :
    0 < Computability.decodeNat E := by
  have hne : Computability.decodeNat E ≠ 0 :=
    fun hz => h ((decodeNat_eq_zero_iff E).mp hz)
  omega

open Classical in
private theorem redFun_correct (x : List Bool) :
    MetaMathlibExt.Complexity.NPComplete.FlowShop.flowShopDec x =
      flowShopSchedulingDec (redFun x) := by
  rw [flowShopDec_eq, schedDec_eq]
  unfold redFun
  cases hux : undelimit x with
  | none =>
    dsimp only
    unfold redConst
    simp [undelimit_delimit, hux]
  | some q =>
    obtain ⟨Jp, E⟩ := q
    dsimp only
    unfold redConst
    simp only [List.append_assoc, undelimit_delimit]
    cases hj : bitDecode (α := List (List ℕ)) Jp with
    | none => simp
    | some jobsL =>
      dsimp only
      cases E with
      | nil =>
        cases haz : allZeroBits Jp with
        | true =>
          apply Bool.decide_congr
          simp only [Computability.decode_encodeNat, BEq.rfl, Bool.and_self, ↓reduceIte]
          constructor
          · intro ⟨hwf, hfeas⟩
            have hall := flowShop_D0_allZero hfeas
            refine ⟨?_, sched_feasible_mk3_D1_of_allZero hall⟩
            refine ⟨?_, ?_, ?_⟩
            · change (0 : ℕ) < 3; decide
            · intro job hmem
              exact hwf job hmem
            · change (0 : ℕ) < 1; decide
          · intro ⟨hwf, hfeas⟩
            have hwf3 : ∀ job ∈ jobsL, job.length = 3 := hwf.2.1
            have hall := allZeroBits_imp_allZero hj haz
            exact ⟨hwf3, flowShop_feasible_D0_of_allZero hall⟩
        | false =>
          apply Bool.decide_congr
          simp only [Computability.decode_encodeNat, BEq.rfl, Bool.and_false, Bool.false_eq_true,
            ↓reduceIte]
          constructor
          · intro ⟨hwf, hfeas⟩
            have hall := flowShop_D0_allZero hfeas
            have haz' := allZeroBits_of_allZero hj hall
            rw [haz] at haz'
            simp at haz'
          · intro ⟨hwf, hfeas⟩
            have h0 : ¬ (0 : ℕ) < (3, jobsL, 0).2.2 := by change ¬ (0 : ℕ) < 0; decide
            exact absurd hwf.2.2 h0
      | cons b E2 =>
        have hDpos : 0 < Computability.decodeNat (b :: E2) :=
          decodeNat_pos_of_ne_nil (by simp)
        apply Bool.decide_congr
        simp only [Computability.decode_encodeNat, List.beq_nil_eq, List.isEmpty_cons,
          Bool.false_and, Bool.false_eq_true, ↓reduceIte]
        constructor
        · intro ⟨hwf, hfeas⟩
          exact ⟨(sched_wellFormed_mk3 hDpos).mpr hwf, feasible_of_flowShop hfeas⟩
        · intro ⟨hwf, hfeas⟩
          exact ⟨(sched_wellFormed_mk3 hDpos).mp hwf, feasible_of_sched hfeas⟩

/-! ### A regular test for the all-zero, zero-deadline family -/

/-- The encoding of the job `[0, 0, 0]` as a framed list block. -/
private abbrev zjob : List Bool := delimit [false, false, false]

/-- The encoding of the jobs part `(n copies of [0, 0, 0])` followed by an empty deadline. -/
private def zenc (n : ℕ) : List Bool := delimit (List.replicate n zjob).flatten

/-- The framed form of one `zjob` block. -/
private abbrev W : List Bool :=
  [true, true, true, false, true, true, true, false, true, true, true, false, true, false]

private theorem delimit_append (a b : List Bool) :
    delimit (a ++ b) = a.flatMap (fun x => [true, x]) ++ delimit b := by
  induction a with
  | nil => rfl
  | cons x a ih => simp [delimit, ih]

private theorem zenc_eq (n : ℕ) : zenc n = (List.replicate n W).flatten ++ [false] := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [zenc, List.replicate_succ, List.flatten_cons, delimit_append, ← zenc, ih]
    rfl

/-- Transition function of the automaton recognizing `W* false`: state `k < 14` is the position
inside `W`, `14` accepts, `15` rejects. -/
private def δ (k : ℕ) (b : Bool) : ℕ :=
  if k = 0 then (if b then 1 else 14)
  else if k < 14 then (if b = W.getD k false then (k + 1) % 14 else 15) else 15

private theorem δ_lt (k : ℕ) (b : Bool) : δ k b < 16 := by
  unfold δ
  split_ifs <;> omega

private def run (k : ℕ) (x : List Bool) : ℕ := x.foldl δ k

private theorem run_dead : ∀ x : List Bool, run 15 x = 15
  | [] => rfl
  | _ :: x => run_dead x

private theorem run_acc (x : List Bool) : run 14 x = 14 ↔ x = [] := by
  cases x with
  | nil => simp [run]
  | cons b x =>
    simp only [reduceCtorEq, iff_false]
    change run 15 x ≠ 14
    rw [run_dead]
    omega

private theorem run_W (r : List Bool) : run 0 (W ++ r) = run 0 r := by
  unfold run
  rw [List.foldl_append]
  rfl

private theorem drop_W : ∀ k < 14, W.drop k = W.getD k false :: W.drop (k + 1) := by decide

private theorem run_mid : ∀ (x : List Bool) (k : ℕ), 1 ≤ k → k ≤ 13 → run k x = 14 →
    ∃ r, x = W.drop k ++ r ∧ run 0 r = 14
  | [], k, _, h₂, h => by simp [run] at h; omega
  | b :: x, k, h₁, h₂, h => by
    change run (δ k b) x = 14 at h
    have hk0 : k ≠ 0 := by omega
    by_cases hb : b = W.getD k false
    · have hδ : δ k b = (k + 1) % 14 := by
        unfold δ
        simp only [hk0, ↓reduceIte, show k < 14 by omega, hb]
      rw [hδ] at h
      rw [drop_W k (by omega), ← hb]
      by_cases h13 : k = 13
      · subst h13
        exact ⟨x, rfl, h⟩
      · rw [Nat.mod_eq_of_lt (by omega)] at h
        obtain ⟨r, rfl, hr⟩ := run_mid x (k + 1) (by omega) (by omega) h
        exact ⟨r, rfl, hr⟩
    · have hδ : δ k b = 15 := by
        unfold δ
        simp only [hk0, ↓reduceIte, show k < 14 by omega, hb]
      rw [hδ, run_dead] at h
      omega

private theorem run_zero_iff : ∀ (n : ℕ) (x : List Bool), x.length ≤ n →
    (run 0 x = 14 ↔ ∃ m, x = (List.replicate m W).flatten ++ [false]) := by
  intro n
  induction n with
  | zero =>
    intro x hx
    rw [List.length_eq_zero_iff.1 (Nat.le_zero.1 hx)]
    constructor
    · intro h; simp [run] at h
    · rintro ⟨m, hm⟩; simp at hm
  | succ n ih =>
    intro x hx
    constructor
    · intro h
      match x, hx, h with
      | [], _, h => simp [run] at h
      | false :: r, _, h =>
        change run 14 r = 14 at h
        rw [run_acc] at h
        exact ⟨0, by simp [h]⟩
      | true :: r, hx, h =>
        change run 1 r = 14 at h
        obtain ⟨r', rfl, hr'⟩ := run_mid r 1 le_rfl (by omega) h
        have hl : r'.length ≤ n := by simp at hx; omega
        obtain ⟨m, rfl⟩ := (ih r' hl).1 hr'
        exact ⟨m + 1, by simp [List.replicate_succ]⟩
    · rintro ⟨m, rfl⟩
      clear hx ih
      induction m with
      | zero => rfl
      | succ m ihm =>
        rw [List.replicate_succ, List.flatten_cons, List.append_assoc, run_W]
        exact ihm

private theorem run_zero_zenc (x : List Bool) : run 0 x = 14 ↔ ∃ n, x = zenc n := by
  rw [run_zero_iff x.length x le_rfl]
  simp only [zenc_eq]

/-- The reduction used below: as `redFun`, but the deadline `1` is supplied exactly on the
regular family of inputs encoding all-zero jobs `[0, 0, 0]` and an empty deadline. -/
private def redFun' (x : List Bool) : List Bool :=
  redConst ++ x ++ (if run 0 x = 14 then [true] else [])

private theorem undelimitBlocks_zjobs (n : ℕ) :
    undelimitBlocks (List.replicate n zjob).flatten =
      some (List.replicate n [false, false, false]) := by
  have h := undelimitBlocks_flatten_delimit (List.replicate n [false, false, false])
  simpa [List.map_replicate] using h

private theorem allZeroBits_zjobs (n : ℕ) : allZeroBits (List.replicate n zjob).flatten = true := by
  unfold allZeroBits
  rw [undelimitBlocks_zjobs]
  simp only [List.all_eq_true, List.mem_replicate]
  rintro job ⟨-, rfl⟩
  rfl

private theorem redFun_zenc (n : ℕ) : redFun (zenc n) = redConst ++ zenc n ++ [true] := by
  have hu : undelimit (zenc n) = some ((List.replicate n zjob).flatten, []) := by
    have := undelimit_delimit (List.replicate n zjob).flatten []
    simpa [zenc] using this
  unfold redFun
  rw [hu]
  simp only [allZeroBits_zjobs, beq_self_eq_true, Bool.and_self, ↓reduceIte]
  simp [zenc, List.append_assoc]
  rfl

private theorem nums_zero {nums : List (List Bool)}
    (h : nums.map Computability.decodeNat = [0, 0, 0]) : nums = [[], [], []] := by
  match nums, h with
  | [], h | [_], h | [_, _], h | _ :: _ :: _ :: _ :: _, h => simp at h
  | [a, b, c], h =>
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at h
    rw [(decodeNat_eq_zero_iff a).1 h.1, (decodeNat_eq_zero_iff b).1 h.2.1,
      (decodeNat_eq_zero_iff c).1 h.2.2]

private theorem job_bits_zero {b : List Bool}
    (h : bitDecode (α := List ℕ) b = some [0, 0, 0]) : b = [false, false, false] := by
  rw [Cslib.Complexity.PolynomialEncoding.decode_list_nat] at h
  obtain ⟨nums, hn, hm⟩ := Option.map_eq_some_iff.1 h
  have hb := Cslib.Complexity.PolynomialEncoding.blocks_decode_sound hn
  rw [hb, nums_zero hm]
  rfl

private theorem jobs_bits_zero : ∀ (jobss : List (List Bool)) (jobsL : List (List ℕ)),
    jobss.mapM (bitDecode (α := List ℕ)) = some jobsL → (∀ job ∈ jobsL, job = [0, 0, 0]) →
      jobss = List.replicate jobss.length [false, false, false]
  | [], _, _, _ => rfl
  | b :: bs, jobsL, h, hall => by
    simp only [List.mapM_cons, Bind.bind, Option.bind] at h
    cases hb : bitDecode (α := List ℕ) b with
    | none => simp [hb] at h
    | some j =>
      cases hbs : bs.mapM (bitDecode (α := List ℕ)) with
      | none => simp [hb, hbs] at h
      | some js =>
        have he : j :: js = jobsL := by simpa [hb, hbs] using h
        subst he
        have hj : j = [0, 0, 0] := hall j (by simp)
        rw [hj] at hb
        rw [job_bits_zero hb, jobs_bits_zero bs js hbs (fun k hk => hall k (by simp [hk]))]
        simp [List.replicate_succ]

private theorem jp_zero {Jp : List Bool} {jobsL : List (List ℕ)}
    (hdec : bitDecode (α := List (List ℕ)) Jp = some jobsL)
    (hall : ∀ job ∈ jobsL, job = [0, 0, 0]) :
    ∃ n, Jp = (List.replicate n zjob).flatten := by
  rw [bitDecode_list_eq] at hdec
  obtain ⟨jobss, hblocks, hmap⟩ := Option.bind_eq_some_iff.mp hdec
  have hJp := Cslib.Complexity.PolynomialEncoding.blocks_decode_sound hblocks
  refine ⟨jobss.length, ?_⟩
  rw [hJp, jobs_bits_zero jobss jobsL hmap hall, List.map_replicate]
  simp

open Classical in
private theorem redFun'_correct (x : List Bool) :
    MetaMathlibExt.Complexity.NPComplete.FlowShop.flowShopDec x =
      flowShopSchedulingDec (redFun' x) := by
  by_cases hz : ∃ n, x = zenc n
  · obtain ⟨n, rfl⟩ := hz
    have hr : redFun' (zenc n) = redFun (zenc n) := by
      rw [redFun_zenc, redFun']
      simp only [(run_zero_zenc _).2 ⟨n, rfl⟩, ↓reduceIte]
    rw [hr]
    exact redFun_correct _
  · have hr : redFun' x = redConst ++ x := by
      have hn : ¬ run 0 x = 14 := fun h => hz ((run_zero_zenc x).1 h)
      simp only [redFun', hn, ↓reduceIte, List.append_nil]
    rw [hr]
    cases hux : undelimit x with
    | none =>
      have : redFun x = redConst ++ x := by unfold redFun; rw [hux]
      rw [← this]
      exact redFun_correct x
    | some q =>
      obtain ⟨Jp, E⟩ := q
      have hx := (Cslib.CookLevin.undelimit_eq_some_iff _ _ _).1 hux
      by_cases hc : E = [] ∧ allZeroBits Jp = true
      · obtain ⟨rfl, haz⟩ := hc
        have hsched : flowShopSchedulingDec (redConst ++ x) = false := by
          rw [schedDec_eq]
          unfold redConst
          simp only [undelimit_delimit, hux]
          cases bitDecode (α := List (List ℕ)) Jp with
          | none => rfl
          | some jobsL =>
            simp only [decide_eq_false_iff_not, not_and]
            intro hwf
            exact absurd hwf.2.2 (by simp [decodeNat_nil])
        rw [hsched, flowShopDec_eq, hux]
        dsimp only
        cases hj : bitDecode (α := List (List ℕ)) Jp with
        | none => rfl
        | some jobsL =>
          dsimp only
          simp only [decide_eq_false_iff_not, not_and]
          intro hwf hfeas
          have hall0 := flowShop_D0_allZero (by simpa [decodeNat_nil] using hfeas)
          have hall : ∀ job ∈ jobsL, job = [0, 0, 0] := by
            intro job hmem
            obtain ⟨j, hj', rfl⟩ := List.mem_iff_getElem.mp hmem
            have hl : jobsL[j].length = 3 := hwf _ hmem
            have h0 := hall0 j hj' 0 (by decide)
            have h1 := hall0 j hj' 1 (by decide)
            have h2 := hall0 j hj' 2 (by decide)
            rw [List.getD_eq_getElem _ _ hj'] at h0 h1 h2
            match hjob : jobsL[j], hl with
            | [a, b, c], _ =>
              rw [hjob] at h0 h1 h2
              simp only [List.getD_cons_zero, List.getD_cons_succ] at h0 h1 h2
              rw [h0, h1, h2]
          obtain ⟨n, rfl⟩ := jp_zero hj hall
          exact hz ⟨n, by simpa [zenc] using hx⟩
      · have : redFun x = redConst ++ x := by
          unfold redFun
          rw [hux]
          have hne : ¬ ((E == [] && allZeroBits Jp) = true) := by
            simpa [Bool.and_eq_true, beq_iff_eq] using hc
          simp only [hne, Bool.false_eq_true, ↓reduceIte]
          rw [hx, List.append_assoc]
        rw [← this]
        exact redFun_correct x

/-! ### Polynomial time

`scan` and `polyScan` are copied from
`CSLibExt/Computability/Complexity/Karp/CardinalitySubsetSum.lean`, where they are private. -/

section Scan

open ComplexityTheory Computability Turing Function TM2Program Cslib.Complexity

private def scan {Q : Type} (step : Q → Bool → Q × List Bool) (finish : Q → List Bool)
    (q : Q) : List Bool → List Bool
  | [] => finish q
  | b :: x => (step q b).2 ++ scan step finish (step q b).1 x

/-- A finite-state scan stores output in reverse order and reverses it once at the end.
Each transition emits a bounded number of bits because the state and input alphabets are finite. -/
private theorem polyScan {Q : Type} [Finite Q]
    (step : Q → Bool → Q × List Bool) (finish : Q → List Bool) (q₀ : Q) :
    IsPolyTime (scan step finish q₀) := by
  classical
  let := Fintype.ofFinite Q
  let prog : Q ⊕ Bool → TM2.Stmt (fun _ : Fin 3 => Bool) (Q ⊕ Bool) Bool
    | .inl q =>
      .peek 0 (fun _ o => o.isNone) <| .branch id
        (emit 1 (finish q) (.inr false))
        (.pop 0 (fun _ o => o.getD false) <| .branch id
          (emit 1 (step q true).2 (.inl (step q true).1))
          (emit 1 (step q false).2 (.inl (step q false).1)))
    | .inr false => moveB 1 2 some id (.inr false) (.inr true)
    | .inr true => .halt
  let comp : Host.Comp := {
    K := Fin 3, Γ := fun _ => Bool, L := Q ⊕ Bool, prog := prog,
    ks := [0, 1, 2], ks_nodup := by decide, mem_ks := by decide }
  let st (x r o : List Bool) : Fin 3 → List Bool := ![x, r, o]
  have up0 (x r o l : List Bool) : update (st x r o) 0 l = st l r o := by
    funext k
    fin_cases k <;> rfl
  have up1 (x r o l : List Bool) : update (st x r o) 1 l = st x l o := by
    funext k
    fin_cases k <;> rfl
  have hr (x : List Bool) (q : Q) (v : Bool) (r : List Bool) :
      Run prog (x.length + 1) ⟨some (.inl q), v, st x r []⟩
        ⟨some (.inr false), true, st [] ((scan step finish q x).reverse ++ r) []⟩ := by
    induction x generalizing q v r with
    | nil =>
      apply Run.single
      simp [prog, TM2.stepAux, emit, stepAux_pushList, scan, up1, st]
    | cons b x ih =>
      have h := ih (step q b).1 b ((step q b).2.reverse ++ r)
      simp only [scan, List.reverse_append, List.append_assoc]
      refine Run.head ?_ h
      cases b <;>
        simp [TM2.step, prog, TM2.stepAux, emit, stepAux_pushList, up0, up1, st]
  let B := Finset.univ.sup fun q : Q =>
    max (finish q).length (max (step q true).2.length (step q false).2.length)
  have bound (x : List Bool) (q : Q) : (scan step finish q x).length ≤ (x.length + 1) * B := by
    have h (q : Q) : max (finish q).length
        (max (step q true).2.length (step q false).2.length) ≤ B :=
      Finset.le_sup (f := fun q : Q =>
        max (finish q).length (max (step q true).2.length (step q false).2.length))
        (Finset.mem_univ q)
    induction x generalizing q with
    | nil => simpa [scan] using (le_max_left _ _).trans (h q)
    | cons b x ih =>
      have hb : (step q b).2.length ≤ B := by cases b <;> have := h q <;> omega
      have hi := ih (step q b).1
      simp only [scan, List.length_append, List.length_cons, Nat.succ_mul] at hi ⊢
      omega
  apply Host.isPolyTime_reduction (c := comp) (cX := 0) (cO := 2)
    (gX := id) (start := .inl q₀) (done := .inr true) (Equiv.refl Bool) _
    ((Polynomial.X + 1) * (Polynomial.C B + 1) + 1) rfl
  intro x
  let y := scan step finish q₀ x
  have h₁ := hr x q₀ false []
  simp only [List.append_nil] at h₁
  obtain ⟨v, S, h₂, _, ho, _⟩ := moveB_run (M := prog)
    (self := Sum.inr false) (next := .inr true) (a := (1 : Fin 3)) (b := 2)
    (d := some) (g := id) rfl (by decide) y.reverse y.reverse [] true
    (st [] y.reverse []) (by simp [st]) rfl rfl
  have hi : update (fun _ : Fin 3 => ([] : List Bool)) 0 x = st x [] [] := by
    funext k
    fin_cases k <;> rfl
  refine ⟨v, S, ?_, ?_⟩
  · change RunLe prog _ ⟨_, _, update _ 0 (x.map id)⟩ _
    rw [List.map_id, hi]
    apply (h₁.trans h₂).le
    have := bound x q₀
    simp [y, Nat.mul_add] at *
    omega
  · simpa [y, st, comp] using ho

end Scan

/-- The streaming form of `redFun'`: the state is `none` before the first bit, then the
automaton state; the prefix `redConst` is emitted with the first bit or at the end. -/
private def stepR : Option (Fin 16) → Bool → Option (Fin 16) × List Bool
  | none, b => (some ⟨δ 0 b, δ_lt 0 b⟩, redConst ++ [b])
  | some k, b => (some ⟨δ k b, δ_lt k b⟩, [b])

private def finishR : Option (Fin 16) → List Bool
  | none => redConst
  | some k => if k.val = 14 then [true] else []

private theorem scan_some : ∀ (x : List Bool) (k : Fin 16),
    scan stepR finishR (some k) x = x ++ (if run k x = 14 then [true] else [])
  | [], k => rfl
  | b :: x, k => by
    rw [scan, stepR, scan_some x]
    rfl

private theorem scan_eq : scan stepR finishR none = redFun' := by
  funext x
  cases x with
  | nil => rfl
  | cons b x =>
    rw [scan, stepR, scan_some x, redFun']
    simp only [List.append_assoc, List.cons_append, List.nil_append]
    rfl

private theorem isPolyTime_redFun' : MetaMathlibExt.ComplexityTheory.IsPolyTime redFun' :=
  scan_eq ▸ polyScan stepR finishR none

/-- **FLOW-SHOP SCHEDULING is NP-hard.** 3-machine flow shop reduces to it by prepending
`m = 3` and supplying the deadline `1` on the regular family of all-zero inputs with an empty
deadline. -/
theorem flowShopScheduling_npHard : ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
    L ∈ MetaMathlibExt.ComplexityTheory.NP →
      Cslib.CookLevin.PolyManyOneRed L flowShopSchedulingDec := fun L hL =>
  Cslib.Complexity.PolyManyOneRed.trans
    (MetaMathlibExt.Complexity.NPComplete.FlowShop.flowShop_npComplete.2 L hL)
    ⟨redFun', isPolyTime_redFun', redFun'_correct⟩


end MetaMathlibExt.Complexity.NPComplete.FlowShopScheduling
