/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.NPComplete.ConstrainedSequencingToMinimizeTardyTaskWeightDefs
public import CSLibExt.Computability.Complexity.Defs
public import CSLibExt.Computability.Complexity.Karp.PartitionComplete
public import CSLibExt.Computability.Complexity.PolynomialEncoding.Copy
public import CSLibExt.Computability.Complexity.PolynomialEncoding.ListNat
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.TuringMachine.Recursive.OfTM2
public import Mathlib.Data.List.GetD
public import Mathlib.Data.List.Perm.Basic

/-!
# CONSTRAINED SEQUENCING TO MINIMIZE TARDY TASK WEIGHT is in NP

A certificate is a skip/take plan over the encoded task records: each bit either sets the next
record aside or selects it, and the set-aside records return, in order, when a record is
selected. A list of flags, one per record, records whether the record's index lies in `S`, and
travels with the records. The functional verifier `Verification.check` reads an instance and a
plan. A multi-stack Turing machine computes it:

* it splits the instance, rejecting undecodable input and the bounds `K = 0` and `J = 0`;
* it pushes one flag per record, and sets the flag of each element of `S` by walking that many
  flags down with a binary decrement, rejecting an element that is not a record index;
* it runs the plan, rejecting a record whose length, deadline or weight is `0`, adding the weight
  of a tardy record to the tardy weight and counting the flagged records that are on time;
* it accepts when every record was selected, the tardy weight is at most `K`, and the count is
  at least `J`.

`Verification.check_iff` shows that some plan of length at most `|x|²` is accepted exactly when
the instance is well formed and feasible, and `Verification.check_poly` that the machine runs in
polynomial time.

The plan certificate, its semantics, the stack machinery (frame reads and writes, binary
addition and comparison) and the structure of the main loop are adapted from
`CSLibExt.Computability.Complexity.Karp.WeightedTardyJobs`.

Source: P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, entry
MAXIMUM CONSTRAINED SEQUENCING TO MINIMIZE TARDY TASK WEIGHT; D. Zuckerman, "On unapproximable
versions of NP-complete problems", SIAM Journal on Computing 25 (1996), 1293-1304, problem 19.
-/

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ConstrainedSequencingToMinimizeTardyTaskWeight

namespace Verification

section Spec

open MetaMathlibExt MetaMathlibExt.BitstringEncoding Computability
open MetaMathlibExt.Complexity.NPComplete
open MetaMathlibExt.Complexity.NPComplete.ConstrainedSequencingToMinimizeTardyTaskWeight
open MetaMathlibExt.Complexity.NPComplete.WeightedTardyJobs (WeightedTardy WeightedTardyStep)

abbrev Job := ℕ × ℕ × ℕ

/-! ### Plans (adapted from `WeightedTardyJobs`) -/

def plan {α : Type} : List Bool → List α → List α → Option (List α)
  | [], jobs, skipped => if jobs.isEmpty && skipped.isEmpty then some [] else none
  | _ :: _, [], _ => none
  | true :: w, j :: jobs, skipped => plan w jobs (j :: skipped)
  | false :: w, j :: jobs, skipped => (plan w (skipped.reverse ++ jobs) []).map (j :: ·)

theorem plan_perm {α : Type} {w : List Bool} {jobs skipped result : List α}
    (h : plan w jobs skipped = some result) : result.Perm (skipped.reverse ++ jobs) := by
  induction w generalizing jobs skipped result with
  | nil => cases jobs <;> cases skipped <;> simp_all [plan]
  | cons b w ih =>
    cases jobs with
    | nil => simp [plan] at h
    | cons j jobs =>
      cases b
      · obtain ⟨l, hl, rfl⟩ := Option.map_eq_some_iff.mp h
        have h' := ih hl
        simp only [List.reverse_nil, List.nil_append] at h'
        exact (h'.cons j).trans List.perm_middle.symm
      · simpa [List.reverse_cons, List.append_assoc] using ih h

theorem plan_skip {α : Type} (s jobs skipped : List α) (w : List Bool) :
    plan (List.replicate s.length true ++ w) (s ++ jobs) skipped =
      plan w jobs (s.reverse ++ skipped) := by
  induction s generalizing skipped with
  | nil => rfl
  | cons a s ih =>
    rw [List.length_cons, List.replicate_succ, List.cons_append, List.cons_append, plan]
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append]
      using ih (a :: skipped)

theorem plan_exists {α : Type} {jobs result : List α} (h : result.Perm jobs) :
    ∃ w, w.length ≤ result.length * jobs.length ∧ plan w jobs [] = some result := by
  induction result generalizing jobs with
  | nil =>
    have hj : jobs = [] := h.nil_eq.symm
    subst jobs
    exact ⟨[], by simp, rfl⟩
  | cons a tail ih =>
    obtain ⟨pre, post, rfl⟩ := List.append_of_mem (h.mem_iff.mp (List.mem_cons_self ..))
    have htail : tail.Perm (pre ++ post) := (h.trans List.perm_middle).cons_inv
    obtain ⟨w, hw, hs⟩ := ih htail
    refine ⟨List.replicate pre.length true ++ false :: w, ?_, ?_⟩
    · simp only [List.length_append, List.length_replicate, List.length_cons, Nat.mul_add] at *
      simp only [Nat.succ_mul, Nat.mul_one]
      omega
    · rw [plan_skip]
      simp [plan, hs]

theorem map_range_getD {α : Type} (xs : List α) (default : α) :
    (List.range xs.length).map (xs.getD · default) = xs := by
  apply List.ext_getElem
  · simp
  · intro n _ hn
    simp [List.getElem?_eq_getElem hn]

/-! ### Job records (adapted from `WeightedTardyJobs`) -/

def pack (ps : List (List Bool)) : List Bool := (ps.map delimit).flatten

theorem pack_cons (p : List Bool) (ps : List (List Bool)) :
    pack (p :: ps) = delimit p ++ pack ps := rfl

theorem pack_append (xs ys : List (List Bool)) : pack (xs ++ ys) = pack xs ++ pack ys := by
  simp [pack]

def decodeJob (p : List Bool) : Option Job :=
  (undelimit p).bind fun (a, r) =>
    (undelimit r).map fun (d, b) => (decodeNat a, decodeNat d, decodeNat b)

theorem bitDecode_pair {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (p : List Bool) : bitDecode (α := α × β) p =
      match undelimit p with
      | none => none
      | some (a, b) =>
        match bitDecode (α := α) a, bitDecode (α := β) b with
        | some j, some k => some (j, k)
        | _, _ => none := rfl

theorem bitDecode_nat (p : List Bool) :
    bitDecode (α := ℕ) p = some (decodeNat p) := rfl

theorem decodeJob_eq (p : List Bool) : decodeJob p = bitDecode p := by
  simp only [decodeJob, bitDecode_pair, bitDecode_nat]
  cases hp : undelimit p with
  | none => rfl
  | some pr =>
    obtain ⟨a, r⟩ := pr
    simp only [Option.bind]
    cases undelimit r <;> simp

theorem decodeJobs_eq (r : List Bool) :
    (undelimitBlocks r).bind (List.mapM decodeJob) = bitDecode (α := List Job) r := by
  change _ = (undelimitBlocks r).bind (List.mapM bitDecode)
  simp only [funext decodeJob_eq]

/-! ### The specification -/

/-- Positive length, deadline and weight. -/
def posJob (j : Job) : Bool := decide (0 < j.1) && decide (0 < j.2.1) && decide (0 < j.2.2)

/-- The step of the weighted tardy jobs computation (elapsed time, tardy weight). -/
def jobStep (acc : ℕ × ℕ) (j : Job) : ℕ × ℕ :=
  let t := acc.1 + j.1
  (t, acc.2 + if j.2.1 < t then j.2.2 else 0)

/-- The increase of the on-time counter: a flagged job that is not tardy. -/
def inc (acc : ℕ × ℕ) (j : Job) (f : Bool) : ℕ :=
  if f && !decide (j.2.1 < acc.1 + j.1) then 1 else 0

/-- Set the flag at position `s`; `none` when there is no position `s`. -/
def markAt : List Bool → ℕ → Option (List Bool)
  | [], _ => none
  | _ :: fl, 0 => some (true :: fl)
  | b :: fl, s + 1 => (markAt fl s).map (b :: ·)

/-- The main loop over the job records `ps` with their flags `fl`, the skipped records `sk` with
their flags `sf`, the state `acc`, the counter `c`, and the bounds `k` and `J`. -/
def loop : List Bool → List (List Bool) → List Bool → List (List Bool) → List Bool →
    ℕ × ℕ → ℕ → ℕ → ℕ → Bool
  | [], ps, _, sk, _, acc, c, k, J =>
      ps.isEmpty && sk.isEmpty && decide (acc.2 ≤ k) && decide (J ≤ c)
  | _ :: _, [], _, _, _, _, _, _, _ => false
  | true :: w, p :: ps, fl, sk, sf, acc, c, k, J =>
      loop w ps fl.tail (p :: sk) (fl.headD false :: sf) acc c k J
  | false :: w, p :: ps, fl, sk, sf, acc, c, k, J =>
      match decodeJob p with
      | none => false
      | some j => posJob j &&
          loop w (sk.reverse ++ ps) (sf.reverse ++ fl.tail) [] [] (jobStep acc j)
            (c + inc acc j (fl.headD false)) k J

/-- The verifier, as a function. -/
def check (x w : List Bool) : Bool :=
  match undelimit x with
  | none => false
  | some (a, b) =>
    match undelimit a, undelimit b with
    | some (raw, kb), some (sraw, jb) =>
      match undelimitBlocks raw, undelimitBlocks sraw with
      | some ps, some ss =>
        match (ss.map decodeNat).foldlM markAt (List.replicate ps.length false) with
        | some fl => decide (0 < decodeNat kb) && decide (0 < decodeNat jb) &&
            loop w ps fl [] [] (0, 0) 0 (decodeNat kb) (decodeNat jb)
        | none => false
      | _, _ => false
    | _, _ => false

/-! ### Flags -/

theorem markAt_eq : ∀ (fl : List Bool) (s : ℕ),
    markAt fl s = if s < fl.length then some (fl.set s true) else none
  | [], s => by simp [markAt]
  | b :: fl, 0 => by simp [markAt]
  | b :: fl, s + 1 => by
    rw [markAt, markAt_eq fl s]
    by_cases h : s < fl.length <;> simp [h]

theorem foldlM_markAt (S : List ℕ) : ∀ fl : List Bool,
    S.foldlM markAt fl =
      if ∀ s ∈ S, s < fl.length then
        some (fl.mapIdx fun i b => b || decide (i ∈ S)) else none := by
  induction S with
  | nil =>
    intro fl
    simp only [List.foldlM_nil, List.not_mem_nil, false_imp_iff, implies_true, ↓reduceIte,
      decide_false, Bool.or_false]
    congr 1
    apply List.ext_getElem <;> simp
  | cons s S ih =>
    intro fl
    rw [List.foldlM_cons, markAt_eq]
    by_cases hs : s < fl.length
    · simp only [hs, ↓reduceIte]
      change List.foldlM markAt (fl.set s true) S = _
      simp only [ih, List.length_set, List.mem_cons, forall_eq_or_imp, hs, true_and]
      split_ifs with h
      · congr 1
        apply List.ext_getElem
        · simp
        · intro i h₁ h₂
          simp only [List.getElem_mapIdx, List.getElem_set]
          by_cases hi : s = i <;> simp [hi, eq_comm]
      · rfl
    · simp [hs]

theorem flags_eq (n : ℕ) (S : List ℕ) :
    S.foldlM markAt (List.replicate n false) =
      if ∀ s ∈ S, s < n then some ((List.range n).map fun i => decide (i ∈ S)) else none := by
  rw [foldlM_markAt]
  simp only [List.length_replicate]
  split_ifs
  · congr 1
    apply List.ext_getElem <;> simp
  · rfl

end Spec

section Correct

open MetaMathlibExt MetaMathlibExt.BitstringEncoding Computability
open MetaMathlibExt.Complexity.NPComplete
open MetaMathlibExt.Complexity.NPComplete.ConstrainedSequencingToMinimizeTardyTaskWeight
open MetaMathlibExt.Complexity.NPComplete.WeightedTardyJobs (WeightedTardy WeightedTardyStep)

/-- Evaluation of a planned order of (record, flag) pairs. -/
private def evalF : List (List Bool × Bool) → ℕ × ℕ → ℕ → ℕ → ℕ → Bool
  | [], acc, c, k, J => decide (acc.2 ≤ k) && decide (J ≤ c)
  | (p, f) :: ord, acc, c, k, J =>
    match decodeJob p with
    | none => false
    | some j => posJob j && evalF ord (jobStep acc j) (c + inc acc j f) k J

private theorem zip_reverse {α β : Type} : ∀ (l₁ : List α) (l₂ : List β), l₁.length = l₂.length →
    (l₁.zip l₂).reverse = l₁.reverse.zip l₂.reverse
  | [], [], _ => rfl
  | a :: l₁, b :: l₂, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    rw [List.zip_cons_cons, List.reverse_cons, zip_reverse l₁ l₂ h, List.reverse_cons,
      List.reverse_cons, List.zip_append (by simpa using h)]
    rfl

private theorem loop_eq : ∀ (w : List Bool) (ps : List (List Bool)) (fl : List Bool)
    (sk : List (List Bool)) (sf : List Bool) (acc : ℕ × ℕ) (c k J : ℕ),
    fl.length = ps.length → sf.length = sk.length →
    loop w ps fl sk sf acc c k J =
      ((plan w (ps.zip fl) (sk.zip sf)).map (evalF · acc c k J)).getD false := by
  intro w
  induction w with
  | nil =>
    intro ps fl sk sf acc c k J h₁ h₂
    cases ps <;> cases fl <;> cases sk <;> cases sf <;> simp_all [loop, plan, evalF]
  | cons b w ih =>
    intro ps fl sk sf acc c k J h₁ h₂
    cases ps with
    | nil =>
      cases fl with
      | nil => simp [loop, plan]
      | cons _ _ => simp at h₁
    | cons p ps =>
      cases fl with
      | nil => simp at h₁
      | cons f fl =>
        simp only [List.length_cons, Nat.add_right_cancel_iff] at h₁
        cases b with
        | true =>
          simp only [loop, List.tail_cons, List.headD_cons, List.zip_cons_cons, plan]
          rw [ih ps fl (p :: sk) (f :: sf) acc c k J h₁ (by simp [h₂])]
          rfl
        | false =>
          simp only [loop, List.tail_cons, List.headD_cons, List.zip_cons_cons, plan]
          have hz : (sk.zip sf).reverse ++ ps.zip fl =
              (sk.reverse ++ ps).zip (sf.reverse ++ fl) := by
            rw [zip_reverse sk sf h₂.symm, List.zip_append (by simp [h₂])]
          rw [hz]
          cases hj : decodeJob p with
          | none =>
            cases plan w ((sk.reverse ++ ps).zip (sf.reverse ++ fl)) [] <;> simp [evalF, hj]
          | some j =>
            dsimp only
            rw [ih (sk.reverse ++ ps) (sf.reverse ++ fl) [] [] _ _ k J (by simp [h₁, h₂]) rfl]
            cases hpl : plan w ((sk.reverse ++ ps).zip (sf.reverse ++ fl)) [] <;>
              simp [evalF, hj, hpl]

/-- The combined state: (elapsed time, tardy weight) and the on-time counter. -/
private def tri (s : (ℕ × ℕ) × ℕ) (jf : Job × Bool) : (ℕ × ℕ) × ℕ :=
  (jobStep s.1 jf.1, s.2 + inc s.1 jf.1 jf.2)

private def finalOk (r : (ℕ × ℕ) × ℕ) (k J : ℕ) : Bool := decide (r.1.2 ≤ k) && decide (J ≤ r.2)

private theorem evalF_decoded : ∀ (ord : List (List Bool × Bool)) (acc : ℕ × ℕ) (c k J : ℕ),
    (∀ pf ∈ ord, (decodeJob pf.1).isSome) →
    evalF ord acc c k J =
      ((ord.map fun pf => ((decodeJob pf.1).getD (0, 0, 0), pf.2)).all (fun jf => posJob jf.1) &&
        finalOk ((ord.map fun pf => ((decodeJob pf.1).getD (0, 0, 0), pf.2)).foldl tri (acc, c))
          k J)
  | [], acc, c, k, J, _ => by simp [evalF, finalOk]
  | (p, f) :: ord, acc, c, k, J, h => by
    obtain ⟨j, hj⟩ := Option.isSome_iff_exists.mp (h (p, f) (List.mem_cons_self ..))
    have ih := evalF_decoded ord (jobStep acc j) (c + inc acc j f) k J
      (fun pf hpf => h pf (List.mem_cons_of_mem _ hpf))
    simp only [evalF, hj, List.map_cons, Option.getD_some, List.all_cons, List.foldl_cons, ih]
    simp only [tri, Bool.and_assoc]

private theorem evalF_undecoded : ∀ (ord : List (List Bool × Bool)) (acc : ℕ × ℕ) (c k J : ℕ),
    (∃ pf ∈ ord, decodeJob pf.1 = none) → evalF ord acc c k J = false
  | [], _, _, _, _, ⟨_, h, _⟩ => by simp at h
  | (p, f) :: ord, acc, c, k, J, ⟨pf, hm, hn⟩ => by
    rcases List.mem_cons.mp hm with rfl | hm
    · simp [evalF, hn]
    · cases hj : decodeJob p with
      | none => simp [evalF, hj]
      | some j =>
        simp [evalF, hj, evalF_undecoded ord _ _ k J ⟨pf, hm, hn⟩]

/-! ### Semantics of the decoded instance -/

private theorem fold_tri (jobs : List Job) (S : List ℕ) : ∀ (order : List ℕ) (t w c : ℕ),
    (order.map fun i => (jobs.getD i (0, 0, 0), decide (i ∈ S))).foldl tri ((t, w), c) =
      (order.foldl (WeightedTardyStep jobs) (t, w), (order.foldl (onTimeStep jobs S) (t, c)).2) ∧
    (order.foldl (WeightedTardyStep jobs) (t, w)).1 = (order.foldl (onTimeStep jobs S) (t, c)).1
  | [], t, w, c => by simp
  | i :: order, t, w, c => by
    simp only [List.map_cons, List.foldl_cons]
    have h := fold_tri jobs S order (t + (jobs.getD i (0, 0, 0)).1)
      (w + if (jobs.getD i (0, 0, 0)).2.1 < t + (jobs.getD i (0, 0, 0)).1 then
        (jobs.getD i (0, 0, 0)).2.2 else 0)
      (c + if i ∈ S ∧ t + (jobs.getD i (0, 0, 0)).1 ≤ (jobs.getD i (0, 0, 0)).2.1 then 1 else 0)
    have hs : tri ((t, w), c) (jobs.getD i (0, 0, 0), decide (i ∈ S)) =
        ((t + (jobs.getD i (0, 0, 0)).1,
          w + if (jobs.getD i (0, 0, 0)).2.1 < t + (jobs.getD i (0, 0, 0)).1 then
            (jobs.getD i (0, 0, 0)).2.2 else 0),
          c + if i ∈ S ∧ t + (jobs.getD i (0, 0, 0)).1 ≤ (jobs.getD i (0, 0, 0)).2.1 then 1
            else 0) := by
      simp only [tri, jobStep, inc]
      congr 2
      by_cases hi : i ∈ S
      · by_cases ht : (jobs.getD i (0, 0, 0)).2.1 < t + (jobs.getD i (0, 0, 0)).1
        · simp [hi]
        · simp [hi]
      · simp [hi]
    rw [hs]
    exact h

/-- The decoded instance is well formed and feasible exactly when the bounds are positive, `S`
holds job indices, and some permutation of the flagged jobs passes. -/
private theorem sem_iff (jobs : List Job) (K : ℕ) (S : List ℕ) (J : ℕ) :
    (WellFormed ((jobs, K), (S, J)) ∧ ConstrainedSequencingFeasible ((jobs, K), (S, J))) ↔
      0 < K ∧ 0 < J ∧ (∀ s ∈ S, s < jobs.length) ∧
        ∃ dec : List (Job × Bool),
          dec.Perm (jobs.zip ((List.range jobs.length).map fun i => decide (i ∈ S))) ∧
          dec.all (fun jf => posJob jf.1) = true ∧
            finalOk (dec.foldl tri ((0, 0), 0)) K J = true := by
  let g : ℕ → Job × Bool := fun i => (jobs.getD i (0, 0, 0), decide (i ∈ S))
  have hg : (List.range jobs.length).map g =
      jobs.zip ((List.range jobs.length).map fun i => decide (i ∈ S)) := by
    apply List.ext_getElem
    · simp
    · intro n h₁ h₂
      simp [g, List.getElem?_eq_getElem (by simpa using h₁ : n < jobs.length)]
  have hpos : ∀ dec : List (Job × Bool),
      dec.Perm (jobs.zip ((List.range jobs.length).map fun i => decide (i ∈ S))) →
      (dec.all (fun jf => posJob jf.1) = true ↔
        ∀ t ∈ jobs, 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2) := by
    intro dec hd
    rw [List.all_eq_true]
    have hm : ∀ x, x ∈ dec ↔ x ∈ jobs.zip ((List.range jobs.length).map fun i => decide (i ∈ S)) :=
      fun x => hd.mem_iff
    have hf : (jobs.zip ((List.range jobs.length).map fun i => decide (i ∈ S))).map Prod.fst =
        jobs := List.map_fst_zip (by simp)
    constructor
    · intro h t ht
      rw [← hf] at ht
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ht
      have := h x ((hm x).mpr hx)
      simpa [posJob, and_assoc] using this
    · intro h x hx
      have hx' := (hm x).mp hx
      have ht : x.1 ∈ jobs := by
        rw [← hf]
        exact List.mem_map_of_mem hx'
      simpa [posJob, and_assoc] using h x.1 ht
  constructor
  · rintro ⟨⟨hjobs, hK, hS, hJ⟩, order, hperm, hw, hc⟩
    refine ⟨hK, hJ, hS, order.map g, ?_, ?_, ?_⟩
    · rw [← hg]
      exact hperm.map g
    · exact (hpos _ (hg ▸ hperm.map g)).mpr hjobs
    · obtain ⟨h₁, -⟩ := fold_tri jobs S order 0 0 0
      simp only [finalOk, g, h₁, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨hw, hc⟩
  · rintro ⟨hK, hJ, hS, dec, hd, hall, hfin⟩
    have hd' : dec.Perm ((List.range jobs.length).map g) := hg ▸ hd
    have hl : ∃ order : List ℕ, dec = order.map g ∧ order.Perm (List.range jobs.length) := by
      have ht : (Relation.Comp (· = List.map g ·) List.Perm) dec (List.range jobs.length) := by
        have he := congrFun (congrFun (List.eq_map_comp_perm g) dec) (List.range jobs.length)
        exact Eq.mpr he hd'
      exact ht
    obtain ⟨order, rfl, hp⟩ := hl
    refine ⟨⟨(hpos _ hd).mp hall, hK, hS, hJ⟩, order, hp, ?_⟩
    obtain ⟨h₁, -⟩ := fold_tri jobs S order 0 0 0
    simp only [finalOk, g, h₁, Bool.and_eq_true, decide_eq_true_eq] at hfin
    exact hfin

end Correct

section CheckIff

open MetaMathlibExt MetaMathlibExt.BitstringEncoding Computability
open MetaMathlibExt.Complexity.NPComplete
open MetaMathlibExt.Complexity.NPComplete.ConstrainedSequencingToMinimizeTardyTaskWeight

private theorem mapM_length {ps : List (List Bool)} {jobs : List Job}
    (h : ps.mapM decodeJob = some jobs) : jobs.length = ps.length := by
  induction ps generalizing jobs with
  | nil => simp at h; simp [← h]
  | cons p ps ih =>
    rw [List.mapM_cons] at h
    cases hp : decodeJob p with
    | none => simp [hp] at h
    | some j =>
      cases hs : ps.mapM decodeJob with
      | none => simp [hp, hs] at h
      | some rest =>
        have : jobs = j :: rest := by simpa [hp, hs] using h.symm
        simp [this, ih hs]

private theorem mapM_decoded {ps : List (List Bool)} {jobs : List Job}
    (h : ps.mapM decodeJob = some jobs) :
    (∀ p ∈ ps, (decodeJob p).isSome) ∧
      ∀ fl : List Bool, (ps.zip fl).map (fun pf => ((decodeJob pf.1).getD (0, 0, 0), pf.2)) =
        jobs.zip fl := by
  induction ps generalizing jobs with
  | nil => simp at h; simp [← h]
  | cons p ps ih =>
    rw [List.mapM_cons] at h
    cases hp : decodeJob p with
    | none => simp [hp] at h
    | some j =>
      cases hs : ps.mapM decodeJob with
      | none => simp [hp, hs] at h
      | some rest =>
        have hj : jobs = j :: rest := by simpa [hp, hs] using h.symm
        subst hj
        obtain ⟨h₁, h₂⟩ := ih hs
        refine ⟨fun q hq => ?_, fun fl => ?_⟩
        · rcases List.mem_cons.mp hq with rfl | hq
          · simp [hp]
          · exact h₁ q hq
        · cases fl with
          | nil => rfl
          | cons f fl => simp [hp, h₂ fl]

private theorem mapM_none {ps : List (List Bool)} (h : ps.mapM decodeJob = none) :
    ∃ p ∈ ps, decodeJob p = none := by
  induction ps with
  | nil => simp at h
  | cons p ps ih =>
    rw [List.mapM_cons] at h
    cases hp : decodeJob p with
    | none => exact ⟨p, List.mem_cons_self .., hp⟩
    | some j =>
      cases hs : ps.mapM decodeJob with
      | none =>
        obtain ⟨q, hq, hn⟩ := ih hs
        exact ⟨q, List.mem_cons_of_mem _ hq, hn⟩
      | some rest => simp [hp, hs] at h

private theorem blocks_length_le {raw : List Bool} {ps : List (List Bool)}
    (h : undelimitBlocks raw = some ps) : ps.length ≤ raw.length := by
  rw [Cslib.Complexity.PolynomialEncoding.blocks_decode_sound h]
  exact length_le_length_flatten_delimit ps

/-- The loop accepts some certificate of bounded length exactly when some permutation of the
flagged records passes. -/
private theorem loop_iff (ps : List (List Bool)) (fl : List Bool) (hl : fl.length = ps.length)
    (k J : ℕ) (B : ℕ) (hB : ps.length * ps.length ≤ B) :
    (∃ w : List Bool, w.length ≤ B ∧ loop w ps fl [] [] (0, 0) 0 k J = true) ↔
      ∃ ord, ord.Perm (ps.zip fl) ∧ evalF ord (0, 0) 0 k J = true := by
  have hz : (ps.zip fl).length = ps.length := by simp [hl]
  constructor
  · rintro ⟨w, -, hw⟩
    rw [loop_eq w ps fl [] [] (0, 0) 0 k J hl rfl] at hw
    change ((plan w (ps.zip fl) []).map _).getD false = true at hw
    cases hpl : plan w (ps.zip fl) [] with
    | none => simp [hpl] at hw
    | some ord =>
      rw [hpl] at hw
      exact ⟨ord, by simpa using plan_perm hpl, by simpa using hw⟩
  · rintro ⟨ord, hp, he⟩
    obtain ⟨w, hw, hs⟩ := plan_exists hp
    refine ⟨w, ?_, ?_⟩
    · rw [hp.length_eq, hz] at hw
      exact hw.trans hB
    · rw [loop_eq w ps fl [] [] (0, 0) 0 k J hl rfl]
      change ((plan w (ps.zip fl) []).map _).getD false = true
      rw [hs]
      exact he

theorem check_iff (x : List Bool) :
    constrainedSequencingDec x = true ↔
      ∃ w : List Bool, w.length ≤ x.length ^ 2 ∧ check x w = true := by
  classical
  unfold constrainedSequencingDec
  rw [bitDecode_pair]
  cases hx : undelimit x with
  | none => simp [check, hx]
  | some pr =>
    obtain ⟨a, b⟩ := pr
    have hxe := (Cslib.CookLevin.undelimit_eq_some_iff x a b).1 hx
    have hxa : a.length ≤ x.length := by simp [hxe]; omega
    simp only
    rw [bitDecode_pair (α := List Job) (β := ℕ) a, bitDecode_pair (α := List ℕ) (β := ℕ) b]
    cases ha : undelimit a with
    | none =>
      cases hb : undelimit b <;> simp [check, hx, ha, hb]
    | some pa =>
      obtain ⟨raw, kb⟩ := pa
      have hae := (Cslib.CookLevin.undelimit_eq_some_iff a raw kb).1 ha
      have hraw : raw.length ≤ x.length := by
        have : raw.length ≤ a.length := by simp [hae]; omega
        omega
      cases hb : undelimit b with
      | none => simp [check, hx, ha, hb]
      | some pb =>
        obtain ⟨sraw, jb⟩ := pb
        simp only [← decodeJobs_eq, Cslib.Complexity.PolynomialEncoding.decode_list_nat,
          bitDecode_nat]
        cases hps : undelimitBlocks raw with
        | none =>
          cases hss : undelimitBlocks sraw <;> simp [check, hx, ha, hb, hps, hss]
        | some ps =>
          cases hss : undelimitBlocks sraw with
          | none => simp [check, hx, ha, hb, hps, hss]
          | some ss =>
            have hn := blocks_length_le hps
            have hB : ps.length * ps.length ≤ x.length ^ 2 := by
              rw [pow_two]; exact Nat.mul_le_mul (by omega) (by omega)
            simp only [check, hx, ha, hb, hps, hss, flags_eq, Option.map_some]
            generalize ss.map decodeNat = S
            cases hj : ps.mapM decodeJob with
            | none =>
              simp only [Option.bind_some, hj, Bool.false_eq_true, false_iff, not_exists,
                not_and]
              intro w _
              split_ifs with hS
              · intro hacc
                simp only [Bool.and_eq_true, decide_eq_true_eq] at hacc
                obtain ⟨-, hl⟩ := hacc
                rw [loop_eq w ps _ [] [] (0, 0) 0 _ _ (by simp) rfl] at hl
                change ((plan w (ps.zip ((List.range ps.length).map fun i =>
                  decide (i ∈ S))) []).map _).getD false = true at hl
                cases hpl : plan w (ps.zip ((List.range ps.length).map fun i =>
                    decide (i ∈ S))) [] with
                | none => rw [hpl] at hl; simp at hl
                | some ord =>
                  rw [hpl] at hl
                  obtain ⟨p, hp, hn⟩ := mapM_none hj
                  have hperm := plan_perm hpl
                  simp only [List.reverse_nil, List.nil_append] at hperm
                  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
                  have hi' : i < (ps.zip ((List.range ps.length).map fun i =>
                      decide (i ∈ S))).length := by simpa using hi
                  have hmem := hperm.mem_iff.mpr (List.getElem_mem hi')
                  have hl' : evalF ord (0, 0) 0 (decodeNat kb) (decodeNat jb) = true := hl
                  rw [evalF_undecoded ord _ _ _ _ ⟨_, hmem, by simpa using hn⟩] at hl'
                  exact absurd hl' (by decide)
              · simp
            | some jobs =>
              simp only [Option.bind_some, hj]
              have hlen := mapM_length hj
              obtain ⟨hdec, hzip⟩ := mapM_decoded hj
              rw [decide_eq_true_iff, sem_iff, hlen]
              by_cases hS : ∀ s ∈ S, s < ps.length
              · simp only [eq_true hS, ↓reduceIte, true_and, Bool.and_eq_true,
                  decide_eq_true_eq]
                let fl := (List.range ps.length).map fun i => decide (i ∈ S)
                have hfl : fl.length = ps.length := by simp [fl]
                have hiff := loop_iff ps fl hfl (decodeNat kb) (decodeNat jb) _ hB
                constructor
                · rintro ⟨hK, hJ, dec, hd, hall, hfin⟩
                  have hd' : dec.Perm ((ps.zip fl).map
                      fun pf => ((decodeJob pf.1).getD (0, 0, 0), pf.2)) := by
                    rw [hzip fl]; exact hd
                  have hl : ∃ ord : List (List Bool × Bool),
                      dec = ord.map (fun pf => ((decodeJob pf.1).getD (0, 0, 0),
                      pf.2)) ∧ ord.Perm (ps.zip fl) := by
                    have ht : (Relation.Comp (· = List.map (fun pf : List Bool × Bool =>
                        ((decodeJob pf.1).getD (0, 0, 0), pf.2)) ·) List.Perm) dec
                        (ps.zip fl) := by
                      have he := congrFun (congrFun (List.eq_map_comp_perm
                        (fun pf : List Bool × Bool =>
                          ((decodeJob pf.1).getD (0, 0, 0), pf.2))) dec) (ps.zip fl)
                      exact Eq.mpr he hd'
                    exact ht
                  obtain ⟨ord, rfl, hp⟩ := hl
                  obtain ⟨w, hw, hl⟩ := hiff.mpr ⟨ord, hp, by
                    rw [evalF_decoded ord _ _ _ _ (fun pf hpf =>
                      hdec pf.1 (List.of_mem_zip (hp.mem_iff.mp hpf)).1)]
                    simp [hall, hfin]⟩
                  exact ⟨w, hw, ⟨hK, hJ⟩, hl⟩
                · rintro ⟨w, hw, ⟨hK, hJ⟩, hl⟩
                  obtain ⟨ord, hp, he⟩ := hiff.mp ⟨w, hw, hl⟩
                  have hdec' : ∀ pf ∈ ord, (decodeJob pf.1).isSome := fun pf hpf =>
                    hdec pf.1 (List.of_mem_zip (hp.mem_iff.mp hpf)).1
                  rw [evalF_decoded ord _ _ _ _ hdec', Bool.and_eq_true] at he
                  refine ⟨hK, hJ, ord.map fun pf => ((decodeJob pf.1).getD (0, 0, 0), pf.2),
                    ?_, he.1, he.2⟩
                  rw [← hzip fl]
                  exact hp.map _
              · simp only [eq_false hS, ↓reduceIte, false_and, and_false]
                simp

/-- Membership in NP, given a polynomial-time machine for `check`. -/
private theorem membership_of_check_poly
    (h : MetaMathlibExt.ComplexityTheory.IsPolyTime
      (fun xw : List Bool × List Bool => check xw.1 xw.2)) :
    constrainedSequencingDec ∈ MetaMathlibExt.ComplexityTheory.NP :=
  ⟨Polynomial.X ^ 2, fun xw => check xw.1 xw.2, h, fun x => by simpa using check_iff x⟩

end CheckIff

section Infra

open MetaMathlibExt MetaMathlibExt.BitstringEncoding
open Turing Function TM2Program Cslib.Complexity
open Cslib.Complexity.PolynomialEncoding (splitB splitB_run copyB_run)

section BitStacks

variable {K Lab : Type} [DecidableEq K]
variable {M : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool}

private def moveBits (a b : K) (self next : Lab) : TM2.Stmt (fun _ : K => Bool) Lab Bool :=
  moveB a b some id self next

private theorem moveBits_run {a b : K} {self next : Lab}
    (hp : M self = moveBits a b self next) (hab : a ≠ b) (v : Bool) (S : K → List Bool) :
    ∃ v', Run M ((S a).length + 1) ⟨some self, v, S⟩
      ⟨some next, v', update (update S a []) b ((S a).reverse ++ S b)⟩ := by
  obtain ⟨v', T, hr, ha, hb, hk⟩ := moveB_run hp hab (S a) (S a) [] v S (by simp)
    (by simp [IsBitBlock]) (by simp [EndsBitBlock])
  refine ⟨v', ?_⟩
  convert hr using 2
  funext k
  by_cases hka : k = a
  · subst k
    simp [ha, hab]
  by_cases hkb : k = b
  · subst k
    simpa using hb.symm
  simp [hka, hkb, hk k hka hkb]

private def readFrame (a b : K) (self next bad : Lab) :
    TM2.Stmt (fun _ : K => Bool) Lab Bool :=
  FramedCNF.Block.read a b some id self next bad

private theorem readFrame_run {a b : K} {self next bad : Lab}
    (hp : M self = readFrame a b self next bad) (hab : a ≠ b)
    (v : Bool) (S : K → List Bool) (p rest : List Bool) (h : S a = delimit p ++ rest) :
    Run M (p.length + 1) ⟨some self, v, S⟩
      ⟨some next, false, update (update S a rest) b (p.reverse ++ S b)⟩ := by
  obtain ⟨T, hr, ha, hb, hk⟩ :=
    FramedCNF.Block.run_delimit hp hab id (fun _ => rfl) p rest v S (by simpa using h)
  convert hr using 2
  funext k
  by_cases hka : k = a
  · subst k
    simp [ha, hab]
  by_cases hkb : k = b
  · subst k
    simpa using hb.symm
  simp [hka, hkb, hk k hka hkb]

private theorem readFrame_bad {a b : K} {self next bad : Lab}
    (hp : M self = readFrame a b self next bad) (hab : a ≠ b)
    (input : List Bool) (v : Bool) (S : K → List Bool) (ha : S a = input)
    (h : undelimit input = none) :
    ∃ v' T, RunLe M (input.length + 1) ⟨some self, v, S⟩ ⟨some bad, v', T⟩ ∧
      ∀ k, k ≠ a → k ≠ b → T k = S k := by
  cases input with
  | nil =>
    refine ⟨false, S, (Run.single ?_).le (by simp), fun _ _ _ => rfl⟩
    simp [hp, readFrame, FramedCNF.Block.read, TM2.stepAux, isBit, ha]
  | cons c input =>
    cases c with
    | false => simp [undelimit] at h
    | true =>
      cases input with
      | nil =>
        refine ⟨false, update S a [], (Run.single ?_).le (by simp), ?_⟩
        · simp [hp, readFrame, FramedCNF.Block.read, TM2.stepAux, isBit, bitOf, ha]
        · intro k hk _
          simp [hk]
      | cons c input =>
        let U := update (update S a input) b (c :: S b)
        have h₁ : Run M 1 ⟨some self, v, S⟩ ⟨some self, c, U⟩ := by
          apply Run.single
          simp [hp, readFrame, FramedCNF.Block.read, TM2.stepAux, isBit, bitOf,
            ha, U, hab.symm]
        obtain ⟨v', T, h₂, hk⟩ := readFrame_bad hp hab input c U
          (by simp [U, hab]) (by simpa [undelimit] using h)
        refine ⟨v', T, (h₁.le le_rfl |>.trans h₂).mono (by simp; omega), ?_⟩
        intro k hka hkb
        simp [hk k hka hkb, U, hka, hkb]
termination_by input.length
decreasing_by grind

private def splitBits (s a b : K) (self next : Lab) :
    TM2.Stmt (fun _ : K => Bool) Lab Bool :=
  splitB s a b some id id self next

private theorem splitBits_run {s a b : K} {self next : Lab}
    (hp : M self = splitBits s a b self next) (hsa : s ≠ a) (hsb : s ≠ b)
    (hab : a ≠ b) (v : Bool) (S : K → List Bool) :
    Run M ((S s).length + 1) ⟨some self, v, S⟩
      ⟨some next, false,
        update (update (update S s []) a ((S s).reverse ++ S a)) b ((S s).reverse ++ S b)⟩ := by
  obtain ⟨T, hr, hs, ha, hb, hk⟩ := splitB_run hp hsa hsb hab id (fun _ => rfl)
    (S s) [] v S (by simp [EndsBitBlock]) (by simp)
  convert hr using 2
  funext k
  by_cases hks : k = s
  · subst k
    simp [hs, hsa, hsb]
  by_cases hka : k = a
  · subst k
    simpa [hab] using ha.symm
  by_cases hkb : k = b
  · subst k
    simpa using hb.symm
  simp [hks, hka, hkb, hk k hks hka hkb]

private def writeBits (a b : K) (chunk : Bool → List Bool) (suffix : List Bool) (self next : Lab) :
    TM2.Stmt (fun _ : K => Bool) Lab Bool :=
  .peek a (fun _ v => v.isSome) <| .branch id
    (.pop a (fun _ v => v.getD false) <| .branch id
      (emit b (chunk true) self) (emit b (chunk false) self))
    (emit b suffix next)

private theorem writeBits_run {a b : K} {self next : Lab}
    {chunk : Bool → List Bool} {suffix : List Bool}
    (hp : M self = writeBits a b chunk suffix self next) (hab : a ≠ b)
    (v : Bool) (S : K → List Bool) :
    Run M ((S a).length + 1) ⟨some self, v, S⟩
      ⟨some next, false,
        update (update S a []) b (((S a).flatMap chunk ++ suffix).reverse ++ S b)⟩ := by
  generalize hx : S a = xs
  induction xs generalizing v S with
  | nil =>
    apply Run.single
    have hu : update S a [] = S := by rw [← hx, Function.update_eq_self]
    simp [hp, writeBits, TM2.stepAux, hx, hu, emit, stepAux_pushList]
  | cons bit xs ih =>
    let T := update (update S a xs) b ((chunk bit).reverse ++ S b)
    have h₁ : Run M 1 ⟨some self, v, S⟩ ⟨some self, bit, T⟩ := by
      apply Run.single
      cases bit <;> simp [hp, writeBits, TM2.stepAux, hx, T, emit, stepAux_pushList, hab.symm]
    have ht : T a = xs := by simp [T, hab]
    have h₂ := ih bit T ht
    have hr := (h₁.trans h₂).of_eq (Nat.add_comm 1 (xs.length + 1))
    convert hr using 2
    funext k
    by_cases hka : k = a
    · subst k
      simp [hab]
    by_cases hkb : k = b
    · subst k
      simp [T, List.reverse_append, List.append_assoc]
    simp [T, hka, hkb]

end BitStacks

section Lift

open Computability

private def liftBit (b : Bool) : List Bool := [true, b]

private def liftBits (xs : List Bool) : List Bool := xs.flatMap liftBit

private theorem delimit_eq (xs : List Bool) : delimit xs = liftBits xs ++ [false] := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [delimit, liftBits, liftBit, ih]

private theorem liftBits_append (xs ys : List Bool) :
    liftBits (xs ++ ys) = liftBits xs ++ liftBits ys := List.flatMap_append

end Lift

section BinaryStacks

variable {K Lab : Type} [DecidableEq K]
variable {M : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool}

private abbrev DigitStep := Bool → Bool → Bool → Bool × List Bool

private def scanDigits (step : DigitStep) : ℕ → Bool → List Bool → List Bool → Bool × List Bool
  | 0, c, _, _ => (c, [])
  | n + 1, c, xs, ys =>
    if xs.isEmpty && ys.isEmpty then (c, [])
    else
      let (c', emit) := step c (xs.headD false) (ys.headD false)
      let (c'', tail) := scanDigits step n c' xs.tail ys.tail
      (c'', emit ++ tail)

private def zipDigits (a b out : K) (step : DigitStep) (self done : Lab) :
    TM2.Stmt (fun _ : K => Bool) Lab Bool :=
  let write c x y := .load (fun _ => (step c x y).1) (emit out (step c x y).2 self)
  let readB c x := .pop b (fun _ o => o.getD false) <|
    .branch id (write c x true) (write c x false)
  let start c := .peek a (fun _ o => o.isSome) <|
    .branch id
      (.pop a (fun _ o => o.getD false) <| .branch id (readB c true) (readB c false))
      (.peek b (fun _ o => o.isSome) <|
        .branch id (readB c false) (.load (fun _ => c) (.goto fun _ => done)))
  .branch id (start true) (start false)

private theorem zipDigits_run {a b out : K} {step : DigitStep} {self done : Lab}
    (hp : M self = zipDigits a b out step self done) (hab : a ≠ b)
    (hao : a ≠ out) (hbo : b ≠ out) (n : ℕ) (c : Bool) (S : K → List Bool)
    (ha : (S a).length ≤ n) (hb : (S b).length ≤ n) :
    let r := scanDigits step n c (S a) (S b)
    RunLe M (n + 1) ⟨some self, c, S⟩
      ⟨some done, r.1, update (update (update S a []) b []) out (r.2.reverse ++ S out)⟩ := by
  dsimp only
  induction n generalizing c S with
  | zero =>
    have ea : S a = [] := by simpa using ha
    have eb : S b = [] := by simpa using hb
    have he : update (update (update S a []) b []) out
        ((scanDigits step 0 c (S a) (S b)).2.reverse ++ S out) = S := by
      funext k
      simp only [Function.update_apply, scanDigits, List.reverse_nil, List.nil_append]
      split_ifs with h₁ h₂ h₃ <;> subst_vars <;> simp_all
    rw [he]
    apply Run.le (n := 1) _ le_rfl
    apply Run.single
    cases c <;> simp [hp, zipDigits, TM2.stepAux, ea, eb, scanDigits]
  | succ n ih =>
    by_cases hnil : S a = [] ∧ S b = []
    · obtain ⟨ea, eb⟩ := hnil
      have he : update (update (update S a []) b []) out
          ((scanDigits step (n + 1) c (S a) (S b)).2.reverse ++ S out) = S := by
        simp only [ea, eb, scanDigits, List.isEmpty_nil, Bool.and_self, ↓reduceIte,
          List.reverse_nil, List.nil_append]
        funext k
        simp only [Function.update_apply]
        split_ifs with h₁ h₂ h₃ <;> subst_vars <;> simp_all
      rw [he]
      apply Run.le (n := 1) _ (by omega)
      apply Run.single
      cases c <;> simp [hp, zipDigits, TM2.stepAux, ea, eb, scanDigits]
    · let headA := (S a).headD false
      let headB := (S b).headD false
      let T := update (update (update S a (S a).tail) b (S b).tail)
        out ((step c headA headB).2.reverse ++ S out)
      have hstep : Run M 1 ⟨some self, c, S⟩ ⟨some self, (step c headA headB).1, T⟩ := by
        apply Run.single
        cases ea : S a with
        | nil =>
          cases eb : S b with
          | nil => exact (hnil ⟨ea, eb⟩).elim
          | cons y ys =>
            have he : update S a [] = S := by
              calc update S a [] = update S a (S a) := congrArg (update S a) ea.symm
                _ = S := update_eq_self _ _
            cases c <;> cases y <;>
              simp [hp, zipDigits, TM2.stepAux, ea, eb, headA, headB, T, emit, stepAux_pushList,
                hab.symm, hbo.symm, he]
        | cons x xs =>
          cases eb : S b with
          | nil =>
            cases c <;> cases x <;>
              simp [hp, zipDigits, TM2.stepAux, ea, eb, headA, headB, T, emit, stepAux_pushList,
                hab.symm, hao.symm, hbo.symm]
          | cons y ys =>
            cases c <;> cases x <;> cases y <;>
              simp [hp, zipDigits, TM2.stepAux, ea, eb, headA, headB, T, emit, stepAux_pushList,
                hab.symm, hao.symm, hbo.symm]
      have hTa : T a = (S a).tail := by simp [T, hab, hao]
      have hTb : T b = (S b).tail := by simp [T, hbo]
      have h₁ : (T a).length ≤ n := by
        rw [hTa, List.length_tail]
        omega
      have h₂ : (T b).length ≤ n := by
        rw [hTb, List.length_tail]
        omega
      have hrec := ih (step c headA headB).1 T h₁ h₂
      simp only [hTa, hTb] at hrec
      have hlen : ((S a).isEmpty && (S b).isEmpty) = false := by
        cases ea : S a <;> cases eb : S b <;> simp_all
      simp only [scanDigits, hlen, Bool.false_eq_true, ↓reduceIte]
      have hr := (hstep.le le_rfl |>.trans hrec).mono (B' := n + 1 + 1) (by omega)
      convert hr using 2
      funext k
      by_cases hko : k = out
      · subst k
        simp [T, headA, headB, List.reverse_append, List.append_assoc]
      by_cases hka : k = a
      · subst k
        simp [hab, hao]
      by_cases hkb : k = b
      · subst k
        simp [hbo]
      simp [T, hko, hka, hkb]

end BinaryStacks

section BinaryArithmetic

open Computability Cslib.Complexity.Karp

private def addDigit (c a b : Bool) : Bool × List Bool :=
  (SSVerify.carry a b c, [a ^^ b ^^ c])

private def sumResult (r : Bool × List Bool) : List Bool :=
  r.2 ++ if r.1 then [true] else []

private theorem scan_add (n : ℕ) (c : Bool) (xs ys : List Bool)
    (hx : xs.length ≤ n) (hy : ys.length ≤ n) :
    sumResult (scanDigits addDigit n c xs ys) = SSVerify.addB c xs ys := by
  induction n generalizing c xs ys with
  | zero =>
    have ex : xs = [] := by simpa using hx
    have ey : ys = [] := by simpa using hy
    subst xs ys
    rfl
  | succ n ih =>
    cases xs with
    | nil =>
      cases ys with
      | nil => rfl
      | cons b ys =>
        have hy' : ys.length ≤ n := by simpa using hy
        simpa [addDigit, scanDigits, sumResult, SSVerify.addB] using
          congrArg (fun s => (false ^^ b ^^ c) :: s)
            (ih (SSVerify.carry false b c) [] ys (by simp) hy')
    | cons a xs =>
      have hx' : xs.length ≤ n := by simpa using hx
      cases ys with
      | nil =>
        have hc : SSVerify.carry a false c = (a && c) := by cases a <;> cases c <;> rfl
        simpa [addDigit, scanDigits, sumResult, SSVerify.addB, SSVerify.incB, hc] using
          congrArg (fun s => (a ^^ c) :: s) (ih (a && c) xs [] hx' (by simp))
      | cons b ys =>
        have hy' : ys.length ≤ n := by simpa using hy
        simpa [addDigit, scanDigits, sumResult, SSVerify.addB] using
          congrArg (fun s => (a ^^ b ^^ c) :: s)
            (ih (SSVerify.carry a b c) xs ys hx' hy')

private def compareDigit (flag a b : Bool) : Bool × List Bool :=
  (if a = b then flag else a, [])

private theorem scan_compare (n : ℕ) (c : Bool) (x y : ℕ)
    (hx : (encodeNat x).length ≤ n) (hy : (encodeNat y).length ≤ n) :
    scanDigits compareDigit n c (encodeNat x) (encodeNat y) =
      (if x = y then c else decide (y < x), []) := by
  have zero_of_empty (a : ℕ) (h : encodeNat a = []) : a = 0 := by
    have hd := congrArg decodeNat h
    rw [decode_encodeNat] at hd
    exact hd
  induction n generalizing c x y with
  | zero =>
    have ex := zero_of_empty x (List.eq_nil_of_length_eq_zero (by omega))
    have ey := zero_of_empty y (List.eq_nil_of_length_eq_zero (by omega))
    subst x y
    simp [scanDigits]
  | succ n ih =>
    by_cases h : ((encodeNat x).isEmpty && (encodeNat y).isEmpty) = true
    · obtain ⟨hx', hy'⟩ := Bool.and_eq_true_iff.mp h
      have ex := zero_of_empty x (List.isEmpty_iff.mp hx')
      have ey := zero_of_empty y (List.isEmpty_iff.mp hy')
      subst x y
      rfl
    have hx' : (encodeNat (x / 2)).length ≤ n := by
      rw [← SSVerify.tail_encodeNat, List.length_tail]
      omega
    have hy' : (encodeNat (y / 2)).length ≤ n := by
      rw [← SSVerify.tail_encodeNat, List.length_tail]
      omega
    simp only [scanDigits, ite_eq_right h, compareDigit, SSVerify.tail_encodeNat,
      SSVerify.headD_encodeNat, List.nil_append]
    rw [ih _ _ _ hx' hy']
    congr 1
    rcases Nat.mod_two_eq_zero_or_one x with hx₂ | hx₂ <;>
      rcases Nat.mod_two_eq_zero_or_one y with hy₂ | hy₂ <;>
      simp only [hx₂, hy₂, Nat.zero_ne_one, decide_false, decide_true] <;>
      split_ifs <;> simp_all <;> omega

end BinaryArithmetic

section ArithmeticMachine

open Computability Cslib.Complexity.Karp Cslib.Complexity.FramedCNF

variable {K Lab : Type} [DecidableEq K]
variable {M : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool}

private def normalizeRev (k : K) (next : Lab) : TM2.Stmt (fun _ : K => Bool) Lab Bool :=
  .peek k (fun _ o => decide (o = some false)) <|
    .branch id (.push k (fun _ => true) (.goto fun _ => next)) (.goto fun _ => next)

private theorem normalizeRev_run {a b : K} {self move next : Lab}
    (hp : M self = normalizeRev a move) (hm : M move = moveBits a b move next)
    (hab : a ≠ b) (raw : List Bool) (v : Bool) (S : K → List Bool) (ha : S a = raw.reverse) :
    ∃ v', RunLe M (raw.length + 3) ⟨some self, v, S⟩
      ⟨some next, v', update (update S a []) b (encodeNat (decodeNat raw) ++ S b)⟩ := by
  let z := decide (raw.getLast? = some false)
  let p := (if z then true :: raw.reverse else raw.reverse)
  let T := update S a p
  have h₁ : Run M 1 ⟨some self, v, S⟩ ⟨some move, z, T⟩ := by
    apply Run.single
    by_cases h : raw.getLast? = some false
    · simp [hp, normalizeRev, TM2.stepAux, ha, h, z, T, p]
    · have ep : p = raw.reverse := by simp [p, z, h]
      have he : T = S := by
        change update S a p = S
        rw [ep, ← ha, update_eq_self]
      simp [hp, normalizeRev, TM2.stepAux, ha, h, z, he]
  obtain ⟨v', h₂⟩ := moveBits_run hm hab z T
  have he : p.reverse = encodeNat (decodeNat raw) := by
    rw [← normalizeNat_eq_encode_decode]
    by_cases h : raw.getLast? = some false <;> simp [p, z, normalizeNat, h]
  have ho : update (update T a []) b ((T a).reverse ++ T b) =
      update (update S a []) b (encodeNat (decodeNat raw) ++ S b) := by
    simp [T, hab.symm, he]
  refine ⟨v', ?_⟩
  rw [← ho]
  apply (h₁.trans h₂).le
  have hlen := length_normalizeNat_le raw
  have he' : p.length = (normalizeNat raw).length := by
    rw [← List.length_reverse, he, normalizeNat_eq_encode_decode]
  simp only [T, update_self]
  omega

private def pushCarry (k : K) (next : Lab) : TM2.Stmt (fun _ : K => Bool) Lab Bool :=
  .branch id (.push k (fun _ => true) (.goto fun _ => next)) (.goto fun _ => next)

private theorem add_run {a b out : K} {self carry next : Lab}
    (hp : M self = zipDigits a b out addDigit self carry)
    (hc : M carry = pushCarry out next) (hab : a ≠ b) (hao : a ≠ out) (hbo : b ≠ out)
    (m n : ℕ) (v : Bool) (S : K → List Bool)
    (ha : S a = encodeNat m) (hb : S b = encodeNat n) (ho : S out = []) (hv : v = false) :
    ∃ v', RunLe M ((encodeNat m).length + (encodeNat n).length + 2) ⟨some self, v, S⟩
      ⟨some next, v', update (update (update S a []) b []) out
        (encodeNat (m + n)).reverse⟩ := by
  subst v
  let N := (encodeNat m).length + (encodeNat n).length
  let r := scanDigits addDigit N false (encodeNat m) (encodeNat n)
  have ha' : (encodeNat m).length ≤ N := Nat.le_add_right ..
  have hb' : (encodeNat n).length ≤ N := Nat.le_add_left ..
  have h₁ := zipDigits_run hp hab hao hbo N false S (ha.symm ▸ ha') (hb.symm ▸ hb')
  rw [ha, hb, ho] at h₁
  let T := update (update (update S a []) b []) out r.2.reverse
  have h₁' : RunLe M (N + 1) ⟨some self, false, S⟩ ⟨some carry, r.1, T⟩ := by
    simpa only [List.append_nil, T, r] using h₁
  have hs : sumResult r = encodeNat (m + n) := by
    rw [show r = _ from rfl, scan_add N _ _ _ ha' hb', SSVerify.addB_encodeNat]
    rfl
  have h₂ : Run M 1 ⟨some carry, r.1, T⟩
      ⟨some next, r.1, update (update (update S a []) b []) out (encodeNat (m + n)).reverse⟩ := by
    rw [← hs]
    apply Run.single
    cases h : r.1 <;> simp [hc, pushCarry, TM2.stepAux, T, sumResult, h, List.reverse_append]
  exact ⟨r.1, (h₁'.trans (h₂.le le_rfl)).mono (by omega)⟩


private theorem compare_run {a b out : K} {self next : Lab}
    (hp : M self = zipDigits a b out compareDigit self next)
    (hab : a ≠ b) (hao : a ≠ out) (hbo : b ≠ out) (m n : ℕ) (S : K → List Bool)
    (ha : S a = encodeNat m) (hb : S b = encodeNat n) :
    RunLe M ((encodeNat m).length + (encodeNat n).length + 1) ⟨some self, false, S⟩
      ⟨some next, decide (n < m), update (update S a []) b []⟩ := by
  let N := (encodeNat m).length + (encodeNat n).length
  have hm : (encodeNat m).length ≤ N := Nat.le_add_right ..
  have hn : (encodeNat n).length ≤ N := Nat.le_add_left ..
  have h := zipDigits_run hp hab hao hbo N false S (ha.symm ▸ hm) (hb.symm ▸ hn)
  have hj : (if m = n then false else decide (n < m)) = decide (n < m) := by
    split_ifs with he <;> simp [he]
  rw [ha, hb, scan_compare N _ _ _ hm hn, hj] at h
  have he : update (update (update S a []) b []) out (S out) = update (update S a []) b [] := by
    conv_lhs => rw [← show update (update S a []) b [] out = S out by simp [hao.symm, hbo.symm]]
    exact update_eq_self _ _
  simpa only [List.reverse_nil, List.nil_append, he, N] using h

end ArithmeticMachine

section Lengths

open Computability Cslib.Complexity.FramedCNF Cslib.Complexity.Karp

private theorem encodeNat_add_length (x y : ℕ) :
    (encodeNat (x + y)).length ≤ (encodeNat x).length + (encodeNat y).length + 1 := by
  have h := SSVerify.length_addB false (encodeNat x) (encodeNat y)
  rwa [SSVerify.addB_encodeNat, Bool.toNat_false, Nat.add_zero] at h

private theorem decoded_length (p : List Bool) :
    (encodeNat (decodeNat p)).length ≤ p.length + 1 := by
  rw [← normalizeNat_eq_encode_decode]
  exact length_normalizeNat_le p

end Lengths

end Infra

section Comp

open MetaMathlibExt MetaMathlibExt.BitstringEncoding
open Turing Function TM2Program Cslib.Complexity
open Computability

private theorem encodeNat_double {x : ℕ} (hx : 0 < x) :
    encodeNat (2 * x) = false :: encodeNat x := by
  rw [TM2Recursive.encodeNat_eq_cons (by omega)]
  have h1 : 2 * x % 2 = 0 := by omega
  have h2 : 2 * x / 2 = x := by omega
  simp [h1, h2]

private theorem encodeNat_double_add_one (x : ℕ) : encodeNat (2 * x + 1) = true :: encodeNat x := by
  rw [TM2Recursive.encodeNat_eq_cons (by omega)]
  have h1 : (2 * x + 1) % 2 = 1 := by omega
  have h2 : (2 * x + 1) / 2 = x := by omega
  simp [h1, h2]

private theorem encodeNat_ones (j q : ℕ) :
    encodeNat (2 ^ j * q + (2 ^ j - 1)) = List.replicate j true ++ encodeNat q := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : 2 ^ (j + 1) = 2 * 2 ^ j := by rw [pow_succ]; ring
    have h2 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
    have he : 2 ^ (j + 1) * q + (2 ^ (j + 1) - 1) = 2 * (2 ^ j * q + (2 ^ j - 1)) + 1 := by
      rw [h1, mul_assoc]
      generalize 2 ^ j * q = u at *
      generalize 2 ^ j = t at *
      omega
    rw [he, encodeNat_double_add_one, ih, List.replicate_succ, List.cons_append]

private theorem encodeNat_zeros (j x : ℕ) (hx : 0 < x) :
    encodeNat (2 ^ j * x) = List.replicate j false ++ encodeNat x := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h1 : 2 ^ (j + 1) * x = 2 * (2 ^ j * x) := by rw [pow_succ]; ring
    have h2 : 0 < 2 ^ j * x := Nat.mul_pos (Nat.two_pow_pos j) hx
    rw [h1, encodeNat_double h2, ih, List.replicate_succ, List.cons_append]

private theorem encodeNat_eq_nil_iff (n : ℕ) : encodeNat n = [] ↔ n = 0 := by
  constructor
  · intro h
    have hd := congrArg decodeNat h
    rwa [decode_encodeNat] at hd
  · rintro rfl
    rfl

/-- Mathlib's decoder reads every nonempty bit list as a positive number. -/
private theorem decodeNat_pos_iff (b : List Bool) : 0 < decodeNat b ↔ b ≠ [] := by
  constructor
  · rintro h rfl
    exact absurd h (by decide)
  · intro hb
    rw [Nat.pos_iff_ne_zero]
    intro h
    have he := (encodeNat_eq_nil_iff _).mpr h
    rw [← Cslib.Complexity.FramedCNF.normalizeNat_eq_encode_decode] at he
    unfold Cslib.Complexity.FramedCNF.normalizeNat at he
    split_ifs at he <;> simp_all

section Components

variable {K Lab : Type} [DecidableEq K]
variable {M : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool}

/-- One round of decrementing the binary number on `a`: a low `0` bit becomes a `1` parked on
`t`; the lowest `1` bit becomes `0` (dropped when it is the top bit). -/
private def decLoop (a t : K) (self restore : Lab) : TM2.Stmt (fun _ : K => Bool) Lab Bool :=
  .pop a (fun _ o => o.getD false) <| .branch id
    (.peek a (fun _ o => o.isSome) <| .branch id
      (.push a (fun _ => false) (.goto fun _ => restore))
      (.goto fun _ => restore))
    (.push t (fun _ => true) (.goto fun _ => self))

private theorem dec_run {a t : K} {self restore next : Lab}
    (hp : M self = decLoop a t self restore) (hr : M restore = moveBits t a restore next)
    (hat : a ≠ t) : ∀ (n m j : ℕ) (v : Bool) (S : K → List Bool),
      (encodeNat m).length ≤ n → 0 < m → S a = encodeNat m → S t = List.replicate j true →
      ∃ v', RunLe M (2 * n + j + 3) ⟨some self, v, S⟩
        ⟨some next, v', update (update S t []) a (encodeNat (2 ^ j * m - 1))⟩ := by
  intro n
  induction n with
  | zero =>
    intro m j v S hl hm
    have : encodeNat m = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [encodeNat_eq_nil_iff] at this
    omega
  | succ n ih =>
    intro m j v S hl hm ha ht
    rcases Nat.even_or_odd' m with ⟨q, rfl | rfl⟩
    · -- even: a low zero
      have hq : 0 < q := by omega
      have he : encodeNat (2 * q) = false :: encodeNat q := encodeNat_double hq
      let T := update (update S a (encodeNat q)) t (true :: S t)
      have h₁ : Run M 1 ⟨some self, v, S⟩ ⟨some self, false, T⟩ := by
        apply Run.single
        simp [hp, decLoop, TM2.stepAux, ha, he, T, hat.symm]
      have hl' : (encodeNat q).length ≤ n := by rw [he] at hl; simpa using hl
      obtain ⟨v', h₂⟩ := ih q (j + 1) false T hl' hq (by simp [T, hat])
        (by simp [T, ht, List.replicate_succ])
      refine ⟨v', ?_⟩
      have hpow : 2 ^ (j + 1) * q = 2 ^ j * (2 * q) := by rw [pow_succ]; ring
      have hT : update (update T t []) a (encodeNat (2 ^ (j + 1) * q - 1)) =
          update (update S t []) a (encodeNat (2 ^ j * (2 * q) - 1)) := by
        rw [hpow]
        funext k
        by_cases hka : k = a
        · subst k; simp
        by_cases hkt : k = t
        · subst k; simp [T, hka]
        · simp [T, hka, hkt]
      rw [hT] at h₂
      exact ((h₁.le le_rfl).trans h₂).mono (by omega)
    · -- odd: the lowest one
      have he : encodeNat (2 * q + 1) = true :: encodeNat q := encodeNat_double_add_one q
      let R := if q = 0 then [] else false :: encodeNat q
      have hR : R = encodeNat (2 * q) := by
        by_cases hq : q = 0
        · subst hq; rfl
        · simp [R, hq, encodeNat_double (Nat.pos_of_ne_zero hq)]
      let T := update S a R
      have h₁ : Run M 1 ⟨some self, v, S⟩ ⟨some restore, decide (q ≠ 0), T⟩ := by
        apply Run.single
        by_cases hq : q = 0
        · subst hq
          have h0 : encodeNat 0 = [] := rfl
          simp [hp, decLoop, TM2.stepAux, ha, he, h0, T, R]
        · have hne : encodeNat q ≠ [] := by rw [Ne, encodeNat_eq_nil_iff]; exact hq
          obtain ⟨b, bs, hbs⟩ := List.exists_cons_of_ne_nil hne
          simp [hp, decLoop, TM2.stepAux, ha, he, T, R, hq, hbs]
      obtain ⟨v', h₂⟩ := moveBits_run (M := M) hr hat.symm (decide (q ≠ 0)) T
      refine ⟨v', ?_⟩
      have hval : encodeNat (2 ^ j * (2 * q + 1) - 1) =
          List.replicate j true ++ encodeNat (2 * q) := by
        rw [← encodeNat_ones j (2 * q)]
        congr 1
        have h2 : 1 ≤ 2 ^ j := Nat.one_le_two_pow
        rw [Nat.mul_add, Nat.mul_one]
        generalize 2 ^ j * (2 * q) = u at *
        omega
      have hT : update (update T t []) a ((T t).reverse ++ T a) =
          update (update S t []) a (encodeNat (2 ^ j * (2 * q + 1) - 1)) := by
        rw [hval]
        funext k
        by_cases hka : k = a
        · subst k; simp [T, hat.symm, ht, hR]
        by_cases hkt : k = t
        · subst k; simp [T, hka]
        · simp [T, hka, hkt]
      rw [hT] at h₂
      refine ((h₁.trans h₂).le le_rfl).mono ?_
      simp [T, hat.symm, ht]
      omega

/-- One round of incrementing the binary number on `a`: a low `1` bit becomes a `0` parked on
`t`; the lowest `0` bit, or the end, becomes `1`. -/
private def incLoop (a t : K) (self restore : Lab) : TM2.Stmt (fun _ : K => Bool) Lab Bool :=
  .pop a (fun _ o => o.getD false) <| .branch id
    (.push t (fun _ => false) (.goto fun _ => self))
    (.push a (fun _ => true) (.goto fun _ => restore))

private theorem inc_run {a t : K} {self restore next : Lab}
    (hp : M self = incLoop a t self restore) (hr : M restore = moveBits t a restore next)
    (hat : a ≠ t) : ∀ (n m j : ℕ) (v : Bool) (S : K → List Bool),
      (encodeNat m).length ≤ n → S a = encodeNat m → S t = List.replicate j false →
      ∃ v', RunLe M (2 * n + j + 3) ⟨some self, v, S⟩
        ⟨some next, v', update (update S t []) a (encodeNat (2 ^ j * (m + 1)))⟩ := by
  intro n
  induction n with
  | zero =>
    intro m j v S hl ha ht
    have hm : encodeNat m = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hm0 : m = 0 := (encodeNat_eq_nil_iff m).mp hm
    subst hm0
    let T := update S a [true]
    have h₁ : Run M 1 ⟨some self, v, S⟩ ⟨some restore, false, T⟩ := by
      apply Run.single
      have h0 : encodeNat 0 = [] := rfl
      simp [hp, incLoop, TM2.stepAux, ha, T, h0]
    obtain ⟨v', h₂⟩ := moveBits_run (M := M) hr hat.symm false T
    refine ⟨v', ?_⟩
    have hT : update (update T t []) a ((T t).reverse ++ T a) =
        update (update S t []) a (encodeNat (2 ^ j * (0 + 1))) := by
      rw [Nat.zero_add, Nat.mul_one, show 2 ^ j = 2 ^ j * 1 by ring,
        encodeNat_zeros j 1 (by decide)]
      funext k
      by_cases hka : k = a
      · subst k; simp [T, hat.symm, ht, show encodeNat 1 = [true] from rfl]
      by_cases hkt : k = t
      · subst k; simp [T, hka]
      · simp [T, hka, hkt]
    rw [hT] at h₂
    refine ((h₁.trans h₂).le le_rfl).mono ?_
    simp [T, hat.symm, ht]
    omega
  | succ n ih =>
    intro m j v S hl ha ht
    rcases Nat.even_or_odd' m with ⟨q, rfl | rfl⟩
    · -- even (possibly zero): the low bit becomes one
      let R := true :: (encodeNat (2 * q)).tail
      have hR : R = encodeNat (2 * q + 1) := by
        rw [encodeNat_double_add_one]
        by_cases hq : q = 0
        · subst hq; rfl
        · simp [R, encodeNat_double (Nat.pos_of_ne_zero hq)]
      let T := update S a R
      have h₁ : Run M 1 ⟨some self, v, S⟩ ⟨some restore, false, T⟩ := by
        apply Run.single
        by_cases hq : q = 0
        · subst hq
          have h0 : encodeNat 0 = [] := rfl
          simp [hp, incLoop, TM2.stepAux, ha, T, R, h0]
        · simp [hp, incLoop, TM2.stepAux, ha, T, R, encodeNat_double (Nat.pos_of_ne_zero hq)]
      obtain ⟨v', h₂⟩ := moveBits_run (M := M) hr hat.symm false T
      refine ⟨v', ?_⟩
      have hT : update (update T t []) a ((T t).reverse ++ T a) =
          update (update S t []) a (encodeNat (2 ^ j * (2 * q + 1))) := by
        rw [encodeNat_zeros j _ (by omega), ← hR]
        funext k
        by_cases hka : k = a
        · subst k; simp [T, hat.symm, ht]
        by_cases hkt : k = t
        · subst k; simp [T, hka]
        · simp [T, hka, hkt]
      rw [hT] at h₂
      refine ((h₁.trans h₂).le le_rfl).mono ?_
      simp [T, hat.symm, ht]
      omega
    · -- odd: a low one carries
      have he : encodeNat (2 * q + 1) = true :: encodeNat q := encodeNat_double_add_one q
      let T := update (update S a (encodeNat q)) t (false :: S t)
      have h₁ : Run M 1 ⟨some self, v, S⟩ ⟨some self, true, T⟩ := by
        apply Run.single
        simp [hp, incLoop, TM2.stepAux, ha, he, T, hat.symm]
      have hl' : (encodeNat q).length ≤ n := by rw [he] at hl; simpa using hl
      obtain ⟨v', h₂⟩ := ih q (j + 1) true T hl' (by simp [T, hat])
        (by simp [T, ht, List.replicate_succ])
      refine ⟨v', ?_⟩
      have hpow : 2 ^ (j + 1) * (q + 1) = 2 ^ j * (2 * q + 1 + 1) := by rw [pow_succ]; ring
      have hT : update (update T t []) a (encodeNat (2 ^ (j + 1) * (q + 1))) =
          update (update S t []) a (encodeNat (2 ^ j * (2 * q + 1 + 1))) := by
        rw [hpow]
        funext k
        by_cases hka : k = a
        · subst k; simp
        by_cases hkt : k = t
        · subst k; simp [T, hka]
        · simp [T, hka, hkt]
      rw [hT] at h₂
      exact ((h₁.le le_rfl).trans h₂).mono (by omega)

end Components

end Comp

section Prog

open MetaMathlibExt MetaMathlibExt.BitstringEncoding
open Turing Function TM2Program Cslib.Complexity
open Computability Cslib.Complexity.Karp Cslib.Complexity.FramedCNF

private inductive K
  | jobs | witness | skipped | elapsed | cost | bound | tmp | payload
  | processRev | dueRev | operand | elapsedCopy | sum
  | inp | aRev | sRev | jRev | jBound | sList | sTmp | sVal | decTmp | walked | back
  | flags | skipFlags | curFlag | count
  deriving DecidableEq

private inductive Field | bound | process | due | weight
  deriving DecidableEq

private inductive Lab
  -- phase A: parse
  | start | readS | revJ | normJ | normJMove | posJ | restoreA | wtjStart | reverseBound
  | restoreJobs | posK | restoreS
  -- phase B: one flag per record
  | count | countRead | countPayload | countWrite | countFlag | countDone
  -- phase C: mark the flags of `S`
  | sLoop | sRead | sNorm | sNormMove | walk | dec | decRestore | walkStep | unwalk
  -- phase D: the plan
  | loop | read (skip : Bool) | restorePayload (skip : Bool) | skip | skipFlag | takeFlag
  | restoreSkipped | restoreFlags | readProcess | readDue
  | norm (f : Field) | normMove (f : Field) | pos (f : Field)
  | addStart (penalty : Bool) | add (penalty : Bool)
  | carry (penalty : Bool) | store (penalty : Bool) | dropFlag
  | compareStart (final : Bool) | compare (final : Bool) | compareDone (final : Bool)
  | onTime | discardWeight | countFlag2 | inc | incRestore | reverseWeight
  | compareJ | compareJRun | compareJDone
  | yes | no
  deriving DecidableEq

private def normSource : Field → K
  | .bound | .process => .processRev
  | .due => .dueRev
  | .weight => .tmp

private def normTarget : Field → K
  | .bound => .bound
  | _ => .operand

private def normNext : Field → Lab
  | .bound => .posK
  | f => .pos f

private def posNext : Field → Lab
  | .bound => .restoreS
  | .process => .addStart false
  | .due => .compareStart false
  | .weight => .addStart true

private def addTarget (penalty : Bool) : K := if penalty then .cost else .elapsed

private def cmpLeft (final : Bool) : K := if final then .cost else .elapsedCopy

private def cmpRight (final : Bool) : K := if final then .bound else .operand

private def yesNo (ok : Bool) : Lab := if ok then .yes else .no

private def cmpNext (final gt : Bool) : Lab :=
  if final then (if gt then .no else .compareJ) else if gt then .reverseWeight else .onTime

/-- Branch on whether stack `k` is nonempty. -/
private def ifNonempty (k : K) (some none : Lab) : TM2.Stmt (fun _ : K => Bool) Lab Bool :=
  .peek k (fun _ o => o.isSome) <| .branch id (.goto fun _ => some) (.goto fun _ => none)

private def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .start => readFrame .inp .aRev .start .readS .no
  | .readS => readFrame .inp .sRev .readS .revJ .no
  | .revJ => moveBits .inp .jRev .revJ .normJ
  | .normJ => normalizeRev .jRev .normJMove
  | .normJMove => moveBits .jRev .jBound .normJMove .posJ
  | .posJ => ifNonempty .jBound .restoreA .no
  | .restoreA => moveBits .aRev .jobs .restoreA .wtjStart
  | .wtjStart => readFrame .jobs .tmp .wtjStart .reverseBound .no
  | .reverseBound => moveBits .jobs .processRev .reverseBound .restoreJobs
  | .restoreJobs => moveBits .tmp .jobs .restoreJobs (.norm .bound)
  | .posK => ifNonempty .bound .restoreS .no
  | .restoreS => moveBits .sRev .sList .restoreS .count
  | .count => ifNonempty .jobs .countRead .countDone
  | .countRead => readFrame .jobs .tmp .countRead .countPayload .no
  | .countPayload => moveBits .tmp .payload .countPayload .countWrite
  | .countWrite => writeBits .payload .back liftBit [false] .countWrite .countFlag
  | .countFlag => .push .flags (fun _ => false) (.goto fun _ => .count)
  | .countDone => moveBits .back .jobs .countDone .sLoop
  | .sLoop => ifNonempty .sList .sRead .loop
  | .sRead => readFrame .sList .sTmp .sRead .sNorm .no
  | .sNorm => normalizeRev .sTmp .sNormMove
  | .sNormMove => moveBits .sTmp .sVal .sNormMove .walk
  | .walk => .peek .sVal (fun _ o => o.isSome) <| .branch id (.goto fun _ => .dec)
      (.pop .flags (fun _ o => o.isSome) <| .branch id
        (.push .flags (fun _ => true) (.goto fun _ => .unwalk)) (.goto fun _ => .no))
  | .dec => decLoop .sVal .decTmp .dec .decRestore
  | .decRestore => moveBits .decTmp .sVal .decRestore .walkStep
  | .walkStep => .peek .flags (fun _ o => o.isSome) <| .branch id
      (.pop .flags (fun _ o => o.getD false) (.push .walked id (.goto fun _ => .walk)))
      (.goto fun _ => .no)
  | .unwalk => moveBits .walked .flags .unwalk .sLoop
  | .loop => .peek .witness (fun _ o => o.isSome) <| .branch id
      (.pop .witness (fun _ o => o.getD false) (.goto Lab.read))
      (.peek .jobs (fun _ o => o.isSome) <| .branch id (.goto fun _ => .no)
        (.peek .skipped (fun _ o => o.isSome) <| .branch id
          (.goto fun _ => .no) (.goto fun _ => .compareStart true)))
  | .read skip => readFrame .jobs .tmp (.read skip) (.restorePayload skip) .no
  | .restorePayload skip => moveBits .tmp .payload (.restorePayload skip)
      (if skip then .skip else .takeFlag)
  | .skip => writeBits .payload .skipped liftBit [false] .skip .skipFlag
  | .skipFlag => .pop .flags (fun _ o => o.getD false) (.push .skipFlags id (.goto fun _ => .loop))
  | .takeFlag => .pop .flags (fun _ o => o.getD false)
      (.push .curFlag id (.goto fun _ => .restoreSkipped))
  | .restoreSkipped => moveBits .skipped .jobs .restoreSkipped .restoreFlags
  | .restoreFlags => moveBits .skipFlags .flags .restoreFlags .readProcess
  | .readProcess => readFrame .payload .processRev .readProcess .readDue .no
  | .readDue => readFrame .payload .dueRev .readDue (.norm .process) .no
  | .norm f => normalizeRev (normSource f) (.normMove f)
  | .normMove f => moveBits (normSource f) (normTarget f) (.normMove f) (normNext f)
  | .pos f => ifNonempty .operand (posNext f) .no
  | .addStart penalty => .load (fun _ => false) (.goto fun _ => .add penalty)
  | .add penalty => zipDigits (addTarget penalty) .operand .sum addDigit
      (.add penalty) (.carry penalty)
  | .carry penalty => pushCarry .sum (.store penalty)
  | .store false => splitBits .sum .elapsed .elapsedCopy (.store false) (.norm .due)
  | .store true => moveBits .sum .cost (.store true) .dropFlag
  | .dropFlag => .pop .curFlag (fun v _ => v) (.goto fun _ => .loop)
  | .compareStart final => .load (fun _ => false) (.goto fun _ => .compare final)
  | .compare final => zipDigits (cmpLeft final) (cmpRight final) .sum compareDigit
      (.compare final) (.compareDone final)
  | .compareDone final => .goto (cmpNext final)
  | .onTime => ifNonempty .payload .discardWeight .no
  | .discardWeight => cleanS [.payload] .discardWeight .countFlag2
  | .countFlag2 => .pop .curFlag (fun _ o => o.getD false) <| .branch id
      (.goto fun _ => .inc) (.goto fun _ => .loop)
  | .inc => incLoop .count .decTmp .inc .incRestore
  | .incRestore => moveBits .decTmp .count .incRestore .loop
  | .reverseWeight => moveBits .payload .tmp .reverseWeight (.norm .weight)
  | .compareJ => .load (fun _ => false) (.goto fun _ => .compareJRun)
  | .compareJRun => zipDigits .jBound .count .sum compareDigit .compareJRun .compareJDone
  | .compareJDone => .goto fun v => yesNo (!v)
  | .yes | .no => .halt

end Prog

section Job

open MetaMathlibExt MetaMathlibExt.BitstringEncoding
open Turing Function TM2Program Cslib.Complexity
open Computability Cslib.Complexity.Karp Cslib.Complexity.FramedCNF

/-- The stacks during the main loop. -/
private def st (r w : List Bool) (sk : List (List Bool)) (fl sf : List Bool) (acc : ℕ × ℕ)
    (c k J : ℕ) : K → List Bool
  | .jobs => r
  | .witness => w
  | .skipped => (pack sk.reverse).reverse
  | .elapsed => encodeNat acc.1
  | .cost => encodeNat acc.2
  | .bound => encodeNat k
  | .flags => fl
  | .skipFlags => sf
  | .count => encodeNat c
  | .jBound => encodeNat J
  | _ => []

private theorem ifNonempty_run {l a b : Lab} {k : K} (hp : prog l = ifNonempty k a b) (v : Bool)
    (S : K → List Bool) :
    Run prog 1 ⟨some l, v, S⟩ ⟨some (if S k = [] then b else a), (S k).head?.isSome, S⟩ := by
  apply Run.single
  cases h : S k <;> simp [hp, ifNonempty, TM2.stepAux, h]

private theorem norm_run (f : Field) (raw : List Bool) (v : Bool) (S : K → List Bool)
    (ha : S (normSource f) = raw.reverse) :
    ∃ v', RunLe prog (raw.length + 3) ⟨some (.norm f), v, S⟩
      ⟨some (normNext f), v',
        update (update S (normSource f) []) (normTarget f)
          (encodeNat (decodeNat raw) ++ S (normTarget f))⟩ :=
  normalizeRev_run (M := prog) (self := .norm f) (move := .normMove f)
    (next := normNext f) rfl rfl (by cases f <;> decide) raw v S ha

private theorem start_add_run (b : Bool) (a d : ℕ) (v : Bool) (S : K → List Bool)
    (ha : S (addTarget b) = encodeNat a) (hd : S .operand = encodeNat d)
    (hs : S .sum = []) :
    ∃ v', RunLe prog ((encodeNat a).length + (encodeNat d).length + 3)
      ⟨some (.addStart b), v, S⟩
      ⟨some (.store b), v', update (update (update S (addTarget b) []) .operand []) .sum
        (encodeNat (a + d)).reverse⟩ := by
  have h₁ : Run prog 1 ⟨some (.addStart b), v, S⟩ ⟨some (.add b), false, S⟩ :=
    Run.single rfl
  obtain ⟨v', h₂⟩ := add_run (M := prog) (self := Lab.add b) (carry := .carry b)
    (next := .store b) rfl rfl (by cases b <;> decide) (by cases b <;> decide)
    (by decide) a d false S ha hd hs rfl
  exact ⟨v', (h₁.le le_rfl |>.trans h₂).mono (by omega)⟩

private theorem start_cmp_run (b : Bool) (a d : ℕ) (v : Bool) (S : K → List Bool)
    (ha : S (cmpLeft b) = encodeNat a) (hd : S (cmpRight b) = encodeNat d) :
    RunLe prog ((encodeNat a).length + (encodeNat d).length + 3)
      ⟨some (.compareStart b), v, S⟩
      ⟨some (cmpNext b (decide (d < a))), decide (d < a),
        update (update S (cmpLeft b) []) (cmpRight b) []⟩ := by
  have h₁ : Run prog 1 ⟨some (.compareStart b), v, S⟩ ⟨some (.compare b), false, S⟩ :=
    Run.single rfl
  have h₂ := compare_run (M := prog) (self := Lab.compare b) (next := .compareDone b)
    rfl (by cases b <;> decide) (by cases b <;> decide) (by cases b <;> decide) a d S ha hd
  have h₃ : Run prog 1 ⟨some (.compareDone b), decide (d < a),
      update (update S (cmpLeft b) []) (cmpRight b) []⟩
      ⟨some (cmpNext b (decide (d < a))), decide (d < a),
        update (update S (cmpLeft b) []) (cmpRight b) []⟩ := Run.single rfl
  exact (h₁.le le_rfl |>.trans h₂ |>.trans (h₃.le le_rfl)).mono (by omega)

/-- The stacks once a selected job's fields are split off: process time and due date reversed,
weight on `payload`, and the job's flag on `curFlag`. -/
private def loaded (r w fl a d b : List Bool) (f : Bool) (acc : ℕ × ℕ) (c k J : ℕ) :
    K → List Bool :=
  update (update (update (update (st r w [] fl [] acc c k J) .processRev a.reverse) .dueRev
    d.reverse) .payload b) .curFlag [f]

private theorem encodeNat_zero' : encodeNat 0 = [] := rfl

private theorem posJob_eq (x y z : ℕ) :
    posJob (x, y, z) = (decide (0 < x) && decide (0 < y) && decide (0 < z)) := rfl

private theorem encodeNat_ne_nil {n : ℕ} (h : n ≠ 0) : encodeNat n ≠ [] := by
  rwa [Ne, encodeNat_eq_nil_iff]

private theorem loaded_run (r w fl a d b : List Bool) (f : Bool) (acc : ℕ × ℕ) (c k J : ℕ)
    (v : Bool) :
    ∃ v' T, RunLe prog (40 * (a.length + d.length + b.length +
      (encodeNat acc.1).length + (encodeNat acc.2).length + (encodeNat c).length + 1))
      ⟨some (.norm .process), v, loaded r w fl a d b f acc c k J⟩
      ⟨some (if posJob (decodeNat a, decodeNat d, decodeNat b) then .loop else .no), v', T⟩ ∧
      (posJob (decodeNat a, decodeNat d, decodeNat b) = true →
        T = st r w [] fl [] (jobStep acc (decodeNat a, decodeNat d, decodeNat b))
          (c + inc acc (decodeNat a, decodeNat d, decodeNat b) f) k J) := by
  let S := loaded r w fl a d b f acc c k J
  let time := acc.1 + decodeNat a
  have ha := decoded_length a
  have hd := decoded_length d
  have hb := decoded_length b
  have ht := encodeNat_add_length acc.1 (decodeNat a)
  have hc := encodeNat_add_length acc.2 (decodeNat b)
  simp only [BinaryNatEncoding.length_encodeNat] at ha hd hb ht hc
  obtain ⟨v₁, h₁⟩ := norm_run .process a v S (by simp [S, loaded, normSource])
  let S₁ := update (update S K.processRev []) K.operand (encodeNat (decodeNat a) ++ S .operand)
  have hS₁ : S₁ .operand = encodeNat (decodeNat a) := by simp [S₁, S, loaded, st]
  have h₂ := ifNonempty_run (l := .pos .process) (a := posNext .process) (b := .no)
    (k := .operand) rfl v₁ S₁
  rw [hS₁] at h₂
  by_cases ha0 : decodeNat a = 0
  · have hp : posJob (decodeNat a, decodeNat d, decodeNat b) = false := by
      simp [posJob_eq, ha0]
    rw [hp]
    simp only [ha0, encodeNat_zero', ↓reduceIte, Bool.false_eq_true] at h₂ ⊢
    refine ⟨_, S₁, (h₁.trans (h₂.le le_rfl)).mono (by omega), fun h => absurd h (by simp)⟩
  have hne := encodeNat_ne_nil ha0
  simp only [hne, ↓reduceIte, posNext] at h₂
  obtain ⟨v₂, h₃⟩ := start_add_run false acc.1 (decodeNat a) _ S₁
    (by simp [S₁, S, loaded, st, addTarget])
    hS₁ (by simp [S₁, S, loaded, st])
  let S₂ := update (update (update S₁ (addTarget false) []) K.operand []) K.sum
    (encodeNat time).reverse
  have h₄ := splitBits_run (M := prog) (s := K.sum) (a := K.elapsed) (b := K.elapsedCopy)
    (self := Lab.store false) (next := .norm .due) rfl (by decide) (by decide) (by decide) v₂ S₂
  let S₃ := update (update (update S₂ K.sum []) K.elapsed ((S₂ .sum).reverse ++ S₂ .elapsed))
    K.elapsedCopy ((S₂ .sum).reverse ++ S₂ .elapsedCopy)
  obtain ⟨v₄, h₅⟩ := norm_run .due d false S₃
    (by simp [S₃, S₂, S₁, S, loaded, normSource, addTarget])
  let S₄ := update (update S₃ K.dueRev []) K.operand (encodeNat (decodeNat d) ++ S₃ .operand)
  have hS₄ : S₄ .operand = encodeNat (decodeNat d) := by
    simp [S₄, S₃, S₂, S₁, S, loaded, st, addTarget]
  have h₆ := ifNonempty_run (l := .pos .due) (a := posNext .due) (b := .no)
    (k := .operand) rfl v₄ S₄
  rw [hS₄] at h₆
  have hrun₁ := h₁.trans (h₂.le le_rfl) |>.trans h₃ |>.trans (h₄.le le_rfl) |>.trans h₅
  by_cases hd0 : decodeNat d = 0
  · have hp : posJob (decodeNat a, decodeNat d, decodeNat b) = false := by
      simp [posJob_eq, hd0]
    rw [hp]
    simp only [hd0, encodeNat_zero', ↓reduceIte, Bool.false_eq_true] at h₆ ⊢
    refine ⟨_, S₄, (hrun₁.trans (h₆.le le_rfl)).mono ?_, fun h => absurd h (by simp)⟩
    simp [S₂, S₁, S, loaded, st, time]
    omega
  have hne' := encodeNat_ne_nil hd0
  simp only [hne', ↓reduceIte, posNext] at h₆
  have h₇ := start_cmp_run false time (decodeNat d) (encodeNat (decodeNat d)).head?.isSome S₄
    (by simp [cmpLeft, S₄, S₃, S₂, S₁, S, loaded, st, addTarget])
    (by simp [cmpRight, S₄, S₃, S₂, S₁, S, loaded, st, addTarget])
  let S₅ := update (update S₄ (cmpLeft false) []) (cmpRight false) []
  have hrun := hrun₁.trans (h₆.le le_rfl) |>.trans h₇
  by_cases hlate : decodeNat d < time
  · -- tardy: add the weight
    rw [decide_eq_true hlate] at hrun
    obtain ⟨v₆, h₈⟩ := moveBits_run (M := prog) (self := Lab.reverseWeight)
      (a := K.payload) (b := K.tmp) (next := .norm .weight) rfl (by decide) true S₅
    let S₆ := update (update S₅ K.payload []) K.tmp ((S₅ .payload).reverse ++ S₅ .tmp)
    obtain ⟨v₇, h₉⟩ := norm_run .weight b v₆ S₆
      (by simp [S₆, S₅, S₄, S₃, S₂, S₁, S, loaded, st, cmpLeft, cmpRight, addTarget, normSource])
    let S₇ := update (update S₆ K.tmp []) K.operand (encodeNat (decodeNat b) ++ S₆ .operand)
    have hS₇ : S₇ .operand = encodeNat (decodeNat b) := by
      simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, S, loaded, st, cmpLeft, cmpRight, addTarget]
    have h₁₀ := ifNonempty_run (l := .pos .weight) (a := posNext .weight) (b := .no)
      (k := .operand) rfl v₇ S₇
    rw [hS₇] at h₁₀
    have hrun₂ := hrun.trans (h₈.le le_rfl) |>.trans h₉
    by_cases hb0 : decodeNat b = 0
    · have hp : posJob (decodeNat a, decodeNat d, decodeNat b) = false := by
        simp [posJob_eq, hb0]
      rw [hp]
      simp only [hb0, encodeNat_zero', ↓reduceIte, Bool.false_eq_true] at h₁₀ ⊢
      refine ⟨_, S₇, (hrun₂.trans (h₁₀.le le_rfl)).mono ?_, fun h => absurd h (by simp)⟩
      simp [S₅, S₄, S₃, S₂, S₁, S, loaded, st, time, cmpLeft, cmpRight, addTarget]
      omega
    have hne'' := encodeNat_ne_nil hb0
    simp only [hne'', ↓reduceIte, posNext] at h₁₀
    have hp : posJob (decodeNat a, decodeNat d, decodeNat b) = true := by
      simp [posJob_eq, Nat.pos_of_ne_zero ha0, Nat.pos_of_ne_zero hd0, Nat.pos_of_ne_zero hb0]
    obtain ⟨v₈, h₁₁⟩ := start_add_run true acc.2 (decodeNat b) _ S₇
      (by simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, S, loaded, st, cmpLeft, cmpRight, addTarget])
      hS₇
      (by simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, S, loaded, st, cmpLeft, cmpRight, addTarget])
    let S₈ := update (update (update S₇ (addTarget true) []) K.operand []) K.sum
      (encodeNat (acc.2 + decodeNat b)).reverse
    obtain ⟨v₉, h₁₂⟩ := moveBits_run (M := prog) (self := Lab.store true)
      (a := K.sum) (b := K.cost) (next := .dropFlag) rfl (by decide) v₈ S₈
    let S₉ := update (update S₈ K.sum []) K.cost ((S₈ .sum).reverse ++ S₈ .cost)
    have h₁₃ : Run prog 1 ⟨some .dropFlag, v₉, S₉⟩ ⟨some .loop, v₉, update S₉ .curFlag []⟩ := by
      apply Run.single
      simp [prog, TM2.stepAux, S₉, S₈, S₇, S₆, S₅, S₄, S₃, S₂, S₁, S, loaded, addTarget,
        cmpLeft, cmpRight]
    have he : update S₉ .curFlag [] =
        st r w [] fl [] (jobStep acc (decodeNat a, decodeNat d, decodeNat b))
          (c + inc acc (decodeNat a, decodeNat d, decodeNat b) f) k J := by
      funext j
      cases j <;> simp [S₉, S₈, S₇, S₆, S₅, S₄, S₃, S₂, S₁, S, loaded, st, cmpLeft, cmpRight,
        addTarget, jobStep, inc, time, show decodeNat d < acc.1 + decodeNat a from hlate, pack]
    rw [hp]
    refine ⟨v₉, _, ?_, fun _ => he⟩
    simp only [↓reduceIte]
    refine (hrun₂.trans (h₁₀.le le_rfl) |>.trans h₁₁ |>.trans (h₁₂.le le_rfl) |>.trans
      (h₁₃.le le_rfl)).mono ?_
    simp [S₈, S₅, S₄, S₃, S₂, S₁, S, loaded, st, cmpLeft, cmpRight, addTarget, time]
    omega
  · -- on time: check the weight, discard it, count a flagged job
    rw [decide_eq_false hlate] at hrun
    have h₈ := ifNonempty_run (l := .onTime) (a := .discardWeight) (b := .no)
      (k := .payload) rfl false S₅
    have hS₅ : S₅ .payload = b := by
      simp [S₅, S₄, S₃, S₂, S₁, S, loaded, cmpLeft, cmpRight, addTarget]
    rw [hS₅] at h₈
    by_cases hb0 : b = []
    · have hp : posJob (decodeNat a, decodeNat d, decodeNat b) = false := by
        simp [posJob_eq, hb0, show decodeNat [] = 0 from rfl]
      rw [hp]
      simp only [hb0, ↓reduceIte] at h₈
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨_, S₅, (hrun.trans (h₈.le le_rfl)).mono ?_, fun h => absurd h (by simp)⟩
      simp [S₂, S₁, S, loaded, st, time]
      omega
    simp only [hb0, ↓reduceIte] at h₈
    have hbpos : 0 < decodeNat b := (decodeNat_pos_iff b).mpr hb0
    have hp : posJob (decodeNat a, decodeNat d, decodeNat b) = true := by
      simp [posJob_eq, Nat.pos_of_ne_zero ha0, Nat.pos_of_ne_zero hd0, hbpos]
    have h₉ := clean_run (M := prog) (ks := [K.payload]) (self := Lab.discardWeight)
      (next := .countFlag2) rfl (by decide) b.length b.head?.isSome S₅ (by
        intro j hj
        have hj' : j = .payload := by simpa using hj
        subst j
        simp [hS₅])
    let S₆ : K → List Bool := fun j => if j ∈ [K.payload] then [] else S₅ j
    have hcur : S₆ .curFlag = [f] := by
      simp [S₆, S₅, S₄, S₃, S₂, S₁, S, loaded, cmpLeft, cmpRight, addTarget]
    let S₇ := update S₆ .curFlag []
    have h₁₀ : Run prog 1 ⟨some .countFlag2, Flag.tag false, S₆⟩
        ⟨some (if f then .inc else .loop), f, S₇⟩ := by
      apply Run.single
      cases f <;> simp [prog, TM2.stepAux, hcur, S₇]
    have hS₇ : S₇ =
        st r w [] fl [] (jobStep acc (decodeNat a, decodeNat d, decodeNat b)) c k J := by
      funext j
      cases j <;> simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, S, loaded, st, cmpLeft, cmpRight,
        addTarget, jobStep, time, show ¬ decodeNat d < acc.1 + decodeNat a from hlate, pack]
    have hrun₂ := hrun.trans (h₈.le le_rfl) |>.trans h₉ |>.trans (h₁₀.le le_rfl)
    rw [hp]
    simp only [↓reduceIte]
    cases f with
    | false =>
      have hi : inc acc (decodeNat a, decodeNat d, decodeNat b) false = 0 := by simp [inc]
      refine ⟨false, S₇, hrun₂.mono ?_, fun _ => by rw [hi, Nat.add_zero, hS₇]⟩
      simp [S₂, S₁, S, loaded, st, time]
      omega
    | true =>
      have hi : inc acc (decodeNat a, decodeNat d, decodeNat b) true = 1 := by
        have hn : ¬ decodeNat d < acc.1 + decodeNat a := hlate
        simp [inc, hn]
      obtain ⟨v₁₁, h₁₁⟩ := inc_run (M := prog) (a := K.count) (t := K.decTmp) (self := .inc)
        (restore := .incRestore) (next := .loop) rfl rfl (by decide)
        (encodeNat c).length c 0 true S₇ le_rfl (by rw [hS₇]; rfl) (by rw [hS₇]; rfl)
      have he : update (update S₇ K.decTmp []) K.count (encodeNat (2 ^ 0 * (c + 1))) =
          st r w [] fl [] (jobStep acc (decodeNat a, decodeNat d, decodeNat b))
            (c + inc acc (decodeNat a, decodeNat d, decodeNat b) true) k J := by
        rw [hi, hS₇, pow_zero, Nat.one_mul]
        funext j
        cases j <;> simp [st]
      rw [he] at h₁₁
      refine ⟨v₁₁, _, (hrun₂.trans h₁₁).mono ?_, fun _ => rfl⟩
      simp [S₂, S₁, S, loaded, st, time]
      omega

end Job

section Loop

open MetaMathlibExt MetaMathlibExt.BitstringEncoding
open Turing Function TM2Program Cslib.Complexity
open Computability Cslib.Complexity.Karp Cslib.Complexity.FramedCNF

/-- Stacks right before the selected job's record is split into its fields. -/
private def pre (r w fl p : List Bool) (f : Bool) (acc : ℕ × ℕ) (c k J : ℕ) : K → List Bool :=
  update (update (st r w [] fl [] acc c k J) .payload p) .curFlag [f]

private theorem read_process_run (p r w fl : List Bool) (f : Bool) (acc : ℕ × ℕ) (c k J : ℕ)
    (v : Bool) :
    ∃ v' T, RunLe prog (45 * (p.length + (encodeNat acc.1).length +
      (encodeNat acc.2).length + (encodeNat c).length + 1))
      ⟨some .readProcess, v, pre r w fl p f acc c k J⟩
      ⟨some (if ((decodeJob p).map posJob).getD false then .loop else .no), v', T⟩ ∧
        ∀ j, decodeJob p = some j → posJob j = true →
          T = st r w [] fl [] (jobStep acc j) (c + inc acc j f) k J := by
  let S := pre r w fl p f acc c k J
  cases hp : undelimit p with
  | none =>
    obtain ⟨v', T, h, _⟩ := readFrame_bad (M := prog) (self := Lab.readProcess)
      (next := .readDue) (bad := .no) (a := K.payload) (b := K.processRev)
      rfl (by decide) p v S (by simp [S, pre]) hp
    refine ⟨v', T, ?_, ?_⟩
    · simpa [decodeJob, hp] using h.mono (by omega :
        p.length + 1 ≤ 45 * (p.length + (encodeNat acc.1).length +
          (encodeNat acc.2).length + (encodeNat c).length + 1))
    · simp [decodeJob, hp]
  | some pair =>
    obtain ⟨a, q⟩ := pair
    have hlin := (Cslib.CookLevin.undelimit_eq_some_iff p a q).1 hp
    let S₁ := update (update S K.payload q) K.processRev (a.reverse ++ S .processRev)
    have he₁ := readFrame_run (M := prog) (self := Lab.readProcess) (next := .readDue)
      (bad := .no) (a := K.payload) (b := K.processRev) rfl (by decide)
      v S a q (by simp [S, pre, hlin])
    have hlen₁ : p.length = 2 * a.length + 1 + q.length := by simp [hlin]
    cases hq : undelimit q with
    | none =>
      obtain ⟨v', T, h₂, _⟩ := readFrame_bad (M := prog) (self := Lab.readDue)
        (next := .norm .process) (bad := .no) (a := K.payload) (b := K.dueRev)
        rfl (by decide) q false S₁ (by simp [S₁]) hq
      refine ⟨v', T, ?_, ?_⟩
      · simpa [decodeJob, hp, hq] using (he₁.le le_rfl |>.trans h₂).mono (by omega :
          a.length + 1 + (q.length + 1) ≤
            45 * (p.length + (encodeNat acc.1).length + (encodeNat acc.2).length +
              (encodeNat c).length + 1))
      · simp [decodeJob, hp, hq]
    | some pair =>
      obtain ⟨d, b⟩ := pair
      have hqeq := (Cslib.CookLevin.undelimit_eq_some_iff q d b).1 hq
      have ht : decodeJob p = some (decodeNat a, decodeNat d, decodeNat b) := by
        simp [decodeJob, hp, hq]
      have hlen₂ : q.length = 2 * d.length + 1 + b.length := by simp [hqeq]
      have hr₂ := readFrame_run (M := prog) (self := Lab.readDue) (next := .norm .process)
        (bad := .no) (a := K.payload) (b := K.dueRev) rfl (by decide)
        false S₁ d b (by simp [S₁, hqeq])
      have he : update (update S₁ K.payload b) K.dueRev (d.reverse ++ S₁ .dueRev) =
          loaded r w fl a d b f acc c k J := by
        funext j
        cases j <;> simp [S₁, S, pre, loaded, st]
      rw [he] at hr₂
      obtain ⟨v', T, hr₃, hT⟩ := loaded_run r w fl a d b f acc c k J false
      simp only [ht, Option.map_some, Option.getD_some, Option.some.injEq]
      refine ⟨v', T, (he₁.le le_rfl |>.trans (hr₂.le le_rfl) |>.trans hr₃).mono (by omega),
        fun j hj hpos => ?_⟩
      subst hj
      exact hT hpos

private theorem read_outer_job (skip : Bool) (p r w : List Bool) (sk : List (List Bool))
    (fl sf : List Bool)
    (acc : ℕ × ℕ) (c k J : ℕ) (v : Bool) :
    ∃ v', Run prog (2 * p.length + 3)
      ⟨some .loop, v, st (delimit p ++ r) (skip :: w) sk fl sf acc c k J⟩
      ⟨some (if skip then .skip else .takeFlag), v',
        update (st r w sk fl sf acc c k J) .payload p⟩ := by
  let S := st (delimit p ++ r) w sk fl sf acc c k J
  have h₁ : Run prog 1 ⟨some .loop, v, st (delimit p ++ r) (skip :: w) sk fl sf acc c k J⟩
      ⟨some (.read skip), skip, S⟩ := by
    apply Run.single
    have he : update (st (delimit p ++ r) (skip :: w) sk fl sf acc c k J) K.witness w = S := by
      funext j
      cases j <;> rfl
    simpa only [prog, TM2.stepAux, st, List.head?_cons, List.tail_cons, Option.isSome_some,
      id_eq, Bool.cond_true, Option.getD_some] using
        congrArg (TM2.Cfg.mk (some (Lab.read skip)) skip) he
  have h₂ := readFrame_run (M := prog) (self := Lab.read skip) (next := .restorePayload skip)
    (bad := .no) (a := K.jobs) (b := K.tmp) rfl (by decide) skip S p r rfl
  let S₂ := update (update S K.jobs r) K.tmp (p.reverse ++ S .tmp)
  obtain ⟨v', h₃⟩ := moveBits_run (M := prog) (self := Lab.restorePayload skip) (a := K.tmp)
    (b := K.payload) (next := if skip then .skip else .takeFlag)
    rfl (by decide) false S₂
  have he : update (update S₂ K.tmp []) K.payload ((S₂ .tmp).reverse ++ S₂ .payload) =
      update (st r w sk fl sf acc c k J) K.payload p := by
    funext j
    cases j <;> simp [S₂, S, st]
  rw [he] at h₃
  exact ⟨v', (h₁.trans h₂ |>.trans h₃).of_eq (by simp [S₂, S, st]; omega)⟩

private theorem skip_run (p r w : List Bool) (sk : List (List Bool)) (fl sf : List Bool)
    (acc : ℕ × ℕ) (c k J : ℕ) (v : Bool) :
    Run prog (p.length + 2)
      ⟨some .skip, v, update (st r w sk fl sf acc c k J) .payload p⟩
      ⟨some .loop, fl.headD false, st r w (p :: sk) fl.tail (fl.headD false :: sf) acc c k J⟩ := by
  let S₁ := update (st r w sk fl sf acc c k J) .payload p
  have h₂ := writeBits_run (M := prog) (a := K.payload) (b := K.skipped)
    (self := Lab.skip) (next := .skipFlag) (chunk := liftBit) (suffix := [false])
    rfl (by decide) v S₁
  have hp : pack (p :: sk).reverse = pack sk.reverse ++ delimit p := by
    simp [List.reverse_cons, pack_append, pack_cons, show pack [] = [] from rfl]
  have he : update (update S₁ K.payload []) K.skipped
      (((S₁ .payload).flatMap liftBit ++ [false]).reverse ++ S₁ .skipped) =
        update (st r w (p :: sk) fl sf acc c k J) .payload [] := by
    funext i
    cases i <;> try rfl
    case skipped =>
      change (((S₁ .payload).flatMap liftBit ++ [false]).reverse ++ S₁ .skipped) =
        (pack (p :: sk).reverse).reverse
      rw [hp, delimit_eq, liftBits, List.reverse_append]
      simp [S₁, st]
  rw [he] at h₂
  have h₃ : Run prog 1
      ⟨some .skipFlag, false, update (st r w (p :: sk) fl sf acc c k J) .payload []⟩
      ⟨some .loop, fl.headD false, st r w (p :: sk) fl.tail (fl.headD false :: sf) acc c k J⟩ := by
    apply Run.single
    have hu : update (st r w (p :: sk) fl sf acc c k J) .payload [] =
        st r w (p :: sk) fl sf acc c k J := by
      funext i; cases i <;> rfl
    rw [hu]
    cases fl with
    | nil =>
      simp only [prog, TM2.stepAux, st, List.head?_nil, Option.getD_none, List.tail_nil,
        List.headD_nil]
      congr 1
      funext i; cases i <;> simp [st]
    | cons b fl =>
      simp only [prog, TM2.stepAux, st, List.head?_cons, Option.getD_some, List.tail_cons,
        List.headD_cons, id_eq]
      congr 1
      funext i; cases i <;> simp [st]
  exact (h₂.trans h₃).of_eq (by simp [S₁])

private theorem take_run (p r w : List Bool) (sk : List (List Bool)) (fl sf : List Bool)
    (acc : ℕ × ℕ) (c k J : ℕ) (v : Bool) :
    ∃ v', Run prog ((pack sk.reverse).length + sf.length + 3)
      ⟨some .takeFlag, v, update (st r w sk fl sf acc c k J) .payload p⟩
      ⟨some .readProcess, v',
        pre (pack sk.reverse ++ r) w (sf.reverse ++ fl.tail) p (fl.headD false) acc c k J⟩ := by
  let S₀ := update (st r w sk fl sf acc c k J) .payload p
  let S₁ := update (update S₀ .flags fl.tail) .curFlag [fl.headD false]
  have h₁ : Run prog 1 ⟨some .takeFlag, v, S₀⟩ ⟨some .restoreSkipped, fl.headD false, S₁⟩ := by
    apply Run.single
    cases fl with
    | nil =>
      simp [prog, TM2.stepAux, S₀, S₁, st]
    | cons b fl =>
      simp [prog, TM2.stepAux, S₀, S₁, st]
  obtain ⟨v₂, h₂⟩ := moveBits_run (M := prog) (self := Lab.restoreSkipped) (a := K.skipped)
    (b := K.jobs) (next := .restoreFlags) rfl (by decide) (fl.headD false) S₁
  let S₂ := update (update S₁ K.skipped []) K.jobs ((S₁ .skipped).reverse ++ S₁ .jobs)
  obtain ⟨v₃, h₃⟩ := moveBits_run (M := prog) (self := Lab.restoreFlags) (a := K.skipFlags)
    (b := K.flags) (next := .readProcess) rfl (by decide) v₂ S₂
  have he : update (update S₂ K.skipFlags []) K.flags ((S₂ .skipFlags).reverse ++ S₂ .flags) =
      pre (pack sk.reverse ++ r) w (sf.reverse ++ fl.tail) p (fl.headD false) acc c k J := by
    funext i
    cases i <;> simp [S₂, S₁, S₀, st, pre, show pack [] = [] from rfl]
  rw [he] at h₃
  exact ⟨v₃, (h₁.trans h₂ |>.trans h₃).of_eq (by simp [S₂, S₁, S₀, st]; omega)⟩

private theorem job_size {p : List Bool} {j : Job} (hj : decodeJob p = some j) (acc : ℕ × ℕ) :
    (encodeNat (jobStep acc j).1).length + (encodeNat (jobStep acc j).2).length ≤
      (encodeNat acc.1).length + (encodeNat acc.2).length + p.length + 4 := by
  obtain ⟨⟨a, q⟩, ha, hq⟩ := Option.bind_eq_some_iff.mp hj
  obtain ⟨⟨d, b⟩, hd, rfl⟩ := Option.map_eq_some_iff.mp hq
  have he₁ := (Cslib.CookLevin.undelimit_eq_some_iff p a q).1 ha
  have he₂ := (Cslib.CookLevin.undelimit_eq_some_iff q d b).1 hd
  have hlen : a.length + b.length ≤ p.length := by
    simp [he₁, he₂]
    omega
  have h₁ := decoded_length a
  have h₂ := decoded_length b
  have ht := encodeNat_add_length acc.1 (decodeNat a)
  have hw := encodeNat_add_length acc.2 (decodeNat b)
  dsimp only [jobStep]
  split <;> simp_all only [Nat.add_zero] <;> omega

private theorem inc_size (acc : ℕ × ℕ) (j : Job) (f : Bool) (c : ℕ) :
    (encodeNat (c + inc acc j f)).length ≤ (encodeNat c).length + 2 := by
  have h := encodeNat_add_length c (inc acc j f)
  have h1 : (encodeNat (inc acc j f)).length ≤ 1 := by
    unfold inc; split <;> decide
  simp only [BinaryNatEncoding.length_encodeNat] at h h1 ⊢
  omega

private theorem pack_eq_nil (ps : List (List Bool)) : pack ps = [] ↔ ps = [] := by
  constructor
  · intro h
    cases ps with
    | nil => rfl
    | cons p ps =>
      have := congrArg List.length h
      simp [pack_cons] at this
  · rintro rfl; rfl

private theorem skipped_isEmpty (s : List (List Bool)) :
    (pack s.reverse).reverse.isEmpty = s.isEmpty := by
  cases h : s with
  | nil => rfl
  | cons p ps =>
    have : pack (p :: ps).reverse ≠ [] := by
      rw [Ne, pack_eq_nil]; simp
    simpa [List.isEmpty_iff] using this

end Loop

section VLoop

open MetaMathlibExt MetaMathlibExt.BitstringEncoding
open Turing Function TM2Program Cslib.Complexity
open Computability Cslib.Complexity.Karp Cslib.Complexity.FramedCNF

private def budget (r : List Bool) (sk : List (List Bool)) (acc : ℕ × ℕ) (c k J : ℕ) : ℕ :=
  6 * (r.length + (pack sk.reverse).length) + (encodeNat acc.1).length +
    (encodeNat acc.2).length + (encodeNat k).length + (encodeNat c).length + (encodeNat J).length

private theorem final_run (acc : ℕ × ℕ) (c k J : ℕ) (w fl sf : List Bool) (v : Bool) :
    ∃ v' T, RunLe prog ((encodeNat acc.2).length + (encodeNat k).length +
        (encodeNat c).length + (encodeNat J).length + 8)
      ⟨some (.compareStart true), v, st [] w [] fl sf acc c k J⟩
      ⟨some (yesNo (decide (acc.2 ≤ k) && decide (J ≤ c))), v', T⟩ := by
  let S := st [] w [] fl sf acc c k J
  have h₁ := start_cmp_run true acc.2 k v S rfl rfl
  by_cases hgt : k < acc.2
  · rw [decide_eq_true hgt] at h₁
    have hl : yesNo (decide (acc.2 ≤ k) && decide (J ≤ c)) = .no := by
      simp [yesNo, Nat.not_le.mpr hgt]
    rw [hl]
    exact ⟨_, _, h₁.mono (by omega)⟩
  · rw [decide_eq_false hgt] at h₁
    simp only [cmpNext, ↓reduceIte, Bool.false_eq_true] at h₁
    let S₁ := update (update S (cmpLeft true) []) (cmpRight true) []
    have h₂ : Run prog 1 ⟨some .compareJ, false, S₁⟩ ⟨some .compareJRun, false, S₁⟩ :=
      Run.single rfl
    have h₃ := compare_run (M := prog) (self := Lab.compareJRun) (next := .compareJDone)
      rfl (by decide) (by decide) (by decide) J c S₁ (by simp [S₁, S, st, cmpLeft, cmpRight])
      (by simp [S₁, S, st, cmpLeft, cmpRight])
    let S₂ := update (update S₁ K.jBound []) K.count []
    have h₄ : Run prog 1 ⟨some .compareJDone, decide (c < J), S₂⟩
        ⟨some (yesNo (!decide (c < J))), decide (c < J), S₂⟩ := Run.single rfl
    have hl : yesNo (!decide (c < J)) = yesNo (decide (acc.2 ≤ k) && decide (J ≤ c)) := by
      simp only [Nat.le_of_not_gt hgt, decide_true, Bool.true_and]
      congr 1
      by_cases h : c < J
      · simp [h, Nat.not_le.mpr h]
      · simp [h, Nat.le_of_not_gt h]
    rw [hl] at h₄
    exact ⟨_, _, (h₁.trans (h₂.le le_rfl) |>.trans h₃ |>.trans (h₄.le le_rfl)).mono (by omega)⟩

private theorem verify_loop {B : ℕ} (k J : ℕ) (w : List Bool) :
    ∀ (ps : List (List Bool)) (sk : List (List Bool)) (fl sf : List Bool) (acc : ℕ × ℕ) (c : ℕ)
      (v : Bool), fl.length = ps.length → sf.length = sk.length →
      budget (pack ps) sk acc c k J ≤ B →
      ∃ v' T, RunLe prog (60 * (B + 1) * (w.length + 1))
        ⟨some .loop, v, st (pack ps) w sk fl sf acc c k J⟩
        ⟨some (yesNo (loop w ps fl sk sf acc c k J)), v', T⟩ := by
  induction w with
  | nil =>
    intro ps sk fl sf acc c v hfl hsf hB
    have hw : ((st (pack ps) [] sk fl sf acc c k J) .witness).head?.isSome = false := rfl
    by_cases hps : ps = []
    · subst hps
      by_cases hsk : sk = []
      · subst hsk
        have hfl' : fl = [] := List.eq_nil_of_length_eq_zero (by simpa using hfl)
        have hsf' : sf = [] := List.eq_nil_of_length_eq_zero (by simpa using hsf)
        subst hfl' hsf'
        have h₁ : Run prog 1 ⟨some .loop, v, st (pack []) [] [] [] [] acc c k J⟩
            ⟨some (.compareStart true), false, st [] [] [] [] [] acc c k J⟩ := by
          apply Run.single
          rfl
        obtain ⟨v', T, h₂⟩ := final_run acc c k J [] [] [] false
        refine ⟨v', T, ?_⟩
        have hl : loop [] [] [] [] [] acc c k J = (decide (acc.2 ≤ k) && decide (J ≤ c)) := by
          simp [loop]
        rw [hl]
        refine (h₁.le le_rfl |>.trans h₂).mono ?_
        simp only [budget] at hB
        simp only [List.length_nil, zero_add, mul_one]
        omega
      · have hne : (pack sk.reverse).reverse ≠ [] := by
          intro h
          have := skipped_isEmpty sk
          rw [h] at this
          cases sk with
          | nil => exact hsk rfl
          | cons _ _ => simp at this
        obtain ⟨b, bs, hbs⟩ := List.exists_cons_of_ne_nil hne
        have h₁ : Run prog 1 ⟨some .loop, v, st (pack []) [] sk fl sf acc c k J⟩
            ⟨some .no, true, st (pack []) [] sk fl sf acc c k J⟩ := by
          apply Run.single
          simp [prog, TM2.stepAux, st, hbs, show pack [] = [] from rfl]
        have hl : loop [] [] fl sk sf acc c k J = false := by
          cases sk with
          | nil => exact absurd rfl hsk
          | cons _ _ => simp [loop]
        refine ⟨true, st (pack []) [] sk fl sf acc c k J, ?_⟩
        rw [hl]
        exact h₁.le (by simp only [List.length_nil, zero_add, mul_one]; omega)
    · have hne : pack ps ≠ [] := by rwa [Ne, pack_eq_nil]
      obtain ⟨b, bs, hbs⟩ := List.exists_cons_of_ne_nil hne
      have h₁ : Run prog 1 ⟨some .loop, v, st (pack ps) [] sk fl sf acc c k J⟩
          ⟨some .no, true, st (pack ps) [] sk fl sf acc c k J⟩ := by
        apply Run.single
        simp [prog, TM2.stepAux, st, hbs]
      have hl : loop [] ps fl sk sf acc c k J = false := by
        cases ps with
        | nil => exact absurd rfl hps
        | cons _ _ => simp [loop]
      refine ⟨true, st (pack ps) [] sk fl sf acc c k J, ?_⟩
      rw [hl]
      exact h₁.le (by simp only [List.length_nil, zero_add, mul_one]; omega)
  | cons sel w ih =>
    intro ps sk fl sf acc c v hfl hsf hB
    cases ps with
    | nil =>
      let S := st (pack []) w sk fl sf acc c k J
      have h₁ : Run prog 1 ⟨some .loop, v, st (pack []) (sel :: w) sk fl sf acc c k J⟩
          ⟨some (.read sel), sel, S⟩ := by
        apply Run.single
        have he : update (st (pack []) (sel :: w) sk fl sf acc c k J) K.witness w = S := by
          funext j
          cases j <;> rfl
        simpa [prog, TM2.stepAux, st] using he
      obtain ⟨v', T, h₂, _⟩ := readFrame_bad (M := prog) (self := Lab.read sel)
        (next := .restorePayload sel) (bad := .no) (a := K.jobs) (b := K.tmp)
        rfl (by decide) [] sel S rfl rfl
      refine ⟨v', T, ?_⟩
      have hl : loop (sel :: w) [] fl sk sf acc c k J = false := by simp [loop]
      rw [hl]
      refine (h₁.le le_rfl |>.trans h₂).mono ?_
      simp only [List.length_cons, List.length_nil, Nat.mul_succ]
      omega
    | cons p ps =>
      have hjobs : pack (p :: ps) = delimit p ++ pack ps := rfl
      rw [hjobs]
      obtain ⟨v₁, h₁⟩ := read_outer_job sel p (pack ps) w sk fl sf acc c k J v
      have hB' : 6 * (2 * p.length + 1 + (pack ps).length + (pack sk.reverse).length) +
          (encodeNat acc.1).length + (encodeNat acc.2).length + (encodeNat k).length +
          (encodeNat c).length + (encodeNat J).length ≤ B := by
        simpa only [budget, hjobs, List.length_append, length_delimit] using hB
      have hsk_le : sk.length ≤ (pack sk.reverse).length := by
        have := length_le_length_flatten_delimit sk.reverse
        simpa [pack] using this
      cases sel with
      | true =>
        have h₂ := skip_run p (pack ps) w sk fl sf acc c k J v₁
        have hb' : budget (pack ps) (p :: sk) acc c k J ≤ B := by
          have hp : pack (p :: sk).reverse = pack sk.reverse ++ delimit p := by
            simp [List.reverse_cons, pack_append, pack_cons, show pack [] = [] from rfl]
          simp only [budget, hp, List.length_append, length_delimit]
          omega
        obtain ⟨v₃, T, h₃⟩ := ih ps (p :: sk) fl.tail (fl.headD false :: sf) acc c _
          (by simp [hfl]) (by simp [hsf]) hb'
        refine ⟨v₃, T, ?_⟩
        have hl : loop (true :: w) (p :: ps) fl sk sf acc c k J =
            loop w ps fl.tail (p :: sk) (fl.headD false :: sf) acc c k J := by simp [loop]
        rw [hl]
        refine ((h₁.trans h₂).le le_rfl |>.trans h₃).mono ?_
        simp only [List.length_cons, Nat.mul_succ]
        omega
      | false =>
        obtain ⟨v₂, h₂⟩ := take_run p (pack ps) w sk fl sf acc c k J v₁
        obtain ⟨v₃, T, h₃, hT⟩ := read_process_run p (pack sk.reverse ++ pack ps) w
          (sf.reverse ++ fl.tail) (fl.headD false) acc c k J v₂
        have hrun := (h₁.trans h₂).le le_rfl |>.trans h₃
        have hb : 2 * p.length + 3 + ((pack sk.reverse).length + sf.length + 3) +
            45 * (p.length + (encodeNat acc.1).length + (encodeNat acc.2).length +
              (encodeNat c).length + 1) ≤ 60 * (B + 1) := by
          omega
        cases hj : decodeJob p with
        | none =>
          simp only [hj, Option.map_none, Option.getD_none, Bool.false_eq_true, ↓reduceIte]
            at hrun
          have hl : loop (false :: w) (p :: ps) fl sk sf acc c k J = false := by
            simp [loop, hj]
          refine ⟨v₃, T, ?_⟩
          rw [hl]
          exact hrun.mono (by simp only [List.length_cons, Nat.mul_succ]; omega)
        | some j =>
          by_cases hpos : posJob j = true
          · simp only [hj, Option.map_some, Option.getD_some, hpos, ↓reduceIte] at hrun
            rw [hT j hj hpos] at hrun
            have hjs := job_size hj acc
            have hcs := inc_size acc j (fl.headD false) c
            have hb' : budget (pack (sk.reverse ++ ps)) [] (jobStep acc j)
                (c + inc acc j (fl.headD false)) k J ≤ B := by
              simp only [budget, pack_append, List.length_append, List.reverse_nil,
                show pack [] = [] from rfl, List.length_nil]
              omega
            obtain ⟨v₄, U, h₄⟩ := ih (sk.reverse ++ ps) [] (sf.reverse ++ fl.tail) []
              (jobStep acc j) (c + inc acc j (fl.headD false)) v₃
              (by simp [hfl, hsf]) rfl hb'
            refine ⟨v₄, U, ?_⟩
            have hl : loop (false :: w) (p :: ps) fl sk sf acc c k J =
                loop w (sk.reverse ++ ps) (sf.reverse ++ fl.tail) [] [] (jobStep acc j)
                  (c + inc acc j (fl.headD false)) k J := by
              simp [loop, hj, hpos]
            rw [hl]
            rw [pack_append] at h₄
            exact (hrun.trans h₄).mono (by simp only [List.length_cons, Nat.mul_succ]; omega)
          · have hf : posJob j = false := by simpa using hpos
            simp only [hj, Option.map_some, Option.getD_some, hf, Bool.false_eq_true,
              ↓reduceIte] at hrun
            have hl : loop (false :: w) (p :: ps) fl sk sf acc c k J = false := by
              simp [loop, hj, hf]
            refine ⟨v₃, T, ?_⟩
            rw [hl]
            exact hrun.mono (by simp only [List.length_cons, Nat.mul_succ]; omega)

end VLoop

section Phases

open MetaMathlibExt MetaMathlibExt.BitstringEncoding
open Turing Function TM2Program Cslib.Complexity
open Computability Cslib.Complexity.Karp Cslib.Complexity.FramedCNF

private theorem blocks_cons (p r : List Bool) :
    undelimitBlocks (delimit p ++ r) = (undelimitBlocks r).map (p :: ·) := by
  cases hr : undelimitBlocks r with
  | some ps =>
    have he : r = pack ps := Cslib.Complexity.PolynomialEncoding.blocks_decode_sound hr
    rw [he, ← pack_cons]
    exact undelimitBlocks_flatten_delimit (p :: ps)
  | none =>
    cases hp : undelimitBlocks (delimit p ++ r) with
    | none => rfl
    | some ps =>
      have he : delimit p ++ r = pack ps :=
        Cslib.Complexity.PolynomialEncoding.blocks_decode_sound hp
      cases ps with
      | nil => cases p <;> simp [delimit, pack] at he
      | cons q qs =>
        rw [pack_cons] at he
        have hh := congrArg undelimit he
        simp only [undelimit_delimit, Option.some.injEq, Prod.mk.injEq] at hh
        rw [hh.2] at hr
        rw [pack, undelimitBlocks_flatten_delimit qs] at hr
        contradiction

private theorem blocks_bad {r : List Bool} (hr : r ≠ []) (h : undelimit r = none) :
    undelimitBlocks r = none := by
  obtain ⟨b, bs, rfl⟩ := List.exists_cons_of_ne_nil hr
  unfold undelimitBlocks
  simp only [List.length_cons, undelimitBlocksAux, h, Option.bind_none]

/-- The stacks during the counting and marking phases. -/
private def stC (r bk fl sl wk sv w : List Bool) (k J : ℕ) : K → List Bool
  | .jobs => r
  | .back => bk
  | .flags => fl
  | .sList => sl
  | .walked => wk
  | .sVal => sv
  | .witness => w
  | .bound => encodeNat k
  | .jBound => encodeNat J
  | _ => []

private theorem stC_eq_st (r fl w : List Bool) (k J : ℕ) :
    stC r [] fl [] [] [] w k J = st r w [] fl [] (0, 0) 0 k J := by
  funext i
  cases i <;> rfl

private theorem count_run (sl w : List Bool) (k J : ℕ) : ∀ (n : ℕ) (r : List Bool)
    (done : List (List Bool)) (m : ℕ) (v : Bool), r.length ≤ n →
    ∃ v' T, RunLe prog (6 * r.length + (pack done).length + 2)
      ⟨some .count, v, stC r (pack done).reverse (List.replicate m false) sl [] [] w k J⟩
      ⟨some (if (undelimitBlocks r).isSome then .sLoop else .no), v', T⟩ ∧
      ∀ ps, undelimitBlocks r = some ps →
        T = stC (pack (done ++ ps)) [] (List.replicate (m + ps.length) false) sl [] [] w k J := by
  intro n
  induction n with
  | zero =>
    intro r done m v hr
    have hr' : r = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hr'
    let S := stC [] (pack done).reverse (List.replicate m false) sl [] [] w k J
    have h₁ := ifNonempty_run (l := .count) (a := .countRead) (b := .countDone) (k := .jobs)
      rfl v S
    simp only [S, stC, ↓reduceIte] at h₁
    obtain ⟨v₂, h₂⟩ := moveBits_run (M := prog) (self := Lab.countDone) (a := K.back)
      (b := K.jobs) (next := .sLoop) rfl (by decide) false S
    have he : update (update S K.back []) K.jobs ((S .back).reverse ++ S .jobs) =
        stC (pack (done ++ [])) [] (List.replicate (m + 0) false) sl [] [] w k J := by
      funext i
      cases i <;> simp [S, stC]
    rw [he] at h₂
    refine ⟨v₂, _, (h₁.trans h₂).le (by simp [S, stC]; omega), ?_⟩
    · intro ps hps
      have : ps = [] := by simpa [undelimitBlocks, undelimitBlocksAux] using hps.symm
      subst this
      rfl
  | succ n ih =>
    intro r done m v hr
    let S := stC r (pack done).reverse (List.replicate m false) sl [] [] w k J
    by_cases hr0 : r = []
    · subst hr0
      have h₁ := ifNonempty_run (l := .count) (a := .countRead) (b := .countDone) (k := .jobs)
        rfl v S
      simp only [S, stC, ↓reduceIte] at h₁
      obtain ⟨v₂, h₂⟩ := moveBits_run (M := prog) (self := Lab.countDone) (a := K.back)
        (b := K.jobs) (next := .sLoop) rfl (by decide) false S
      have he : update (update S K.back []) K.jobs ((S .back).reverse ++ S .jobs) =
          stC (pack (done ++ [])) [] (List.replicate (m + 0) false) sl [] [] w k J := by
        funext i
        cases i <;> simp [S, stC]
      rw [he] at h₂
      refine ⟨v₂, _, (h₁.trans h₂).le (by simp [S, stC]; omega), ?_⟩
      · intro ps hps
        have : ps = [] := by simpa [undelimitBlocks, undelimitBlocksAux] using hps.symm
        subst this
        rfl
    obtain ⟨b, bs, hbs⟩ := List.exists_cons_of_ne_nil hr0
    have h₁ : Run prog 1 ⟨some .count, v, S⟩ ⟨some .countRead, true, S⟩ := by
      have h := ifNonempty_run (l := .count) (a := .countRead) (b := .countDone) (k := .jobs)
        rfl v S
      simpa [S, stC, hbs] using h
    cases hu : undelimit r with
    | none =>
      obtain ⟨v', T, h₂, _⟩ := readFrame_bad (M := prog) (self := Lab.countRead)
        (next := .countPayload) (bad := .no) (a := K.jobs) (b := K.tmp)
        rfl (by decide) r true S rfl hu
      refine ⟨v', T, ?_, ?_⟩
      · simpa [blocks_bad hr0 hu] using (h₁.le le_rfl |>.trans h₂).mono (by omega)
      · simp [blocks_bad hr0 hu]
    | some pr =>
      obtain ⟨p, r'⟩ := pr
      have hre := (Cslib.CookLevin.undelimit_eq_some_iff r p r').1 hu
      have h₂ := readFrame_run (M := prog) (self := Lab.countRead) (next := .countPayload)
        (bad := .no) (a := K.jobs) (b := K.tmp) rfl (by decide) true S p r' (by simp [S, stC, hre])
      let S₂ := update (update S K.jobs r') K.tmp (p.reverse ++ S .tmp)
      obtain ⟨v₃, h₃⟩ := moveBits_run (M := prog) (self := Lab.countPayload) (a := K.tmp)
        (b := K.payload) (next := .countWrite) rfl (by decide) false S₂
      let S₃ := update (update S₂ K.tmp []) K.payload ((S₂ .tmp).reverse ++ S₂ .payload)
      have h₄ := writeBits_run (M := prog) (a := K.payload) (b := K.back)
        (self := Lab.countWrite) (next := .countFlag) (chunk := liftBit) (suffix := [false])
        rfl (by decide) v₃ S₃
      let S₄ := update (update S₃ K.payload []) K.back
        (((S₃ .payload).flatMap liftBit ++ [false]).reverse ++ S₃ .back)
      have h₅ : Run prog 1 ⟨some .countFlag, false, S₄⟩
          ⟨some .count, false,
            stC r' (pack (done ++ [p])).reverse (List.replicate (m + 1) false) sl [] [] w k J⟩ := by
        apply Run.single
        simp only [prog, TM2.stepAux]
        congr 1
        funext i
        cases i <;> simp [S₄, S₃, S₂, S, stC, pack_append, pack_cons, show pack [] = [] from rfl,
          delimit_eq, liftBits, List.replicate_succ]
      have hlen : r.length = 2 * p.length + 1 + r'.length := by simp [hre]
      obtain ⟨v₆, T, h₆, hT⟩ := ih r' (done ++ [p]) (m + 1) false (by omega)
      have hblk : undelimitBlocks r = (undelimitBlocks r').map (p :: ·) := by
        rw [hre, blocks_cons]
      refine ⟨v₆, T, ?_, ?_⟩
      · have hl : (undelimitBlocks r).isSome = (undelimitBlocks r').isSome := by
          rw [hblk]; cases undelimitBlocks r' <;> rfl
        rw [hl]
        refine ((h₁.trans h₂ |>.trans h₃ |>.trans h₄ |>.trans h₅).le le_rfl |>.trans h₆).mono ?_
        simp [S₃, S₂, S, stC, pack_append, pack_cons, show pack [] = [] from rfl]
        omega
      · intro ps hps
        rw [hblk] at hps
        obtain ⟨ps', hps', rfl⟩ := Option.map_eq_some_iff.mp hps
        rw [hT ps' hps']
        simp [Nat.add_assoc, Nat.add_comm 1]

end Phases

section Walk

open MetaMathlibExt MetaMathlibExt.BitstringEncoding
open Turing Function TM2Program Cslib.Complexity
open Computability Cslib.Complexity.Karp Cslib.Complexity.FramedCNF

private theorem walk_run (r sl w : List Bool) (k J L : ℕ) : ∀ (s : ℕ) (F W : List Bool) (v : Bool),
    (encodeNat s).length ≤ L →
    ∃ v' T, RunLe prog ((min s F.length + 1) * (2 * L + 8) + W.length + F.length + 2)
      ⟨some .walk, v, stC r [] F sl W (encodeNat s) w k J⟩
      ⟨some (if s < F.length then .sLoop else .no), v', T⟩ ∧
      (s < F.length → T = stC r [] (W.reverse ++ F.set s true) sl [] [] w k J) := by
  intro s
  induction s with
  | zero =>
    intro F W v hL
    cases F with
    | nil =>
      refine ⟨false, stC r [] [] sl W (encodeNat 0) w k J, (Run.single ?_).le (by omega),
        fun h => absurd h (by simp)⟩
      simp [prog, TM2.stepAux, stC, encodeNat_zero']
    | cons b F =>
      let S₁ := stC r [] (true :: F) sl W [] w k J
      have h₁ : Run prog 1 ⟨some .walk, v, stC r [] (b :: F) sl W (encodeNat 0) w k J⟩
          ⟨some .unwalk, true, S₁⟩ := by
        apply Run.single
        simp only [prog, TM2.stepAux, stC, encodeNat_zero']
        simp only [List.head?_nil, Option.isSome_none, id_eq, Bool.cond_false, List.head?_cons,
          Option.isSome_some, Bool.cond_true, List.tail_cons]
        congr 1
        funext i; cases i <;> simp [S₁, stC]
      obtain ⟨v₂, h₂⟩ := moveBits_run (M := prog) (self := Lab.unwalk) (a := K.walked)
        (b := K.flags) (next := .sLoop) rfl (by decide) true S₁
      have he : update (update S₁ K.walked []) K.flags ((S₁ .walked).reverse ++ S₁ .flags) =
          stC r [] (W.reverse ++ (b :: F).set 0 true) sl [] [] w k J := by
        funext i; cases i <;> simp [S₁, stC]
      rw [he] at h₂
      refine ⟨v₂, _, (h₁.trans h₂).le ?_, fun _ => rfl⟩
      simp [S₁, stC]
      omega
  | succ s ih =>
    intro F W v hL
    let S := stC r [] F sl W (encodeNat (s + 1)) w k J
    have hne := encodeNat_ne_nil (Nat.succ_ne_zero s)
    obtain ⟨e, es, hes⟩ := List.exists_cons_of_ne_nil hne
    have h₁ : Run prog 1 ⟨some .walk, v, S⟩ ⟨some .dec, true, S⟩ := by
      apply Run.single
      simp [prog, TM2.stepAux, S, stC, hes]
    obtain ⟨v₂, h₂⟩ := dec_run (M := prog) (a := K.sVal) (t := K.decTmp) (self := .dec)
      (restore := .decRestore) (next := .walkStep) rfl rfl (by decide) L (s + 1) 0 true S hL
      (Nat.succ_pos s) rfl rfl
    have he₂ : update (update S K.decTmp []) K.sVal (encodeNat (2 ^ 0 * (s + 1) - 1)) =
        stC r [] F sl W (encodeNat s) w k J := by
      funext i; cases i <;> simp [S, stC]
    rw [he₂] at h₂
    have hL' : (encodeNat s).length ≤ L := by
      have := Nat.size_le_size (Nat.le_add_right s 1)
      simp only [BinaryNatEncoding.length_encodeNat] at hL ⊢
      omega
    cases F with
    | nil =>
      have h₃ : Run prog 1 ⟨some .walkStep, v₂, stC r [] [] sl W (encodeNat s) w k J⟩
          ⟨some .no, false, stC r [] [] sl W (encodeNat s) w k J⟩ := by
        apply Run.single
        simp [prog, TM2.stepAux, stC]
      refine ⟨false, _, ((h₁.le le_rfl).trans h₂ |>.trans (h₃.le le_rfl)).mono ?_,
        fun h => absurd h (by simp)⟩
      simp
      omega
    | cons b F =>
      have h₃ : Run prog 1 ⟨some .walkStep, v₂, stC r [] (b :: F) sl W (encodeNat s) w k J⟩
          ⟨some .walk, b, stC r [] F sl (b :: W) (encodeNat s) w k J⟩ := by
        apply Run.single
        simp only [prog, TM2.stepAux, stC, List.head?_cons, Option.isSome_some, id_eq,
          Bool.cond_true, Option.getD_some, List.tail_cons]
        congr 1
        funext i; cases i <;> simp [stC]
      obtain ⟨v₄, T, h₄, hT⟩ := ih F (b :: W) b hL'
      refine ⟨v₄, T, ?_, ?_⟩
      · have hl : (s + 1 < (b :: F).length) = (s < F.length) := by simp
        simp only [hl]
        refine ((h₁.le le_rfl).trans h₂ |>.trans (h₃.le le_rfl) |>.trans h₄).mono ?_
        simp only [List.length_cons]
        have hm : min (s + 1) (F.length + 1) = min s F.length + 1 := by omega
        rw [hm]
        have h2 : (min s F.length + 1 + 1) * (2 * L + 8) =
            (min s F.length + 1) * (2 * L + 8) + (2 * L + 8) := Nat.succ_mul _ _
        omega
      · intro h
        rw [hT (by simpa using h)]
        simp

end Walk

section SLoop

open MetaMathlibExt MetaMathlibExt.BitstringEncoding
open Turing Function TM2Program Cslib.Complexity
open Computability Cslib.Complexity.Karp Cslib.Complexity.FramedCNF

/-- The flags after marking every element of `S`, read from its framed bits `sl`. -/
private def sres (sl F : List Bool) : Option (List Bool) :=
  (undelimitBlocks sl).bind fun ss => (ss.map decodeNat).foldlM markAt F

private theorem sres_nil (F : List Bool) : sres [] F = some F := by
  simp [sres, undelimitBlocks, undelimitBlocksAux]

private theorem sres_cons (p sl F : List Bool) :
    sres (delimit p ++ sl) F =
      if decodeNat p < F.length then sres sl (F.set (decodeNat p) true)
      else (undelimitBlocks sl).bind fun _ => none := by
  simp only [sres, blocks_cons]
  cases undelimitBlocks sl with
  | none => split_ifs <;> rfl
  | some ss =>
    simp only [Option.map_some, Option.bind_some, List.map_cons, List.foldlM_cons, markAt_eq]
    split_ifs <;> rfl

private theorem sres_length {sl F fl : List Bool} (h : sres sl F = some fl) :
    fl.length = F.length := by
  obtain ⟨ss, -, hf⟩ := Option.bind_eq_some_iff.mp h
  rw [foldlM_markAt] at hf
  split_ifs at hf
  simp only [Option.some.injEq] at hf
  rw [← hf, List.length_mapIdx]

private theorem sloop_run (r w : List Bool) (k J : ℕ) : ∀ (n : ℕ) (sl F : List Bool) (v : Bool),
    sl.length ≤ n →
    ∃ v' T, RunLe prog (24 * (F.length + 2) * (sl.length + 1))
      ⟨some .sLoop, v, stC r [] F sl [] [] w k J⟩
      ⟨some (if (sres sl F).isSome then .loop else .no), v', T⟩ ∧
      ∀ fl, sres sl F = some fl → T = stC r [] fl [] [] [] w k J := by
  intro n
  induction n with
  | zero =>
    intro sl F v hsl
    have hsl' : sl = [] := List.eq_nil_of_length_eq_zero (by omega)
    subst hsl'
    have h₁ := ifNonempty_run (l := .sLoop) (a := .sRead) (b := .loop) (k := .sList) rfl v
      (stC r [] F [] [] [] w k J)
    simp only [stC, ↓reduceIte] at h₁
    refine ⟨_, _, h₁.le (by nlinarith), ?_⟩
    · intro fl hfl
      rw [sres_nil] at hfl
      cases hfl
      rfl
  | succ n ih =>
    intro sl F v hsl
    by_cases hs0 : sl = []
    · subst hs0
      have h₁ := ifNonempty_run (l := .sLoop) (a := .sRead) (b := .loop) (k := .sList) rfl v
        (stC r [] F [] [] [] w k J)
      simp only [stC, ↓reduceIte] at h₁
      rw [sres_nil]
      refine ⟨_, _, h₁.le (by nlinarith), ?_⟩
      · intro fl hfl
        cases hfl
        rfl
    let S := stC r [] F sl [] [] w k J
    obtain ⟨b, bs, hbs⟩ := List.exists_cons_of_ne_nil hs0
    have h₁ : Run prog 1 ⟨some .sLoop, v, S⟩ ⟨some .sRead, true, S⟩ := by
      have h := ifNonempty_run (l := .sLoop) (a := .sRead) (b := .loop) (k := .sList) rfl v S
      simpa [S, stC, hbs] using h
    cases hu : undelimit sl with
    | none =>
      obtain ⟨v', T, h₂, _⟩ := readFrame_bad (M := prog) (self := Lab.sRead)
        (next := .sNorm) (bad := .no) (a := K.sList) (b := K.sTmp)
        rfl (by decide) sl true S rfl hu
      have hn : sres sl F = none := by simp [sres, blocks_bad hs0 hu]
      refine ⟨v', T, ?_, ?_⟩
      · rw [hn]
        exact (h₁.le le_rfl |>.trans h₂).mono (by nlinarith)
      · simp [hn]
    | some pr =>
      obtain ⟨p, sl'⟩ := pr
      have hse := (Cslib.CookLevin.undelimit_eq_some_iff sl p sl').1 hu
      have hlen : sl.length = 2 * p.length + 1 + sl'.length := by simp [hse]
      have h₂ := readFrame_run (M := prog) (self := Lab.sRead) (next := .sNorm)
        (bad := .no) (a := K.sList) (b := K.sTmp) rfl (by decide) true S p sl'
        (by simp [S, stC, hse])
      let S₂ := update (update S K.sList sl') K.sTmp (p.reverse ++ S .sTmp)
      obtain ⟨v₃, h₃⟩ := normalizeRev_run (M := prog) (self := .sNorm) (move := .sNormMove)
        (next := .walk) (a := K.sTmp) (b := K.sVal) rfl rfl (by decide) p false S₂
        (by simp [S₂, S, stC])
      have he₃ : update (update S₂ K.sTmp []) K.sVal (encodeNat (decodeNat p) ++ S₂ .sVal) =
          stC r [] F sl' [] (encodeNat (decodeNat p)) w k J := by
        funext i; cases i <;> simp [S₂, S, stC]
      rw [he₃] at h₃
      have hL := decoded_length p
      obtain ⟨v₄, T₄, h₄, hT₄⟩ := walk_run r sl' w k J (p.length + 1) (decodeNat p) F [] v₃ hL
      have hmin : (min (decodeNat p) F.length + 1) * (2 * (p.length + 1) + 8) ≤
          (F.length + 1) * (2 * (p.length + 1) + 8) :=
        Nat.mul_le_mul_right _ (by omega)
      have hrun := (h₁.trans h₂).le le_rfl |>.trans h₃ |>.trans h₄
      by_cases hlt : decodeNat p < F.length
      · simp only [hlt, ↓reduceIte] at hrun
        rw [hT₄ hlt] at hrun
        simp only [List.reverse_nil, List.nil_append] at hrun
        obtain ⟨v₅, T, h₅, hT⟩ := ih sl' (F.set (decodeNat p) true) v₄ (by omega)
        rw [List.length_set] at h₅
        have hres : sres sl F = sres sl' (F.set (decodeNat p) true) := by
          rw [hse, sres_cons]; simp [hlt]
        refine ⟨v₅, T, ?_, ?_⟩
        · rw [hres]
          refine (hrun.trans h₅).mono ?_
          simp only [List.length_nil]
          rw [hlen]
          nlinarith
        · intro fl hfl
          rw [hres] at hfl
          exact hT fl hfl
      · simp only [hlt, ↓reduceIte] at hrun
        have hn : sres sl F = none := by
          rw [hse, sres_cons]
          simp only [hlt, ↓reduceIte]
          cases undelimitBlocks sl' <;> rfl
        refine ⟨v₄, T₄, ?_, ?_⟩
        · rw [hn]
          refine hrun.mono ?_
          simp only [List.length_nil]
          rw [hlen]
          nlinarith
        · simp [hn]

end SLoop

section Parse

open MetaMathlibExt MetaMathlibExt.BitstringEncoding
open Turing Function TM2Program Cslib.Complexity
open Computability Cslib.Complexity.Karp Cslib.Complexity.FramedCNF

/-- The input layout: `x` on `inp`, the certificate on `witness`. -/
private def init (x w : List Bool) : K → List Bool :=
  update (update (fun _ => []) .inp x) .witness w

/-- After the outer frames are split and `J` is checked. -/
private def stJ (a sraw w : List Bool) (J : ℕ) : K → List Bool
  | .aRev => a.reverse
  | .sRev => sraw.reverse
  | .jBound => encodeNat J
  | .witness => w
  | _ => []

private theorem xbad_run (x w : List Bool) (hx : undelimit x = none) :
    ∃ v T, RunLe prog (x.length + 1) ⟨some .start, false, init x w⟩ ⟨some .no, v, T⟩ := by
  obtain ⟨v, T, h, _⟩ := readFrame_bad (M := prog) (self := Lab.start) (next := .readS)
    (bad := .no) (a := K.inp) (b := K.aRev) rfl (by decide) x false (init x w)
    (by simp [init]) hx
  exact ⟨v, T, h⟩

private theorem bbad_run (x w a b : List Bool) (hx : x = delimit a ++ b) (hb : undelimit b = none) :
    ∃ v T, RunLe prog (x.length + 2) ⟨some .start, false, init x w⟩ ⟨some .no, v, T⟩ := by
  let S := init x w
  have h₁ := readFrame_run (M := prog) (self := Lab.start) (next := .readS) (bad := .no)
    (a := K.inp) (b := K.aRev) rfl (by decide) false S a b (by simp [S, init, hx])
  let S₁ := update (update S K.inp b) K.aRev (a.reverse ++ S .aRev)
  obtain ⟨v, T, h₂, _⟩ := readFrame_bad (M := prog) (self := Lab.readS) (next := .revJ)
    (bad := .no) (a := K.inp) (b := K.sRev) rfl (by decide) b false S₁ (by simp [S₁]) hb
  have hl : x.length = 2 * a.length + 1 + b.length := by simp [hx]
  exact ⟨v, T, (h₁.le le_rfl |>.trans h₂).mono (by omega)⟩

private theorem parseJ_run (x w a b sraw jb : List Bool) (hx : x = delimit a ++ b)
    (hb : b = delimit sraw ++ jb) :
    ∃ v T, RunLe prog (2 * x.length + 10) ⟨some .start, false, init x w⟩
      ⟨some (if decodeNat jb = 0 then .no else .restoreA), v, T⟩ ∧
      (decodeNat jb ≠ 0 → T = stJ a sraw w (decodeNat jb)) := by
  let S := init x w
  have h₁ := readFrame_run (M := prog) (self := Lab.start) (next := .readS) (bad := .no)
    (a := K.inp) (b := K.aRev) rfl (by decide) false S a b (by simp [S, init, hx])
  let S₁ := update (update S K.inp b) K.aRev (a.reverse ++ S .aRev)
  have h₂ := readFrame_run (M := prog) (self := Lab.readS) (next := .revJ) (bad := .no)
    (a := K.inp) (b := K.sRev) rfl (by decide) false S₁ sraw jb (by simp [S₁, hb])
  let S₂ := update (update S₁ K.inp jb) K.sRev (sraw.reverse ++ S₁ .sRev)
  obtain ⟨v₃, h₃⟩ := moveBits_run (M := prog) (self := Lab.revJ) (a := K.inp) (b := K.jRev)
    (next := .normJ) rfl (by decide) false S₂
  let S₃ := update (update S₂ K.inp []) K.jRev ((S₂ .inp).reverse ++ S₂ .jRev)
  obtain ⟨v₄, h₄⟩ := normalizeRev_run (M := prog) (self := .normJ) (move := .normJMove)
    (next := .posJ) (a := K.jRev) (b := K.jBound) rfl rfl (by decide) jb v₃ S₃
    (by simp [S₃, S₂, S₁, S, init])
  let S₄ := update (update S₃ K.jRev []) K.jBound (encodeNat (decodeNat jb) ++ S₃ .jBound)
  have h₅ := ifNonempty_run (l := .posJ) (a := .restoreA) (b := .no) (k := .jBound) rfl v₄ S₄
  have hS₄ : S₄ .jBound = encodeNat (decodeNat jb) := by simp [S₄, S₃, S₂, S₁, S, init]
  rw [hS₄] at h₅
  simp only [encodeNat_eq_nil_iff] at h₅
  have hl₁ : x.length = 2 * a.length + 1 + b.length := by simp [hx]
  have hl₂ : b.length = 2 * sraw.length + 1 + jb.length := by simp [hb]
  refine ⟨_, S₄, ((h₁.trans h₂ |>.trans h₃).le le_rfl |>.trans h₄ |>.trans (h₅.le le_rfl)).mono
    ?_, fun _ => ?_⟩
  · simp [S₂, S₁, S, init]
    omega
  · funext i
    cases i <;> simp [S₄, S₃, S₂, S₁, S, init, stJ]

private theorem abad_run (a sraw w : List Bool) (J : ℕ) (v : Bool) (ha : undelimit a = none) :
    ∃ v' T, RunLe prog (2 * a.length + 2) ⟨some .restoreA, v, stJ a sraw w J⟩
      ⟨some .no, v', T⟩ := by
  let S := stJ a sraw w J
  obtain ⟨v₁, h₁⟩ := moveBits_run (M := prog) (self := Lab.restoreA) (a := K.aRev) (b := K.jobs)
    (next := .wtjStart) rfl (by decide) v S
  let S₁ := update (update S K.aRev []) K.jobs ((S .aRev).reverse ++ S .jobs)
  obtain ⟨v₂, T, h₂, _⟩ := readFrame_bad (M := prog) (self := Lab.wtjStart)
    (next := .reverseBound) (bad := .no) (a := K.jobs) (b := K.tmp) rfl (by decide) a v₁ S₁
    (by simp [S₁, S, stJ]) ha
  exact ⟨v₂, T, (h₁.le le_rfl |>.trans h₂).mono (by simp [S, stJ]; omega)⟩

private theorem parseK_run (a sraw w raw kb : List Bool) (J : ℕ) (v : Bool)
    (ha : a = delimit raw ++ kb) :
    ∃ v' T, RunLe prog (3 * a.length + sraw.length + 10) ⟨some .restoreA, v, stJ a sraw w J⟩
      ⟨some (if decodeNat kb = 0 then .no else .count), v', T⟩ ∧
      (decodeNat kb ≠ 0 → T = stC raw [] [] sraw [] [] w (decodeNat kb) J) := by
  let S := stJ a sraw w J
  obtain ⟨v₆, h₆⟩ := moveBits_run (M := prog) (self := Lab.restoreA) (a := K.aRev) (b := K.jobs)
    (next := .wtjStart) rfl (by decide) v S
  let S₆ := update (update S K.aRev []) K.jobs ((S .aRev).reverse ++ S .jobs)
  have h₇ := readFrame_run (M := prog) (self := Lab.wtjStart) (next := .reverseBound) (bad := .no)
    (a := K.jobs) (b := K.tmp) rfl (by decide) v₆ S₆ raw kb (by simp [S₆, S, stJ, ha])
  let S₇ := update (update S₆ K.jobs kb) K.tmp (raw.reverse ++ S₆ .tmp)
  obtain ⟨v₈, h₈⟩ := moveBits_run (M := prog) (self := Lab.reverseBound) (a := K.jobs)
    (b := K.processRev) (next := .restoreJobs) rfl (by decide) false S₇
  let S₈ := update (update S₇ K.jobs []) K.processRev ((S₇ .jobs).reverse ++ S₇ .processRev)
  obtain ⟨v₉, h₉⟩ := moveBits_run (M := prog) (self := Lab.restoreJobs) (a := K.tmp)
    (b := K.jobs) (next := .norm .bound) rfl (by decide) v₈ S₈
  let S₉ := update (update S₈ K.tmp []) K.jobs ((S₈ .tmp).reverse ++ S₈ .jobs)
  obtain ⟨v₁₀, h₁₀⟩ := norm_run .bound kb v₉ S₉ (by simp [S₉, S₈, S₇, S₆, S, stJ, normSource])
  let S₁₀ := update (update S₉ (normSource .bound) []) (normTarget .bound)
    (encodeNat (decodeNat kb) ++ S₉ (normTarget .bound))
  have h₁₁ := ifNonempty_run (l := .posK) (a := .restoreS) (b := .no) (k := .bound) rfl v₁₀ S₁₀
  have hS₁₀ : S₁₀ .bound = encodeNat (decodeNat kb) := by
    simp [S₁₀, S₉, S₈, S₇, S₆, S, stJ, normSource, normTarget]
  rw [hS₁₀] at h₁₁
  simp only [encodeNat_eq_nil_iff] at h₁₁
  have hl₃ : a.length = 2 * raw.length + 1 + kb.length := by simp [ha]
  have r₁ := (h₆.trans h₇ |>.trans h₈ |>.trans h₉).le le_rfl
  by_cases hK : decodeNat kb = 0
  · simp only [hK, ↓reduceIte] at h₁₁
    simp only [hK, ↓reduceIte, ne_eq, not_true_eq_false, false_imp_iff, and_true]
    refine ⟨_, S₁₀, (r₁.trans h₁₀ |>.trans (h₁₁.le le_rfl)).mono ?_⟩
    simp [S₈, S₇, S₆, S, stJ]
    omega
  · simp only [hK, ↓reduceIte] at h₁₁ ⊢
    obtain ⟨v₁₂, h₁₂⟩ := moveBits_run (M := prog) (self := Lab.restoreS) (a := K.sRev)
      (b := K.sList) (next := .count) rfl (by decide) _ S₁₀
    have he : update (update S₁₀ K.sRev []) K.sList ((S₁₀ .sRev).reverse ++ S₁₀ .sList) =
        stC raw [] [] sraw [] [] w (decodeNat kb) J := by
      funext i
      cases i <;> simp [S₁₀, S₉, S₈, S₇, S₆, S, stJ, normSource, normTarget, stC]
    rw [he] at h₁₂
    have r₂ := (h₁₁.trans h₁₂).le le_rfl
    refine ⟨v₁₂, _, (r₁.trans h₁₀ |>.trans r₂).mono ?_, fun _ => rfl⟩
    simp [S₁₀, S₉, S₈, S₇, S₆, S, stJ, normSource, normTarget]
    omega

end Parse

section Final

open MetaMathlibExt MetaMathlibExt.BitstringEncoding
open Turing Function TM2Program Cslib.Complexity
open Computability Cslib.Complexity.Karp Cslib.Complexity.FramedCNF
open MetaMathlibExt.Complexity.NPComplete.ConstrainedSequencingToMinimizeTardyTaskWeight

private theorem check_eq {x w a b raw kb sraw jb : List Bool} (hx : undelimit x = some (a, b))
    (ha : undelimit a = some (raw, kb)) (hb : undelimit b = some (sraw, jb)) :
    check x w = match undelimitBlocks raw, undelimitBlocks sraw with
      | some ps, some ss =>
        match (ss.map decodeNat).foldlM markAt (List.replicate ps.length false) with
        | some fl => decide (0 < decodeNat kb) && decide (0 < decodeNat jb) &&
            loop w ps fl [] [] (0, 0) 0 (decodeNat kb) (decodeNat jb)
        | none => false
      | _, _ => false := by
  rw [check, hx]
  simp only [ha, hb]
  rfl

private theorem check_false_of_bounds {x w a b raw kb sraw jb : List Bool}
    (hx : undelimit x = some (a, b)) (ha : undelimit a = some (raw, kb))
    (hb : undelimit b = some (sraw, jb)) (h : decodeNat kb = 0 ∨ decodeNat jb = 0) :
    check x w = false := by
  rw [check_eq hx ha hb]
  split
  · split
    · rcases h with h | h <;> simp [h]
    · rfl
  · rfl

private theorem verify_run (x w : List Bool) :
    ∃ v T, RunLe prog (1000 * (x.length + w.length + 2) ^ 2)
      ⟨some .start, false, init x w⟩ ⟨some (yesNo (check x w)), v, T⟩ := by
  have hsq : x.length + 2 ≤ (x.length + w.length + 2) ^ 2 :=
    calc x.length + 2 ≤ x.length + w.length + 2 := by omega
      _ ≤ (x.length + w.length + 2) ^ 2 := Nat.le_self_pow (by norm_num) _
  cases hx : undelimit x with
  | none =>
    obtain ⟨v, T, h⟩ := xbad_run x w hx
    refine ⟨v, T, ?_⟩
    simpa [check, hx, yesNo] using h.mono (by nlinarith)
  | some pr =>
    obtain ⟨a, b⟩ := pr
    have hxe := (Cslib.CookLevin.undelimit_eq_some_iff x a b).1 hx
    have hxl : x.length = 2 * a.length + 1 + b.length := by simp [hxe]
    cases hb : undelimit b with
    | none =>
      obtain ⟨v, T, h⟩ := bbad_run x w a b hxe hb
      refine ⟨v, T, ?_⟩
      have hc : check x w = false := by
        cases ha : undelimit a <;> simp [check, hx, ha, hb]
      rw [hc]
      exact h.mono (by nlinarith)
    | some pb =>
      obtain ⟨sraw, jb⟩ := pb
      have hbe := (Cslib.CookLevin.undelimit_eq_some_iff b sraw jb).1 hb
      have hbl : b.length = 2 * sraw.length + 1 + jb.length := by simp [hbe]
      obtain ⟨v₁, T₁, h₁, hT₁⟩ := parseJ_run x w a b sraw jb hxe hbe
      by_cases hJ : decodeNat jb = 0
      · simp only [hJ, ↓reduceIte] at h₁
        refine ⟨v₁, T₁, ?_⟩
        have hc : check x w = false := by
          cases ha : undelimit a with
          | none => simp [check, hx, ha, hb]
          | some pa =>
            obtain ⟨raw, kb⟩ := pa
            exact check_false_of_bounds hx ha hb (Or.inr hJ)
        rw [hc]
        exact h₁.mono (by nlinarith)
      simp only [hJ, ↓reduceIte] at h₁
      rw [hT₁ hJ] at h₁
      cases ha : undelimit a with
      | none =>
        obtain ⟨v₂, T₂, h₂⟩ := abad_run a sraw w (decodeNat jb) v₁ ha
        refine ⟨v₂, T₂, ?_⟩
        have hc : check x w = false := by simp [check, hx, ha, hb]
        rw [hc]
        exact (h₁.trans h₂).mono (by nlinarith)
      | some pa =>
        obtain ⟨raw, kb⟩ := pa
        have hae := (Cslib.CookLevin.undelimit_eq_some_iff a raw kb).1 ha
        have hal : a.length = 2 * raw.length + 1 + kb.length := by simp [hae]
        obtain ⟨v₂, T₂, h₂, hT₂⟩ := parseK_run a sraw w raw kb (decodeNat jb) v₁ hae
        by_cases hK : decodeNat kb = 0
        · simp only [hK, ↓reduceIte] at h₂
          refine ⟨v₂, T₂, ?_⟩
          rw [check_false_of_bounds hx ha hb (Or.inl hK)]
          exact (h₁.trans h₂).mono (by nlinarith)
        simp only [hK, ↓reduceIte] at h₂
        rw [hT₂ hK] at h₂
        have hrun₁ := h₁.trans h₂
        obtain ⟨v₃, T₃, h₃, hT₃⟩ := count_run sraw w (decodeNat kb) (decodeNat jb) raw.length raw
          [] 0 v₂ le_rfl
        rw [show (pack ([] : List (List Bool))).reverse = [] from rfl,
          show List.replicate 0 false = [] from rfl] at h₃
        cases hps : undelimitBlocks raw with
        | none =>
          simp only [hps, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at h₃
          refine ⟨v₃, T₃, ?_⟩
          have hc : check x w = false := by
            rw [check_eq hx ha hb, hps]
          rw [hc]
          refine (hrun₁.trans h₃).mono ?_
          simp only [show (pack ([] : List (List Bool))).length = 0 from rfl]
          nlinarith
        | some ps =>
          simp only [hps, Option.isSome_some, ↓reduceIte] at h₃
          rw [hT₃ ps hps, List.nil_append, Nat.zero_add] at h₃
          have hpsl : ps.length ≤ raw.length := blocks_length_le hps
          obtain ⟨v₄, T₄, h₄, hT₄⟩ := sloop_run (pack ps) w (decodeNat kb) (decodeNat jb)
            sraw.length sraw (List.replicate ps.length false) v₃ le_rfl
          rw [List.length_replicate] at h₄
          have hrun₂ := hrun₁.trans h₃ |>.trans h₄
          have hbig : 24 * (ps.length + 2) * (sraw.length + 1) ≤
              24 * (x.length + w.length + 2) ^ 2 := by
            have h1 : ps.length + 2 ≤ x.length + w.length + 2 := by omega
            have h2 : sraw.length + 1 ≤ x.length + w.length + 2 := by omega
            nlinarith
          cases hss : undelimitBlocks sraw with
          | none =>
            have hn : sres sraw (List.replicate ps.length false) = none := by
              simp [sres, hss]
            simp only [hn, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hrun₂
            refine ⟨v₄, T₄, ?_⟩
            have hc : check x w = false := by
              rw [check_eq hx ha hb, hps, hss]
            rw [hc]
            refine hrun₂.mono ?_
            simp only [show (pack ([] : List (List Bool))).length = 0 from rfl]
            nlinarith
          | some ss =>
            cases hfl : (ss.map decodeNat).foldlM markAt (List.replicate ps.length false) with
            | none =>
              have hn : sres sraw (List.replicate ps.length false) = none := by
                simp [sres, hss, hfl]
              simp only [hn, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hrun₂
              refine ⟨v₄, T₄, ?_⟩
              have hc : check x w = false := by
                rw [check_eq hx ha hb, hps, hss]
                simp only [hfl]
              rw [hc]
              refine hrun₂.mono ?_
              simp only [show (pack ([] : List (List Bool))).length = 0 from rfl]
              nlinarith
            | some fl =>
              have hs : sres sraw (List.replicate ps.length false) = some fl := by
                simp [sres, hss, hfl]
              simp only [hs, Option.isSome_some, ↓reduceIte] at hrun₂
              rw [hT₄ fl hs, stC_eq_st] at hrun₂
              have hflen : fl.length = ps.length := by
                rw [sres_length hs, List.length_replicate]
              obtain ⟨v₅, T₅, h₅⟩ := verify_loop (B := budget (pack ps) [] (0, 0) 0 (decodeNat kb)
                (decodeNat jb)) (decodeNat kb) (decodeNat jb) w ps [] fl [] (0, 0) 0 v₄ hflen
                rfl le_rfl
              refine ⟨v₅, T₅, ?_⟩
              have hc : check x w = loop w ps fl [] [] (0, 0) 0 (decodeNat kb) (decodeNat jb) := by
                rw [check_eq hx ha hb, hps, hss]
                simp only [hfl, Nat.pos_of_ne_zero hK, Nat.pos_of_ne_zero hJ, decide_true,
                  Bool.true_and]
              rw [hc]
              have hB : budget (pack ps) [] (0, 0) 0 (decodeNat kb) (decodeNat jb) ≤
                  8 * x.length + 2 := by
                have hk := decoded_length kb
                have hj := decoded_length jb
                have hraw : pack ps = raw :=
                  (Cslib.Complexity.PolynomialEncoding.blocks_decode_sound hps).symm
                rw [hraw]
                simp only [budget, List.reverse_nil, show pack [] = [] from rfl, List.length_nil,
                  Nat.add_zero, show encodeNat 0 = [] from rfl, List.length_nil] at hk hj ⊢
                omega
              have hmul : 60 * (budget (pack ps) [] (0, 0) 0 (decodeNat kb) (decodeNat jb) + 1) *
                  (w.length + 1) ≤ 540 * (x.length + w.length + 2) ^ 2 := by
                have h1 : budget (pack ps) [] (0, 0) 0 (decodeNat kb) (decodeNat jb) + 1 ≤
                    9 * (x.length + w.length + 2) := by omega
                have h2 : w.length + 1 ≤ x.length + w.length + 2 := by omega
                nlinarith
              refine (hrun₂.trans h₅).mono ?_
              simp only [show (pack ([] : List (List Bool))).length = 0 from rfl]
              nlinarith

private def ks : List K :=
  [.jobs, .witness, .skipped, .elapsed, .cost, .bound, .tmp, .payload, .processRev, .dueRev,
  .operand, .elapsedCopy, .sum, .inp, .aRev, .sRev, .jRev, .jBound, .sList, .sTmp, .sVal,
  .decTmp, .walked, .back, .flags, .skipFlags, .curFlag, .count]

private noncomputable instance kFintype : Fintype K :=
  Fintype.ofList ks (fun k => by cases k <;> decide)

private noncomputable instance labFintype : Fintype Lab :=
  Fintype.ofList
    [.start, .readS, .revJ, .normJ, .normJMove, .posJ, .restoreA, .wtjStart, .reverseBound,
    .restoreJobs, .posK, .restoreS, .count, .countRead, .countPayload, .countWrite, .countFlag,
    .countDone, .sLoop, .sRead, .sNorm, .sNormMove, .walk, .dec, .decRestore, .walkStep,
    .unwalk, .loop, .read false, .read true, .restorePayload false, .restorePayload true, .skip,
    .skipFlag, .takeFlag, .restoreSkipped, .restoreFlags, .readProcess, .readDue, .norm .bound,
    .norm .process, .norm .due, .norm .weight, .normMove .bound, .normMove .process, .normMove
    .due, .normMove .weight, .pos .bound, .pos .process, .pos .due, .pos .weight, .addStart
    false, .addStart true, .add false, .add true, .carry false, .carry true, .store false,
    .store true, .dropFlag, .compareStart false, .compareStart true, .compare false, .compare
    true, .compareDone false, .compareDone true, .onTime, .discardWeight, .countFlag2, .inc,
    .incRestore, .reverseWeight, .compareJ, .compareJRun, .compareJDone, .yes, .no]
    (fun l => by
      cases l
      all_goals first | decide | (rename_i x; cases x <;> decide))

private noncomputable def comp : Host.Comp where
  K := K
  Γ := fun _ => Bool
  L := Lab
  prog := prog
  ks := ks
  ks_nodup := by decide
  mem_ks := fun k => by cases k <;> decide

theorem check_poly : ComplexityTheory.IsPolyTime
    (fun xw : List Bool × List Bool => check xw.1 xw.2) :=
  Host.isPolyTime_verifier (c := comp) (cX := .inp) (cW := .witness)
    (gX := id) (gW := id) (start := .start) (yes := .yes) (no := .no)
    check (Polynomial.C 1000 * (Polynomial.X + 2) ^ 2)
    (fun h => K.noConfusion h) (fun h => Lab.noConfusion h) rfl rfl fun x w => by
      obtain ⟨v, T, hr⟩ := verify_run x w
      refine ⟨v, T, ?_⟩
      change RunLe prog _ ⟨some .start, false,
        update (update (fun _ => []) .inp (x.map id)) .witness (w.map id)⟩
        ⟨some (yesNo (check x w)), v, T⟩
      rw [List.map_id, List.map_id]
      have he : (if check x w then Lab.yes else Lab.no) = yesNo (check x w) := rfl
      exact hr.mono (by simp [Nat.add_assoc])

/-- CONSTRAINED SEQUENCING TO MINIMIZE TARDY TASK WEIGHT is in NP. -/
private theorem constrainedSequencing_mem_NP :
    constrainedSequencingDec ∈ MetaMathlibExt.ComplexityTheory.NP :=
  membership_of_check_poly check_poly

end Final

end Verification

/-- **CONSTRAINED SEQUENCING TO MINIMIZE TARDY TASK WEIGHT is in NP.** A polynomial-time
multi-stack Turing machine checks a skip/take plan of polynomial length. -/
public theorem constrainedSequencing_mem_NP :
    constrainedSequencingDec ∈ MetaMathlibExt.ComplexityTheory.NP :=
  Verification.constrainedSequencing_mem_NP

end MetaMathlibExt.Complexity.NPComplete.ConstrainedSequencingToMinimizeTardyTaskWeight
