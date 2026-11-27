/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
import CSLibExt.Computability.Complexity.Karp.PartitionComplete
import CSLibExt.Computability.Complexity.PolynomialEncoding.Copy
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Permutation

/-!
# WEIGHTED NUMBER OF TARDY JOBS is NP-complete

Jobs with processing times, due dates, and weights, and a bound `K`. The question is whether
some ordering has weighted number of tardy jobs at most `K`: a job is tardy if it completes
after its due date, and contributes its weight when tardy, computed by a fold over the
ordering.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances. The decoder accepts more than the
canonical encodings `bitEncode i` of instances: Mathlib's binary decoder of natural numbers reads
every bit list, so a correctly framed bitstring with a natural-number field ending in a false bit,
which the encoder never produces, still decodes, and is a yes-instance exactly when the instance
it decodes to is feasible. For example, `[false, false]` decodes to the instance `([], 2)` and is
accepted, although the canonical encoding of `([], 2)` is `[false, false, true]`.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).

The proof establishes membership using a polynomial-time schedule verifier and
hardness by a reduction from binary PARTITION. The reduction is Karp's KNAPSACK ∝ SEQUENCING
construction (processing times equal to penalties, `T_i = P_i = a_i`, and a common deadline
`D_i = b`) applied to the doubled PARTITION instance: a list `a` becomes the jobs
`(2 a_i, ∑ a, 2 a_i)` with bound `K = ∑ a`, so the knapsack target `b = ∑ a` is half the total
processing time.

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), WEIGHTED NUMBER OF TARDY
JOBS (1||sum w_j U_j); R. M. Karp, "Reducibility among combinatorial problems", in
*Complexity of Computer Computations* (1972), 85–103: JOB SEQUENCING (problem 19, p. 95) and
KNAPSACK ∝ SEQUENCING (p. 100).
-/

namespace MetaMathlibExt.Complexity.NPComplete.WeightedTardyJobs

@[expose] public section

/-- **Weighted tardy jobs instances.** An instance of WEIGHTED NUMBER OF TARDY JOBS is a pair
consisting of a finite list of jobs, each a triple $(p, d, w)$ of natural numbers giving its
processing time $p$, due date $d$ and weight $w$, and a natural number $K$, the bound. -/
abbrev WeightedTardyJobsInstance := List (ℕ × ℕ × ℕ) × ℕ


/-- **One step of the weighted tardy jobs computation.** Let $J$ be a list of jobs, each a triple
$(p, d, w)$ of natural numbers (processing time, due date, weight). Given a state $(t, s)$ and a
natural number $j$, let $(p, d, w)$ be the job at position $j$ of $J$, counting from $0$, or
$(0, 0, 0)$ if $J$ has no position $j$, and let $t' = t + p$. The step returns $(t', s + w)$ if
$d < t'$, and $(t', s)$ otherwise. -/
def WeightedTardyStep (jobs : List (ℕ × ℕ × ℕ)) (state : ℕ × ℕ) (j : ℕ) : ℕ × ℕ :=
  let t := state.1 + (jobs.getD j (0, 0, 0)).1
  (t, state.2 + if (jobs.getD j (0, 0, 0)).2.1 < t then (jobs.getD j (0, 0, 0)).2.2 else 0)

/-- **Weighted number of tardy jobs of an ordering.** Let $J$ be a list of jobs, each a triple of
natural numbers (processing time, due date, weight), and write $(p_i, d_i, w_i)$ for the job at
position $i$ of $J$, counting from $0$, with $(p_i, d_i, w_i) = (0, 0, 0)$ when $J$ has no
position $i$. For a list $(j_1, \dots, j_m)$ of natural numbers, the weighted number of tardy
jobs of this order is the sum of $w_{j_k}$ over all $k$ with $d_{j_k} < C_k$, where
$C_k = p_{j_1} + \dots + p_{j_k}$ is the completion time of the $k$-th job. -/
def WeightedTardy (jobs : List (ℕ × ℕ × ℕ)) (order : List ℕ) : ℕ :=
  (order.foldl (WeightedTardyStep jobs) (0, 0)).2


/-- **Feasible weighted tardy jobs instances.** A weighted tardy jobs instance, consisting of a
list of $n$ jobs and a bound $K$, is feasible when there is an ordering of its jobs, that is, a
list of the job indices $0, 1, \dots, n - 1$ in which each index occurs exactly once, whose
weighted number of tardy jobs is at most $K$. -/
def WeightedTardyJobsFeasible
    (i : WeightedTardyJobsInstance) : Prop :=
  ∃ order : List ℕ, order.Perm (List.range i.1.length) ∧
    WeightedTardy i.1 order ≤ i.2

open Classical in
/-- **The weighted number of tardy jobs decision problem.** WEIGHTED NUMBER OF TARDY JOBS is the
decision problem that accepts a bitstring $x$ exactly when $x$ decodes, under the canonical
bitstring encoding of weighted tardy jobs instances, to a feasible instance, that is, an instance
having an ordering of its jobs whose weighted number of tardy jobs is at most its bound. A
bitstring that decodes to no instance is rejected. The decoder also reads bitstrings that the
encoder never produces: every bit list decodes to a natural number, so a correctly framed
bitstring with a natural-number field ending in a false bit decodes too, and is accepted exactly
when the instance it decodes to is feasible. -/
noncomputable def weightedTardyJobsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := WeightedTardyJobsInstance) x with
  | some i => decide (WeightedTardyJobsFeasible i)
  | none => false

end

open BitstringEncoding

/-! ### Correctness of the scheduling reduction -/

private def job (due a : ℕ) : ℕ × ℕ × ℕ := (2 * a, due, 2 * a)

private def partitionJobs (as : List ℕ) : WeightedTardyJobsInstance :=
  (as.map (job as.sum), as.sum)

private def addTardy (d : ℕ) (acc : ℕ × ℕ) (a : ℕ) : ℕ × ℕ :=
  (acc.1 + 2 * a, acc.2 + if d < acc.1 + 2 * a then 2 * a else 0)

private theorem map_range_getD {α : Type} (xs : List α) (default : α) :
    (List.range xs.length).map (xs.getD · default) = xs := by
  apply List.ext_getElem
  · simp
  · intro n _ hn
    simp [List.getElem?_eq_getElem hn]

private theorem foldl_indices (d : ℕ) (as order : List ℕ) (acc : ℕ × ℕ) :
    order.foldl (WeightedTardyStep (as.map (job d))) acc =
      (order.map (as.getD · 0)).foldl (addTardy d) acc := by
  rw [List.foldl_map]
  congr 1
  funext s j
  simp only [WeightedTardyStep, addTardy, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : as[j]? with
  | none => simp
  | some a => simp [job, Nat.mul_comm 2 a]

private theorem foldl_tardy_le (d : ℕ) (as : List ℕ) (t w : ℕ) :
    (as.foldl (addTardy d) (t, w)).2 ≤ w + 2 * as.sum := by
  induction as generalizing t w with
  | nil => simp
  | cons a as ih =>
    simp only [List.foldl_cons, addTardy, List.sum_cons]
    specialize ih (t + 2 * a) (w + if d < t + 2 * a then 2 * a else 0)
    have hfee : (if d < t + 2 * a then 2 * a else 0) ≤ 2 * a := by split <;> omega
    omega

private theorem foldl_all_tardy (d : ℕ) (as : List ℕ) (t w : ℕ) (h : d < t) :
    (as.foldl (addTardy d) (t, w)).2 = w + 2 * as.sum := by
  induction as generalizing t w with
  | nil => simp
  | cons a as ih =>
    have h' : d < t + 2 * a := by omega
    simp [addTardy, h', ih (t + 2 * a) (w + 2 * a) h']
    omega

private theorem foldl_on_time (d : ℕ) (as : List ℕ) (t w : ℕ)
    (h : t + 2 * as.sum ≤ d) :
    as.foldl (addTardy d) (t, w) = (t + 2 * as.sum, w) := by
  induction as generalizing t w with
  | nil => simp
  | cons a as ih =>
    simp only [List.sum_cons] at h ⊢
    have h₁ : ¬ d < t + 2 * a := by omega
    simp [addTardy, h₁, ih (t + 2 * a) w (by omega : t + 2 * a + 2 * as.sum ≤ d)]
    omega

private theorem find_on_time_prefix (d : ℕ) (as : List ℕ) (t w : ℕ) :
    ∃ early late : List ℕ, as = early ++ late ∧
      (early.sum = 0 ∨ t + 2 * early.sum ≤ d) ∧
      (as.foldl (addTardy d) (t, w)).2 = w + 2 * late.sum := by
  induction as generalizing t w with
  | nil => exact ⟨[], [], rfl, .inl rfl, by simp⟩
  | cons a as ih =>
    by_cases h : d < t + 2 * a
    · refine ⟨[], a :: as, rfl, .inl rfl, ?_⟩
      simp [addTardy, h, foldl_all_tardy d as _ _ h]
      omega
    · obtain ⟨early, late, e, hb, hc⟩ := ih (t + 2 * a) w
      refine ⟨a :: early, late, by simp [e], .inr ?_, ?_⟩
      · simp only [List.sum_cons]
        rcases hb with hb | hb <;> omega
      · simpa [addTardy, h] using hc

private theorem partitionJobs_correct (as : List ℕ) :
    WeightedTardyJobsFeasible (partitionJobs as) ↔ Partition.PartitionFeasible as := by
  constructor
  · rintro ⟨order, hp, hw⟩
    have hm : (order.map (as.getD · 0)).Perm as := by
      simpa only [partitionJobs, List.length_map, map_range_getD] using
        hp.map (as.getD · 0)
    obtain ⟨early, late, hsplit, hbound, hweight⟩ :=
      find_on_time_prefix as.sum (order.map (as.getD · 0)) 0 0
    change WeightedTardy (as.map (job as.sum)) order ≤ as.sum at hw
    rw [WeightedTardy, foldl_indices, hweight] at hw
    rw [hsplit] at hm
    obtain ⟨s, hs, hsub⟩ := List.exists_perm_sublist (List.sublist_append_left early late) hm
    have hsum := hm.sum_eq
    rw [List.sum_append] at hsum
    have hse := hs.sum_eq
    refine ⟨s, hsub, ?_⟩
    rcases hbound with hbound | hbound <;> omega
  · rintro ⟨s, hsub, hsum⟩
    rw [← map_range_getD as 0] at hsub
    obtain ⟨early, hearly, rfl⟩ := List.sublist_map_iff.mp hsub
    obtain ⟨late, hperm⟩ := hearly.exists_perm_append
    refine ⟨early ++ late, by simpa [partitionJobs] using hperm.symm, ?_⟩
    have hmap : ((early ++ late).map (as.getD · 0)).Perm as := by
      simpa only [map_range_getD] using hperm.symm.map (as.getD · 0)
    have htot := hmap.sum_eq
    rw [List.map_append, List.sum_append] at htot
    change WeightedTardy (as.map (job as.sum)) (early ++ late) ≤ as.sum
    have htime := foldl_on_time as.sum (early.map (as.getD · 0)) 0 0 (by omega)
    rw [WeightedTardy, foldl_indices, List.map_append, List.foldl_append, htime]
    have := foldl_tardy_le as.sum (late.map (as.getD · 0))
      (0 + 2 * (early.map (as.getD · 0)).sum) 0
    omega

open Turing Function TM2Program Cslib.Complexity
open Cslib.Complexity.PolynomialEncoding (splitB splitB_run copyB_run)

/-! ### Bitstring framing and stack operations -/

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

/-! ### The polynomial-time PARTITION reduction

The existing PARTITION transducer emits the framed target followed by the
doubled entries. The machine below copies the target into each job and emits
the extra framing required by the scheduling encoding. Empty PARTITION is
handled separately from the malformed-input sentinel.
-/

namespace Reduction

open Computability Cslib.Complexity.Karp

private def liftBit (b : Bool) : List Bool := [true, b]

private def liftBits (xs : List Bool) : List Bool := xs.flatMap liftBit

private theorem delimit_eq (xs : List Bool) : delimit xs = liftBits xs ++ [false] := by
  induction xs with
  | nil => rfl
  | cons b xs ih => simp [delimit, liftBits, liftBit, ih]

private theorem liftBits_append (xs ys : List Bool) :
    liftBits (xs ++ ys) = liftBits xs ++ liftBits ys := List.flatMap_append

private def lift₂ (b : Bool) : List Bool := liftBits (liftBit b)

private def lift₃ (b : Bool) : List Bool := liftBits (lift₂ b)

private theorem liftBits_flatMap {α : Type} (xs : List α) (f : α → List Bool) :
    liftBits (xs.flatMap f) = xs.flatMap (liftBits ∘ f) := by
  rw [liftBits, List.flatMap_assoc]
  rfl

private def triple (p d : List Bool) : List Bool :=
  (p.flatMap lift₃ ++ lift₂ false) ++ (d.flatMap lift₃ ++ lift₂ false) ++
    (p.flatMap lift₂ ++ liftBit false)

private theorem triple_eq (p d : List Bool) :
    triple p d = liftBits (delimit (delimit p ++ delimit d ++ p)) := by
  simp [triple, delimit_eq, liftBits, lift₂, liftBit, List.flatMap_assoc, List.append_assoc]
  rfl

private theorem length_flatMap_const {α β : Type} (xs : List α) (f : α → List β) (n : ℕ)
    (h : ∀ a, (f a).length = n) : (xs.flatMap f).length = n * xs.length := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [h, ih, Nat.mul_succ, Nat.add_comm]

private theorem triple_length (p d : List Bool) :
    (triple p d).length = 12 * p.length + 8 * d.length + 10 := by
  have h₂ (b : Bool) : (lift₂ b).length = 4 := by cases b <;> decide
  have h₃ (b : Bool) : (lift₃ b).length = 8 := by cases b <;> decide
  simp only [triple, List.length_append, length_flatMap_const _ _ _ h₂,
    length_flatMap_const _ _ _ h₃, h₂, liftBit, List.length_cons, List.length_nil]
  omega

private inductive K | input | due | tmp | part | dueCopy | weight | jobs | out
  deriving DecidableEq

private inductive Lab
  | target | moveTarget | loop | readJob | copies | copyDue | restoreDue
  | emitPart | emitDue | emitWeight | endJobs | emitBound | output | done
  deriving DecidableEq

private def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .target => readFrame .input .tmp .target .moveTarget .done
  | .moveTarget => moveBits .tmp .due .moveTarget .loop
  | .loop => .peek .input (fun _ o => o.isSome) <|
      .branch id (.goto fun _ => .readJob)
        (.peek .due (fun _ o => o.isSome) <| .branch id
          (.peek .jobs (fun _ o => o.isSome) <|
            .branch id (.goto fun _ => .endJobs) (.goto fun _ => .done))
          (.goto fun _ => .endJobs))
  | .readJob => readFrame .input .tmp .readJob .copies .done
  | .copies => splitBits .tmp .part .weight .copies .copyDue
  | .copyDue => moveBits .due .tmp .copyDue .restoreDue
  | .restoreDue => splitBits .tmp .due .dueCopy .restoreDue .emitPart
  | .emitPart => writeBits .part .jobs lift₃ (lift₂ false) .emitPart .emitDue
  | .emitDue => writeBits .dueCopy .jobs lift₃ (lift₂ false) .emitDue .emitWeight
  | .emitWeight => writeBits .weight .jobs lift₂ (liftBit false) .emitWeight .loop
  | .endJobs => emit .jobs [false] .emitBound
  | .emitBound => moveBits .due .jobs .emitBound .output
  | .output => moveBits .jobs .out .output .done
  | .done => .halt


private def st (input due jobs : List Bool) : K → List Bool
  | .input => input
  | .due => due
  | .jobs => jobs
  | _ => []

private theorem round_run (p r d acc : List Bool) (v : Bool) :
    ∃ v', Run prog (4 * p.length + 3 * d.length + 8)
      ⟨some .loop, v, st (delimit p ++ r) d acc⟩
      ⟨some .loop, v', st r d ((triple p d).reverse ++ acc)⟩ := by
  let S := st (delimit p ++ r) d acc
  have h₀ : Run prog 1 ⟨some .loop, v, S⟩ ⟨some .readJob, true, S⟩ := by
    apply Run.single
    cases p <;> rfl
  have h₁ := readFrame_run (M := prog) (self := Lab.readJob)
    (a := K.input) (b := K.tmp) (next := .copies) (bad := .done) rfl
    (by decide) true S p r rfl
  let S₁ := update (update S K.input r) K.tmp (p.reverse ++ S .tmp)
  have h₂ := splitBits_run (M := prog) (self := Lab.copies) (s := K.tmp)
    (a := K.part) (b := K.weight) (next := .copyDue) rfl
    (by decide) (by decide) (by decide) false S₁
  let S₂ := update (update (update S₁ K.tmp []) K.part ((S₁ .tmp).reverse ++ S₁ .part))
    K.weight ((S₁ .tmp).reverse ++ S₁ .weight)
  obtain ⟨v₃, h₃⟩ := moveBits_run (M := prog) (self := Lab.copyDue)
    (a := K.due) (b := K.tmp) (next := .restoreDue) rfl (by decide) false S₂
  let S₃ := update (update S₂ K.due []) K.tmp ((S₂ .due).reverse ++ S₂ .tmp)
  have h₄ := splitBits_run (M := prog) (self := Lab.restoreDue) (s := K.tmp)
    (a := K.due) (b := K.dueCopy) (next := .emitPart) rfl
    (by decide) (by decide) (by decide) v₃ S₃
  let S₄ := update (update (update S₃ K.tmp []) K.due ((S₃ .tmp).reverse ++ S₃ .due))
    K.dueCopy ((S₃ .tmp).reverse ++ S₃ .dueCopy)
  have h₅ := writeBits_run (M := prog) (self := Lab.emitPart) (a := K.part)
    (b := K.jobs) (next := .emitDue) (chunk := lift₃) (suffix := lift₂ false)
    rfl (by decide) false S₄
  let S₅ := update (update S₄ K.part []) K.jobs
    (((S₄ .part).flatMap lift₃ ++ lift₂ false).reverse ++ S₄ .jobs)
  have h₆ := writeBits_run (M := prog) (self := Lab.emitDue) (a := K.dueCopy)
    (b := K.jobs) (next := .emitWeight) (chunk := lift₃) (suffix := lift₂ false)
    rfl (by decide) false S₅
  let S₆ := update (update S₅ K.dueCopy []) K.jobs
    (((S₅ .dueCopy).flatMap lift₃ ++ lift₂ false).reverse ++ S₅ .jobs)
  have h₇ := writeBits_run (M := prog) (self := Lab.emitWeight) (a := K.weight)
    (b := K.jobs) (next := .loop) (chunk := lift₂) (suffix := liftBit false)
    rfl (by decide) false S₆
  refine ⟨false, ?_⟩
  have hr := h₀.trans h₁ |>.trans h₂ |>.trans h₃ |>.trans h₄ |>.trans h₅ |>.trans h₆ |>.trans h₇
  have htime : 1 + (p.length + 1) + ((S₁ .tmp).length + 1) + ((S₂ .due).length + 1) +
      ((S₃ .tmp).length + 1) + ((S₄ .part).length + 1) + ((S₅ .dueCopy).length + 1) +
      ((S₆ .weight).length + 1) = 4 * p.length + 3 * d.length + 8 := by
    simp [S₆, S₅, S₄, S₃, S₂, S₁, S, st]
    omega
  convert hr.of_eq htime using 2
  funext k
  cases k <;> simp [st, S₆, S₅, S₄, S₃, S₂, S₁, S, triple,
    List.reverse_append, List.append_assoc]

private def finish (d acc : List Bool) (ps : List (List Bool)) : List Bool :=
  let pre := acc.reverse ++ ps.flatMap (triple · d)
  if pre = [] ∧ d ≠ [] then [] else pre ++ [false] ++ d

private theorem finish_cons (d acc p : List Bool) (ps : List (List Bool)) :
    finish d acc (p :: ps) = finish d ((triple p d).reverse ++ acc) ps := by
  simp [finish, List.reverse_append, List.append_assoc]

private theorem end_run (d acc : List Bool) (v : Bool) :
    ∃ v' S, RunLe prog (acc.length + 2 * d.length + 5)
      ⟨some .loop, v, st [] d acc⟩ ⟨some .done, v', S⟩ ∧
        S .out = finish d acc [] := by
  by_cases h : acc = [] ∧ d ≠ []
  · rcases h with ⟨rfl, hd⟩
    refine ⟨false, st [] d [], (Run.single ?_).le (by omega), by simp [st, finish, hd]⟩
    obtain ⟨b, ds, rfl⟩ := List.exists_cons_of_ne_nil hd
    rfl
  · let S := st [] d acc
    let S₁ := update S K.jobs (false :: acc)
    have h₁ : ∃ v₁, Run prog 1 ⟨some .loop, v, S⟩ ⟨some .endJobs, v₁, S⟩ := by
      cases d with
      | nil => exact ⟨false, Run.single rfl⟩
      | cons b ds =>
        cases acc with
        | nil => simp at h
        | cons c cs => exact ⟨true, Run.single rfl⟩
    obtain ⟨v₁, h₁⟩ := h₁
    have h₂ : Run prog 1 ⟨some .endJobs, v₁, S⟩ ⟨some .emitBound, v₁, S₁⟩ :=
      Run.single rfl
    obtain ⟨v₃, h₃⟩ := moveBits_run (M := prog) (self := Lab.emitBound)
      (a := K.due) (b := K.jobs) (next := .output) rfl (by decide) v₁ S₁
    let S₃ := update (update S₁ K.due []) K.jobs ((S₁ .due).reverse ++ S₁ .jobs)
    obtain ⟨v₄, h₄⟩ := moveBits_run (M := prog) (self := Lab.output)
      (a := K.jobs) (b := K.out) (next := .done) rfl (by decide) v₃ S₃
    refine ⟨v₄, _, (h₁.trans h₂ |>.trans h₃ |>.trans h₄).le ?_, ?_⟩
    · simp [S₃, S₁, S, st]
      omega
    · simp [S₃, S₁, S, st, finish, List.reverse_append, h]

private def transform (x : List Bool) : List Bool :=
  match undelimit x with
  | none => []
  | some (d, r) =>
    match undelimitBlocks r with
    | none => []
    | some ps => finish d [] ps

private theorem loop_run (d : List Bool) : ∀ (n : ℕ) (r acc : List Bool) (v : Bool),
    r.length ≤ n →
    ∃ v' S, RunLe prog (acc.length + 40 * (r.length + 1) * (d.length + 1))
      ⟨some .loop, v, st r d acc⟩ ⟨some .done, v', S⟩ ∧
        S .out = ((undelimitBlocksAux n r).map (finish d acc)).getD [] := by
  intro n
  induction n with
  | zero =>
    intro r acc v hn
    have hr : r = [] := by simpa using hn
    subst r
    obtain ⟨v', S, hr, hout⟩ := end_run d acc v
    exact ⟨v', S, hr.mono (by simp; omega), by simpa [undelimitBlocksAux] using hout⟩
  | succ n ih =>
    intro r acc v hn
    cases r with
    | nil =>
      obtain ⟨v', S, hr, hout⟩ := end_run d acc v
      exact ⟨v', S, hr.mono (by simp; omega), by simpa [undelimitBlocksAux] using hout⟩
    | cons b bs =>
      generalize hr : b :: bs = r at *
      have h₀ : Run prog 1 ⟨some .loop, v, st r d acc⟩
          ⟨some .readJob, true, st r d acc⟩ := by rw [← hr]; exact Run.single rfl
      have hAux : undelimitBlocksAux (n + 1) r =
          (undelimit r).bind fun p => (undelimitBlocksAux n p.2).map (p.1 :: ·) := by
        rw [← hr]; rfl
      cases hd : undelimit r with
      | none =>
        obtain ⟨v', S, hbad, hk⟩ := readFrame_bad (M := prog) (a := K.input) (b := K.tmp)
          (self := Lab.readJob) (next := .copies) (bad := .done) rfl (by decide) r true
          (st r d acc) rfl hd
        have hout : S .out = [] := hk .out (by decide) (by decide)
        refine ⟨v', S, (h₀.le le_rfl |>.trans hbad).mono ?_, ?_⟩
        · nlinarith
        · simp [hAux, hd, hout]
      | some pair =>
        obtain ⟨p, r'⟩ := pair
        have he := (Cslib.CookLevin.undelimit_eq_some_iff r p r').1 hd
        rw [he] at hn ⊢
        rw [he] at hAux hd
        have hlen : (delimit p ++ r').length = 2 * p.length + 1 + r'.length := by simp
        obtain ⟨v₁, h₁⟩ := round_run p r' d acc v
        obtain ⟨v₂, S, h₂, hout⟩ := ih r' ((triple p d).reverse ++ acc) v₁ (by omega)
        refine ⟨v₂, S, (h₁.le le_rfl |>.trans h₂).mono ?_, ?_⟩
        · rw [hlen]
          simp only [List.length_append, List.length_reverse, triple_length]
          nlinarith
        · rw [hout, hAux, hd]
          cases h : undelimitBlocksAux n r' <;> simp [h, finish_cons]

private theorem run (x : List Bool) :
    ∃ v S, RunLe prog (45 * (x.length + 1) ^ 2)
      ⟨some .target, false, update (fun _ => []) .input x⟩
      ⟨some .done, v, S⟩ ∧ S .out = transform x := by
  have hinit : update (fun _ => []) K.input x = st x [] [] := by
    funext k
    cases k <;> rfl
  rw [hinit]
  cases h : undelimit x with
  | none =>
    obtain ⟨v, S, hr, hk⟩ := readFrame_bad (M := prog) (a := K.input) (b := K.tmp)
      (self := Lab.target) (next := .moveTarget) (bad := .done) rfl (by decide)
      x false (st x [] []) rfl h
    refine ⟨v, S, hr.mono ?_, ?_⟩
    · nlinarith
    · simpa [transform, h, st] using hk .out (by decide) (by decide)
  | some pair =>
    obtain ⟨d, r⟩ := pair
    obtain rfl := (Cslib.CookLevin.undelimit_eq_some_iff x d r).1 h
    let S := st (delimit d ++ r) [] []
    let T := update (update S K.input r) K.tmp (d.reverse ++ S .tmp)
    have h₁ := readFrame_run (M := prog) (a := K.input) (b := K.tmp)
      (self := Lab.target) (next := .moveTarget) (bad := .done) rfl (by decide)
      false S d r rfl
    obtain ⟨v₁, h₂⟩ := moveBits_run (M := prog) (a := K.tmp) (b := K.due)
      (self := Lab.moveTarget) (next := .loop) rfl (by decide) false T
    have he : update (update T K.tmp []) K.due ((T .tmp).reverse ++ T .due) =
        st r d [] := by
      funext k
      cases k <;> simp [T, S, st]
    rw [he] at h₂
    obtain ⟨v₂, U, hr, hout⟩ := loop_run d r.length r [] v₁ le_rfl
    refine ⟨v₂, U, ((h₁.trans h₂).le le_rfl |>.trans hr).mono ?_, ?_⟩
    · simp [length_delimit, T, S, st]
      nlinarith
    · rw [hout, transform, h]
      simp only [undelimitBlocks]
      cases undelimitBlocksAux r.length r <;> rfl

private def ks : List K := [.input, .due, .tmp, .part, .dueCopy, .weight, .jobs, .out]

private noncomputable instance kFintype : Fintype K :=
  Fintype.ofList ks (fun k => by cases k <;> decide)

private noncomputable instance labFintype : Fintype Lab :=
  Fintype.ofList [.target, .moveTarget, .loop, .readJob, .copies, .copyDue, .restoreDue,
    .emitPart, .emitDue, .emitWeight, .endJobs, .emitBound, .output, .done]
    (fun l => by cases l <;> decide)

private noncomputable def comp : Host.Comp where
  K := K
  Γ := fun _ => Bool
  L := Lab
  prog := prog
  ks := ks
  ks_nodup := by decide
  mem_ks := fun k => by cases k <;> decide

private theorem transform_poly : ComplexityTheory.IsPolyTime transform :=
  Host.isPolyTime_reduction (c := comp) (cX := .input) (cO := .out)
    (gX := id) (start := .target) (done := .done) (Equiv.refl Bool)
    transform (Polynomial.C 45 * (Polynomial.X + 1) ^ 2)
    rfl fun x => by
      obtain ⟨v, S, hr, ho⟩ := run x
      refine ⟨v, S, ?_, ?_⟩
      · change RunLe prog _ ⟨some .target, false, update (fun _ => []) .input (x.map id)⟩
          ⟨some .done, v, S⟩
        rw [List.map_id]
        exact hr.mono (by simp)
      · change S .out = (transform x).map id
        rwa [List.map_id]

private theorem transform_encodeSS (as : List ℕ) (t : ℕ) (h : as ≠ [] ∨ t = 0) :
    transform (encodeSS as t) = bitEncode (as.map (fun a => (a, t, a)), t) := by
  have hs : undelimitBlocks
      (as.flatMap (fun a => delimit (encodeNat a))) = some (as.map encodeNat) := by
    simpa only [List.flatMap_def, List.map_map, Function.comp_def]
      using undelimitBlocks_flatten_delimit (as.map encodeNat)
  rw [encodeSS, transform, undelimit_delimit]
  simp only [hs]
  have encode_pair {α β : Type} [BitstringEncoding α] [BitstringEncoding β] (a : α) (b : β) :
      bitEncode (a, b) = delimit (bitEncode a) ++ bitEncode b := rfl
  have encode_list {α : Type} [BitstringEncoding α] (as : List α) :
      bitEncode as = ((as.map bitEncode).map delimit).flatten := rfl
  simp only [finish, List.reverse_nil, List.nil_append, List.flatMap_map, triple_eq,
    encode_pair, encode_list, BinaryNatEncoding.bitEncode_nat, List.map_map, Function.comp_def,
    ← List.flatMap_def, List.append_assoc]
  conv_rhs => rw [delimit_eq, liftBits_flatMap, List.append_assoc]
  have hn : ¬ ((as.flatMap fun a => liftBits (delimit (delimit (encodeNat a) ++
      (delimit (encodeNat t) ++ encodeNat a)))) = [] ∧ encodeNat t ≠ []) := by
    rintro ⟨hnil, hnonzero⟩
    rcases h with has | rfl
    · cases as with
      | nil => simp at has
      | cons a as =>
        have hn₁ := (List.append_eq_nil_iff.mp hnil).1
        rcases he : delimit (delimit (encodeNat a) ++
            (delimit (encodeNat t) ++ encodeNat a)) with _ | ⟨b, bs⟩
        · have hh := length_delimit (delimit (encodeNat a) ++
            (delimit (encodeNat t) ++ encodeNat a))
          simp [he] at hh
        · dsimp only at hn₁
          rw [he] at hn₁
          simp [liftBits, liftBit] at hn₁
    · exact hnonzero rfl
  rw [ite_eq_right hn]
  rfl

private theorem transform_noSS : transform noSS = [] := by decide

private theorem reduce_correct (x : List Bool) :
    Partition.partitionDec x =
      weightedTardyJobsDec (transform (Partition.reduceToSubsetSum x)) := by
  classical
  cases h : bitDecode (α := List ℕ) x with
  | none =>
    rw [Partition.partitionDec, Partition.reduceToSubsetSum, h, transform_noSS]
    rfl
  | some as =>
    have hs : as.map (· * 2) ≠ [] ∨ as.sum = 0 := by cases as <;> simp
    rw [Partition.partitionDec, Partition.reduceToSubsetSum, h, transform_encodeSS _ _ hs,
      weightedTardyJobsDec, bitDecode_bitEncode]
    have he : ((as.map (· * 2)).map fun a => (a, as.sum, a), as.sum) =
        partitionJobs as := by simp [partitionJobs, job, List.map_map, Function.comp_def,
        Nat.mul_comm]
    rw [he]
    exact Bool.eq_iff_iff.mpr (by simp [partitionJobs_correct])

private theorem hardness : NPHard weightedTardyJobsDec := by
  refine NPHard.of_polyManyOneRed Partition.partition_npComplete.2
    ⟨transform ∘ Partition.reduceToSubsetSum, ?_, reduce_correct⟩
  obtain ⟨f⟩ := Partition.MembershipMachine.isPolyTime_reduceToSubsetSum
  obtain ⟨g⟩ := transform_poly
  exact tm2ComputableInPolyTime_comp f g

end Reduction

/-! ### Schedule certificates

A true bit skips one remaining job. A false bit schedules the next job,
removes it, and restarts at the front of the remaining jobs. The certificate
ends when every job has been scheduled. Each pass uses at most one bit per
remaining job.
-/

namespace Verification

open Computability

private abbrev Job := ℕ × ℕ × ℕ

private def plan {α : Type} : List Bool → List α → List α → Option (List α)
  | [], jobs, skipped => if jobs.isEmpty && skipped.isEmpty then some [] else none
  | _ :: _, [], _ => none
  | true :: w, j :: jobs, skipped => plan w jobs (j :: skipped)
  | false :: w, j :: jobs, skipped => (plan w (skipped.reverse ++ jobs) []).map (j :: ·)

private theorem plan_perm {α : Type} {w : List Bool} {jobs skipped result : List α}
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

private theorem plan_skip {α : Type} (s jobs skipped : List α) (w : List Bool) :
    plan (List.replicate s.length true ++ w) (s ++ jobs) skipped =
      plan w jobs (s.reverse ++ skipped) := by
  induction s generalizing skipped with
  | nil => rfl
  | cons a s ih =>
    rw [List.length_cons, List.replicate_succ, List.cons_append, List.cons_append, plan]
    simpa only [List.reverse_cons, List.append_assoc, List.singleton_append]
      using ih (a :: skipped)

private theorem plan_exists {α : Type} {jobs result : List α} (h : result.Perm jobs) :
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

private def jobStep (acc : ℕ × ℕ) (j : Job) : ℕ × ℕ :=
  let t := acc.1 + j.1
  (t, acc.2 + if j.2.1 < t then j.2.2 else 0)

private theorem feasible_iff (jobs : List Job) (k : ℕ) :
    WeightedTardyJobsFeasible (jobs, k) ↔
      ∃ ord : List Job, ord.Perm jobs ∧ (ord.foldl jobStep (0, 0)).2 ≤ k := by
  let f := (jobs.getD · (0, 0, 0))
  have hmap (order : List ℕ) :
      WeightedTardy jobs order = ((order.map f).foldl jobStep (0, 0)).2 := by
    rw [List.foldl_map]
    rfl
  constructor
  · rintro ⟨order, hperm, hcost⟩
    refine ⟨order.map f, ?_, ?_⟩
    · simpa only [f, map_range_getD] using hperm.map f
    · rwa [← hmap]
  · rintro ⟨ord, hperm, hcost⟩
    have hj : (List.range jobs.length).map f = jobs := map_range_getD jobs (0, 0, 0)
    rw [← hj] at hperm
    have hl : ∃ order : List ℕ, ord = order.map f ∧ order.Perm (List.range jobs.length) := by
      have ht : (Relation.Comp (· = List.map f ·) List.Perm) ord
          (List.range jobs.length) := by
        have he := congrFun (congrFun (List.eq_map_comp_perm f) ord) (List.range jobs.length)
        exact Eq.mpr he hperm
      exact ht
    obtain ⟨order, rfl, hp⟩ := hl
    exact ⟨order, hp, (hmap _).symm ▸ hcost⟩

private def pack (ps : List (List Bool)) : List Bool := (ps.map delimit).flatten

private theorem pack_cons (p : List Bool) (ps : List (List Bool)) :
    pack (p :: ps) = delimit p ++ pack ps := rfl

private theorem parse_pack_prefix (p r : List Bool) :
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

private def decodeJob (p : List Bool) : Option Job :=
  (undelimit p).bind fun (a, r) =>
    (undelimit r).map fun (d, b) => (decodeNat a, decodeNat d, decodeNat b)

private theorem bitDecode_pair {α β : Type} [BitstringEncoding α] [BitstringEncoding β]
    (p : List Bool) : bitDecode (α := α × β) p =
      match undelimit p with
      | none => none
      | some (a, b) =>
        match bitDecode (α := α) a, bitDecode (α := β) b with
        | some j, some k => some (j, k)
        | _, _ => none := rfl

private theorem bitDecode_nat (p : List Bool) :
    bitDecode (α := ℕ) p = some (decodeNat p) := rfl

private theorem decodeJob_eq (p : List Bool) : decodeJob p = bitDecode p := by
  simp only [decodeJob, bitDecode_pair, bitDecode_nat]
  cases hp : undelimit p with
  | none => rfl
  | some pr =>
    obtain ⟨a, r⟩ := pr
    simp only [Option.bind]
    cases undelimit r <;> simp

private def decodeJobs (r : List Bool) : Option (List Job) :=
  (undelimitBlocks r).bind (List.mapM decodeJob)

private theorem decodeJobs_eq (r : List Bool) : decodeJobs r = bitDecode r := by
  change _ = (undelimitBlocks r).bind (List.mapM bitDecode)
  simp only [decodeJobs, funext decodeJob_eq]

private theorem decodeJobs_frame (p r : List Bool) :
    decodeJobs (delimit p ++ r) =
      (decodeJob p).bind fun j => (decodeJobs r).map (j :: ·) := by
  unfold decodeJobs
  rw [parse_pack_prefix]
  cases h : undelimitBlocks r with
  | none => cases decodeJob p <;> rfl
  | some ps =>
    rw [Option.map_some, Option.bind, List.mapM_cons]
    cases decodeJob p <;> cases h₂ : List.mapM decodeJob ps <;> simp [h₂]

private theorem decodeJobs_prefix (ps : List (List Bool)) (r : List Bool) :
    decodeJobs (pack ps ++ r) =
      (ps.mapM decodeJob).bind fun pre => (decodeJobs r).map (pre ++ ·) := by
  induction ps with
  | nil =>
    simp only [pack, List.map_nil, List.flatten_nil, List.nil_append, List.mapM_nil]
    cases decodeJobs r <;> rfl
  | cons p ps ih =>
    rw [pack_cons, List.append_assoc, decodeJobs_frame, ih]
    rw [List.mapM_cons]
    cases decodeJob p <;> cases ps.mapM decodeJob <;> cases decodeJobs r <;> rfl

private theorem decodeJobs_nil_iff (r : List Bool) : decodeJobs r = some [] ↔ r = [] := by
  constructor
  · unfold decodeJobs
    intro h
    obtain ⟨ps, hp, hm⟩ := Option.bind_eq_some_iff.mp h
    cases ps with
    | nil => exact Cslib.Complexity.PolynomialEncoding.blocks_decode_sound hp
    | cons p ps =>
      cases h : decodeJob p <;> cases hs : ps.mapM decodeJob <;>
        simp [List.mapM_cons, h, hs] at hm
  · rintro rfl
    rfl

private def checkLoop : List Bool → List Bool → List (List Bool) → (ℕ × ℕ) → ℕ → Bool
  | [], raw, skipped, acc, k => raw.isEmpty && skipped.isEmpty && decide (acc.2 ≤ k)
  | b :: w, raw, skipped, acc, k =>
      match undelimit raw with
      | none => false
      | some (p, tail) =>
        if b then checkLoop w tail (p :: skipped) acc k
        else match decodeJob p with
          | none => false
          | some j => checkLoop w (pack skipped.reverse ++ tail) [] (jobStep acc j) k

private def check (x w : List Bool) : Bool :=
  match undelimit x with
  | none => false
  | some (raw, k) => checkLoop w raw [] (0, 0) (decodeNat k)

private def evalPlan (w : List Bool) (r skipped : List Job) (acc : ℕ × ℕ) (k : ℕ) : Bool :=
  match plan w r skipped with
  | none => false
  | some ord => decide ((ord.foldl jobStep acc).2 ≤ k)

private theorem checkLoop_eq (w r : List Bool) (s : List (List Bool)) (acc : ℕ × ℕ) (k : ℕ) :
    checkLoop w r s acc k =
      ((decodeJobs r).bind fun rs =>
        (s.mapM decodeJob).map fun ss => evalPlan w rs ss acc k).getD false := by
  induction w generalizing r s acc with
  | nil =>
    cases r with
    | nil =>
      cases s with
      | nil => rfl
      | cons p s =>
        cases hp : decodeJob p <;> cases hs : s.mapM decodeJob <;>
          simp [checkLoop, decodeJobs, undelimitBlocks, undelimitBlocksAux, hp, hs,
            List.mapM_cons, evalPlan, plan]
    | cons b r =>
      cases hr : decodeJobs (b :: r) with
      | none => rfl
      | some rs =>
        cases rs with
        | nil => simp [decodeJobs_nil_iff] at hr
        | cons j rs =>
          cases s.mapM decodeJob <;> simp [checkLoop, evalPlan, plan]
  | cons b w ih =>
    cases hr : undelimit r with
    | none =>
      cases hd : decodeJobs r with
      | none => simp [checkLoop, hr]
      | some js =>
        cases js with
        | nil =>
          rw [checkLoop, hr]
          cases s.mapM decodeJob <;> rfl
        | cons j js =>
          obtain ⟨ps, hp, hm⟩ := Option.bind_eq_some_iff.mp hd
          have he : r = pack ps := Cslib.Complexity.PolynomialEncoding.blocks_decode_sound hp
          cases ps with
          | nil => simp at hm
          | cons p ps => simp [he, pack_cons] at hr
    | some p =>
      obtain ⟨p, tail⟩ := p
      obtain rfl := (Cslib.CookLevin.undelimit_eq_some_iff r p tail).1 hr
      have hrev : s.reverse.mapM decodeJob = (s.mapM decodeJob).map List.reverse := by
        induction s with
        | nil => rfl
        | cons j s ih =>
          rw [List.reverse_cons, List.mapM_append, ih]
          cases h₁ : decodeJob j <;> cases h₂ : s.mapM decodeJob <;>
            simp [List.mapM_cons, h₁, h₂]
      cases b <;>
        simp only [checkLoop, undelimit_delimit, Bool.false_eq_true, ↓reduceIte,
          decodeJobs_frame, evalPlan, ih, decodeJobs_prefix, hrev, List.mapM_cons]
      all_goals
        cases decodeJob p <;> cases decodeJobs tail <;> cases s.mapM decodeJob <;>
          simp only [Option.bind_none, Option.bind_some, Option.map_none, Option.map_some,
            Option.getD_none, Option.getD_some, List.mapM_nil, plan]
      all_goals try rfl
      rename_i j jobs skipped
      cases hplan : plan w (skipped.reverse ++ jobs) [] with
      | none => simp [hplan]
      | some _ =>
        simp [hplan]
        rfl

end Verification

/-! ### Binary addition and comparison on stacks -/

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

namespace Verification

open Computability

private theorem jobs_length_le {r : List Bool} {jobs : List Job}
    (h : decodeJobs r = some jobs) : jobs.length ≤ r.length := by
  obtain ⟨ps, hp, hm⟩ := Option.bind_eq_some_iff.mp h
  rw [Cslib.Complexity.PolynomialEncoding.blocks_decode_sound hp]
  have hlength : jobs.length = ps.length := by
    clear h hp r
    induction ps generalizing jobs with
    | nil => simp at hm; simp [← hm]
    | cons p ps ih =>
      rw [List.mapM_cons] at hm
      cases h : decodeJob p with
      | none => simp [h] at hm
      | some j =>
        cases hs : ps.mapM decodeJob with
        | none => simp [h, hs] at hm
        | some rest =>
          have hj : jobs = j :: rest := by simpa [h, hs] using hm.symm
          simp [hj, ih hs]
  rw [hlength]
  exact length_le_length_flatten_delimit ps

private theorem check_iff (x : List Bool) : weightedTardyJobsDec x = true ↔
    ∃ w : List Bool, w.length ≤ x.length ^ 2 ∧ check x w = true := by
  classical
  rw [weightedTardyJobsDec, bitDecode_pair]
  simp only [bitDecode_nat, ← decodeJobs_eq]
  cases h : undelimit x with
  | none => simp [check, h]
  | some pair =>
    obtain ⟨r, k⟩ := pair
    obtain rfl := (Cslib.CookLevin.undelimit_eq_some_iff x r k).1 h
    simp only [check, undelimit_delimit, checkLoop_eq, List.mapM_nil]
    cases hj : decodeJobs r with
    | none => simp
    | some jobs =>
      change decide (WeightedTardyJobsFeasible (jobs, decodeNat k)) = true ↔
        ∃ w : List Bool, w.length ≤ (delimit r ++ k).length ^ 2 ∧
          evalPlan w jobs [] (0, 0) (decodeNat k) = true
      rw [decide_eq_true_eq, feasible_iff]
      constructor
      · rintro ⟨ord, hp, ht⟩
        obtain ⟨w, hw, hs⟩ := plan_exists hp
        have hl := jobs_length_le hj
        have hx : jobs.length ≤ (delimit r ++ k).length := by
          simp only [List.length_append, length_delimit]
          omega
        rw [hp.length_eq, ← pow_two] at hw
        exact ⟨w, hw.trans (Nat.pow_le_pow_left hx _), by simp [evalPlan, hs, ht]⟩
      · rintro ⟨w, _, hw⟩
        cases hs : plan w jobs [] with
        | none => simp [evalPlan, hs] at hw
        | some ord =>
          exact ⟨ord, by simpa using plan_perm hs, by simpa [evalPlan, hs] using hw⟩

end Verification

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

namespace Verification

open Computability Cslib.Complexity.Karp Cslib.Complexity.FramedCNF

/-! ### The verifier machine

The verifier stores the skipped prefix in reverse so it can restore the
prefix when a job is selected. It normalizes number payloads according to
the repository decoder before doing arithmetic. The remaining encoded jobs
pay for any increase in the bit lengths of the elapsed time and tardy weight.
-/

private inductive K
  | jobs | witness | skipped | elapsed | cost | bound | tmp | payload
  | processRev | dueRev | operand | elapsedCopy | sum
  deriving DecidableEq

private inductive Field | bound | process | due | weight
  deriving DecidableEq

private inductive Lab
  | start | reverseBound | restoreJobs | loop
  | read (skip : Bool) | restorePayload (skip : Bool) | skip | restoreSkipped
  | readProcess | readDue
  | norm (f : Field) | normMove (f : Field)
  | addStart (penalty : Bool) | add (penalty : Bool)
  | carry (penalty : Bool) | store (penalty : Bool)
  | compareStart (final : Bool) | compare (final : Bool) | compareDone (final : Bool)
  | discardWeight | reverseWeight | yes | no
  deriving DecidableEq

private def normSource : Field → K
  | .bound | .process => .processRev
  | .due => .dueRev
  | .weight => .tmp

private def normTarget : Field → K
  | .bound => .bound
  | _ => .operand

private def normNext : Field → Lab
  | .bound => .loop
  | .process => .addStart false
  | .due => .compareStart false
  | .weight => .addStart true

private def addTarget (penalty : Bool) : K := if penalty then .cost else .elapsed

private def cmpLeft (final : Bool) : K := if final then .cost else .elapsedCopy

private def cmpRight (final : Bool) : K := if final then .bound else .operand

private def yesNo (ok : Bool) : Lab := if ok then .yes else .no

private def cmpNext (final gt : Bool) : Lab :=
  if final then yesNo (!gt) else if gt then .reverseWeight else .discardWeight

private def prog : Lab → TM2.Stmt (fun _ : K => Bool) Lab Bool
  | .start => readFrame .jobs .tmp .start .reverseBound .no
  | .reverseBound => moveBits .jobs .processRev .reverseBound .restoreJobs
  | .restoreJobs => moveBits .tmp .jobs .restoreJobs (.norm .bound)
  | .loop => .peek .witness (fun _ o => o.isSome) <| .branch id
      (.pop .witness (fun _ o => o.getD false) (.goto Lab.read))
      (.peek .jobs (fun _ o => o.isSome) <| .branch id (.goto fun _ => .no)
        (.peek .skipped (fun _ o => o.isSome) <| .branch id
          (.goto fun _ => .no) (.goto fun _ => .compareStart true)))
  | .read skip => readFrame .jobs .tmp (.read skip) (.restorePayload skip) .no
  | .restorePayload skip => moveBits .tmp .payload (.restorePayload skip)
      (if skip then .skip else .restoreSkipped)
  | .skip => writeBits .payload .skipped Reduction.liftBit [false] .skip .loop
  | .restoreSkipped => moveBits .skipped .jobs .restoreSkipped .readProcess
  | .readProcess => readFrame .payload .processRev .readProcess .readDue .no
  | .readDue => readFrame .payload .dueRev .readDue (.norm .process) .no
  | .norm f => normalizeRev (normSource f) (.normMove f)
  | .normMove f => moveBits (normSource f) (normTarget f) (.normMove f) (normNext f)
  | .addStart penalty => .load (fun _ => false) (.goto fun _ => .add penalty)
  | .add penalty => zipDigits (addTarget penalty) .operand .sum addDigit
      (.add penalty) (.carry penalty)
  | .carry penalty => pushCarry .sum (.store penalty)
  | .store false => splitBits .sum .elapsed .elapsedCopy (.store false) (.norm .due)
  | .store true => moveBits .sum .cost (.store true) .loop
  | .compareStart final => .load (fun _ => false) (.goto fun _ => .compare final)
  | .compare final => zipDigits (cmpLeft final) (cmpRight final) .sum compareDigit
      (.compare final) (.compareDone final)
  | .compareDone final => .goto (cmpNext final)
  | .discardWeight => cleanS [.payload] .discardWeight .loop
  | .reverseWeight => moveBits .payload .tmp .reverseWeight (.norm .weight)
  | .yes | .no => .halt

private def st (r w : List Bool) (skipped : List (List Bool)) (acc : ℕ × ℕ) (k : ℕ) : K → List Bool
  | .jobs => r
  | .witness => w
  | .skipped => (pack skipped.reverse).reverse
  | .elapsed => encodeNat acc.1
  | .cost => encodeNat acc.2
  | .bound => encodeNat k
  | _ => []

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

private theorem encodeNat_add_length (x y : ℕ) :
    (encodeNat (x + y)).length ≤ (encodeNat x).length + (encodeNat y).length + 1 := by
  have h := SSVerify.length_addB false (encodeNat x) (encodeNat y)
  rwa [SSVerify.addB_encodeNat, Bool.toNat_false, Nat.add_zero] at h

private theorem decoded_length (p : List Bool) :
    (encodeNat (decodeNat p)).length ≤ p.length + 1 := by
  rw [← normalizeNat_eq_encode_decode]
  exact length_normalizeNat_le p

private theorem pack_append (xs ys : List (List Bool)) : pack (xs ++ ys) = pack xs ++ pack ys := by
  simp [pack]

private def budget (r : List Bool) (s : List (List Bool)) (acc : ℕ × ℕ) (k : ℕ) : ℕ :=
  6 * (r.length + (pack s.reverse).length) +
    (encodeNat acc.1).length + (encodeNat acc.2).length + (encodeNat k).length


private def loaded (r w a d b : List Bool) (acc : ℕ × ℕ) (k : ℕ) : K → List Bool :=
  update (update (update (st r w [] acc k) .processRev a.reverse) .dueRev d.reverse) .payload b

private theorem loaded_run (r w a d b : List Bool) (acc : ℕ × ℕ) (k : ℕ) (v : Bool) :
    ∃ v', RunLe prog (32 * (a.length + d.length + b.length +
      (encodeNat acc.1).length + (encodeNat acc.2).length + 1))
      ⟨some (.norm .process), v, loaded r w a d b acc k⟩
      ⟨some .loop, v', st r w [] (jobStep acc (decodeNat a, decodeNat d, decodeNat b)) k⟩ := by
  let S := loaded r w a d b acc k
  let time := acc.1 + decodeNat a
  obtain ⟨v₁, h₁⟩ := norm_run .process a v S (by simp [S, loaded, normSource])
  let S₁ := update (update S K.processRev []) K.operand (encodeNat (decodeNat a) ++ S .operand)
  obtain ⟨v₂, h₂⟩ := start_add_run false acc.1 (decodeNat a) v₁ S₁
    (by simp [S₁, S, loaded, st, addTarget])
    (by simp [S₁, S, loaded, st]) (by simp [S₁, S, loaded, st])
  let S₂ := update (update (update S₁ (addTarget false) []) K.operand []) K.sum
    (encodeNat time).reverse
  have h₃ := splitBits_run (M := prog) (s := K.sum) (a := K.elapsed) (b := K.elapsedCopy)
    (self := Lab.store false) (next := .norm .due) rfl (by decide) (by decide) (by decide) v₂ S₂
  let S₃ := update (update (update S₂ K.sum []) K.elapsed ((S₂ .sum).reverse ++ S₂ .elapsed))
    K.elapsedCopy ((S₂ .sum).reverse ++ S₂ .elapsedCopy)
  obtain ⟨v₄, h₄⟩ := norm_run .due d false S₃
    (by simp [S₃, S₂, S₁, S, loaded, normSource, addTarget])
  let S₄ := update (update S₃ K.dueRev []) K.operand (encodeNat (decodeNat d) ++ S₃ .operand)
  have h₅ := start_cmp_run false time (decodeNat d) v₄ S₄
    (by simp [cmpLeft, S₄, S₃, S₂, S₁, S, loaded, st, addTarget])
    (by simp [cmpRight, S₄, S₃, S₂, S₁, S, loaded, st, addTarget])
  let S₅ := update (update S₄ (cmpLeft false) []) (cmpRight false) []
  have hrun := h₁.trans h₂ |>.trans (h₃.le le_rfl) |>.trans h₄ |>.trans h₅
  have ha := decoded_length a
  have hd := decoded_length d
  have hb := decoded_length b
  have ht := encodeNat_add_length acc.1 (decodeNat a)
  have hc := encodeNat_add_length acc.2 (decodeNat b)
  simp only [BinaryNatEncoding.length_encodeNat] at ha hd hb ht hc
  by_cases hlate : decodeNat d < time
  · rw [decide_eq_true hlate] at hrun
    obtain ⟨v₆, h₆⟩ := moveBits_run (M := prog) (self := Lab.reverseWeight)
      (a := K.payload) (b := K.tmp) (next := .norm .weight) rfl (by decide) true S₅
    let S₆ := update (update S₅ K.payload []) K.tmp ((S₅ .payload).reverse ++ S₅ .tmp)
    obtain ⟨v₇, h₇⟩ := norm_run .weight b v₆ S₆
      (by simp [S₆, S₅, S₄, S₃, S₂, S₁, S, loaded, st, cmpLeft, cmpRight, addTarget, normSource])
    let S₇ := update (update S₆ K.tmp []) K.operand (encodeNat (decodeNat b) ++ S₆ .operand)
    obtain ⟨v₈, h₈⟩ := start_add_run true acc.2 (decodeNat b) v₇ S₇
      (by simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, S, loaded, st, cmpLeft, cmpRight, addTarget])
      (by simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, S, loaded, st, cmpRight, addTarget])
      (by simp [S₇, S₆, S₅, S₄, S₃, S₂, S₁, S, loaded, st, cmpLeft, cmpRight, addTarget])
    let S₈ := update (update (update S₇ (addTarget true) []) K.operand []) K.sum
      (encodeNat (acc.2 + decodeNat b)).reverse
    obtain ⟨v₉, h₉⟩ := moveBits_run (M := prog) (self := Lab.store true)
      (a := K.sum) (b := K.cost) (next := .loop) rfl (by decide) v₈ S₈
    have he : update (update S₈ K.sum []) K.cost ((S₈ .sum).reverse ++ S₈ .cost) =
        st r w [] (jobStep acc (decodeNat a, decodeNat d, decodeNat b)) k := by
      funext j
      cases j <;> simp [S₈, S₇, S₆, S₅, S₄, S₃, S₂, S₁, S, loaded, st, cmpLeft, cmpRight,
        addTarget, jobStep, time, show decodeNat d < acc.1 + decodeNat a from hlate, pack]
    rw [he] at h₉
    refine ⟨v₉, (hrun.trans (h₆.le le_rfl) |>.trans h₇ |>.trans h₈ |>.trans
      (h₉.le le_rfl)).mono ?_⟩
    simp [S₈, S₅, S₄, S₃, S₂, S₁, S, loaded, cmpLeft, cmpRight, addTarget, time]
    omega
  · rw [decide_eq_false hlate] at hrun
    have h₆ := clean_run (M := prog) (ks := [K.payload]) (self := Lab.discardWeight)
      (next := .loop) rfl (by decide) b.length false S₅ (by
        intro j hj
        have hj' : j = .payload := by simpa using hj
        subst j
        simp [S₅, S₄, S₃, S₂, S₁, S, loaded, cmpLeft, cmpRight, addTarget])
    have he : (fun j => if j ∈ [K.payload] then [] else S₅ j) =
        st r w [] (jobStep acc (decodeNat a, decodeNat d, decodeNat b)) k := by
      funext j
      cases j <;> simp [S₅, S₄, S₃, S₂, S₁, S, loaded, st, cmpLeft, cmpRight, addTarget,
        jobStep, time, show ¬ decodeNat d < acc.1 + decodeNat a from hlate, pack]
    rw [he] at h₆
    refine ⟨false, (hrun.trans h₆).mono ?_⟩
    simp [S₂, time]
    omega


private theorem read_process_run (p r w : List Bool) (acc : ℕ × ℕ) (k : ℕ) (v : Bool) :
    ∃ v' T, RunLe prog (35 * (p.length + (encodeNat acc.1).length +
      (encodeNat acc.2).length + 1))
      ⟨some .readProcess, v, update (st r w [] acc k) .payload p⟩
      ⟨some (if (decodeJob p).isSome then .loop else .no), v', T⟩ ∧
        ∀ j, decodeJob p = some j → T = st r w [] (jobStep acc j) k := by
  let S := update (st r w [] acc k) .payload p
  cases hp : undelimit p with
  | none =>
    obtain ⟨v', T, h, _⟩ := readFrame_bad (M := prog) (self := Lab.readProcess)
      (next := .readDue) (bad := .no) (a := K.payload) (b := K.processRev)
      rfl (by decide) p v S (by simp [S]) hp
    refine ⟨v', T, ?_, ?_⟩
    · simpa [decodeJob, hp] using h.mono (by omega :
        p.length + 1 ≤ 35 * (p.length + (encodeNat acc.1).length +
          (encodeNat acc.2).length + 1))
    · simp [decodeJob, hp]
  | some pair =>
    obtain ⟨a, q⟩ := pair
    have hlin := (Cslib.CookLevin.undelimit_eq_some_iff p a q).1 hp
    let S₁ := update (update S K.payload q) K.processRev (a.reverse ++ S .processRev)
    have he₁ := readFrame_run (M := prog) (self := Lab.readProcess) (next := .readDue)
      (bad := .no) (a := K.payload) (b := K.processRev) rfl (by decide)
      v S a q (by simp [S, hlin])
    have hlen₁ : p.length = 2 * a.length + 1 + q.length := by simp [hlin]
    cases hq : undelimit q with
    | none =>
      obtain ⟨v', T, h₂, _⟩ := readFrame_bad (M := prog) (self := Lab.readDue)
        (next := .norm .process) (bad := .no) (a := K.payload) (b := K.dueRev)
        rfl (by decide) q false S₁ (by simp [S₁]) hq
      refine ⟨v', T, ?_, ?_⟩
      · simpa [decodeJob, hp, hq] using (he₁.le le_rfl |>.trans h₂).mono (by omega :
          a.length + 1 + (q.length + 1) ≤
            35 * (p.length + (encodeNat acc.1).length + (encodeNat acc.2).length + 1))
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
          loaded r w a d b acc k := by
        funext j
        cases j <;> simp [S₁, S, loaded, st]
      rw [he] at hr₂
      obtain ⟨v', hr₃⟩ := loaded_run r w a d b acc k false
      simp only [ht, Option.isSome_some, ↓reduceIte, Option.some.injEq]
      exact ⟨v', _, (he₁.le le_rfl |>.trans (hr₂.le le_rfl) |>.trans hr₃).mono (by omega),
        fun _ hj => hj ▸ rfl⟩

private theorem read_outer_job (skip : Bool) (p r w : List Bool) (s : List (List Bool))
    (acc : ℕ × ℕ) (k : ℕ) (v : Bool) :
    ∃ v', Run prog (2 * p.length + 3)
      ⟨some .loop, v, st (delimit p ++ r) (skip :: w) s acc k⟩
      ⟨some (if skip then .skip else .restoreSkipped), v', update (st r w s acc k) .payload p⟩ := by
  let S := st (delimit p ++ r) w s acc k
  have h₁ : Run prog 1 ⟨some .loop, v, st (delimit p ++ r) (skip :: w) s acc k⟩
      ⟨some (.read skip), skip, S⟩ := by
    apply Run.single
    have he : update (st (delimit p ++ r) (skip :: w) s acc k) K.witness w = S := by
      funext j
      cases j <;> rfl
    simpa only [prog, TM2.stepAux, st, List.head?_cons, List.tail_cons, Option.isSome_some,
      id_eq, Bool.cond_true, Option.getD_some] using
        congrArg (TM2.Cfg.mk (some (Lab.read skip)) skip) he
  have h₂ := readFrame_run (M := prog) (self := Lab.read skip) (next := .restorePayload skip)
    (bad := .no) (a := K.jobs) (b := K.tmp) rfl (by decide) skip S p r rfl
  let S₂ := update (update S K.jobs r) K.tmp (p.reverse ++ S .tmp)
  obtain ⟨v', h₃⟩ := moveBits_run (M := prog) (self := Lab.restorePayload skip) (a := K.tmp)
    (b := K.payload) (next := if skip then .skip else .restoreSkipped)
    rfl (by decide) false S₂
  have he : update (update S₂ K.tmp []) K.payload ((S₂ .tmp).reverse ++ S₂ .payload) =
      update (st r w s acc k) K.payload p := by
    funext j
    cases j <;> simp [S₂, S, st]
  rw [he] at h₃
  exact ⟨v', (h₁.trans h₂ |>.trans h₃).of_eq (by simp [S₂, S, st]; omega)⟩


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

private theorem skipped_isEmpty (s : List (List Bool)) :
    (pack s.reverse).reverse.isEmpty = s.isEmpty := by
  cases s with
  | nil => rfl
  | cons p ps =>
    have h := length_le_length_flatten_delimit (p :: ps).reverse
    rw [List.length_reverse, List.length_cons] at h
    have he : (pack (p :: ps).reverse).reverse ≠ [] := by
      intro he
      have hl := congrArg List.length he
      simp only [List.length_reverse, List.length_nil, pack] at hl
      omega
    exact List.isEmpty_eq_false_iff.mpr he

private theorem verify_loop {B : ℕ} (w : List Bool) :
    ∀ (r : List Bool) (s : List (List Bool)) (acc : ℕ × ℕ) (k : ℕ) (v : Bool),
      budget r s acc k ≤ B →
      ∃ v' T, RunLe prog (45 * (B + 1) * (w.length + 1))
        ⟨some .loop, v, st r w s acc k⟩
        ⟨some (yesNo (checkLoop w r s acc k)), v', T⟩ := by
  induction w with
  | nil =>
    intro r s acc k v hB
    have hp (p : List Bool) : p.head?.isSome = !p.isEmpty := by cases p <;> rfl
    have hsk : ((st r [] s acc k) .skipped).head?.isSome = !s.isEmpty := by
      rw [hp, st, skipped_isEmpty]
    have hw : ((st r [] s acc k) .witness).head?.isSome = false := rfl
    have hj : ((st r [] s acc k) .jobs).head?.isSome = !r.isEmpty := hp r
    by_cases he : (r.isEmpty && s.isEmpty) = true
    · obtain ⟨hr, hs⟩ := Bool.and_eq_true_iff.mp he
      have h₁ : Run prog 1 ⟨some .loop, v, st r [] s acc k⟩
          ⟨some (.compareStart true), false, st r [] s acc k⟩ := by
        apply Run.single
        simp only [prog, TM2.stepAux, hw, hj, hsk, hr, hs, id_eq, Bool.not_true, Bool.cond_false]
      have h₂ := start_cmp_run true acc.2 k false (st r [] s acc k) rfl rfl
      have ht : cmpNext true (decide (k < acc.2)) = yesNo (checkLoop [] r s acc k) := by
        by_cases h : k < acc.2
        · simp [cmpNext, checkLoop, hr, hs, h, Nat.not_le_of_lt h]
        · simp [cmpNext, checkLoop, hr, hs, h, Nat.le_of_not_gt h]
      rw [ht] at h₂
      refine ⟨_, _, (h₁.le le_rfl |>.trans h₂).mono ?_⟩
      simp only [budget] at hB
      simp only [List.length_nil, zero_add, mul_one]
      omega
    · have hf : (r.isEmpty && s.isEmpty) = false := Bool.eq_false_iff.mpr he
      have h₁ : Run prog 1 ⟨some .loop, v, st r [] s acc k⟩
          ⟨some .no, true, st r [] s acc k⟩ := by
        apply Run.single
        have hp₁ := Bool.and_eq_false_iff.mp hf
        rcases hp₁ with hr | hs
        · simp only [prog, TM2.stepAux, hw, hj, hr, id_eq, Bool.not_false,
            Bool.cond_false, Bool.cond_true]
        · cases hr : r.isEmpty <;>
            simp only [prog, TM2.stepAux, hw, hj, hsk, hr, hs, id_eq, Bool.not_true,
              Bool.not_false, Bool.cond_false, Bool.cond_true]
      have ht : checkLoop [] r s acc k = false := by
        simp only [checkLoop, hf, Bool.false_and]
      refine ⟨true, st r [] s acc k, ?_⟩
      rw [ht]
      exact h₁.le (by simp only [List.length_nil, zero_add, mul_one]; omega)
  | cons sel w ih =>
    intro r s acc k v hB
    cases hr : undelimit r with
    | none =>
      let S := st r w s acc k
      have h₁ : Run prog 1 ⟨some .loop, v, st r (sel :: w) s acc k⟩
          ⟨some (.read sel), sel, S⟩ := by
        apply Run.single
        have he : update (st r (sel :: w) s acc k) K.witness w = S := by
          funext j
          cases j <;> rfl
        simpa [prog, TM2.stepAux, st] using he
      obtain ⟨v', T, h₂, _⟩ := readFrame_bad (M := prog) (self := Lab.read sel)
        (next := .restorePayload sel) (bad := .no) (a := K.jobs) (b := K.tmp)
        rfl (by decide) r sel S rfl hr
      refine ⟨v', T, ?_⟩
      simp only [checkLoop, hr, yesNo, Bool.false_eq_true, ↓reduceIte]
      refine (h₁.le le_rfl |>.trans h₂).mono ?_
      simp only [budget] at hB
      simp only [List.length_cons, Nat.mul_succ]
      omega
    | some pair =>
      obtain ⟨p, tail⟩ := pair
      obtain rfl := (Cslib.CookLevin.undelimit_eq_some_iff r p tail).1 hr
      obtain ⟨v₁, h₁⟩ := read_outer_job sel p tail w s acc k v
      let S₁ := update (st tail w s acc k) K.payload p
      have hB' : 6 * (2 * p.length + 1 + tail.length + (pack s.reverse).length) +
          (encodeNat acc.1).length + (encodeNat acc.2).length + (encodeNat k).length ≤ B := by
        simpa only [budget, List.length_append, length_delimit] using hB
      cases sel
      · obtain ⟨v₂, h₂⟩ := moveBits_run (M := prog) (a := K.skipped) (b := K.jobs)
          (self := Lab.restoreSkipped) (next := .readProcess) rfl (by decide) v₁ S₁
        have he : update (update S₁ K.skipped []) K.jobs ((S₁ .skipped).reverse ++ S₁ .jobs) =
            update (st (pack s.reverse ++ tail) w [] acc k) .payload p := by
          funext i
          cases i <;> simp [S₁, st, pack]
        rw [he] at h₂
        obtain ⟨v₃, T, h₃, ht⟩ := read_process_run p (pack s.reverse ++ tail) w acc k v₂
        have hb : 2 * p.length + 3 + ((S₁ .skipped).length + 1) +
            35 * (p.length + (encodeNat acc.1).length + (encodeNat acc.2).length + 1) ≤
              45 * (B + 1) := by
          simp [S₁, st, -BinaryNatEncoding.length_encodeNat]
          omega
        have hrun := (h₁.trans h₂).le le_rfl |>.trans h₃
        cases hj : decodeJob p with
        | none =>
          simp only [hj, Option.isSome_none, Bool.false_eq_true, ↓reduceIte] at hrun
          have hcheck : checkLoop (false :: w) (delimit p ++ tail) s acc k = false := by
            simp [checkLoop, hj]
          refine ⟨v₃, T, ?_⟩
          rw [hcheck]
          exact hrun.mono (by simp only [List.length_cons, Nat.mul_succ]; omega)
        | some j =>
          simp only [hj, Option.isSome_some, ↓reduceIte, ht j hj] at hrun
          have hb' : budget (pack s.reverse ++ tail) [] (jobStep acc j) k ≤ B := by
            have hs := job_size hj acc
            simp [budget, List.length_append, show pack [] = [] from rfl,
              -BinaryNatEncoding.length_encodeNat]
            omega
          obtain ⟨v₄, U, h₄⟩ := ih (pack s.reverse ++ tail) [] (jobStep acc j) k v₃ hb'
          refine ⟨v₄, U, ?_⟩
          have hcheck : checkLoop (false :: w) (delimit p ++ tail) s acc k =
              checkLoop w (pack s.reverse ++ tail) [] (jobStep acc j) k := by simp [checkLoop, hj]
          rw [hcheck]
          exact (hrun.trans h₄).mono (by simp only [List.length_cons, Nat.mul_succ]; omega)
      · have h₂ := writeBits_run (M := prog) (a := K.payload) (b := K.skipped)
          (self := Lab.skip) (next := .loop) (chunk := Reduction.liftBit) (suffix := [false])
          rfl (by decide) v₁ S₁
        have hp : pack (p :: s).reverse = pack s.reverse ++ delimit p := by
          simp [List.reverse_cons, pack_append, pack_cons, show pack [] = [] from rfl]
        have he : update (update S₁ K.payload []) K.skipped
            (((S₁ .payload).flatMap Reduction.liftBit ++ [false]).reverse ++ S₁ .skipped) =
              st tail w (p :: s) acc k := by
          funext i
          cases i <;> try rfl
          case skipped =>
            change (((S₁ .payload).flatMap Reduction.liftBit ++ [false]).reverse ++ S₁ .skipped) =
              (pack (p :: s).reverse).reverse
            rw [hp, Reduction.delimit_eq, Reduction.liftBits, List.reverse_append]
            simp [S₁, st]
        rw [he] at h₂
        have hb' : budget tail (p :: s) acc k ≤ B := by
          simp only [budget, hp, List.length_append, length_delimit]
          omega
        obtain ⟨v₃, T, h₃⟩ := ih tail (p :: s) acc k false hb'
        refine ⟨v₃, T, ?_⟩
        have hcheck : checkLoop (true :: w) (delimit p ++ tail) s acc k =
            checkLoop w tail (p :: s) acc k := by simp [checkLoop]
        rw [hcheck]
        refine ((h₁.trans h₂).le le_rfl |>.trans h₃).mono ?_
        simp [S₁, List.length_cons, Nat.mul_succ]
        omega


private theorem verify_run (x w : List Bool) :
    ∃ v T, RunLe prog (500 * (x.length + w.length + 1) ^ 2)
      ⟨some .start, false, update (update (fun _ => []) .jobs x) .witness w⟩
      ⟨some (yesNo (check x w)), v, T⟩ := by
  have hinit : update (update (fun _ => []) K.jobs x) K.witness w =
      st x w [] (0, 0) 0 := by
    funext j
    cases j <;> rfl
  rw [hinit]
  let S := st x w [] (0, 0) 0
  cases hx : undelimit x with
  | none =>
    obtain ⟨v, T, hr, _⟩ := readFrame_bad (M := prog) (self := Lab.start)
      (a := K.jobs) (b := K.tmp) (next := .reverseBound) (bad := .no) rfl
      (by decide) x false S rfl hx
    refine ⟨v, T, ?_⟩
    simpa only [check, hx, yesNo, Bool.false_eq_true, ↓reduceIte] using hr.mono (by
      let m := x.length + w.length + 1
      have h : m ≤ m ^ 2 := by
        rw [pow_two]
        exact Nat.le_mul_of_pos_right _ (by omega)
      have h' : x.length + 1 ≤ m := by dsimp [m]; omega
      exact h'.trans (h.trans (Nat.le_mul_of_pos_left _ (by decide))) :
        x.length + 1 ≤ 500 * (x.length + w.length + 1) ^ 2)
  | some pair =>
    obtain ⟨raw, kraw⟩ := pair
    have he := (Cslib.CookLevin.undelimit_eq_some_iff x raw kraw).1 hx
    have hl : x.length = 2 * raw.length + 1 + kraw.length := by simp [he]
    have h₁ := readFrame_run (M := prog) (self := Lab.start) (a := K.jobs) (b := K.tmp)
      (next := .reverseBound) (bad := .no) rfl (by decide) false S raw kraw
      (by simpa only [S, st] using he)
    let S₁ := update (update S K.jobs kraw) K.tmp (raw.reverse ++ S .tmp)
    obtain ⟨v₂, h₂⟩ := moveBits_run (M := prog) (self := Lab.reverseBound) (a := K.jobs)
      (b := K.processRev) (next := .restoreJobs) rfl (by decide) false S₁
    let S₂ := update (update S₁ K.jobs []) K.processRev ((S₁ .jobs).reverse ++ S₁ .processRev)
    obtain ⟨v₃, h₃⟩ := moveBits_run (M := prog) (self := Lab.restoreJobs) (a := K.tmp)
      (b := K.jobs) (next := .norm .bound) rfl (by decide) v₂ S₂
    let S₃ := update (update S₂ K.tmp []) K.jobs ((S₂ .tmp).reverse ++ S₂ .jobs)
    obtain ⟨v₄, h₄⟩ := norm_run .bound kraw v₃ S₃ (by simp [normSource, S₃, S₂, S₁, S, st])
    have hcor : update (update S₃ (normSource .bound) []) (normTarget .bound)
          (encodeNat (decodeNat kraw) ++ S₃ (normTarget .bound)) =
        st raw w [] (0, 0) (decodeNat kraw) := by
      funext j
      cases j <;> simp [S₃, S₂, S₁, S, st, normSource, normTarget, show encodeNat 0 = [] from rfl]
    rw [hcor] at h₄
    have henc := decoded_length kraw
    have hb : budget raw [] (0, 0) (decodeNat kraw) ≤ 8 * (x.length + 1) := by
      simp [budget, pack, BinaryNatEncoding.length_encodeNat] at henc ⊢
      omega
    obtain ⟨v, T, hr⟩ := verify_loop w raw [] (0, 0) (decodeNat kraw) v₄ hb
    refine ⟨v, T, ?_⟩
    rw [check, hx]
    refine ((h₁.trans h₂ |>.trans h₃).le le_rfl |>.trans h₄ |>.trans hr).mono ?_
    have hmul : (8 * (x.length + 1) + 1) * (w.length + 1) ≤
        9 * (x.length + w.length + 1) ^ 2 := by
      rw [pow_two, ← mul_assoc]
      exact Nat.mul_le_mul (by omega) (by omega)
    simp [S₂, S₁, S, st]
    have hbound := Nat.mul_le_mul_left 45 hmul
    nlinarith

private def ks : List K :=
  [.jobs, .witness, .skipped, .elapsed, .cost, .bound, .tmp, .payload, .processRev, .dueRev,
    .operand, .elapsedCopy, .sum]

private noncomputable instance kFintype : Fintype K :=
  Fintype.ofList ks (fun k => by cases k <;> decide)

private noncomputable instance labFintype : Fintype Lab :=
  Fintype.ofList
    [.start, .reverseBound, .restoreJobs, .loop, .read false, .read true,
      .restorePayload false, .restorePayload true, .skip, .restoreSkipped, .readProcess, .readDue,
      .norm .bound, .norm .process, .norm .due, .norm .weight,
      .normMove .bound, .normMove .process, .normMove .due, .normMove .weight,
      .addStart false, .addStart true, .add false, .add true, .carry false, .carry true,
      .store false, .store true, .compareStart false, .compareStart true, .compare false,
      .compare true, .compareDone false, .compareDone true, .discardWeight, .reverseWeight,
      .yes, .no]
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

private theorem check_poly : ComplexityTheory.IsPolyTime
    (fun xw : List Bool × List Bool => check xw.1 xw.2) :=
  Host.isPolyTime_verifier (c := comp) (cX := .jobs) (cW := .witness)
    (gX := id) (gW := id) (start := .start) (yes := .yes) (no := .no)
    check (Polynomial.C 500 * (Polynomial.X + 1) ^ 2)
    (fun h => K.noConfusion h) (fun h => Lab.noConfusion h) rfl rfl fun x w => by
      obtain ⟨v, T, hr⟩ := verify_run x w
      refine ⟨v, T, ?_⟩
      change RunLe prog _ ⟨some .start, false,
        update (update (fun _ => []) .jobs (x.map id)) .witness (w.map id)⟩
        ⟨some (yesNo (check x w)), v, T⟩
      rw [List.map_id, List.map_id]
      exact hr.mono (by simp [Nat.add_assoc])

private theorem membership : weightedTardyJobsDec ∈ ComplexityTheory.NP :=
  ⟨Polynomial.X ^ 2, fun xw => check xw.1 xw.2, check_poly, fun x => by
    simpa using check_iff x⟩

end Verification

/-- **WEIGHTED NUMBER OF TARDY JOBS is NP-complete.** The weighted number of tardy jobs decision
problem lies in NP, and every decision problem in NP has a polynomial-time many-one reduction to
it.

Source: M. R. Garey and D. S. Johnson,
*Computers and Intractability* (1979), WEIGHTED NUMBER OF TARDY JOBS (1||sum w_j U_j). -/
public theorem weightedTardyJobs_npComplete :
    weightedTardyJobsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L weightedTardyJobsDec :=
  ⟨Verification.membership, Reduction.hardness⟩

end MetaMathlibExt.Complexity.NPComplete.WeightedTardyJobs
