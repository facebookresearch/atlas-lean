/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A `TimeM` verifier for SAT with polynomial declared time
-/
module

public import Cslib.Algorithms.Lean.TimeM
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Logics.Propositional.CNF.Semantics
public import CSLibExt.Computability.TimeMComplexity

/-!
# A `TimeM` verifier for SAT with polynomial declared time

A concrete verifier `satVerifier` for the SAT decision problem
`Cslib.CookLevin.satDec`, with polynomial declared `TimeM` time. This
module proves the verifier's correctness, `satVerifier_verifies` (the
verifier accepts exactly the satisfiable encodings, with witness bound
`X` in the sense of `Cslib.TimeMComplexity.Verifies`), and a
declared-time bound, `satVerifier_verifierInDeclaredPolyTime`
(declared time at most `X ^ 2 + X`, a bound on the trusted annotation
only). The actual ingredients of canonical `NP` membership are
`satVerifier_verifies` plus a separate `ComplexityTheory.IsPolyTime`
fact for the verifier's computed function. Canonical `NP` membership
then follows through the repackaging lemma
`Cslib.TimeMComplexity.mem_NP_of_verifies` as soon as the verifier's
computed function is known to be `ComplexityTheory.IsPolyTime`
(`satDec_mem_NP_of_isPolyTime`); that canonical evidence must be
proved independently for this verifier and does not follow from its
declared-time bound. `satDec` is defined over the canonical
CNF encoding in `Cslib.CookLevin` on the shared
`MetaMathlibExt.ComplexityTheory.DecisionProblem` type.

Variable indices in `encodeCNF` are binary-coded, so an index can be
exponential in the input length. The NP witness therefore cannot list the
value of variable `i` at position `i`. Instead the witness lists values for
the variables *occurring* in the formula, in occurrence order (`varsOf`),
and the verifier looks a variable up in the parallel occurrence and witness
lists, first occurrence winning (`lookupVar`).

Cost model, in `TimeM` declared ticks: one tick per variable comparison in
`lookupVar`, plus one tick per literal examined in `checkClause`. Decoding
the input with the existing pure `decodeCNF` is uncharged preprocessing on
the input (charged 0); the polynomial time bound `X ^ 2 + X` accounts for
all charged steps.

Scope: a `TimeM` verifier for SAT with polynomial declared time, plus
canonical NP membership conditional on independent canonical evidence
for the verifier's computed function. No Cook–Levin NP-hardness or
NP-completeness claim.
-/

@[expose] public section

namespace Cslib.CookLevin

open Cslib.Logic.PL

open Cslib.Algorithms.Lean (TimeM)
open Polynomial

/-- Variables occurring in `φ`, in order of occurrence (with duplicates). -/
def varsOf (φ : CNF) : List Nat := φ.flatMap fun C => C.map Prod.fst

/-- Look up variable `x` in the parallel lists of occurring variables and
witness values; first occurrence wins, default `false`. One tick per
variable compared, zero ticks in the base cases. -/
def lookupVar : List Nat → List Bool → Nat → TimeM Nat Bool
  | [], _, _ => pure false
  | _, [], _ => pure false
  | n :: ns, b :: bs, x =>
      TimeM.tick 1 >>= fun _ =>
        if x = n then pure b else lookupVar ns bs x

/-- Check one clause against the witness: empty clause fails; otherwise
scan literals in order, succeeding at the first satisfied literal. One
tick per literal examined, plus the lookup cost. -/
def checkClause (vars : List Nat) (w : List Bool) :
    CNFClause → TimeM Nat Bool
  | [] => pure false
  | l :: ls =>
      TimeM.tick 1 >>= fun _ =>
        lookupVar vars w l.1 >>= fun v =>
          if v = l.2 then pure true else checkClause vars w ls

/-- Check every clause of a CNF formula against the witness. -/
def checkCNF (vars : List Nat) (w : List Bool) : CNF → TimeM Nat Bool
  | [] => pure true
  | C :: Cs =>
      checkClause vars w C >>= fun ok =>
        if ok = true then checkCNF vars w Cs else pure false

/-- The SAT verifier: decode the input (uncharged pure preprocessing),
reject on decode failure, otherwise check the formula against the witness
interpreted in occurrence order. -/
def satVerifier : List Bool × List Bool → TimeM Nat Bool := fun xw =>
  match decodeCNF xw.1 with
  | none => pure false
  | some φ => checkCNF (varsOf φ) xw.2 φ

/-- Lookup costs at most one tick per occurring variable. -/
theorem lookupVar_time_le (ns : List Nat) (bs : List Bool) (x : Nat) :
    (lookupVar ns bs x).time ≤ ns.length := by
  induction ns generalizing bs with
  | nil => simp [lookupVar]
  | cons n ns ih =>
      cases bs with
      | nil => simp [lookupVar]
      | cons b bs' =>
          simp only [lookupVar, TimeM.time_bind, TimeM.time_tick]
          by_cases h : x = n
          · rw [ite_eq_left h]
            simp only [TimeM.time_pure, List.length_cons]
            omega
          · rw [ite_eq_right h]
            have hrec := ih bs'
            simp only [List.length_cons]
            omega

/-- Looking up in the witness built from an assignment `v` returns `v x`
for occurring variables and `false` otherwise. -/
theorem lookupVar_ret_map (v : Nat → Bool) (ns : List Nat) (x : Nat) :
    (lookupVar ns (ns.map v) x).ret = if x ∈ ns then v x else false := by
  induction ns with
  | nil => simp [lookupVar]
  | cons n ns ih =>
      simp only [List.map_cons, lookupVar, TimeM.ret_bind]
      by_cases h : x = n
      · simp [h]
      · simp [h, ih]

/-- A clause check succeeds iff the clause is satisfied (canonical
`CNFClause.Satisfies`) by the looked-up witness values. -/
theorem checkClause_ret (vars : List Nat) (w : List Bool) (C : CNFClause) :
    (checkClause vars w C).ret = true ↔
      C.Satisfies (fun x => (lookupVar vars w x).ret) := by
  rw [CNFClause.satisfies_def]
  induction C with
  | nil => simp [checkClause]
  | cons l ls ih =>
      rcases l with ⟨x0, b0⟩
      simp only [checkClause, TimeM.ret_bind]
      by_cases h : (lookupVar vars w x0).ret = b0
      · rw [ite_eq_left h]
        simp only [TimeM.ret_pure]
        constructor
        · intro _
          exact ⟨(x0, b0), by simp, h⟩
        · intro _
          trivial
      · rw [ite_eq_right h, ih]
        constructor
        · rintro ⟨⟨x, b⟩, hm, hl⟩
          exact ⟨(x, b), List.mem_cons.mpr (Or.inr hm), hl⟩
        · rintro ⟨⟨x, b⟩, hm, hl⟩
          rw [List.mem_cons] at hm
          rcases hm with heq | htail
          · have hpair : x = x0 ∧ b = b0 := by
              simpa only [Prod.mk.injEq] using heq
            obtain ⟨rfl, rfl⟩ := hpair
            exact (h hl).elim
          · exact ⟨(x, b), htail, hl⟩

/-- A clause check costs at most one tick plus one lookup per literal. -/
theorem checkClause_time_le (vars : List Nat) (w : List Bool)
    (C : CNFClause) :
    (checkClause vars w C).time ≤ C.length * (vars.length + 1) := by
  induction C with
  | nil => simp [checkClause]
  | cons l ls ih =>
      simp only [checkClause, TimeM.time_bind, TimeM.time_tick]
      have hlook := lookupVar_time_le vars w l.1
      have hexpand : (ls.length + 1) * (vars.length + 1) =
          ls.length * (vars.length + 1) + (vars.length + 1) := by
        rw [Nat.add_mul, Nat.one_mul]
      by_cases h : (lookupVar vars w l.1).ret = l.2
      · rw [ite_eq_left h]
        simp only [TimeM.time_pure, List.length_cons]
        rw [hexpand]
        omega
      · rw [ite_eq_right h]
        simp only [List.length_cons]
        rw [hexpand]
        omega

/-- A formula check succeeds iff the formula is satisfied
(canonical `CNF.Satisfies`) by the looked-up witness values. -/
theorem checkCNF_ret (vars : List Nat) (w : List Bool) (φ : CNF) :
    (checkCNF vars w φ).ret = true ↔
      φ.Satisfies (fun x => (lookupVar vars w x).ret) := by
  rw [CNF.satisfies_def]
  induction φ with
  | nil => simp [checkCNF]
  | cons C Cs ih =>
      simp only [checkCNF, TimeM.ret_bind]
      by_cases h : (checkClause vars w C).ret = true
      · rw [ite_eq_left h, ih]
        constructor
        · intro htail C' hC'
          rw [List.mem_cons] at hC'
          rcases hC' with rfl | hC'
          · rw [checkClause_ret] at h
            exact h
          · exact htail C' hC'
        · intro hall C' hC'
          exact hall C' (List.mem_cons.mpr (Or.inr hC'))
      · rw [ite_eq_right h]
        simp only [TimeM.ret_pure]
        constructor
        · intro hcontra
          cases hcontra
        · intro hall
          have hCsat := hall C (by simp)
          rw [← checkClause_ret] at hCsat
          exact (h hCsat).elim

/-- A formula check costs at most the total literal count times the
per-literal cost of one tick plus one lookup. -/
theorem checkCNF_time_le (vars : List Nat) (w : List Bool) (φ : CNF) :
    (checkCNF vars w φ).time ≤
      (φ.map List.length).sum * (vars.length + 1) := by
  induction φ with
  | nil => simp [checkCNF]
  | cons C Cs ih =>
      simp only [checkCNF, TimeM.time_bind]
      have hclause := checkClause_time_le vars w C
      have hexpand : (C.length + (Cs.map List.length).sum) *
          (vars.length + 1) = C.length * (vars.length + 1) +
            (Cs.map List.length).sum * (vars.length + 1) :=
        Nat.add_mul _ _ _
      by_cases h : (checkClause vars w C).ret = true
      · rw [ite_eq_left h]
        simp only [List.map_cons, List.sum_cons]
        rw [hexpand]
        omega
      · rw [ite_eq_right h]
        simp only [TimeM.time_pure, List.map_cons, List.sum_cons]
        rw [hexpand]
        omega

/-- The occurrence list has one entry per literal of the formula. -/
theorem varsOf_length (φ : CNF) :
    (varsOf φ).length = (φ.map List.length).sum := by
  simp [varsOf, List.length_flatMap, List.length_map]

/-- Every variable of a literal in the formula occurs in `varsOf`. -/
theorem mem_varsOf {x : Nat} {b : Bool} {C : CNFClause} {φ : CNF}
    (hC : (x, b) ∈ C) (hφ : C ∈ φ) : x ∈ varsOf φ := by
  have hx : x ∈ C.map Prod.fst := List.mem_map.mpr ⟨(x, b), hC, rfl⟩
  unfold varsOf
  exact List.mem_flatMap.mpr ⟨C, hφ, hx⟩

/-- The total literal count is bounded by the encoding length: each
encoded clause contributes at least its literal count. -/
theorem sum_length_le_encodeCNF_length (φ : CNF) :
    (φ.map List.length).sum ≤ (encodeCNF φ).length := by
  have hle : ∀ ψ : CNF, (ψ.map List.length).sum ≤
      (ψ.map fun C => (encodeClause C).length).sum := by
    intro ψ
    induction ψ with
    | nil => simp
    | cons C ψ ih =>
        simp only [List.map_cons, List.sum_cons]
        have hC : C.length ≤ (encodeClause C).length := by
          rw [encodeClause_length]
          omega
        exact Nat.add_le_add hC ih
  rw [encodeCNF_length]
  have hmain := hle φ
  omega

/-- The verifier rejects immediately on decode failure. -/
theorem satVerifier_none {x w : List Bool} (h : decodeCNF x = none) :
    satVerifier (x, w) = pure false := by
  simp [satVerifier, h]

/-- On a successful decode, the verifier checks the decoded formula. -/
theorem satVerifier_some {x w : List Bool} {φ : CNF}
    (h : decodeCNF x = some φ) :
    satVerifier (x, w) = checkCNF (varsOf φ) w φ := by
  simp [satVerifier, h]

/-- The verifier runs in time at most `N ^ 2 + N` in the combined length
`N` of input and witness: with `n` the literal count, `n ≤ N` and the
check costs at most `n * (n + 1) ≤ N * (N + 1)`. -/
theorem satVerifier_time_le (xw : List Bool × List Bool) :
    (satVerifier xw).time ≤
      (Polynomial.X ^ 2 + Polynomial.X).eval
        (xw.1.length + xw.2.length) := by
  obtain ⟨x, w⟩ := xw
  show (satVerifier (x, w)).time ≤
    (Polynomial.X ^ 2 + Polynomial.X).eval (x.length + w.length)
  cases hdec : decodeCNF x with
  | none =>
      rw [satVerifier_none hdec]
      simp
  | some φ =>
      have hx : x = encodeCNF φ := (decodeCNF_eq_some_iff x φ).mp hdec
      rw [satVerifier_some hdec]
      have hn_le : (φ.map List.length).sum ≤ x.length + w.length := by
        have h1 := sum_length_le_encodeCNF_length φ
        rw [hx]
        exact le_trans h1 (Nat.le_add_right _ _)
      have htime : (checkCNF (varsOf φ) w φ).time ≤
          (φ.map List.length).sum * ((φ.map List.length).sum + 1) := by
        have hcheck := checkCNF_time_le (varsOf φ) w φ
        rwa [varsOf_length] at hcheck
      have hmul : (φ.map List.length).sum *
            ((φ.map List.length).sum + 1) ≤
          (x.length + w.length) * ((x.length + w.length) + 1) :=
        Nat.mul_le_mul hn_le (Nat.add_le_add_right hn_le 1)
      have heval : (Polynomial.X ^ 2 + Polynomial.X).eval
            (x.length + w.length) =
          (x.length + w.length) * ((x.length + w.length) + 1) := by
        simp only [Polynomial.eval_add, Polynomial.eval_pow,
          Polynomial.eval_X]
        generalize x.length + w.length = N
        rw [pow_two, Nat.mul_add, Nat.mul_one]
      rw [heval]
      exact le_trans htime hmul

/-- The SAT verifier's declared time is polynomially bounded, with bound
`X ^ 2 + X` in the combined input and witness length. -/
theorem satVerifier_verifierInDeclaredPolyTime :
    Cslib.TimeMComplexity.VerifierInDeclaredPolyTime satVerifier :=
  ⟨Polynomial.X ^ 2 + Polynomial.X, satVerifier_time_le⟩

/-- `satVerifier` verifies `satDec` with witness bound `X`: the witness
lists assignment values for the occurring variables in occurrence order
(length the literal count, at most the input length), and acceptance is
equivalent to satisfiability of the decoded formula. -/
theorem satVerifier_verifies :
    Cslib.TimeMComplexity.Verifies satVerifier satDec Polynomial.X := by
  intro x
  constructor
  · intro hx
    have hx' : satDec x = true := hx
    by_cases hmem : x ∈ SATLang
    · have hex : ∃ φ : CNF, encodeCNF φ = x ∧ CNFSat φ := hmem
      obtain ⟨φ, henc, hsat⟩ := hex
      have hex2 : ∃ v : Nat → Bool, φ.Satisfies v :=
        cnfSat_iff_exists_satisfies.mp hsat
      obtain ⟨v, hv⟩ := hex2
      refine ⟨(varsOf φ).map v, ?_, ?_⟩
      · have hlen : ((varsOf φ).map v).length =
            (φ.map List.length).sum := by
          rw [List.length_map, varsOf_length]
        rw [hlen]
        simp only [Polynomial.eval_X]
        rw [← henc]
        exact sum_length_le_encodeCNF_length φ
      · have hdec : decodeCNF x = some φ := by
          rw [← henc]
          exact decodeCNF_encodeCNF φ
        rw [satVerifier_some hdec, checkCNF_ret]
        intro C hC
        obtain ⟨⟨a, b⟩, hm, hval⟩ := hv C hC
        refine ⟨(a, b), hm, ?_⟩
        show (lookupVar (varsOf φ) ((varsOf φ).map v) a).ret = b
        rw [lookupVar_ret_map]
        have ha : a ∈ varsOf φ := mem_varsOf hm hC
        rw [ite_eq_left ha]
        exact hval
    · have hfalse : satDec x = false := by
        unfold satDec
        rw [ite_eq_right hmem]
      rw [hfalse] at hx'
      cases hx'
  · rintro ⟨w, -, hw⟩
    cases hdec : decodeCNF x with
    | none =>
        rw [satVerifier_none hdec] at hw
        simp at hw
    | some φ =>
        have hx : x = encodeCNF φ := (decodeCNF_eq_some_iff x φ).mp hdec
        rw [satVerifier_some hdec] at hw
        have hsat : CNFSat φ :=
          cnfSat_iff_exists_satisfies.mpr
            ⟨fun i => (lookupVar (varsOf φ) w i).ret,
              (checkCNF_ret (varsOf φ) w φ).mp hw⟩
        have hmem : x ∈ SATLang := by
          show IsSATEncoded x
          exact ⟨φ, hx.symm, hsat⟩
        show satDec x = true
        unfold satDec
        rw [ite_eq_left hmem]

/-- Canonical NP membership of SAT, conditional on the verifier's
computed function being polynomial-time in the canonical TM2 sense.
That evidence must be proved independently for `satVerifier`,
covering in particular the uncharged `decodeCNF` and `varsOf`
computations; it does not follow from
`satVerifier_verifierInDeclaredPolyTime`, which bounds only the
trusted declared-time annotation. -/
theorem satDec_mem_NP_of_isPolyTime
    (h : MetaMathlibExt.ComplexityTheory.IsPolyTime
      fun xw => (satVerifier xw).ret) :
    satDec ∈ MetaMathlibExt.ComplexityTheory.NP :=
  Cslib.TimeMComplexity.mem_NP_of_verifies satVerifier_verifies h

end Cslib.CookLevin
