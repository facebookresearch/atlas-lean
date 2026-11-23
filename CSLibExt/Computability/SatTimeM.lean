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

/-- **Occurrence list of a CNF formula.** For a CNF formula $\varphi = (C_1, \dots, C_m)$, the
occurrence list of $\varphi$ is the list of the variable indices of its literals, in order: the
variables of the literals of $C_1$ in order, then those of $C_2$, and so on up to $C_m$.
Duplicates are kept, so a variable appears once for each literal in which it occurs. -/
def varsOf (φ : CNF) : List Nat := φ.flatMap fun C => C.map Prod.fst

/-- **Witness lookup.** Given a list $N = (n_1, \dots, n_k)$ of natural numbers, a list
$w = (b_1, \dots, b_m)$ of booleans and a natural number $x$, the lookup of $x$ in $N$ and $w$ is
the timed computation (a returned boolean together with a natural-number cost) that scans the
pairs $(n_1, b_1), (n_2, b_2), \dots$ in order, charging one tick for each pair it examines, and
returns $b_i$ for the first $i$ with $n_i = x$; if either list runs out first, it returns false at
no further cost.

It is used with $N$ the variables occurring in a formula and $w$ the witness values, so the first
occurrence of a variable wins. -/
def lookupVar : List Nat → List Bool → Nat → TimeM Nat Bool
  | [], _, _ => pure false
  | _, [], _ => pure false
  | n :: ns, b :: bs, x =>
      TimeM.tick 1 >>= fun _ =>
        if x = n then pure b else lookupVar ns bs x

/-- **Clause check against a witness.** Given a list $N$ of natural numbers, a list $w$ of
booleans and a CNF clause $C$, the check of $C$ against $N$ and $w$ is the timed computation (a
returned boolean together with a natural-number cost) that scans the literals $(x, b)$ of $C$ in
order: for each it charges one tick, then looks up $x$ in $N$ and $w$, paying the cost of the
lookup, and returns true if the value found equals the polarity $b$; otherwise it moves on to the
next literal. When the literals are exhausted it returns false at no further cost; in particular
the empty clause fails. -/
def checkClause (vars : List Nat) (w : List Bool) :
    CNFClause → TimeM Nat Bool
  | [] => pure false
  | l :: ls =>
      TimeM.tick 1 >>= fun _ =>
        lookupVar vars w l.1 >>= fun v =>
          if v = l.2 then pure true else checkClause vars w ls

/-- **Formula check against a witness.** Given a list $N$ of natural numbers, a list $w$ of
booleans and a CNF formula $\varphi$, the check of $\varphi$ against $N$ and $w$ is the timed
computation that runs the clause check against $N$ and $w$ on the clauses of $\varphi$ in order,
adding up their costs, and returns false as soon as one of them returns false. If every clause
check returns true, in particular if $\varphi$ has no clauses, it returns true. -/
def checkCNF (vars : List Nat) (w : List Bool) : CNF → TimeM Nat Bool
  | [] => pure true
  | C :: Cs =>
      checkClause vars w C >>= fun ok =>
        if ok = true then checkCNF vars w Cs else pure false

/-- **The SAT verifier.** The SAT verifier takes a pair $(x, w)$ of lists of Booleans, an input
$x$ and a witness $w$, and returns a Boolean together with a declared time cost. If the complete
CNF decoder fails on $x$, it returns false at cost $0$. If $x$ decodes to a CNF formula
$\varphi$, it returns the result and the cost of the CNF check of $\varphi$ against the witness
$w$ and the occurrence list of $\varphi$, so that $w$ is read as values for the variables of
$\varphi$ in order of occurrence.

Decoding the input is uncharged preprocessing: it adds nothing to the declared cost. -/
def satVerifier : List Bool × List Bool → TimeM Nat Bool := fun xw =>
  match decodeCNF xw.1 with
  | none => pure false
  | some φ => checkCNF (varsOf φ) xw.2 φ

/-- **Cost bound for witness lookup.** For every list $N$ of natural numbers, every list $w$ of
booleans and every natural number $x$, the cost of looking up $x$ in $N$ and $w$ is at most the
length of $N$. -/
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

/-- **Lookup in the witness of an assignment.** Let $v$ be a function from the natural numbers to
the booleans, $N = (n_1, \dots, n_k)$ a list of natural numbers and $x$ a natural number. Looking
up $x$ in $N$ and the list $(v(n_1), \dots, v(n_k))$ returns $v(x)$ if $x$ occurs in $N$, and false
otherwise. -/
theorem lookupVar_ret_map (v : Nat → Bool) (ns : List Nat) (x : Nat) :
    (lookupVar ns (ns.map v) x).ret = if x ∈ ns then v x else false := by
  induction ns with
  | nil => simp [lookupVar]
  | cons n ns ih =>
      simp only [List.map_cons, lookupVar, TimeM.ret_bind]
      by_cases h : x = n
      · simp [h]
      · simp [h, ih]

/-- **Correctness of the witness clause check.** Let $N$ be a list of natural numbers, $w$ a list
of booleans and $C$ a CNF clause. The check of $C$ against $N$ and $w$ returns true if and only
if $C$ is satisfied by the assignment that sends each natural number $x$ to the value returned by
looking up $x$ in $N$ and $w$. -/
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

/-- **Cost bound for the witness clause check.** Let $N$ be a list of natural numbers, $w$ a list
of booleans and $C$ a CNF clause, viewed as a list of $\ell$ literals (repetitions counted). The
cost of checking $C$ against $N$ and $w$ is at most $\ell \cdot (|N| + 1)$, where $|N|$ is the
length of $N$.

Each literal examined costs one tick plus one lookup, and a lookup costs at most $|N|$. -/
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

/-- **Correctness of the witness formula check.** Let $N$ be a list of natural numbers, $w$ a list
of booleans and $\varphi$ a CNF formula. The check of $\varphi$ against $N$ and $w$ returns true if
and only if $\varphi$ is satisfied by the assignment that sends each natural number $x$ to the value
returned by looking up $x$ in $N$ and $w$. -/
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

/-- **Cost bound for the witness formula check.** Let $N$ be a list of natural numbers, $w$ a list
of booleans and $\varphi$ a CNF formula, and let $L$ be the sum of the lengths of the clauses of
$\varphi$ (its total number of literals). The cost of checking $\varphi$ against $N$ and $w$ is at
most $L \cdot (|N| + 1)$, where $|N|$ is the length of $N$. -/
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

/-- **Length of the occurrence list.** For every CNF formula $\varphi$, the length of the
occurrence list of $\varphi$ equals the total number of literals of $\varphi$, that is, the sum
over the clauses of $\varphi$ of their lengths. -/
theorem varsOf_length (φ : CNF) :
    (varsOf φ).length = (φ.map List.length).sum := by
  simp [varsOf, List.length_flatMap, List.length_map]

/-- **Variables of a formula occur in its occurrence list.** Let $\varphi$ be a CNF formula, $C$ a
clause of $\varphi$ and $(x, b)$ a literal of $C$. Then $x$ belongs to the list of variables
occurring in $\varphi$. -/
theorem mem_varsOf {x : Nat} {b : Bool} {C : CNFClause} {φ : CNF}
    (hC : (x, b) ∈ C) (hφ : C ∈ φ) : x ∈ varsOf φ := by
  have hx : x ∈ C.map Prod.fst := List.mem_map.mpr ⟨(x, b), hC, rfl⟩
  unfold varsOf
  exact List.mem_flatMap.mpr ⟨C, hφ, hx⟩

/-- **The literal count is at most the code length.** For every CNF formula $\varphi$, the sum
over the clauses of $\varphi$ of their lengths (the total number of literals of $\varphi$) is at
most the length of the length-prefixed binary code of $\varphi$.

Each encoded clause contributes at least its literal count. -/
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

/-- **The SAT verifier rejects undecodable inputs.** For all lists of Booleans $x$ and $w$, if
the complete CNF decoder fails on $x$, then the SAT verifier on $(x, w)$ returns false at
declared time cost $0$. -/
theorem satVerifier_none {x w : List Bool} (h : decodeCNF x = none) :
    satVerifier (x, w) = pure false := by
  simp [satVerifier, h]

/-- **The SAT verifier on a decodable input.** For all lists of Booleans $x$ and $w$ and every
CNF formula $\varphi$, if the complete CNF decoder returns $\varphi$ on $x$, then the SAT verifier
on $(x, w)$ coincides with the CNF check of $\varphi$ against the witness $w$ and the occurrence
list of $\varphi$: both the returned Boolean and the declared time cost are the same. -/
theorem satVerifier_some {x w : List Bool} {φ : CNF}
    (h : decodeCNF x = some φ) :
    satVerifier (x, w) = checkCNF (varsOf φ) w φ := by
  simp [satVerifier, h]

/-- **Declared time bound of the SAT verifier.** For all lists of Booleans $x$ (the input) and
$w$ (the witness), the declared time cost of the SAT verifier on $(x, w)$ is at most $N^2 + N$,
where $N = |x| + |w|$ is the sum of their lengths.

If $x$ decodes to a formula with $n$ literals, then $n \le N$ and the check costs at most
$n(n + 1) \le N(N + 1)$. -/
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

/-- **The SAT verifier has polynomial declared time.** There is a polynomial $q$ with natural
number coefficients such that for all lists of Booleans $x$ (the input) and $w$ (the witness),
the declared time cost of the SAT verifier on $(x, w)$ is at most $q(|x| + |w|)$.

One can take $q = X^2 + X$. This bounds only the trusted cost annotation. -/
theorem satVerifier_verifierInDeclaredPolyTime :
    Cslib.TimeMComplexity.VerifierInDeclaredPolyTime satVerifier :=
  ⟨Polynomial.X ^ 2 + Polynomial.X, satVerifier_time_le⟩

/-- **The SAT verifier verifies SAT.** The SAT verifier verifies the SAT decision problem with
witness bound the polynomial $X$: for every list $x$ of Booleans, $x$ encodes a satisfiable CNF
formula if and only if there is a list $w$ of Booleans, of length at most the length of $x$, such
that the SAT verifier on $(x, w)$ returns true.

The intended witness lists values for the variables occurring in the decoded formula, in order of
occurrence; its length is the literal count, which is at most the input length. -/
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

/-- **SAT is in NP if its verifier is polynomial-time.** If the function sending a pair $(x, w)$
of lists of Booleans to the Boolean returned by the SAT verifier on $(x, w)$ is polynomial-time
computable, by a multi-stack Turing machine under the canonical bitstring encodings, then the
SAT decision problem belongs to NP.

This hypothesis must be proved separately: it does not follow from the polynomial bound on the
SAT verifier's declared time, which constrains only a trusted cost annotation and leaves the
decoding of the input uncharged. -/
theorem satDec_mem_NP_of_isPolyTime
    (h : MetaMathlibExt.ComplexityTheory.IsPolyTime
      fun xw => (satVerifier xw).ret) :
    satDec ∈ MetaMathlibExt.ComplexityTheory.NP :=
  Cslib.TimeMComplexity.mem_NP_of_verifies satVerifier_verifies h

end Cslib.CookLevin
