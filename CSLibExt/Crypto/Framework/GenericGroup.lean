/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Crypto.Framework.Oracle
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Tactic.Abel

/-!
# Generic group model with deeply embedded programs

A functional-coherence model of a generic group of order `q`: programs are deeply
embedded syntax trees over label indices, compiled to the canonical `OracleComp`
execution framework and run against a fixed-encoding oracle.

## Scope

* The encoding is a fixed bijection — a permutation `enc : Equiv.Perm (ZMod q)` — of the
  exponent group `ZMod q`, with `1 < q`. Uniform *sampling* of the encoding is not modeled:
  every result quantifies over all `enc`, so each holds for a sampled encoding a fortiori,
  pointwise.
* Additive-exponent presentation: the label of `a : ZMod q` stands for `g ^ a` for an
  abstract fixed generator; represented multiplication adds exponents, inversion negates,
  the identity is exponent `0`, and exponentiation to `n` is `n • x`.
* Label equality is plain decidable equality on `ZMod q`.
* Functional coherence only: no security bounds are claimed, and no bitstring injections or
  collision bounds in the style of Shoup are modeled.

## Programs

`GProg n` is explicit program syntax over `n` labels addressed by `Fin n` indices: `ret`
returns an indexed label, `mul`/`inv` issue one oracle query over indexed labels and run a
continuation with the answer bound at a fresh index, and `eqTest` branches on indexed
equality. A program never holds a value of the label type: every label it handles comes
from its inputs or from oracle answers, referenced by index only.

Environments are extended snoc-style: the inputs come first, and each oracle answer is
appended at index `Fin.last`, with earlier indices preserved by `Fin.castSucc` (see
`snocEnv`). Evaluation (`eval`) is structural recursion over the syntax, so every program
is finite syntax and evaluation always terminates; queries are answered through the oracle
function and `DecidableEq` supplied by the evaluator.

`GProg` is the representation-independent source language; execution goes through the
canonical `OracleComp` framework. The evaluator-side compiler `GProg.compile` translates
source syntax into `OracleComp (Query L) L L`: `ret` becomes `pure`, `mul`/`inv` issue an
oracle query whose answer extends the environment snoc-style, and `eqTest` becomes pure
branching. Compilation happens at the evaluator, so programs still hold no label values.
`OracleComp.run` and `OracleComp.queries` give execution and its transcript, in agreement
with the reference semantics (`compile_run`, `compile_queries`), and `numQueries` is a
canonical structural query bound (`isQueryBounded_compile`).

`runProg` accepts only `GProg` syntax: it compiles the program and runs it through
`OracleComp.run` against the deterministic oracle `oracleOf enc` for the fixed encoding.

## Why deep embedding

A rank-2 interface — programs polymorphic in the label type `L` — cannot enforce
genericity in Lean: Lean has no internal parametricity, so a putatively generic program
may inspect the label type it is instantiated with. For example, such a program can
typecase on `L = ZMod 7` and, at that instance only, synthesize the literal label `0` out
of thin air — a label that need not be the identity and that no oracle query produced —
while still typechecking as "generic". The polymorphism rules out nothing.

Deep embedding rules out synthesis by construction: `GProg` has no constructor carrying a
label value, only `Fin` indices into the environment, so there is no syntax for a literal
label. Relabeling invariance is then a theorem (`eval_natural`): evaluation commutes with
any renaming of labels that the oracle respects.

The concrete representation exists only in the evaluator: the encoding permutation `enc`,
the `ZMod q` arithmetic, and the `enc`/`enc.symm` conversions appear only in `oracleOf`,
`idLabel`, `gmul`, `ginv`, and `runProg`, which instantiates evaluation at `Label q`.
-/

@[expose] public section

namespace Cslib.Crypto.Framework.GenericGroup

/-- Queries over an abstract label type: multiply two labels, or invert one label. -/
abbrev Query (L : Type) : Type := (L × L) ⊕ L

/-- Deeply embedded generic programs over `n` labels addressed by `Fin` indices.

`ret i` returns the `i`-th label; `mul i j k` and `inv i k` issue one oracle query over
the indexed labels and run the continuation `k` with the answer bound at a fresh index;
`eqTest i j kt kf` runs `kt` or `kf` depending on whether the indexed labels agree.

A program mentions labels only through indices: no constructor holds a label value, so a
program can neither inspect nor synthesize label representations. Indices address the
labels received so far — the inputs first, then the oracle answers in order — with
environments extended snoc-style (see `snocEnv`): the continuation of `mul`/`inv` sees
the answer at index `Fin.last _`, and earlier labels through `Fin.castSucc`. -/
inductive GProg : Nat → Type where
  | ret {n} (i : Fin n) : GProg n
  | mul {n} (i j : Fin n) (k : GProg (n + 1)) : GProg n
  | inv {n} (i : Fin n) (k : GProg (n + 1)) : GProg n
  | eqTest {n} (i j : Fin n) (kt kf : GProg n) : GProg n

/-- Snoc-style environment extension: append answer `x` after the `n` existing labels, so
the answer is found at index `Fin.last n` while earlier indices are preserved by
`Fin.castSucc`. -/
def snocEnv {L : Type} {n : Nat} (env : Fin n → L) (x : L) : Fin (n + 1) → L :=
  fun i => if h : (i : Nat) < n then env ⟨i, h⟩ else x

theorem snocEnv_pos {L : Type} {n : Nat} (env : Fin n → L) (x : L) (t : Fin (n + 1))
    (h : (t : Nat) < n) : snocEnv env x t = env ⟨(t : Nat), h⟩ := dite_eq_left h

theorem snocEnv_neg {L : Type} {n : Nat} (env : Fin n → L) (x : L) (t : Fin (n + 1))
    (h : ¬ (t : Nat) < n) : snocEnv env x t = x := dite_eq_right h

@[simp] theorem snocEnv_last {L : Type} {n : Nat} (env : Fin n → L) (x : L) :
    snocEnv env x (Fin.last n) = x := by
  have h : ¬ ((Fin.last n : Fin (n + 1)) : Nat) < n := by
    rw [Fin.val_last]
    exact lt_irrefl n
  exact snocEnv_neg env x _ h

@[simp] theorem snocEnv_castSucc {L : Type} {n : Nat} (env : Fin n → L) (x : L)
    (i : Fin n) : snocEnv env x i.castSucc = env i := by
  have h : ((i.castSucc : Fin (n + 1)) : Nat) < n := by
    rw [Fin.val_castSucc]
    exact i.isLt
  rw [snocEnv_pos env x _ h]
  congr 1

/-- Evaluate a program against an oracle: `mul`/`inv` extend the environment with the
oracle answer, `eqTest` branches on indexed equality via the evaluator's `DecidableEq`.
Structural recursion over the syntax, so evaluation always terminates. -/
def eval {L : Type} [DecidableEq L] (O : Query L → L) {n : Nat} (env : Fin n → L) :
    GProg n → L
  | .ret i => env i
  | .mul i j k => eval O (snocEnv env (O (.inl (env i, env j)))) k
  | .inv i k => eval O (snocEnv env (O (.inr (env i)))) k
  | .eqTest i j kt kf => if env i = env j then eval O env kt else eval O env kf

@[simp] theorem eval_ret {L : Type} [DecidableEq L] (O : Query L → L) {n : Nat}
    (env : Fin n → L) (i : Fin n) : eval O env (.ret i) = env i := rfl

@[simp] theorem eval_mul {L : Type} [DecidableEq L] (O : Query L → L) {n : Nat}
    (env : Fin n → L) (i j : Fin n) (k : GProg (n + 1)) :
    eval O env (.mul i j k) = eval O (snocEnv env (O (.inl (env i, env j)))) k := rfl

@[simp] theorem eval_inv {L : Type} [DecidableEq L] (O : Query L → L) {n : Nat}
    (env : Fin n → L) (i : Fin n) (k : GProg (n + 1)) :
    eval O env (.inv i k) = eval O (snocEnv env (O (.inr (env i)))) k := rfl

@[simp] theorem eval_eqTest {L : Type} [DecidableEq L] (O : Query L → L) {n : Nat}
    (env : Fin n → L) (i j : Fin n) (kt kf : GProg n) :
    eval O env (.eqTest i j kt kf)
      = (if env i = env j then eval O env kt else eval O env kf) := rfl

/-- Worst-case static query bound: `mul`/`inv` issue one query plus the continuation's,
`eqTest` takes the worse branch, `ret` issues none. Every program is finite syntax, `eval`
terminates by structural recursion, and the queries issued on any path are at most
`numQueries` (see `length_queriesOf_le`). -/
def numQueries {n : Nat} : GProg n → Nat
  | .ret _ => 0
  | .mul _ _ k => 1 + numQueries k
  | .inv _ k => 1 + numQueries k
  | .eqTest _ _ kt kf => max (numQueries kt) (numQueries kf)

@[simp] theorem numQueries_ret {n : Nat} (i : Fin n) :
    numQueries (.ret i) = 0 := rfl

@[simp] theorem numQueries_mul {n : Nat} (i j : Fin n) (k : GProg (n + 1)) :
    numQueries (.mul i j k) = 1 + numQueries k := rfl

@[simp] theorem numQueries_inv {n : Nat} (i : Fin n) (k : GProg (n + 1)) :
    numQueries (.inv i k) = 1 + numQueries k := rfl

@[simp] theorem numQueries_eqTest {n : Nat} (i j : Fin n) (kt kf : GProg n) :
    numQueries (.eqTest i j kt kf) = max (numQueries kt) (numQueries kf) := rfl

/-- The queries issued along the path `eval` takes: the same recursion as `eval`,
collecting each query instead of answering it. -/
def queriesOf {L : Type} [DecidableEq L] (O : Query L → L) {n : Nat} (env : Fin n → L) :
    GProg n → List (Query L)
  | .ret _ => []
  | .mul i j k => .inl (env i, env j) :: queriesOf O (snocEnv env (O (.inl (env i, env j)))) k
  | .inv i k => .inr (env i) :: queriesOf O (snocEnv env (O (.inr (env i)))) k
  | .eqTest i j kt kf => if env i = env j then queriesOf O env kt else queriesOf O env kf

@[simp] theorem queriesOf_ret {L : Type} [DecidableEq L] (O : Query L → L) {n : Nat}
    (env : Fin n → L) (i : Fin n) : queriesOf O env (.ret i) = [] := rfl

@[simp] theorem queriesOf_mul {L : Type} [DecidableEq L] (O : Query L → L) {n : Nat}
    (env : Fin n → L) (i j : Fin n) (k : GProg (n + 1)) :
    queriesOf O env (.mul i j k)
      = .inl (env i, env j) :: queriesOf O (snocEnv env (O (.inl (env i, env j)))) k := rfl

@[simp] theorem queriesOf_inv {L : Type} [DecidableEq L] (O : Query L → L) {n : Nat}
    (env : Fin n → L) (i : Fin n) (k : GProg (n + 1)) :
    queriesOf O env (.inv i k)
      = .inr (env i) :: queriesOf O (snocEnv env (O (.inr (env i)))) k := rfl

@[simp] theorem queriesOf_eqTest {L : Type} [DecidableEq L] (O : Query L → L) {n : Nat}
    (env : Fin n → L) (i j : Fin n) (kt kf : GProg n) :
    queriesOf O env (.eqTest i j kt kf)
      = (if env i = env j then queriesOf O env kt else queriesOf O env kf) := rfl

/-- The path `eval` takes issues at most `numQueries` queries, against every oracle. -/
theorem length_queriesOf_le {L : Type} [DecidableEq L] (O : Query L → L) {n : Nat}
    (env : Fin n → L) (p : GProg n) :
    (queriesOf O env p).length ≤ numQueries p := by
  induction p with
  | ret i => simp [queriesOf_ret, numQueries_ret]
  | mul i j k ih =>
    simp only [queriesOf_mul, numQueries_mul, List.length_cons]
    have h := ih (snocEnv env (O (.inl (env i, env j))))
    omega
  | inv i k ih =>
    simp only [queriesOf_inv, numQueries_inv, List.length_cons]
    have h := ih (snocEnv env (O (.inr (env i))))
    omega
  | eqTest i j kt kf iht ihf =>
    simp only [queriesOf_eqTest, numQueries_eqTest]
    by_cases h : env i = env j
    · have e : (if env i = env j then queriesOf O env kt else queriesOf O env kf)
          = queriesOf O env kt := by simp [h]
      rw [e]
      exact (iht env).trans (Nat.le_max_left _ _)
    · have e : (if env i = env j then queriesOf O env kt else queriesOf O env kf)
          = queriesOf O env kf := by simp [h]
      rw [e]
      exact (ihf env).trans (Nat.le_max_right _ _)

/-- Compiler from `GProg` source syntax into the canonical `OracleComp` execution
framework: `ret` is `pure` of the indexed label, `mul`/`inv` issue one oracle query
over the indexed labels and compile the continuation against the snoc-extended
environment, and `eqTest` is pure branching on indexed equality. The compiler runs at
the evaluator, over evaluator-supplied environments, so compiled programs hold no
label values beyond their inputs. -/
def GProg.compile {L : Type} [DecidableEq L] {n : Nat} (env : Fin n → L) :
    GProg n → OracleComp (Query L) L L
  | .ret i => .pure (env i)
  | .mul i j k => OracleComp.query (.inl (env i, env j)) fun ans =>
      compile (snocEnv env ans) k
  | .inv i k => OracleComp.query (.inr (env i)) fun ans =>
      compile (snocEnv env ans) k
  | .eqTest i j kt kf => if env i = env j then compile env kt else compile env kf

@[simp] theorem compile_ret {L : Type} [DecidableEq L] {n : Nat} (env : Fin n → L)
    (i : Fin n) : GProg.compile env (.ret i) = .pure (env i) := rfl

@[simp] theorem compile_mul {L : Type} [DecidableEq L] {n : Nat} (env : Fin n → L)
    (i j : Fin n) (k : GProg (n + 1)) :
    GProg.compile env (.mul i j k) = OracleComp.query (.inl (env i, env j)) fun ans =>
      GProg.compile (snocEnv env ans) k := rfl

@[simp] theorem compile_inv {L : Type} [DecidableEq L] {n : Nat} (env : Fin n → L)
    (i : Fin n) (k : GProg (n + 1)) :
    GProg.compile env (.inv i k) = OracleComp.query (.inr (env i)) fun ans =>
      GProg.compile (snocEnv env ans) k := rfl

@[simp] theorem compile_eqTest {L : Type} [DecidableEq L] {n : Nat} (env : Fin n → L)
    (i j : Fin n) (kt kf : GProg n) :
    GProg.compile env (.eqTest i j kt kf)
      = (if env i = env j then GProg.compile env kt else GProg.compile env kf) := rfl

/-- Running a compiled program through the canonical `OracleComp.run` agrees with the
reference evaluator. -/
theorem compile_run {L : Type} [DecidableEq L] (O : Query L → L) {n : Nat}
    (env : Fin n → L) (p : GProg n) :
    OracleComp.run O (GProg.compile env p) = eval O env p := by
  induction p with
  | ret i => rfl
  | mul i j k ih => exact ih _
  | inv i k ih => exact ih _
  | eqTest i j kt kf iht ihf =>
    simp only [compile_eqTest, eval_eqTest]
    by_cases h : env i = env j
    · have e : (if env i = env j then GProg.compile env kt else GProg.compile env kf)
          = GProg.compile env kt := by simp [h]
      rw [e]
      have e' : (if env i = env j then eval O env kt else eval O env kf)
          = eval O env kt := by simp [h]
      rw [e']
      exact iht _
    · have e : (if env i = env j then GProg.compile env kt else GProg.compile env kf)
          = GProg.compile env kf := by simp [h]
      rw [e]
      have e' : (if env i = env j then eval O env kt else eval O env kf)
          = eval O env kf := by simp [h]
      rw [e']
      exact ihf _

/-- The static `numQueries` bound is a canonical structural query bound on the compiled
program, hence bounds every run by `OracleComp.length_queries_le`. -/
theorem isQueryBounded_compile {L : Type} [DecidableEq L] {n : Nat} (env : Fin n → L)
    (p : GProg n) :
    FreeM.IsQueryBounded (numQueries p) (GProg.compile env p) := by
  induction p with
  | ret i =>
    simp only [compile_ret, numQueries_ret]
    exact FreeM.isQueryBounded_pure _ _
  | mul i j k ih =>
    simp only [compile_mul, numQueries_mul]
    rw [add_comm (1 : ℕ)]
    exact FreeM.isQueryBounded_liftBind fun b => ih _
  | inv i k ih =>
    simp only [compile_inv, numQueries_inv]
    rw [add_comm (1 : ℕ)]
    exact FreeM.isQueryBounded_liftBind fun b => ih _
  | eqTest i j kt kf iht ihf =>
    simp only [compile_eqTest, numQueries_eqTest]
    by_cases h : env i = env j
    · have e : (if env i = env j then GProg.compile env kt else GProg.compile env kf)
          = GProg.compile env kt := by simp [h]
      rw [e]
      exact FreeM.IsQueryBounded.mono (Nat.le_max_left _ _) (iht _)
    · have e : (if env i = env j then GProg.compile env kt else GProg.compile env kf)
          = GProg.compile env kf := by simp [h]
      rw [e]
      exact FreeM.IsQueryBounded.mono (Nat.le_max_right _ _) (ihf _)

/-- Canonical transcript of one framework query followed by a continuation. -/
theorem queries_query {L : Type} (O : Query L → L) (x : Query L)
    (k : L → OracleComp (Query L) L L) :
    OracleComp.queries O (OracleComp.query x k) = x :: OracleComp.queries O (k (O x)) :=
  rfl

/-- The canonical query transcript of a compiled program is the reference trace. -/
theorem compile_queries {L : Type} [DecidableEq L] (O : Query L → L) {n : Nat}
    (env : Fin n → L) (p : GProg n) :
    OracleComp.queries O (GProg.compile env p) = queriesOf O env p := by
  induction p with
  | ret i => rfl
  | mul i j k ih =>
    simp only [compile_mul, queriesOf_mul, queries_query]
    rw [ih _]
  | inv i k ih =>
    simp only [compile_inv, queriesOf_inv, queries_query]
    rw [ih _]
  | eqTest i j kt kf iht ihf =>
    simp only [compile_eqTest, queriesOf_eqTest]
    by_cases h : env i = env j
    · have e : (if env i = env j then GProg.compile env kt else GProg.compile env kf)
          = GProg.compile env kt := by simp [h]
      rw [e]
      have e' : (if env i = env j then queriesOf O env kt else queriesOf O env kf)
          = queriesOf O env kt := by simp [h]
      rw [e']
      exact iht _
    · have e : (if env i = env j then GProg.compile env kt else GProg.compile env kf)
          = GProg.compile env kf := by simp [h]
      rw [e]
      have e' : (if env i = env j then queriesOf O env kt else queriesOf O env kf)
          = queriesOf O env kf := by simp [h]
      rw [e']
      exact ihf _

/-- Labels are exponents modulo `q`: the label of `a` stands for `g ^ a`. -/
abbrev Label (q : ℕ) [Fact (1 < q)] : Type := ZMod q

/-- The generic-group oracle under a fixed encoding permutation: decode the labels,
add (or negate) the exponents, and re-encode. -/
def oracleOf {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) : Query (Label q) → Label q
  | .inl (a, b) => enc (enc.symm a + enc.symm b)
  | .inr a => enc (-enc.symm a)

theorem oracleOf_inl {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q))
    (a b : Label q) :
    oracleOf enc (.inl (a, b)) = enc (enc.symm a + enc.symm b) := rfl

/-- The identity label under a fixed encoding: the encoding of exponent `0`. Note this
is `enc 0`, not the literal label `0`; the two agree only if `enc` fixes `0`. -/
def idLabel {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) : Label q := enc 0

/-- Represented multiplication, through the oracle. -/
def gmul {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) (a b : Label q) : Label q :=
  oracleOf enc (.inl (a, b))

/-- Represented inversion, through the oracle. -/
def ginv {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) (a : Label q) : Label q :=
  oracleOf enc (.inr a)

@[simp] theorem gmul_eq {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) (a b : Label q) :
    gmul enc a b = enc (enc.symm a + enc.symm b) := rfl

@[simp] theorem ginv_eq {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) (a : Label q) :
    ginv enc a = enc (-enc.symm a) := rfl

@[simp] theorem idLabel_eq {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) :
    idLabel enc = enc 0 := rfl

/-- Represented multiplication is associative, for every encoding. -/
theorem gmul_assoc {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) (a b c : Label q) :
    gmul enc (gmul enc a b) c = gmul enc a (gmul enc b c) := by
  simp only [gmul_eq, Equiv.symm_apply_apply]
  congr 1
  exact add_assoc _ _ _

/-- The identity label is a right identity, for every encoding. -/
theorem gmul_id {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) (a : Label q) :
    gmul enc a (idLabel enc) = a := by
  simp only [gmul_eq, idLabel_eq, Equiv.symm_apply_apply, add_zero,
    Equiv.apply_symm_apply]

/-- The identity label is a left identity, for every encoding. -/
theorem id_gmul {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) (a : Label q) :
    gmul enc (idLabel enc) a = a := by
  simp only [gmul_eq, idLabel_eq, Equiv.symm_apply_apply, zero_add,
    Equiv.apply_symm_apply]

/-- Right inverse law, for every encoding. -/
theorem gmul_ginv {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) (a : Label q) :
    gmul enc a (ginv enc a) = idLabel enc := by
  simp only [gmul_eq, ginv_eq, idLabel_eq, Equiv.symm_apply_apply, add_neg_cancel]

/-- Left inverse law, for every encoding. -/
theorem ginv_gmul {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) (a : Label q) :
    gmul enc (ginv enc a) a = idLabel enc := by
  simp only [gmul_eq, ginv_eq, idLabel_eq, Equiv.symm_apply_apply, neg_add_cancel]

/-- Evaluate a deeply embedded program against the fixed-encoding oracle, through the
canonical execution: compile the `GProg` source program and run it with
`OracleComp.run`. Only `GProg` syntax is accepted: there is no way to supply a literal
label. -/
def runProg {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q))
    {n : Nat} (inputs : Fin n → Label q) (p : GProg n) : Label q :=
  OracleComp.run (oracleOf enc) (GProg.compile inputs p)

theorem runProg_eq {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q))
    {n : Nat} (inputs : Fin n → Label q) (p : GProg n) :
    runProg enc inputs p
      = OracleComp.run (oracleOf enc) (GProg.compile inputs p) := rfl

/-- The canonical run agrees with the reference evaluator. -/
theorem runProg_eq_eval {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q))
    {n : Nat} (inputs : Fin n → Label q) (p : GProg n) :
    runProg enc inputs p = eval (oracleOf enc) inputs p :=
  compile_run _ _ _

/-- Inputs for `powProg`: the accumulator at index `0`, the base at index `1`. -/
def powInputs {q : ℕ} [Fact (1 < q)] (acc base : Label q) : Fin 2 → Label q :=
  fun i => if i = 0 then acc else base

@[simp] theorem powInputs_zero {q : ℕ} [Fact (1 < q)] (acc base : Label q) :
    powInputs acc base 0 = acc := by simp [powInputs]

@[simp] theorem powInputs_one {q : ℕ} [Fact (1 < q)] (acc base : Label q) :
    powInputs acc base 1 = base := by
  simp [powInputs, show (1 : Fin 2) ≠ 0 from by decide]

/-- Recursion behind `powProg`: starting from accumulator index `acc` and base index
`base`, issue one multiplication query per step for `m` steps, rebinding the accumulator
to each answer. -/
def powProgAux (m : Nat) {n : Nat} (acc base : Fin n) : GProg n :=
  match m with
  | 0 => .ret acc
  | m + 1 => .mul acc base (powProgAux m (Fin.last n) base.castSucc)

@[simp] theorem powProgAux_zero {n : Nat} (acc base : Fin n) :
    powProgAux 0 acc base = .ret acc := rfl

@[simp] theorem powProgAux_succ (m : Nat) {n : Nat} (acc base : Fin n) :
    powProgAux (m + 1) acc base
      = .mul acc base (powProgAux m (Fin.last n) base.castSucc) := rfl

/-- Honest exponentiation as a deeply embedded program: from accumulator and base inputs,
issue one multiplication query per step for `m` steps. The program is pure `GProg`
syntax over indices `0` and `1`. -/
def powProg (m : Nat) : GProg 2 := powProgAux m 0 1

theorem powProg_eq (m : Nat) : powProg m = powProgAux m 0 1 := rfl

/-- Correctness of `powProgAux` from any accumulator: evaluation encodes `m • x + a`,
where `x` is the base exponent and `a` the accumulator exponent. -/
theorem eval_powProgAux {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) (m : ℕ)
    {n : ℕ} (env : Fin n → Label q) (acc base : Fin n) :
    eval (oracleOf enc) env (powProgAux m acc base)
      = enc (m • enc.symm (env base) + enc.symm (env acc)) := by
  induction m generalizing n env acc base with
  | zero =>
    simp only [powProgAux_zero, eval_ret, zero_nsmul, zero_add, Equiv.apply_symm_apply]
  | succ m ih =>
    simp only [powProgAux_succ, eval_mul, ih, snocEnv_last, snocEnv_castSucc,
      oracleOf_inl, Equiv.symm_apply_apply]
    congr 1
    rw [add_nsmul, one_nsmul]
    abel

/-- Honest exponentiation is correct: from the supplied identity label and base label, the
run is the encoding of `m • x`. The literal label `0` is never assumed to be the
identity. -/
theorem run_powProg {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) (m : ℕ)
    (x : ZMod q) :
    runProg enc (powInputs (idLabel enc) (enc x)) (powProg m) = enc (m • x) := by
  rw [runProg_eq_eval, powProg_eq, eval_powProgAux, powInputs_zero, powInputs_one]
  simp only [idLabel_eq, Equiv.symm_apply_apply, add_zero]

/-- The exponentiation recursion issues exactly `m` queries. -/
theorem numQueries_powProgAux (m : ℕ) {n : ℕ} (acc base : Fin n) :
    numQueries (powProgAux m acc base) = m := by
  induction m generalizing n acc base with
  | zero => simp only [powProgAux_zero, numQueries_ret]
  | succ m ih =>
    simp only [powProgAux_succ, numQueries_mul, ih]
    omega

/-- The exponentiation program issues exactly `m` queries. -/
theorem numQueries_powProg (m : ℕ) : numQueries (powProg m) = m :=
  numQueries_powProgAux m 0 1

/-- The exponentiation recursion issues exactly `m` queries along its path, against every
oracle. -/
theorem length_queriesOf_powProgAux {L : Type} [DecidableEq L] (O : Query L → L)
    (m : ℕ) {n : ℕ} (env : Fin n → L) (acc base : Fin n) :
    (queriesOf O env (powProgAux m acc base)).length = m := by
  induction m generalizing n env acc base with
  | zero => simp [powProgAux_zero, queriesOf_ret]
  | succ m ih =>
    simp only [powProgAux_succ, queriesOf_mul, List.length_cons, ih]

/-- The exponentiation program issues exactly `m` queries along its path, against every
oracle. -/
theorem length_queriesOf_powProg {L : Type} [DecidableEq L] (O : Query L → L) (m : ℕ)
    (env : Fin 2 → L) :
    (queriesOf O env (powProg m)).length = m :=
  length_queriesOf_powProgAux O m env 0 1

/-- Environment extension respects relabeling: if `env2 = phi ∘ env1` and the new
answers agree up to `phi`, so do the extended environments. -/
theorem snocEnv_congr_phi {L L' : Type} (phi : L ≃ L') {n : Nat}
    (env1 : Fin n → L) (env2 : Fin n → L') (henv : ∀ i, env2 i = phi (env1 i))
    (x1 : L) (x2 : L') (hx : x2 = phi x1) (t : Fin (n + 1)) :
    snocEnv env2 x2 t = phi (snocEnv env1 x1 t) := by
  by_cases h : (t : Nat) < n
  · rw [snocEnv_pos _ _ _ h, snocEnv_pos _ _ _ h, henv]
  · rw [snocEnv_neg _ _ _ h, snocEnv_neg _ _ _ h, hx]

/-- Naturality (relabeling invariance): evaluation commutes with any label renaming `phi`
that the oracles respect. If the environments agree up to `phi`, so do the results. -/
theorem eval_natural {L L' : Type} [DecidableEq L] [DecidableEq L']
    (O1 : Query L → L) (O2 : Query L' → L') (phi : L ≃ L')
    (hmul : ∀ a b, O2 (.inl (phi a, phi b)) = phi (O1 (.inl (a, b))))
    (hinv : ∀ a, O2 (.inr (phi a)) = phi (O1 (.inr a)))
    {n : Nat} (p : GProg n) (env1 : Fin n → L) (env2 : Fin n → L')
    (henv : ∀ i, env2 i = phi (env1 i)) :
    eval O2 env2 p = phi (eval O1 env1 p) := by
  induction p with
  | ret i =>
    simp only [eval_ret]
    exact henv i
  | mul i j k ih =>
    simp only [eval_mul]
    refine ih _ _ ?_
    intro t
    refine snocEnv_congr_phi _ _ _ henv _ _ ?_ t
    rw [henv i, henv j, hmul]
  | inv i k ih =>
    simp only [eval_inv]
    refine ih _ _ ?_
    intro t
    refine snocEnv_congr_phi _ _ _ henv _ _ ?_ t
    rw [henv i, hinv]
  | eqTest i j kt kf iht ihf =>
    simp only [eval_eqTest]
    have hiff : env2 i = env2 j ↔ env1 i = env1 j := by
      rw [henv i, henv j]
      exact ⟨fun h => phi.injective h, congrArg phi⟩
    by_cases h : env1 i = env1 j
    · have e2 : (if env2 i = env2 j then eval O2 env2 kt else eval O2 env2 kf)
          = eval O2 env2 kt := by simp [hiff.mpr h]
      have e1 : (if env1 i = env1 j then eval O1 env1 kt else eval O1 env1 kf)
          = eval O1 env1 kt := by simp [h]
      rw [e2, e1]
      exact iht _ _ henv
    · have e2 : (if env2 i = env2 j then eval O2 env2 kt else eval O2 env2 kf)
          = eval O2 env2 kf := by simp [show env2 i ≠ env2 j from fun hh => h (hiff.mp hh)]
      have e1 : (if env1 i = env1 j then eval O1 env1 kt else eval O1 env1 kf)
          = eval O1 env1 kf := by simp [h]
      rw [e2, e1]
      exact ihf _ _ henv

end Cslib.Crypto.Framework.GenericGroup
