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
# Generic group model over `OracleComp`

A functional-coherence model of a generic group of order `q`, evaluated through
`Cslib.Crypto.Framework.OracleComp`: programs are oracle computations whose queries are
group multiplications and inversions of opaque labels, answered by a fixed encoding oracle.

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

A generic program is an `OracleComp` value over group-operation queries, evaluated by
`OracleComp.run` against the deterministic oracle `oracleOf enc` for the fixed encoding.
The program type does not by itself prevent native arithmetic on labels inside
continuations; genericity of the concrete exponentiation program is certified structurally:
`powProg` is built only from oracle queries, `pure`, and `bind` over the given input labels.
-/

@[expose] public section

namespace Cslib.Crypto.Framework.GenericGroup

/-- Labels are exponents modulo `q`: the label of `a` stands for `g ^ a`. -/
abbrev Label (q : ℕ) : Type := ZMod q

/-- Queries: multiply two labels, or invert one label. -/
abbrev Query (q : ℕ) : Type := (Label q × Label q) ⊕ Label q

/-- The generic-group oracle under a fixed encoding permutation: decode the labels,
add (or negate) the exponents, and re-encode. -/
def oracleOf {q : ℕ} (enc : Equiv.Perm (ZMod q)) : Query q → Label q
  | .inl (a, b) => enc (enc.symm a + enc.symm b)
  | .inr a => enc (-enc.symm a)

/-- The identity label under a fixed encoding: the encoding of exponent `0`. Note this
is `enc 0`, not the literal label `0`; the two agree only if `enc` fixes `0`. -/
def idLabel {q : ℕ} (enc : Equiv.Perm (ZMod q)) : Label q := enc 0

/-- Represented multiplication, through the oracle. -/
def gmul {q : ℕ} (enc : Equiv.Perm (ZMod q)) (a b : Label q) : Label q :=
  oracleOf enc (.inl (a, b))

/-- Represented inversion, through the oracle. -/
def ginv {q : ℕ} (enc : Equiv.Perm (ZMod q)) (a : Label q) : Label q :=
  oracleOf enc (.inr a)

@[simp] theorem gmul_eq {q : ℕ} (enc : Equiv.Perm (ZMod q)) (a b : Label q) :
    gmul enc a b = enc (enc.symm a + enc.symm b) := rfl

@[simp] theorem ginv_eq {q : ℕ} (enc : Equiv.Perm (ZMod q)) (a : Label q) :
    ginv enc a = enc (-enc.symm a) := rfl

@[simp] theorem idLabel_eq {q : ℕ} (enc : Equiv.Perm (ZMod q)) : idLabel enc = enc 0 := rfl

/-- Represented multiplication is associative, for every encoding. -/
theorem gmul_assoc {q : ℕ} (enc : Equiv.Perm (ZMod q)) (a b c : Label q) :
    gmul enc (gmul enc a b) c = gmul enc a (gmul enc b c) := by
  simp only [gmul_eq, Equiv.symm_apply_apply]
  congr 1
  exact add_assoc _ _ _

/-- The identity label is a right identity, for every encoding. -/
theorem gmul_id {q : ℕ} (enc : Equiv.Perm (ZMod q)) (a : Label q) :
    gmul enc a (idLabel enc) = a := by
  simp only [gmul_eq, idLabel_eq, Equiv.symm_apply_apply, add_zero,
    Equiv.apply_symm_apply]

/-- The identity label is a left identity, for every encoding. -/
theorem id_gmul {q : ℕ} (enc : Equiv.Perm (ZMod q)) (a : Label q) :
    gmul enc (idLabel enc) a = a := by
  simp only [gmul_eq, idLabel_eq, Equiv.symm_apply_apply, zero_add,
    Equiv.apply_symm_apply]

/-- Right inverse law, for every encoding. -/
theorem gmul_ginv {q : ℕ} (enc : Equiv.Perm (ZMod q)) (a : Label q) :
    gmul enc a (ginv enc a) = idLabel enc := by
  simp only [gmul_eq, ginv_eq, idLabel_eq, Equiv.symm_apply_apply, add_neg_cancel]

/-- Left inverse law, for every encoding. -/
theorem ginv_gmul {q : ℕ} (enc : Equiv.Perm (ZMod q)) (a : Label q) :
    gmul enc (ginv enc a) a = idLabel enc := by
  simp only [gmul_eq, ginv_eq, idLabel_eq, Equiv.symm_apply_apply, neg_add_cancel]

/-- A generic program: an oracle computation over group-operation queries. See the module
documentation for the genericity limitation this type does and does not enforce. -/
abbrev Prog (q : ℕ) (α : Type) : Type := OracleComp (Query q) (Label q) α

/-- Evaluate a generic program against the fixed-encoding oracle. -/
def runProg {q : ℕ} (enc : Equiv.Perm (ZMod q)) {α : Type} (c : Prog q α) : α :=
  OracleComp.run (oracleOf enc) c

theorem runProg_eq {q : ℕ} (enc : Equiv.Perm (ZMod q)) {α : Type} (c : Prog q α) :
    runProg enc c = OracleComp.run (oracleOf enc) c := rfl

/-- Honest exponentiation: starting from an accumulator (the identity label) and a base
label, issue one multiplication query per step for `n` steps. The program is built only
from oracle queries, `pure`, and `bind` over the given input labels. -/
def powProg {q : ℕ} : ℕ → Label q → Label q → Prog q (Label q)
  | 0, acc, _ => .pure acc
  | n + 1, acc, base =>
    OracleComp.query (.inl (acc, base)) fun lbl => powProg n lbl base

@[simp] theorem run_powProg_zero {q : ℕ} (enc : Equiv.Perm (ZMod q))
    (acc base : Label q) : runProg enc (powProg 0 acc base) = acc := rfl

@[simp] theorem run_powProg_succ {q : ℕ} (enc : Equiv.Perm (ZMod q)) (n : ℕ)
    (acc base : Label q) :
    runProg enc (powProg (n + 1) acc base) =
      runProg enc (powProg n (gmul enc acc base) base) := rfl

@[simp] theorem queries_powProg_zero {q : ℕ} (enc : Equiv.Perm (ZMod q))
    (acc base : Label q) :
    OracleComp.queries (oracleOf enc) (powProg 0 acc base) = [] := rfl

@[simp] theorem queries_powProg_succ {q : ℕ} (enc : Equiv.Perm (ZMod q)) (n : ℕ)
    (acc base : Label q) :
    OracleComp.queries (oracleOf enc) (powProg (n + 1) acc base) =
      .inl (acc, base) :: OracleComp.queries (oracleOf enc)
        (powProg n (gmul enc acc base) base) := rfl

/-- Correctness of `powProg` from any accumulator: the run encodes `n • x + a`, where `x`
is the base exponent and `a` the accumulator exponent. -/
theorem run_powProg_core {q : ℕ} (enc : Equiv.Perm (ZMod q)) (n : ℕ)
    (acc base : Label q) :
    runProg enc (powProg n acc base) = enc (n • enc.symm base + enc.symm acc) := by
  induction n generalizing acc with
  | zero => simp only [run_powProg_zero, zero_nsmul, zero_add, Equiv.apply_symm_apply]
  | succ n ih =>
    simp only [run_powProg_succ, ih, gmul_eq, Equiv.symm_apply_apply]
    congr 1
    rw [add_nsmul, one_nsmul]
    abel

/-- Honest exponentiation is correct: from the supplied identity label and base label, the
run is the encoding of `n • x`. The literal label `0` is never assumed to be the identity. -/
theorem run_powProg {q : ℕ} (enc : Equiv.Perm (ZMod q)) (n : ℕ) (x : ZMod q) :
    runProg enc (powProg n (idLabel enc) (enc x)) = enc (n • x) := by
  simp only [run_powProg_core, idLabel_eq, Equiv.symm_apply_apply, add_zero]

/-- The exponentiation program issues exactly `n` queries. -/
theorem queries_powProg_length {q : ℕ} (enc : Equiv.Perm (ZMod q)) (n : ℕ)
    (acc base : Label q) :
    (OracleComp.queries (oracleOf enc) (powProg n acc base)).length = n := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih => simp only [queries_powProg_succ, List.length_cons, ih]

/-- The exponentiation program is structurally `n`-bounded, hence bounded against every
oracle by `OracleComp.length_queries_le`. -/
theorem isQueryBounded_powProg {q : ℕ} (n : ℕ) (acc base : Label q) :
    FreeM.IsQueryBounded n (powProg n acc base) := by
  induction n generalizing acc with
  | zero => exact FreeM.isQueryBounded_pure _ _
  | succ n ih => exact FreeM.isQueryBounded_liftBind fun b => ih b

end Cslib.Crypto.Framework.GenericGroup
