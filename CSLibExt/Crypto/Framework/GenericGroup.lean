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

`Prog L α` alone enforces nothing: it is just an `OracleComp` over group-operation queries
`Query L`, so a caller-specialized value such as `.pure 0 : Prog (Label q) (Label q)` is a
perfectly good `Prog`. The genericity interface is `GenericProg`: a program polymorphic in
the label type `L` that uses only oracle queries (and the given `DecidableEq L`) to obtain
and combine labels. Because such a program is polymorphic in `L`, it cannot inspect or
synthesize label representations: there is no literal label to write down and no native
arithmetic on labels to perform; every label it handles comes from its inputs or from
oracle answers. The `.pure 0` shape is not a `GenericProg` — it pins down the concrete
`Label q` — and is rejected by `runProg`'s signature, which accepts only `GenericProg`.

The concrete representation exists only in the evaluator: the encoding permutation `enc`,
the `ZMod q` arithmetic, and the `enc`/`enc.symm` conversions appear only in `oracleOf`,
`idLabel`, `gmul`, `ginv`, and `runProg`, which instantiates `L := Label q` to evaluate a
generic program against the deterministic oracle `oracleOf enc` for the fixed encoding.
-/

@[expose] public section

namespace Cslib.Crypto.Framework.GenericGroup

/-- Queries over an abstract label type: multiply two labels, or invert one label. -/
abbrev Query (L : Type) : Type := (L × L) ⊕ L

/-- A generic program over abstract labels: an oracle computation over group-operation
queries, polymorphic in the label type `L`. -/
abbrev Prog (L : Type) (α : Type) : Type := OracleComp (Query L) L α

/-- A caller-facing generic program with inputs in `iota L` and outputs in `omega L`,
polymorphic in the label type `L`. The caller cannot pick `L` — the evaluator
instantiates it — so there are no literal labels to write down and no native arithmetic
on labels to perform; labels can only be passed along, combined through oracle queries,
and compared for equality via the given `DecidableEq L`. -/
def GenericProg (iota omega : Type → Type) : Type 1 :=
  ∀ (L : Type) [DecidableEq L], iota L → Prog L (omega L)

/-- Labels are exponents modulo `q`: the label of `a` stands for `g ^ a`. -/
abbrev Label (q : ℕ) [Fact (1 < q)] : Type := ZMod q

/-- The generic-group oracle under a fixed encoding permutation: decode the labels,
add (or negate) the exponents, and re-encode. -/
def oracleOf {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) : Query (Label q) → Label q
  | .inl (a, b) => enc (enc.symm a + enc.symm b)
  | .inr a => enc (-enc.symm a)

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

/-- Evaluate a generic program against the fixed-encoding oracle, instantiating the
abstract label type at `Label q`. Only `GenericProg` values are accepted: a
caller-specialized `Prog (Label q)` is rejected by the signature. -/
def runProg {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q))
    {iota omega : Type → Type} (P : GenericProg iota omega) (i : iota (Label q)) :
    omega (Label q) :=
  OracleComp.run (oracleOf enc) (P _ i)

theorem runProg_eq {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q))
    {iota omega : Type → Type} (P : GenericProg iota omega) (i : iota (Label q)) :
    runProg enc P i = OracleComp.run (oracleOf enc) (P _ i) := rfl

/-- Recursion behind `powProg`: starting from an accumulator and a base label, issue one
multiplication query per step for `n` steps. -/
def powProgAux {L : Type} : ℕ → L → L → Prog L L
  | 0, acc, _ => .pure acc
  | n + 1, acc, base =>
    OracleComp.query (.inl (acc, base)) fun lbl => powProgAux n lbl base

/-- Honest exponentiation as a generic program: from `(n, acc, base)`, issue one
multiplication query per step for `n` steps. The program is polymorphic in the label type
and built only from oracle queries, `pure`, and `bind` over the given input labels. -/
def powProg : GenericProg (fun L => ℕ × L × L) id :=
  fun _ _ p => powProgAux p.1 p.2.1 p.2.2

@[simp] theorem run_powProg_zero {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q))
    (acc base : Label q) : runProg enc powProg (0, acc, base) = acc := rfl

@[simp] theorem run_powProg_succ {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) (n : ℕ)
    (acc base : Label q) :
    runProg enc powProg (n + 1, acc, base) =
      runProg enc powProg (n, gmul enc acc base, base) := rfl

@[simp] theorem queries_powProg_zero {L : Type} [DecidableEq L] (O : Query L → L)
    (acc base : L) :
    OracleComp.queries O (powProg L (0, acc, base)) = [] := rfl

@[simp] theorem queries_powProg_succ {L : Type} [DecidableEq L] (O : Query L → L) (n : ℕ)
    (acc base : L) :
    OracleComp.queries O (powProg L (n + 1, acc, base)) =
      .inl (acc, base) :: OracleComp.queries O
        (powProg L (n, O (.inl (acc, base)), base)) := rfl

/-- Correctness of `powProg` from any accumulator: the run encodes `n • x + a`, where `x`
is the base exponent and `a` the accumulator exponent. -/
theorem run_powProg_core {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) (n : ℕ)
    (acc base : Label q) :
    runProg enc powProg (n, acc, base) = enc (n • enc.symm base + enc.symm acc) := by
  induction n generalizing acc with
  | zero => simp only [run_powProg_zero, zero_nsmul, zero_add, Equiv.apply_symm_apply]
  | succ n ih =>
    simp only [run_powProg_succ, ih, gmul_eq, Equiv.symm_apply_apply]
    congr 1
    rw [add_nsmul, one_nsmul]
    abel

/-- Honest exponentiation is correct: from the supplied identity label and base label, the
run is the encoding of `n • x`. The literal label `0` is never assumed to be the identity. -/
theorem run_powProg {q : ℕ} [Fact (1 < q)] (enc : Equiv.Perm (ZMod q)) (n : ℕ) (x : ZMod q) :
    runProg enc powProg (n, idLabel enc, enc x) = enc (n • x) := by
  simp only [run_powProg_core, idLabel_eq, Equiv.symm_apply_apply, add_zero]

/-- The exponentiation program issues exactly `n` queries, against every oracle and at
every label type. -/
theorem queries_powProg_length {L : Type} [DecidableEq L] (O : Query L → L) (n : ℕ)
    (acc base : L) :
    (OracleComp.queries O (powProg L (n, acc, base))).length = n := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih => simp only [queries_powProg_succ, List.length_cons, ih]

/-- The exponentiation program is structurally `n`-bounded at every label type, hence
bounded against every oracle by `OracleComp.length_queries_le`. -/
theorem isQueryBounded_powProg {L : Type} [DecidableEq L] (n : ℕ) (acc base : L) :
    FreeM.IsQueryBounded n (powProg L (n, acc, base)) := by
  induction n generalizing acc with
  | zero => exact FreeM.isQueryBounded_pure _ _
  | succ n ih => exact FreeM.isQueryBounded_liftBind fun b => ih b

end Cslib.Crypto.Framework.GenericGroup
