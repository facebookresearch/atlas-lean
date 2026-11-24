/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# QSAT_k is Sigma_k^P-complete, uniformly in k

Source:
L. J. Stockmeyer, "The polynomial-time hierarchy", Theoretical Computer Science 3 (1977),
1-22; A. R. Meyer, "A polynomial hierarchy" (see also S. Arora and B. Barak, Computational
Complexity: A Modern Approach, 2009, Chapter 5).
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Computability.Complexity
public import MathlibExt.Computability.BinaryNatEncoding
public import CSLibExt.Computability.CookLevin
public import CSLibExt.Computability.Complexity.Classes

@[expose] public section

namespace MetaMathlibExt.Complexity.KeyTheorems.QSATKComplete

open Cslib.Complexity.Classes
open MetaMathlibExt.ComplexityTheory

/-!
# QSAT_k is Sigma_k^P-complete, uniformly in k

`QSAT_k`, the set of true quantified Boolean formulas whose quantifier prefix has exactly `k`
alternating blocks (starting with `∃`), is `Σ_k^p`-complete, uniformly in `k`: for every
`k ≥ 1`, `QSAT_k` is in `Σ_k^p` and every `Σ_k^p` language polynomial-time many-one
reduces to it. The case `k = 1` is SAT, the case of unbounded `k` is TQBF. (For `k = 0` the
statement would be false: quantifier-free satisfiability is NP-complete, while `Σ_0^p = P`,
so the uniform statement is over `k + 1`.) The matrix is an unrestricted Boolean circuit
(AND/OR/NOT gates over the quantified variables, with sharing), not a CNF: a CNF
matrix does not give the claimed complete problem at every depth. For example, with a CNF
matrix, `QSAT_2` is `∃ ∀ CNF`, and after guessing the existential variables the universal
part is checkable clause-by-clause in polynomial time (a CNF is universally valid iff
every clause is), so the CNF version would lie in `NP`, and `Σ_2^p`-hardness would collapse
`Σ_2^p` to `NP`. The instance decodes to a quantifier prefix (existential `true` /
universal `false` paired with a variable index) and an unrestricted circuit matrix;
well-formedness requires the prefix to be nonempty with first quantifier existential,
to quantify each variable `0, …, m - 1` exactly once, every formula variable to be
quantified, and the prefix to have exactly `k` blocks.
-/

/-- **Gates of a quantified Boolean formula matrix.** A gate of a matrix circuit is a pair $(t, r)$
of a natural number $t$, its kind, and a list $r$ of natural numbers, its references. The kinds
are read as follows: kind $0$ with $r = [v]$ is the variable $v$, kind $1$ with $r = [b]$ is the
constant true if $b = 1$ and false otherwise, kind $2$ is a negation, kind $3$ a conjunction and
kind $4$ a disjunction, where for kinds $2$, $3$ and $4$ the references are indices of gates.

A circuit matrix is thus an unrestricted Boolean formula with sharing, not a formula in
conjunctive normal form. -/
abbrev QBFMatrixGate := ℕ × List ℕ

/-- **Evaluation of a QBF matrix gate.** Given a list $s$ of truth values (the values of the earlier
gates) and an assignment $\alpha$ of a truth value to every natural number, the value of a gate
$(t, r)$ is computed as follows, where $s_a$ is the $a$-th entry of $s$ if $a$ is less than the
length of $s$ and false otherwise: if $t = 0$ and $r = [v]$, it is $\alpha(v)$; if $t = 1$ and
$r = [b]$, it is true exactly when $b = 1$; if $t = 2$ and $r = [a]$, it is the negation of $s_a$;
if $t = 3$, it is true exactly when $s_a$ is true for every $a$ in $r$; if $t = 4$, it is true
exactly when $s_a$ is true for some $a$ in $r$; for every other gate it is false. -/
def qbfGateEval (vs : List Bool) (assign : ℕ → Bool) : QBFMatrixGate → Bool
  | (0, [v]) => assign v
  | (1, [b]) => b = 1
  | (2, [a]) => !(vs.getD a false)
  | (3, l) => l.all (fun a => vs.getD a false)
  | (4, l) => l.any (fun a => vs.getD a false)
  | _ => false

/-- **Evaluation of a QBF matrix circuit.** Given a matrix circuit $C = (g_0, \dots, g_{m-1})$, a
list of gates, and an assignment $\alpha$ of a truth value to every natural number, the list
$(s_0, \dots, s_{m-1})$ of the values of the gates of $C$, where $s_i$ is the value of the gate
$g_i$ given the values $(s_0, \dots, s_{i-1})$ of the earlier gates and the assignment $\alpha$. -/
def qbfCircuitEval (C : List QBFMatrixGate) (assign : ℕ → Bool) : List Bool :=
  C.foldl (fun vs g => vs ++ [qbfGateEval vs assign g]) []

/-- **Variables of a QBF matrix circuit.** For a matrix circuit $C$, a list of gates, the list of
the variables $v$ of the gates of $C$ of the form $(0, [v])$, in the order of the gates of $C$ and
with repetitions. -/
def qbfCircuitVars (C : List QBFMatrixGate) : List ℕ :=
  C.flatMap (fun g => match g with | (0, [v]) => [v] | _ => [])

/-- **Well-formed QBF matrix circuits.** A matrix circuit $C = (g_0, \dots, g_{m-1})$, a list of
gates, is well formed when for every $j < m$ whose gate $g_j = (t, r)$ has kind $t \in \{2, 3, 4\}$
(negation, conjunction or disjunction), every reference $a$ in $r$ satisfies $a < j$. -/
def qbfCircuitWellFormed (C : List QBFMatrixGate) : Prop :=
  ∀ j (h : j < C.length), ∀ a ∈ (C[j]'h).2,
    (C[j]'h).1 = 2 ∨ (C[j]'h).1 = 3 ∨ (C[j]'h).1 = 4 → a < j

/-- **Truth of a quantified Boolean formula with circuit matrix.** Let $P$ be a quantifier prefix,
a list of pairs $(q, v)$ of a quantifier $q$, $\exists$ (true) or $\forall$ (false), and a
variable $v \in \mathbb{N}$; let $\varphi$ be a matrix circuit and $\alpha$ an assignment of a
truth value to every natural number. Truth of $(P, \varphi)$ under $\alpha$ is defined by
recursion on $P$. If $P$ is empty, it means that $\varphi$ is nonempty and the value of its last
gate under $\alpha$ is true. If $P$ starts with $(q, v)$ followed by the prefix $P'$, it means that
$(P', \varphi)$ is true under $\alpha[v \mapsto \mathrm{true}]$ or under
$\alpha[v \mapsto \mathrm{false}]$ when $q$ is $\exists$, and under both when $q$ is $\forall$,
where $\alpha[v \mapsto b]$ agrees with $\alpha$ except that it sends $v$ to $b$. -/
def EvalQBFK (pref : List (Bool × ℕ)) (φ : List QBFMatrixGate)
    (assign : ℕ → Bool) : Prop :=
  match pref with
  | [] => (qbfCircuitEval φ assign).getLast? = some true
  | (isEx, v) :: rest =>
    if isEx then
      EvalQBFK rest φ (Function.update assign v true) ∨
        EvalQBFK rest φ (Function.update assign v false)
    else
      EvalQBFK rest φ (Function.update assign v true) ∧
        EvalQBFK rest φ (Function.update assign v false)

/-- **Quantifier alternations after a given quantifier.** For a quantifier $p$ and a quantifier
prefix $(q_1, v_1), \dots, (q_n, v_n)$, the number of indices $1 \le i \le n$ with
$q_i \ne q_{i-1}$, where $q_0 = p$. -/
def blockCountAux (prev : Bool) : List (Bool × ℕ) → ℕ
  | [] => 0
  | (b, _) :: rest => (if b = prev then 0 else 1) + blockCountAux b rest

/-- **Number of quantifier blocks.** The number of maximal blocks of consecutive equal quantifiers
in a quantifier prefix $(q_1, v_1), \dots, (q_n, v_n)$: it is $0$ if $n = 0$, and otherwise $1$
plus the number of indices $2 \le i \le n$ with $q_i \ne q_{i-1}$. -/
def blockCount : List (Bool × ℕ) → ℕ
  | [] => 0
  | (b, _) :: rest => 1 + blockCountAux b rest

open Classical in
/-- **The decision problem $\mathrm{QSAT}_k$.** For a natural number $k$, $\mathrm{QSAT}_k$ accepts
a bitstring $x$ exactly when $x$ decodes, under the standard bitstring encoding, to a pair
$(P, \varphi)$ of a quantifier prefix $P = (q_1, v_1), \dots, (q_n, v_n)$, where each $q_i$ is
$\exists$ (true) or $\forall$ (false) and each $v_i$ is a natural number, and a matrix circuit
$\varphi$, such that: $P$ is nonempty and $q_1$ is $\exists$; $(v_1, \dots, v_n)$ is a
permutation of $(0, \dots, n - 1)$; every variable of $\varphi$ is less than $n$; $\varphi$ is
well formed; $P$ has exactly $k$ quantifier blocks; and $(P, \varphi)$ is true under the
assignment that sends every variable to false. A bitstring that does not decode is rejected. -/
noncomputable def qsatKDec (k : ℕ) :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := List (Bool × ℕ) × List QBFMatrixGate) x with
  | some i => decide (
      i.1.head?.map Prod.fst = some true ∧
      List.Perm (i.1.map Prod.snd) (List.range i.1.length) ∧
      (∀ v ∈ qbfCircuitVars i.2, v < i.1.length) ∧ qbfCircuitWellFormed i.2 ∧
      blockCount i.1 = k ∧
      EvalQBFK i.1 i.2 (fun _ => false))
  | none => false

/-- **$\mathrm{QSAT}_k$ is $\Sigma_k^p$-complete, uniformly in $k$.** For every natural number
$k \ge 1$, the decision problem $\mathrm{QSAT}_k$ lies in $\Sigma_k^p$, and every decision problem
$L$ in $\Sigma_k^p$ reduces to $\mathrm{QSAT}_k$ by a polynomial-time many-one reduction.

Source: L. J. Stockmeyer, "The polynomial-time hierarchy", Theoretical Computer Science 3
(1977), 1-22; A. R. Meyer, "A polynomial hierarchy" (see also S. Arora and B. Barak,
Computational Complexity: A Modern Approach, 2009, Chapter 5). -/
public theorem_wanted qsat_k_sigma_k_complete :
    ∀ k : ℕ, qsatKDec (k + 1) ∈ SigmaK (k + 1) ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ SigmaK (k + 1) → Cslib.CookLevin.PolyManyOneRed L (qsatKDec (k + 1))

end MetaMathlibExt.Complexity.KeyTheorems.QSATKComplete
