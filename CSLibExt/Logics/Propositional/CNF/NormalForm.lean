/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Equivalent conjunctive normal form by distribution
-/
module

public import CSLibExt.Logics.Propositional.CNF.Semantics
public import CSLibExt.Logics.Propositional.NaturalDeduction.Semantics

/-!
# Equivalent conjunctive normal form by distribution

Every proposition is equivalent to a formula in conjunctive normal form.  This
file computes such a CNF, in the CSLibExt CNF representation, for upstream CSLib
propositions over any type of atoms named by `ι : Atom → ℕ`, and proves that it
has the same truth value as the proposition under every valuation.

The construction pushes Boolean complements to the atoms (as negative literals)
and distributes `∨` over `∧`. `cnfOf ι pos A` is a CNF of `A` (if `pos`) or of
its Boolean complement (true exactly when `A` is false), by recursion on the
polarity: `A ∨ B` becomes the clause-wise product of the CNFs of `A` and `B`,
and `A → B` the product of the complement's CNF of `A` with the CNF of `B`.
Each call builds only the polarity it needs, conjunction-like nodes thread an
accumulator (`cnfAcc`), and a chain of disjunction-like nodes is distributed one
disjunct at a time (`cnfOr`), so deep chains of either kind do not recopy their
partial results; no cost theorem is claimed. The complement is not upstream's
`¬A`, which is `A → ⊥` with `⊥` an atom; the two agree when `⊥` is false.

The output can be exponentially larger than the input, which is unavoidable for
an equivalent CNF (the parity function needs exponentially many clauses); the
Tseitin transformation (`CSLibExt/Algorithms/SAT/Tseitin`) is the linear-size,
equisatisfiable alternative.

## Main definitions

- `CNF.disj φ ψ` : the CNF of the disjunction of `φ` and `ψ`, one clause
  `C ++ D` for every pair of clauses.
- `Proposition.cnfAcc ι pos A acc`, `Proposition.cnfOr ι pos A S` : the builders
  (prepend to `acc`; disjoin with `S`).
- `Proposition.cnfOf ι pos A` : a CNF of `A` or of its Boolean complement, with
  the atom `a` as the variable `ι a`; `toCNF ι A` and `toNegCNF ι A` are its two
  polarities.

## Main results

- `Proposition.satisfies_cnfAcc_cnfOr` : the builders' semantics.
- `Proposition.satisfies_cnfOf` : `(cnfOf ι pos A).Satisfies σ ↔ A.evalBool (σ ∘ ι) = pos`
  for every assignment `σ`; `satisfies_toCNF_iff` and `satisfies_toNegCNF_iff`
  are its two polarities.
- `Proposition.cnfSat_toCNF_bot_iff` : for injective `ι`, `A.toCNF ι` with the
  unit clause `¬⊥` added is satisfiable iff `A` has a model with upstream's atom
  `⊥` false. (Without that clause the question is trivial: every proposition
  over atoms alone is true under the all-true valuation.)
-/

@[expose] public section

universe u

namespace Cslib.Logic.PL

namespace CNF

/-- **Disjunction of two CNFs.** For CNFs $\varphi = C_1 \land \dots \land C_m$ and
$\psi = D_1 \land \dots \land D_n$, their disjunction is the CNF with one clause $C_i \lor D_j$
(the literals of $C_i$ followed by those of $D_j$) for each pair $(i, j)$, listed with $i$ as the
outer and $j$ as the inner index. It expresses $(\bigwedge_i C_i) \lor (\bigwedge_j D_j)$ as
$\bigwedge_{i,j} (C_i \lor D_j)$. -/
def disj (φ ψ : CNF) : CNF := φ.flatMap fun C ↦ ψ.map fun D ↦ C ++ D

theorem satisfies_disj {σ : Nat → Bool} {φ ψ : CNF} :
    (disj φ ψ).Satisfies σ ↔ φ.Satisfies σ ∨ ψ.Satisfies σ := by
  simp only [disj, Satisfies, List.mem_flatMap, List.mem_map, forall_exists_index, and_imp]
  constructor
  · intro h
    by_contra hneg
    push Not at hneg
    obtain ⟨⟨C, hC, hCs⟩, ⟨D, hD, hDs⟩⟩ := hneg
    obtain ⟨l, hl, hls⟩ := h _ C hC D hD rfl
    rcases List.mem_append.mp hl with hl | hl
    · exact hCs ⟨l, hl, hls⟩
    · exact hDs ⟨l, hl, hls⟩
  · rintro (h | h) _ C hC D _ rfl
    · obtain ⟨l, hl, hls⟩ := h C hC
      exact ⟨l, List.mem_append_left _ hl, hls⟩
    · obtain ⟨l, hl, hls⟩ := h D ‹_›
      exact ⟨l, List.mem_append_right _ hl, hls⟩

end CNF

variable {Atom : Type u}

namespace Proposition

mutual

/-- **Accumulating CNF builder.** Let $\iota$ number the atoms by natural numbers, read a literal
$(n, p)$ as variable $n$ with polarity $p$, and write $1$ and $0$ for the polarities true and
false. For a polarity $p$, a proposition $\varphi$ and a CNF $S$, the CNF
$\mathcal{A}_p(\varphi, S)$ is defined by recursion on $\varphi$, together with the disjoining
builder $\mathcal{O}_p$. For an atom $a$, $\mathcal{A}_p(a, S)$ is the unit clause
$[(\iota(a), p)]$ followed by the clauses of $S$. Conjunction-like nodes thread the accumulator:
$\mathcal{A}_1(A \land B, S) = \mathcal{A}_1(A, \mathcal{A}_1(B, S))$,
$\mathcal{A}_0(A \lor B, S) = \mathcal{A}_0(A, \mathcal{A}_0(B, S))$ and
$\mathcal{A}_0(A \to B, S) = \mathcal{A}_1(A, \mathcal{A}_0(B, S))$. Disjunction-like nodes go
through $\mathcal{O}$: writing $X \mathbin{+\!\!+} S$ for the clauses of $X$ followed by those of
$S$ and $[\,]$ for the empty CNF,
$\mathcal{A}_1(A \lor B, S) = \mathcal{O}_1(A, \mathcal{A}_1(B, [\,])) \mathbin{+\!\!+} S$,
$\mathcal{A}_1(A \to B, S) = \mathcal{O}_0(A, \mathcal{A}_1(B, [\,])) \mathbin{+\!\!+} S$ and
$\mathcal{A}_0(A \land B, S) = \mathcal{O}_0(A, \mathcal{A}_0(B, [\,])) \mathbin{+\!\!+} S$.

An assignment $\sigma$ satisfies $\mathcal{A}_p(\varphi, S)$ exactly when $\varphi$ has truth
value $p$ under $\sigma \circ \iota$ and $\sigma$ satisfies $S$. -/
def cnfAcc (ι : Atom → ℕ) : Bool → Proposition Atom → CNF → CNF
  | pos, atom a, acc => [(ι a, pos)] :: acc
  | true, and A B, acc => cnfAcc ι true A (cnfAcc ι true B acc)
  | false, or A B, acc => cnfAcc ι false A (cnfAcc ι false B acc)
  | false, imp A B, acc => cnfAcc ι true A (cnfAcc ι false B acc)
  | true, or A B, acc => cnfOr ι true A (cnfAcc ι true B []) ++ acc
  | true, imp A B, acc => cnfOr ι false A (cnfAcc ι true B []) ++ acc
  | false, and A B, acc => cnfOr ι false A (cnfAcc ι false B []) ++ acc

/-- **Disjoining CNF builder.** Let $\iota$ number the atoms by natural numbers, read a literal
$(n, p)$ as variable $n$ with polarity $p$, and write $1$ and $0$ for the polarities true and
false. For a polarity $p$, a proposition $\varphi$ and a CNF $S$, the CNF
$\mathcal{O}_p(\varphi, S)$ is defined by recursion on $\varphi$, together with the accumulating
CNF builder $\mathcal{A}_p$. Write $X \otimes S$ for the disjunction of two CNFs $X$ and $S$ and
$[\,]$ for the empty CNF. For an atom $a$, $\mathcal{O}_p(a, S) = U \otimes S$, where $U$ is the
CNF whose only clause is the unit clause $[(\iota(a), p)]$. Disjunction-like nodes are consumed
from the left: $\mathcal{O}_1(A \lor B, S) = \mathcal{O}_1(A, \mathcal{O}_1(B, S))$,
$\mathcal{O}_1(A \to B, S) = \mathcal{O}_0(A, \mathcal{O}_1(B, S))$ and
$\mathcal{O}_0(A \land B, S) = \mathcal{O}_0(A, \mathcal{O}_0(B, S))$. Conjunction-like nodes go
through $\mathcal{A}$:
$\mathcal{O}_1(A \land B, S) = \mathcal{A}_1(A, \mathcal{A}_1(B, [\,])) \otimes S$,
$\mathcal{O}_0(A \lor B, S) = \mathcal{A}_0(A, \mathcal{A}_0(B, [\,])) \otimes S$ and
$\mathcal{O}_0(A \to B, S) = \mathcal{A}_1(A, \mathcal{A}_0(B, [\,])) \otimes S$.

An assignment $\sigma$ satisfies $\mathcal{O}_p(\varphi, S)$ exactly when $\varphi$ has truth
value $p$ under $\sigma \circ \iota$ or $\sigma$ satisfies $S$. -/
def cnfOr (ι : Atom → ℕ) : Bool → Proposition Atom → CNF → CNF
  | true, or A B, S => cnfOr ι true A (cnfOr ι true B S)
  | true, imp A B, S => cnfOr ι false A (cnfOr ι true B S)
  | false, and A B, S => cnfOr ι false A (cnfOr ι false B S)
  | pos, atom a, S => CNF.disj [[(ι a, pos)]] S
  | true, and A B, S => CNF.disj (cnfAcc ι true A (cnfAcc ι true B [])) S
  | false, or A B, S => CNF.disj (cnfAcc ι false A (cnfAcc ι false B [])) S
  | false, imp A B, S => CNF.disj (cnfAcc ι true A (cnfAcc ι false B [])) S

end

/-- **CNF of a proposition at a polarity.** Let $\iota$ number the atoms by natural numbers. For a
polarity $p$ and a proposition $\varphi$, the CNF of $\varphi$ at polarity $p$ is the result of the
accumulating CNF builder at polarity $p$ on $\varphi$ with the empty CNF as accumulator; the atom
$a$ becomes the variable $\iota(a)$.

An assignment $\sigma$ satisfies it exactly when $\varphi$ has truth value $p$ under
$\sigma \circ \iota$, so it is a CNF of $\varphi$ when $p$ is true and of the Boolean complement of
$\varphi$ when $p$ is false. Only the requested polarity is built: a proposition already in
conjunctive normal form gets a CNF of linear size at polarity true, although the CNF of its
complement can be exponentially larger. -/
def cnfOf (ι : Atom → ℕ) (pos : Bool) (A : Proposition Atom) : CNF := cnfAcc ι pos A []

/-- **CNF of a proposition.** Let $\iota$ number the atoms by natural numbers. The CNF of a
proposition $A$ is its CNF at polarity true, with the atom $a$ as the variable $\iota(a)$.

An assignment $\sigma$ satisfies it exactly when $A$ is true under $\sigma \circ \iota$. -/
def toCNF (ι : Atom → ℕ) (A : Proposition Atom) : CNF := cnfOf ι true A

/-- **CNF of the complement of a proposition.** Let $\iota$ number the atoms by natural numbers.
The complement CNF of a proposition $A$ is its CNF at polarity false, with the atom $a$ as the
variable $\iota(a)$.

An assignment $\sigma$ satisfies it exactly when $A$ is false under $\sigma \circ \iota$. This is
not the negation $\lnot A$, which is $A \to \bot$ with $\bot$ an atom: that proposition can be
true together with $A$ when the atom $\bot$ is true. -/
def toNegCNF (ι : Atom → ℕ) (A : Proposition Atom) : CNF := cnfOf ι false A

theorem satisfies_cnfAcc_cnfOr (ι : Atom → ℕ) (A : Proposition Atom) (σ : Nat → Bool) :
    ∀ pos (acc S : CNF),
      ((cnfAcc ι pos A acc).Satisfies σ ↔ A.evalBool (σ ∘ ι) = pos ∧ acc.Satisfies σ) ∧
      ((cnfOr ι pos A S).Satisfies σ ↔ A.evalBool (σ ∘ ι) = pos ∨ S.Satisfies σ) := by
  induction A with
  | atom a =>
    intro pos acc S
    constructor
    · simp [cnfAcc]
    · simp only [cnfOr, CNF.satisfies_disj]
      simp
  | and A B ihA ihB | or A B ihA ihB | imp A B ihA ihB =>
    have hA1 : ∀ pos acc, (cnfAcc ι pos A acc).Satisfies σ ↔
        A.evalBool (σ ∘ ι) = pos ∧ acc.Satisfies σ := fun pos acc ↦ (ihA pos acc []).1
    have hA2 : ∀ pos S, (cnfOr ι pos A S).Satisfies σ ↔
        A.evalBool (σ ∘ ι) = pos ∨ S.Satisfies σ := fun pos S ↦ (ihA pos [] S).2
    have hB1 : ∀ pos acc, (cnfAcc ι pos B acc).Satisfies σ ↔
        B.evalBool (σ ∘ ι) = pos ∧ acc.Satisfies σ := fun pos acc ↦ (ihB pos acc []).1
    have hB2 : ∀ pos S, (cnfOr ι pos B S).Satisfies σ ↔
        B.evalBool (σ ∘ ι) = pos ∨ S.Satisfies σ := fun pos S ↦ (ihB pos [] S).2
    intro pos acc S
    cases pos <;> constructor <;>
    · simp only [cnfAcc, cnfOr, CNF.satisfies_append, CNF.satisfies_disj, hA1, hA2, hB1, hB2,
        evalBool, CNF.satisfies_nil]
      cases A.evalBool (σ ∘ ι) <;> cases B.evalBool (σ ∘ ι) <;> simp

theorem satisfies_cnfOf (ι : Atom → ℕ) (pos : Bool) (A : Proposition Atom) (σ : Nat → Bool) :
    (cnfOf ι pos A).Satisfies σ ↔ A.evalBool (σ ∘ ι) = pos := by
  rw [cnfOf, (satisfies_cnfAcc_cnfOr ι A σ pos [] []).1]
  simp

/-- **Equivalent CNF.** Let $\iota$ number the atoms by natural numbers. For every proposition $A$
and every assignment $\sigma$ of Boolean values to the natural-number variables, the CNF of $A$
built with atom $a$ as variable $\iota(a)$ is satisfied by $\sigma$ if and only if $A$ evaluates
to true under the valuation $\sigma \circ \iota$ of the atoms. -/
theorem satisfies_toCNF_iff (ι : Atom → ℕ) (A : Proposition Atom) (σ : Nat → Bool) :
    (A.toCNF ι).Satisfies σ ↔ A.evalBool (σ ∘ ι) = true :=
  satisfies_cnfOf ι true A σ

theorem satisfies_toNegCNF_iff (ι : Atom → ℕ) (A : Proposition Atom) (σ : Nat → Bool) :
    (A.toNegCNF ι).Satisfies σ ↔ A.evalBool (σ ∘ ι) = false :=
  satisfies_cnfOf ι false A σ

/-- **Satisfiability of a CNF with falsum false.** Let the atoms have a distinguished atom $\bot$
and let $\iota$ be an injective numbering of the atoms by natural numbers. For every proposition
$A$, the CNF consisting of the unit clause with the single negative literal on variable
$\iota(\bot)$ followed by the clauses of the CNF of $A$ (atom $a$ read as variable $\iota(a)$) is
satisfiable if and only if some valuation $v$ of the atoms with $v(\bot)$ false makes $A$ true. -/
theorem cnfSat_toCNF_bot_iff [Bot Atom] {ι : Atom → ℕ} (hι : Function.Injective ι)
    (A : Proposition Atom) :
    CNFSat ([(ι ⊥, false)] :: A.toCNF ι) ↔
      ∃ v : Atom → Bool, v ⊥ = false ∧ A.evalBool v = true := by
  rw [cnfSat_iff_exists_satisfies]
  constructor
  · rintro ⟨σ, hσ⟩
    simp only [CNF.satisfies_cons, CNFClause.satisfies_def, List.mem_singleton,
      exists_eq_left] at hσ
    exact ⟨σ ∘ ι, hσ.1, (satisfies_toCNF_iff ι A σ).mp hσ.2⟩
  · rintro ⟨v, hv, hA⟩
    classical
    let σ : Nat → Bool := fun x ↦ if h : ∃ a, ι a = x then v h.choose else false
    have hcomp : σ ∘ ι = v := by
      funext a
      have h : ∃ a', ι a' = ι a := ⟨a, rfl⟩
      simp only [σ, Function.comp, h, dite_true]
      exact congrArg v (hι h.choose_spec)
    refine ⟨σ, ?_⟩
    simp only [CNF.satisfies_cons, CNFClause.satisfies_def, List.mem_singleton, exists_eq_left]
    refine ⟨?_, (satisfies_toCNF_iff ι A σ).mpr (hcomp ▸ hA)⟩
    have : σ (ι ⊥) = v ⊥ := congrFun hcomp ⊥
    rw [this, hv]

end Proposition

end Cslib.Logic.PL
