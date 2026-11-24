/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.Order.Filter.AtTopBot.Defs
public import MathlibExt.Combinatorics.InfiniteWord.PureMorphicWord

/-!
# Dumont–Thomas numeration

For an admissible sequence, `morphIterate_getElem_eq_substitutionAutomaton_tail` identifies
the letter at its weighted position with the final state of the substitution automaton.
The theorem `substitutionAutomaton_admissibleSequence` identifies the state after each digit
with the corresponding letter of the sequence.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Substitutions in the sense of Labbé and Lepšová.** A substitution is a map $\eta$ sending
each letter of an alphabet $A$ to a finite word over $A$, extended to finite words by
concatenation, such that $\eta$ is non-erasing (the word $\eta(a)$ is nonempty for every letter
$a \in A$) and some letter $a \in A$ is growing, that is, $|\eta^k(a)| \to \infty$ as
$k \to \infty$, where $\eta^k$ is the $k$-th iterate of $\eta$. The alphabet $A$ need not be
finite.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Section 2 (Preliminaries). -/
public def IsSubstitution {A : Type*} (η : A → List A) : Prop :=
  IsNonErasing η ∧
    ∃ a, Filter.Tendsto (fun k => (morphIterate η k [a]).length) Filter.atTop Filter.atTop

/-- **Substitutions are non-erasing.** Every substitution $\eta$ in the sense of Labbé and
Lepšová is non-erasing: $\eta(a)$ is a nonempty word for every letter $a$.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 2. -/
public theorem IsSubstitution.isNonErasing {A : Type*} {η : A → List A}
    (h : IsSubstitution η) : IsNonErasing η := h.1

/-- **Admissible sequence.** Let $\eta$ send each letter of an alphabet $A$ to a finite word
over $A$, and let $k \ge 0$. A finite sequence $(m_i, a_i)_{0 \le i \le k}$ of pairs, each made
of a finite word $m_i$ over $A$ and a letter $a_i \in A$, is admissible with respect to $\eta$
when the word $m_i a_i$ is a prefix of $\eta(a_{i+1})$ for every $i < k$.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Definition 3.1 (after Dumont and Thomas). -/
public def IsAdmissibleSequence {A : Type*} (η : A → List A) (s : ℕ → List A × A) (k : ℕ) :
    Prop :=
  ∀ i < k, (s i).1 ++ [(s i).2] <+: η (s (i + 1)).2

/-- **Admissible sequences starting from a letter.** Let $\eta$ map each letter of an alphabet
$A$ to a finite word over $A$, and let $a \in A$. A finite sequence $(m_i, a_i)_{0 \le i \le k}$
of pairs, each made of a finite word $m_i$ over $A$ and a letter $a_i \in A$, is
$a$-admissible when it is admissible with respect to $\eta$ and moreover the word $m_k a_k$ is a
prefix of $\eta(a)$.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Definition 3.1. -/
public def IsLetterAdmissibleSequence {A : Type*} (η : A → List A) (a : A)
    (s : ℕ → List A × A) (k : ℕ) : Prop :=
  IsAdmissibleSequence η s k ∧ (s k).1 ++ [(s k).2] <+: η a

/-- **One-term sequences are admissible.** Let $\eta$ send each letter of an alphabet $A$ to a
finite word over $A$. Every one-term sequence $(m_0, a_0)$, with $m_0$ a finite word over $A$
and $a_0 \in A$, is admissible with respect to $\eta$: the admissibility condition is vacuous
for a sequence with the single index $0$.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Definition 3.1. -/
public theorem isAdmissibleSequence_zero {A : Type*} (η : A → List A) (s : ℕ → List A × A) :
    IsAdmissibleSequence η s 0 := fun _ hi => absurd hi (Nat.not_lt_zero _)

/-- **Substitution automaton.** Let $\eta$ map each letter of an alphabet $A$ to a finite word
over $A$. The substitution automaton $\mathcal{A}_{\eta,\cdot}$ of $\eta$ is the deterministic
automaton with output whose states are the letters of $A$ (the alphabet need not be finite):
reading a digit $i \in \mathbb{N}$ in the state $b$ moves to the letter $\eta(b)_i$ of $\eta(b)$
at position $i$, counting from $0$, and is undefined when $i \ge |\eta(b)|$. For a letter $b$
and a finite word $w$ of digits, the automaton started at $b$ returns the state reached after
reading $w$ from left to right (on the empty word this is $b$ itself), or no state when some step
of the run is undefined.

Every state is final, so a digit word is accepted from a letter $b$ exactly when the run from $b$
is defined. When $A$ is finite, digits outside the paper's alphabet
$\{0, \dots, \max_c |\eta(c)| - 1\}$ are never readable, so the accepted language is unchanged.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Section 2 (the DFAO `𝒜_{η,a}`). -/
public def substitutionAutomaton {A : Type*} (η : A → List A) : A → List ℕ → Option A
  | b, [] => some b
  | b, i :: w => (η b)[i]?.bind fun c => substitutionAutomaton η c w

/-- **The substitution automaton on the empty word.** For every letter map $\eta$ and every
letter $b$, the substitution automaton $\mathcal{A}_{\eta,\cdot}$ started at $b$ ends in the
state $b$ after reading the empty digit word.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 2. -/
public theorem substitutionAutomaton_nil {A : Type*} (η : A → List A) (b : A) :
    substitutionAutomaton η b [] = some b := rfl

/-- **Reading a nonempty digit word.** Let $\eta$ be a letter map, $b$ a letter, $i$ a digit and
$w$ a digit word. If $i < |\eta(b)|$, then the value of the substitution automaton started at $b$
on the word $iw$ (the digit $i$ followed by $w$) equals its value started at $\eta(b)_i$ on $w$,
where $\eta(b)_i$ is the letter of $\eta(b)$ at position $i$, counting from $0$. If
$i \ge |\eta(b)|$, the run on $iw$ is undefined.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 2. -/
public theorem substitutionAutomaton_cons {A : Type*} (η : A → List A) (b : A) (i : ℕ)
    (w : List ℕ) :
    substitutionAutomaton η b (i :: w) =
      (η b)[i]?.bind fun c => substitutionAutomaton η c w := rfl

namespace substitutionAutomaton_admissibleSequence

private theorem run_append {A : Type*} (η : A → List A) (x : A) (u v : List ℕ) :
    substitutionAutomaton η x (u ++ v) =
      (substitutionAutomaton η x u).bind (fun a => substitutionAutomaton η a v) := by
  induction u generalizing x with
  | nil => rfl
  | cons d u ih =>
    simp only [List.cons_append, substitutionAutomaton_cons, ih, Option.bind_assoc]

end substitutionAutomaton_admissibleSequence

-- Admissibility supplies all the transitions. Keep the named substitution hypothesis.
set_option linter.unusedVariables false in
/-- **The automaton reads off the letters of an admissible sequence.** Let $\eta$ be a
substitution, let $x$ be a letter, let $k \ge 1$, and let $(m_i, a_i)_{i = 0, \dots, k-1}$ be an
$x$-admissible sequence. Then for every $i < k$, the substitution automaton started at $x$ ends in
the state $a_i$ after reading the digit word $|m_{k-1}|\,|m_{k-2}| \cdots |m_i|$, whose digits are
the lengths of $m_{k-1}, \dots, m_i$ in this order.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Lemma 3.6. -/
public theorem substitutionAutomaton_admissibleSequence {A : Type*} (η : A → List A)
    (hη : IsSubstitution η) (k : ℕ) (hk : 1 ≤ k) (x : A) (s : ℕ → List A × A)
    (hs : IsLetterAdmissibleSequence η x s (k - 1)) :
    ∀ i < k,
      substitutionAutomaton η x ((List.range (k - i)).map fun t => (s (k - 1 - t)).1.length) =
        some (s i).2 := by
  have step {m : List A} {a b : A} (h : m ++ [a] <+: η b) :
      (η b)[m.length]? = some a := by
    obtain ⟨rest, hrest⟩ := h
    rw [← hrest, List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
    rfl
  have run (n : ℕ) (hn : n < k) :
      substitutionAutomaton η x ((List.range (n + 1)).map fun t => (s (k - 1 - t)).1.length) =
        some (s (k - 1 - n)).2 := by
    induction n with
    | zero =>
      change substitutionAutomaton η x [(s (k - 1)).1.length] = some (s (k - 1)).2
      simp only [substitutionAutomaton_cons, step hs.2, Option.bind_some,
        substitutionAutomaton_nil]
    | succ n ih =>
      have hp : (s (k - 1 - (n + 1))).1 ++ [(s (k - 1 - (n + 1))).2] <+:
          η (s (k - 1 - n)).2 := by
        simpa only [show k - 1 - (n + 1) + 1 = k - 1 - n by omega] using
          hs.1 (k - 1 - (n + 1)) (by omega)
      rw [@List.range_succ (n + 1), List.map_append,
        substitutionAutomaton_admissibleSequence.run_append, ih (by omega)]
      simp only [List.map_singleton, Option.bind_some, substitutionAutomaton_cons, step hp,
        substitutionAutomaton_nil]
  intro i hi
  simpa only [show k - 1 - i + 1 = k - i by omega, show k - 1 - (k - 1 - i) = i by omega]
    using run (k - 1 - i) (by omega)

/-- **Two runs of the Fibonacci automaton.** For the Fibonacci substitution $0 \mapsto 01$,
$1 \mapsto 0$ on the alphabet $\{0, 1\}$, the substitution automaton started at the letter $0$
ends in the state $0$ after reading the digit word $10$, and its run on the digit word $11$ is
undefined, so $11$ is rejected.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 2 and Proposition 9.2 (Fibonacci substitution). -/
public theorem substitutionAutomaton_fibonacci_small :
    substitutionAutomaton (fun a : Fin 2 => if a = 0 then [0, 1] else [0]) 0 [1, 0] = some 0 ∧
      substitutionAutomaton (fun a : Fin 2 => if a = 0 then [0, 1] else [0]) 0 [1, 1] =
        none := by
  decide

namespace morphIterate_getElem_eq_substitutionAutomaton_tail

private theorem iterate_split {A : Type*} (η : A → List A) {w u v : List A}
    (h : morphExtend η w = u ++ v) (n : ℕ) :
    morphIterate η (n + 1) w = morphIterate η n u ++ morphIterate η n v := by
  induction n with
  | zero => exact h
  | succ n ih =>
    rw [morphIterate, ih, morphExtend_append]
    rfl

private theorem iterate_append {A : Type*} (η : A → List A) (k : ℕ) (u v : List A) :
    morphIterate η k (u ++ v) = morphIterate η k u ++ morphIterate η k v := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [morphIterate, ih, morphExtend_append]

-- The suffix after the selected letter absorbs the unvisited part of each image.
private theorem read_with_suffix {A : Type*} (η : A → List A) (s : ℕ → List A × A)
    (p : ℕ) (x : A) (suffix : List A)
    (hs : 0 < p → IsLetterAdmissibleSequence η x s (p - 1)) :
    ∃ a, (morphIterate η p (x :: suffix))[
        ∑ j ∈ Finset.range p, (morphIterate η j (s j).1).length]? = some a ∧
      substitutionAutomaton η x ((List.range p).reverse.map fun j => (s j).1.length) = some a := by
  induction p generalizing x suffix with
  | zero => exact ⟨x, by simp [morphIterate, substitutionAutomaton]⟩
  | succ p ih =>
    obtain ⟨hadm, rest, hrest⟩ := hs (Nat.zero_lt_succ p)
    simp only [Nat.add_one_sub_one] at hadm hrest
    have himage : η x = (s p).1 ++ (s p).2 :: rest := by
      simpa using hrest.symm
    have hstep : (η x)[(s p).1.length]? = some (s p).2 := by
      rw [himage, List.getElem?_append_right (Nat.le_refl _)]
      simp
    have hsplit : morphExtend η (x :: suffix) =
        (s p).1 ++ (s p).2 :: (rest ++ morphExtend η suffix) := by
      change η x ++ morphExtend η suffix = _
      simp [himage]
    rw [iterate_split η hsplit p, Finset.sum_range_succ,
      List.getElem?_append_right (by omega), Nat.add_sub_cancel,
      List.range_succ, List.reverse_append]
    simp only [List.reverse_singleton, List.singleton_append, List.map_cons,
      substitutionAutomaton_cons, hstep, Option.bind_some]
    apply ih
    intro hp
    refine ⟨fun i hi => hadm i (by omega), ?_⟩
    simpa [Nat.sub_add_cancel hp] using hadm (p - 1) (by omega)

end morphIterate_getElem_eq_substitutionAutomaton_tail

set_option linter.unusedVariables false in
/-- **Letters of an iterated image are read by the automaton.** Let $\eta$ be a substitution
on an alphabet $A$, let $p \ge 1$ and $x \in A$, let $(m_i, a_i)_{i = 0, \dots, p-1}$ be an
$x$-admissible sequence, and put $\ell = \sum_{j=0}^{p-1} |\eta^j(m_j)|$. Let
$\mathcal{A}_{\eta,x}$ be the automaton of $\eta$ started at $x$. Then $\eta^p(x)$ has a letter
at position $\ell$ (counting from $0$) exactly when the run of $\mathcal{A}_{\eta,x}$ on the
digit word $|m_{p-1}|\,|m_{p-2}| \cdots |m_0|$ is defined, and in that case this letter is the
state in which the run ends.

In the source the digit word is $\mathrm{tail}_{\eta,p,x}(\ell)$; by Lemmas 3.3 and 3.9 the
$x$-admissible sequences correspond bijectively to the positions $\ell < |\eta^p(x)|$.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Lemma 3.11. -/
public theorem morphIterate_getElem_eq_substitutionAutomaton_tail {A : Type*}
    (η : A → List A) (hη : IsSubstitution η) (p : ℕ) (hp : 1 ≤ p) (x : A)
    (s : ℕ → List A × A) (hs : IsLetterAdmissibleSequence η x s (p - 1)) :
    (morphIterate η p [x])[∑ j ∈ Finset.range p, (morphIterate η j (s j).1).length]? =
      substitutionAutomaton η x ((List.range p).reverse.map fun j => (s j).1.length) := by
  obtain ⟨a, hread, hrun⟩ :=
    morphIterate_getElem_eq_substitutionAutomaton_tail.read_with_suffix η s p x [] (fun _ => hs)
  exact hread.trans hrun.symm

-- Keep the source's named hypothesis even though the admissible chain alone gives the bound.
set_option linter.unusedVariables false in
/-- **Weighted length of an admissible sequence.** Let $\eta$ be a substitution on an alphabet
$A$, extended to finite words by concatenation, and let $(m_i, a_i)_{0 \le i \le k}$ be a
sequence of pairs of a finite word $m_i$ over $A$ and a letter $a_i \in A$ that is admissible
with respect to $\eta$. Then $\sum_{j=0}^{k} |\eta^j(m_j)| < |\eta^k(m_k a_k)|$, where
$\eta^j$ is the $j$-th iterate of $\eta$ and $|w|$ is the length of a word $w$.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Lemma 3.3 (Dumont and Thomas, Lemma 1.1). -/
public theorem admissibleSequence_weightedLength_lt {A : Type*} (η : A → List A)
    (hη : IsSubstitution η) (s : ℕ → List A × A) (k : ℕ) (hs : IsAdmissibleSequence η s k) :
    ∑ j ∈ Finset.range (k + 1), (morphIterate η j (s j).1).length <
      (morphIterate η k ((s k).1 ++ [(s k).2])).length := by
  -- Read the shorter chain from the terminal letter `aₖ`.
  have hadm (hk : 0 < k) : IsLetterAdmissibleSequence η (s k).2 s (k - 1) := by
    refine ⟨fun i hi => hs i (by omega), ?_⟩
    simpa only [Nat.sub_add_cancel hk] using hs (k - 1) (by omega)
  obtain ⟨a, hread, _⟩ :=
    morphIterate_getElem_eq_substitutionAutomaton_tail.read_with_suffix η s k (s k).2 [] hadm
  obtain ⟨hlen, _⟩ := List.getElem?_eq_some_iff.mp hread
  rw [Finset.sum_range_succ, morphIterate_getElem_eq_substitutionAutomaton_tail.iterate_append,
    List.length_append]
  omega

/-- **Two-sided periodic points.** Let $\eta$ map each letter of an alphabet $A$ to a finite
word over $A$, extended to finite words by concatenation, with iterates $\eta^j$; let
$u = (u_i)_{i \in \mathbb{Z}}$ be a two-sided word over $A$ and let $p$ be a natural number.
Then $u$ is a two-sided periodic point of $\eta$ with period $p$ when $p \ge 1$, for every
natural number $n$ the word $\eta^p(u_0 u_1 \cdots u_{n-1})$ is a prefix of the right-infinite
word $u_0 u_1 u_2 \cdots$, and for every natural number $m$ the word
$\eta^p(u_{-m} \cdots u_{-2} u_{-1})$ is a suffix of the left-infinite word
$\cdots u_{-3} u_{-2} u_{-1}$.

When $\eta$ is non-erasing this says that $\eta^p(u) = u$, where $\eta$ acts on the two-sided
word $\cdots u_{-2} u_{-1} \mid u_0 u_1 \cdots$ letterwise and keeps the origin between
$\eta(u_{-1})$ and $\eta(u_0)$.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Section 2 (periodic points `Per(η)`). -/
public def IsTwoSidedPeriodicPoint {A : Type*} (η : A → List A) (u : ℤ → A) (p : ℕ) : Prop :=
  1 ≤ p ∧
    (∀ n i (hi : i < (morphIterate η p ((List.range n).map fun j : ℕ => u j)).length),
      (morphIterate η p ((List.range n).map fun j : ℕ => u j))[i] = u i) ∧
    ∀ m i (hi : i < (morphIterate η p
        ((List.range m).reverse.map fun j : ℕ => u (-1 - (j : ℤ)))).length),
      (morphIterate η p ((List.range m).reverse.map fun j : ℕ => u (-1 - (j : ℤ))))[
        (morphIterate η p ((List.range m).reverse.map fun j : ℕ => u (-1 - (j : ℤ)))).length -
          1 - i]'(by omega) = u (-1 - (i : ℤ))

/-- **Periods of two-sided periodic points are positive.** Let $\eta$ send each letter of an
alphabet $A$ to a finite word over $A$. If a two-sided word $u : \mathbb{Z} \to A$ is a
periodic point of $\eta$ with period $p$, then $p \ge 1$.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 2. -/
public theorem IsTwoSidedPeriodicPoint.one_le {A : Type*} {η : A → List A} {u : ℤ → A} {p : ℕ}
    (h : IsTwoSidedPeriodicPoint η u p) : 1 ≤ p := h.1

/-- **Two-sided periodic points with growing seed.** Let $\eta$ map each letter of an alphabet
$A$ to a finite word over $A$, extended to finite words by concatenation, with iterates
$\eta^k$; let $u = (u_i)_{i \in \mathbb{Z}}$ be a two-sided word over $A$ and let $p$ be a
natural number. Then $u$ is a periodic point of $\eta$ with growing seed and least period $p$
when $\eta$ is a substitution, $p$ is the least natural number $q$ such that $u$ is a two-sided
periodic point of $\eta$ with period $q$, and both seed letters $u_{-1}$ and $u_0$ are growing,
that is, $|\eta^k(u_{-1})| \to \infty$ and $|\eta^k(u_0)| \to \infty$ as $k \to \infty$.

This is the standing hypothesis of Sections 4 to 9 of the source.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Sections 2 and 4 (two-sided periodic point with growing
seed `s = u₋₁|u₀`, and its period). -/
public def IsPeriodicPointWithGrowingSeed {A : Type*} (η : A → List A) (u : ℤ → A) (p : ℕ) :
    Prop :=
  IsSubstitution η ∧ IsLeast {q | IsTwoSidedPeriodicPoint η u q} p ∧
    Filter.Tendsto (fun k => (morphIterate η k [u 0]).length) Filter.atTop Filter.atTop ∧
    Filter.Tendsto (fun k => (morphIterate η k [u (-1)]).length) Filter.atTop Filter.atTop

/-- **Periodic points with growing seed are two-sided periodic points.** Let $\eta$ map each
letter of an alphabet $A$ to a finite word over $A$, let $u = (u_i)_{i \in \mathbb{Z}}$ be a
two-sided word over $A$ and let $p$ be a natural number. If $u$ is a two-sided periodic point
of $\eta$ with growing seed and least period $p$, then $u$ is a two-sided periodic point of
$\eta$ with period $p$.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 4. -/
public theorem IsPeriodicPointWithGrowingSeed.isTwoSidedPeriodicPoint {A : Type*}
    {η : A → List A} {u : ℤ → A} {p : ℕ} (h : IsPeriodicPointWithGrowingSeed η u p) :
    IsTwoSidedPeriodicPoint η u p := h.2.1.1

/-- **Dumont–Thomas complement representations.** Let $\eta$ map each letter of an alphabet $A$
to a finite word over $A$, extended to finite words by concatenation, with iterates $\eta^j$;
let $u = (u_i)_{i \in \mathbb{Z}}$ be a two-sided word over $A$ and let $p$ be a natural
number. A finite word $w$ of natural-number digits is a Dumont–Thomas complement
representation of an integer $n$ with respect to $\eta$, $u$ and $p$ when one of the following
four conditions holds. Either $n = 0$ and $w$ is the one-digit word $0$; or $n = -1$ and $w$ is
the one-digit word $1$; or $n = N$ for a natural number $N \ge 1$ and there are a natural
number $k$ divisible by $p$ and a $u_0$-admissible sequence $(m_i, a_i)_{0 \le i \le k-1}$
such that the word $m_{k-1} m_{k-2} \cdots m_{k-p}$ is nonempty,
$u_0 u_1 \cdots u_{N-1} = \eta^{k-1}(m_{k-1}) \cdots \eta^0(m_0)$ and $w$ is the digit word
$0, |m_{k-1}|, \ldots, |m_0|$; or $n = -N$ for a natural number $N \ge 2$ and, writing
$L_k = |\eta^k(u_{-1})|$, there are a natural number $k$ divisible by $p$ with $N \le L_k$
and a $u_{-1}$-admissible sequence $(m_i, a_i)_{0 \le i \le k-1}$ such that
$\eta^{p-1}(m_{k-1}) \cdots \eta^0(m_{k-p}) \, a_{k-p} \ne \eta^p(u_{-1})$,
$u_{-L_k} u_{-L_k+1} \cdots u_{-N-1} = \eta^{k-1}(m_{k-1}) \cdots \eta^0(m_0)$ (the empty word
when $N = L_k$) and $w$ is the digit word $1, |m_{k-1}|, \ldots, |m_0|$.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Section 4 (definition of Dumont–Thomas complement
numeration systems for `ℤ`). -/
public def IsDumontThomasRep {A : Type*} (η : A → List A) (u : ℤ → A) (p : ℕ) (n : ℤ)
    (w : List ℕ) : Prop :=
  (n = 0 ∧ w = [0]) ∨ (n = -1 ∧ w = [1]) ∨
    (∃ (N k : ℕ) (s : ℕ → List A × A), 1 ≤ N ∧ n = N ∧ p ∣ k ∧
      IsLetterAdmissibleSequence η (u 0) s (k - 1) ∧
      ((List.range p).map fun t => (s (k - 1 - t)).1).flatten ≠ [] ∧
      (List.range N).map (fun j : ℕ => u j) =
        ((List.range k).reverse.map fun j => morphIterate η j (s j).1).flatten ∧
      w = 0 :: (List.range k).reverse.map fun j => (s j).1.length) ∨
    (∃ (N k : ℕ) (s : ℕ → List A × A), 2 ≤ N ∧ n = -N ∧ p ∣ k ∧
      N ≤ (morphIterate η k [u (-1)]).length ∧
      IsLetterAdmissibleSequence η (u (-1)) s (k - 1) ∧
      ((List.range p).map fun t => morphIterate η (p - 1 - t) (s (k - 1 - t)).1).flatten ++
          [(s (k - p)).2] ≠ morphIterate η p [u (-1)] ∧
      (List.range ((morphIterate η k [u (-1)]).length - N)).map
          (fun t : ℕ => u ((t : ℤ) - (morphIterate η k [u (-1)]).length)) =
        ((List.range k).reverse.map fun j => morphIterate η j (s j).1).flatten ∧
      w = 1 :: (List.range k).reverse.map fun j => (s j).1.length)

/-- **A Dumont–Thomas representation of zero.** For every map $\eta$ sending each letter of an
alphabet $A$ to a finite word over $A$, every two-sided word $u = (u_i)_{i \in \mathbb{Z}}$ over
$A$ and every natural number $p$, the one-digit word $0$ is a Dumont–Thomas complement
representation of the integer $0$ with respect to $\eta$, $u$ and $p$.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 4 (definition of `rep_u`). -/
public theorem isDumontThomasRep_zero {A : Type*} (η : A → List A) (u : ℤ → A) (p : ℕ) :
    IsDumontThomasRep η u p 0 [0] := Or.inl ⟨rfl, rfl⟩

/-- **Dumont–Thomas representation of minus one.** Let $\eta$ send each letter of an alphabet
$A$ to a finite word over $A$, let $u$ be a two-sided infinite word over $A$, and let $p$ be a
natural number. Then the one-digit word $1$ is the Dumont–Thomas complement representation of
$-1$ for $\eta$, $u$ and $p$, that is, $\operatorname{rep}_u(-1) = 1$; no hypothesis on $\eta$,
$u$ or $p$ is needed.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 4 (definition of `rep_u`). -/
public theorem isDumontThomasRep_neg_one {A : Type*} (η : A → List A) (u : ℤ → A) (p : ℕ) :
    IsDumontThomasRep η u p (-1) [1] := Or.inr (Or.inl ⟨rfl, rfl⟩)

/-- **Seed automaton.** Let $\eta$ be a letter map and let $s = b|a$ be the seed formed by the
letters $b$ and $a$. The automaton $\mathcal{A}_{\eta,s}$ has a new initial state, which is not
final, with a transition labelled $0$ to $a$ and a transition labelled $1$ to $b$; from a letter
it runs like the substitution automaton $\mathcal{A}_{\eta,\cdot}$. So its value on a digit word
is: undefined on the empty word; $\mathcal{A}_{\eta,a}(w)$ on $0w$, the state reached from $a$ by
reading $w$ (undefined when that run is undefined); $\mathcal{A}_{\eta,b}(w)$ on $1w$, likewise;
and undefined on every word whose first digit is at least $2$.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Section 6 (the automaton `𝒜_{η,s}`). -/
public def seedAutomaton {A : Type*} (η : A → List A) (b a : A) : List ℕ → Option A
  | [] => none
  | 0 :: w => substitutionAutomaton η a w
  | 1 :: w => substitutionAutomaton η b w
  | (_ + 2) :: _ => none

/-- **Seed automaton after reading the digit 0.** Let $\eta$ be a letter map, let $a$ and $b$ be
letters, and let $\mathcal{A}_{\eta,s}$ be the seed automaton for the seed $s = b|a$. For every
digit word $w$, the value of $\mathcal{A}_{\eta,s}$ on the word $0w$ (the digit $0$ followed by
$w$) equals the value $\mathcal{A}_{\eta,a}(w)$ of the substitution automaton started at $a$ on
$w$: either both are undefined, or both are the same state.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 6, Equation (automata relations). -/
public theorem seedAutomaton_zero_cons {A : Type*} (η : A → List A) (b a : A) (w : List ℕ) :
    seedAutomaton η b a (0 :: w) = substitutionAutomaton η a w := rfl

/-- **Seed automaton after reading the digit 1.** Let $\eta$ be a letter map, let $a$ and $b$ be
letters, and let $\mathcal{A}_{\eta,s}$ be the seed automaton for the seed $s = b|a$. For every
digit word $w$, the value of $\mathcal{A}_{\eta,s}$ on the word $1w$ (the digit $1$ followed by
$w$) equals the value $\mathcal{A}_{\eta,b}(w)$ of the substitution automaton started at $b$ on
$w$: either both are undefined, or both are the same state.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 6, Equation (automata relations). -/
public theorem seedAutomaton_one_cons {A : Type*} (η : A → List A) (b a : A) (w : List ℕ) :
    seedAutomaton η b a (1 :: w) = substitutionAutomaton η b w := rfl

/-- **The seed automaton rejects the empty word.** Let $\eta$ send each letter of an alphabet
$A$ to a finite word over $A$, and let $a, b \in A$. The automaton $\mathcal{A}_{\eta,s}$ of
the seed $s = b|a$ does not accept the empty word.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 6. -/
public theorem seedAutomaton_nil {A : Type*} (η : A → List A) (b a : A) :
    seedAutomaton η b a [] = none := rfl

/-- **Digit word along last letters.** Let $\eta$ send each letter of an alphabet $A$ to a
finite word over $A$. For $k \in \mathbb{N}$ and a letter $c \in A$, the word
$\mathrm{last}_{\eta,k}(c)$ of natural numbers is defined by recursion on $k$:
$\mathrm{last}_{\eta,0}(c)$ is the empty word; if $\eta(c)$ is nonempty with last letter $d$,
then $\mathrm{last}_{\eta,k+1}(c)$ is the digit $|\eta(c)| - 1$ followed by
$\mathrm{last}_{\eta,k}(d)$; and if $\eta(c)$ is empty, then $\mathrm{last}_{\eta,k+1}(c)$ is
the empty word.

For a substitution $\eta$, a number $p \ge 1$ and a letter $c \in A$, the word
$\mathrm{last}_{\eta,p}(c)$ is the digit word of the last position of $\eta^p(c)$, written
$\mathrm{tail}_{\eta,p,c}(|\eta^p(c)| - 1)$ in the source. In Section 7 of the source, where
$u : \mathbb{Z} \to A$ is a two-sided periodic point of $\eta$ with least period $p$ and seed
letters $u_{-1}$ and $u_0$, the words $W_{\max} = \mathrm{last}_{\eta,p}(u_{-1})$ and
$W_{\min} = 0^p$ are used.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Section 7 (the words `W_min` and `W_max`). -/
public def lastLetterDigits {A : Type*} (η : A → List A) : ℕ → A → List ℕ
  | 0, _ => []
  | k + 1, c =>
    match (η c).getLast? with
    | some d => ((η c).length - 1) :: lastLetterDigits η k d
    | none => []

/-- **Recurrence for the last-letter digit word.** Let $\eta$ map each letter of an alphabet $A$
to a finite word over $A$. For a natural number $j$ and a letter $e \in A$, the last-letter
digit word of $j$ steps from $e$ is obtained by repeating the following step $j$ times, starting
at $e$ and stopping early if the image of the current letter is empty: from the current letter
$x$, record the digit $|\eta(x)| - 1$ and move to the last letter of $\eta(x)$. Let $c, d \in A$
and let $k$ be a natural number. If $\eta(c)$ is nonempty and its last letter is $d$, then the
last-letter digit word of $k + 1$ steps from $c$ is the digit $|\eta(c)| - 1$ followed by the
last-letter digit word of $k$ steps from $d$.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 7. -/
public theorem lastLetterDigits_succ_of_getLast? {A : Type*} (η : A → List A) (k : ℕ) (c d : A)
    (h : (η c).getLast? = some d) :
    lastLetterDigits η (k + 1) c = ((η c).length - 1) :: lastLetterDigits η k d := by
  simp [lastLetterDigits, h]

/-- **Last-letter digit word for the Fibonacci substitution.** Let $\varphi$ be the Fibonacci
substitution on the alphabet $\{0, 1\}$, given by $\varphi(0) = 01$ and $\varphi(1) = 0$.
Following the last letter twice from the letter $1$, where each step from a letter $c$ records
the digit $|\varphi(c)| - 1$ and moves to the last letter of $\varphi(c)$, gives the digit word
$01$: the word $\varphi(1) = 0$ gives the digit $|\varphi(1)| - 1 = 0$ and ends with $0$, and
then the word $\varphi(0) = 01$ gives the digit $|\varphi(0)| - 1 = 1$ and ends with $1$.

This digit word $01$ is the word that Labbé and Lepšová denote $W_{\max}$ for the Fibonacci
substitution, written there $a \mapsto ab$, $b \mapsto a$ with $a = 0$ and $b = 1$, and the
period $p = 2$.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, proof of Proposition 9.2 (`W_max = 01`). -/
public theorem lastLetterDigits_fibonacci :
    lastLetterDigits (fun a : Fin 2 => if a = 0 then [0, 1] else [0]) 2 1 = [0, 1] := by
  decide

/-- **The complement radix order.** For finite words $w$ and $w'$ over $\mathbb{N}$, write
$|w|$ for the length of $w$. Then $w \prec w'$ holds exactly in the following three cases:
$w$ starts with $1$ and $w'$ starts with $0$; both words start with $0$, and either
$|w| < |w'|$, or $|w| = |w'|$ and $w$ is lexicographically smaller than $w'$ (radix order);
both words start with $1$, and either $|w| > |w'|$, or $|w| = |w'|$ and $w$ is
lexicographically smaller than $w'$ (reversed radix order). In particular, a word that does
not start with $0$ or $1$ is never related to any word.

On the words starting with $0$ or $1$ this is the order $\prec$ of the paper.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Section 8 (definition of the total order `≺`). -/
public def ComplementRadixLT (w w' : List ℕ) : Prop :=
  (w.head? = some 1 ∧ w'.head? = some 0) ∨
    (w.head? = some 0 ∧ w'.head? = some 0 ∧
      (w.length < w'.length ∨ (w.length = w'.length ∧ w < w'))) ∨
    (w.head? = some 1 ∧ w'.head? = some 1 ∧
      (w'.length < w.length ∨ (w.length = w'.length ∧ w < w')))

/-- **Examples of the complement radix order.** In the complement radix order $\prec$ on
finite words over $\mathbb{N}$, $111 \prec 10$, $10 \prec 1$, $1 \prec 0$, $0 \prec 00$,
$00 \prec 01$ and $01 \prec 000$. These are the consecutive comparisons in the chain
$\cdots \prec 111 \prec 10 \prec 1 \prec 0 \prec 00 \prec 01 \prec 000$ given in the paper.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 8 (example after the definition of `≺`). -/
public theorem complementRadixLT_examples :
    ComplementRadixLT [1, 1, 1] [1, 0] ∧ ComplementRadixLT [1, 0] [1] ∧
      ComplementRadixLT [1] [0] ∧ ComplementRadixLT [0] [0, 0] ∧
      ComplementRadixLT [0, 0] [0, 1] ∧ ComplementRadixLT [0, 1] [0, 0, 0] := by
  simp only [ComplementRadixLT]
  refine ⟨by simp, by simp, by simp, by simp, ?_, by simp⟩
  simp only [List.head?_cons, List.length_cons, List.length_nil]
  exact Or.inr (Or.inl ⟨trivial, trivial,
    Or.inr ⟨trivial, List.Lex.cons (List.Lex.rel Nat.zero_lt_one)⟩⟩)

/-- **The Dumont–Thomas image language.** Let $\eta$ send each letter of an alphabet $A$ to a
finite word over $A$, let $u : \mathbb{Z} \to A$ and let $p \in \mathbb{N}$. Write
$\mathcal{A}_{\eta,s}$ for the seed automaton of $\eta$ with seed $s = u_{-1} | u_0$, and
$W_{\max}$ for the digit word obtained by following the last letter from $u_{-1}$ for at most
$p$ steps: at a letter $c$ it records $|\eta(c)| - 1$ and moves to the last letter of
$\eta(c)$, stopping early if $\eta(c)$ is empty. The language is the set of finite words $w$
over $\mathbb{N}$ such that $|w| = \ell p + 1$ for some $\ell \in \mathbb{N}$, $w$ is accepted
by $\mathcal{A}_{\eta,s}$, $w$ does not start with the word $0 0^p$, and $w$ does not start
with the word $1 W_{\max}$.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Lemma 8.3 and Theorem 8.4. -/
public def dumontThomasLanguage {A : Type*} (η : A → List A) (u : ℤ → A) (p : ℕ) :
    Set (List ℕ) :=
  {w | (∃ ℓ : ℕ, w.length = ℓ * p + 1) ∧ (seedAutomaton η (u (-1)) (u 0) w).isSome ∧
    ¬ (0 :: List.replicate p 0) <+: w ∧ ¬ (1 :: lastLetterDigits η p (u (-1))) <+: w}

/-- **Membership in the Dumont–Thomas image language.** Let $\eta$ send each letter of an
alphabet $A$ to a finite word over $A$, let $u : \mathbb{Z} \to A$ and $p \in \mathbb{N}$, and
let $\mathcal{A}_{\eta,s}$ be the automaton of the seed $s = u_{-1}|u_0$. A word $w$ of natural
numbers lies in the image language of $\eta$, $u$ and $p$ if and only if the length of $w$ is
$\ell p + 1$ for some $\ell \in \mathbb{N}$, $\mathcal{A}_{\eta,s}$ accepts $w$, $w$ does not
start with $0\,0^p$, and $w$ does not start with $1\,\mathrm{last}_{\eta,p}(u_{-1})$, where
$\mathrm{last}_{\eta,p}(u_{-1})$ is the digit word along last letters with $p$ steps starting
from $u_{-1}$.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Lemma 8.3. -/
public theorem mem_dumontThomasLanguage {A : Type*} (η : A → List A) (u : ℤ → A) (p : ℕ)
    (w : List ℕ) :
    w ∈ dumontThomasLanguage η u p ↔
      (∃ ℓ : ℕ, w.length = ℓ * p + 1) ∧ (seedAutomaton η (u (-1)) (u 0) w).isSome ∧
        ¬ (0 :: List.replicate p 0) <+: w ∧ ¬ (1 :: lastLetterDigits η p (u (-1))) <+: w :=
  Iff.rfl

/-- **Two's complement value.** For a word $w = w_{k-1} \cdots w_0$ of natural numbers,
written with $w_{k-1}$ first, the two's complement value is the integer
$\mathrm{val}_{2c}(w) = \sum_{i<k} w_i 2^i - w_{k-1} 2^k$; the empty word has value $0$.
For a binary word (all digits in $\{0, 1\}$) this is the usual two's complement value.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Section 9.1. -/
public def twosComplementValue (w : List ℕ) : ℤ :=
  (∑ i ∈ Finset.range w.length, (w.reverse.getD i 0 : ℤ) * 2 ^ i) -
    (w.headD 0 : ℤ) * 2 ^ w.length

/-- **Two's complement values of small words.** The two's complement values $\mathrm{val}_{2c}$
of the binary words $1$, $10$, $101$ and $011$ (most significant digit first) are $-1$, $-2$, $-3$
and $3$ respectively.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 9.1 (table of `rep_{2c}`). -/
public theorem twosComplementValue_examples :
    twosComplementValue [1] = -1 ∧ twosComplementValue [1, 0] = -2 ∧
      twosComplementValue [1, 0, 1] = -3 ∧ twosComplementValue [0, 1, 1] = 3 := by
  decide

/-- **Fibonacci complement value.** Let $(F_i)_{i \ge 0}$ be the Fibonacci numbers with
$F_0 = 1$, $F_1 = 2$ and $F_{i+2} = F_{i+1} + F_i$. The Fibonacci complement value of a word
$w = w_{k-1} \cdots w_1 w_0$ of natural numbers, written most significant digit first, is the
integer $\operatorname{val}_{\mathcal{F}c}(w) = \sum_{i=0}^{k-1} w_i F_i - w_{k-1} F_k$ when
$k \ge 1$, and $0$ when $w$ is empty.

Source: Sébastien Labbé and Jana Lepšová, *Dumont-Thomas Complement Numeration Systems for
ℤ*, INTEGERS 24 (2024), Article A112, Section 9.2. -/
public def fibonacciComplementValue (w : List ℕ) : ℤ :=
  (∑ i ∈ Finset.range w.length, (w.reverse.getD i 0 : ℤ) * (Nat.fib (i + 2) : ℤ)) -
    (w.headD 0 : ℤ) * (Nat.fib (w.length + 2) : ℤ)

/-- **Values of small Fibonacci complement words.** The Fibonacci complement values of the
digit words $1$, $100$, $001$ and $010$ (most significant digit first) are $-1$, $-2$, $1$ and
$2$, respectively.

Source: Labbé and Lepšová, *Dumont-Thomas Complement Numeration Systems for ℤ*, INTEGERS 24
(2024), Article A112, Section 9.2. -/
public theorem fibonacciComplementValue_examples :
    fibonacciComplementValue [1] = -1 ∧ fibonacciComplementValue [1, 0, 0] = -2 ∧
      fibonacciComplementValue [0, 0, 1] = 1 ∧ fibonacciComplementValue [0, 1, 0] = 2 := by
  decide

end

end MetaMathlibExt
