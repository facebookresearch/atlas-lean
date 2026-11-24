/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Real.GoldenRatio
public import Mathlib.Order.Filter.AtTopBot.Basic
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Data.Set.Card
public import MathlibExt.Combinatorics.InfiniteWord.PureMorphicWord
public import WantedExt.NumberTheory.GeneralizedHofstadterOrderWanted

/-!
# Wythoff's game with terminal positions

Statements from Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal
Positions or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6.

The game `K^ℓ` is Wythoff's game on two piles (remove a positive number of tokens from one
pile, or the same positive number from both) in which every position `(x, y)` with
`x + y ≤ ℓ` is terminal: no move is allowed from it. Its P-positions are the unique stable
and absorbing set of the (well-founded) move relation, `MetaMathlibExt.pPositions_unique`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Moves of Wythoff's game with terminal positions.** Let $\ell$ be a natural number. In the
game $K^\ell$, whose positions are pairs $(x, y)$ of natural numbers (the sizes of two piles of
tokens), there is a move from $(x, y)$ to $(x', y')$ when $x + y > \ell$ and either $y' = y$ and
$x' < x$, or $x' = x$ and $y' < y$, or $x = x' + k$ and $y = y' + k$ for some $k > 0$. Thus the
positions with $x + y \le \ell$ are terminal, and from any other position a move removes a
positive number of tokens from one pile, or the same positive number from both piles.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6, the game
`K^ℓ` of Theorem 17 (`jis-2026-26.1.6-thm-17`): Wythoff's moves with terminal positions
`{(x, y) | x + y ≤ ℓ}`. -/
def wythoffTerminalMove (ℓ : ℕ) (p q : ℕ × ℕ) : Prop :=
  ℓ < p.1 + p.2 ∧
    ((q.2 = p.2 ∧ q.1 < p.1) ∨ (q.1 = p.1 ∧ q.2 < p.2) ∨
      (∃ k, 0 < k ∧ q.1 + k = p.1 ∧ q.2 + k = p.2))

/-- **No moves from terminal positions.** Let $\ell$ be a natural number. In the game $K^\ell$
(Wythoff's game in which the positions $(x, y)$ with $x + y \le \ell$ are terminal), there is no
move from a position $(x, y)$ with $x + y \le \ell$ to any position.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, terminal positions of `K^ℓ` (Theorem 17). -/
theorem not_wythoffTerminalMove_of_terminal {ℓ : ℕ} {p : ℕ × ℕ} (hp : p.1 + p.2 ≤ ℓ)
    (q : ℕ × ℕ) : ¬wythoffTerminalMove ℓ p q := fun h => by
  have := h.1
  omega

/-- **A move to the origin in $K^0$.** In the game $K^0$ (Wythoff's game in which only $(0, 0)$ is
terminal), there is a move from the position $(1, 0)$ to the position $(0, 0)$.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Wythoff's moves (Theorem 17). -/
theorem wythoffTerminalMove_zero_one_zero : wythoffTerminalMove 0 (1, 0) (0, 0) :=
  ⟨by decide, Or.inl ⟨rfl, by decide⟩⟩

/-- **The mex sequence of Wythoff's game with terminal positions.** Fix a natural number $\ell$.
The sequence $(a_n)_{n \ge 0}$ is defined recursively: $a_n$ is the least natural number greater
than $\ell$ that differs from $a_i$ and from $a_i + i + \ell + 1$ for every $i < n$. Writing
$b_i = a_i + i + \ell + 1$, this says that $a_n$ is the least natural number outside
$\{0, 1, \dots, \ell\} \cup \{a_i, b_i : i < n\}$; in particular $a_0 = \ell + 1$ and
$b_0 = 2\ell + 2$.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Theorem 17, equation (mexdef) (`jis-2026-26.1.6-thm-17`). -/
noncomputable def wythoffMexA (ℓ : ℕ) (n : ℕ) : ℕ :=
  sInf {m : ℕ | ℓ < m ∧ ∀ i : Fin n,
    m ≠ wythoffMexA ℓ i ∧ m ≠ wythoffMexA ℓ i + i + ℓ + 1}
termination_by n
decreasing_by all_goals exact i.isLt

/-- **The companion of the mex sequence.** Fix a natural number $\ell$ and let $(a_n)$ be the mex
sequence of $K^\ell$ (Wythoff's game in which the positions $(x, y)$ with $x + y \le \ell$ are
terminal). Its companion sequence is $b_n = a_n + n + \ell + 1$ for every natural number $n$.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Theorem 17, equation (mexdef). -/
noncomputable def wythoffMexB (ℓ n : ℕ) : ℕ := wythoffMexA ℓ n + n + ℓ + 1

/-- **The term $a_0$ of the mex sequence.** For every natural number $\ell$, the mex sequence
$(a_n)$ of $K^\ell$ (Wythoff's game in which the positions $(x, y)$ with $x + y \le \ell$ are
terminal) satisfies $a_0 = \ell + 1$.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Theorem 17 (`(a₀, b₀) = (ℓ + 1, 2ℓ + 2)`). -/
theorem wythoffMexA_zero (ℓ : ℕ) : wythoffMexA ℓ 0 = ℓ + 1 := by
  rw [wythoffMexA]
  simp only [IsEmpty.forall_iff, and_true]
  apply le_antisymm
  · exact Nat.sInf_le (Nat.lt_succ_self ℓ)
  · exact Nat.sInf_mem (s := {m | ℓ < m}) ⟨ℓ + 1, Nat.lt_succ_self ℓ⟩

/-- **The term $a_1$ of the mex sequence.** Let $\ell \ge 1$, let $K^\ell$ be Wythoff's game in
which the positions $(x, y)$ with $x + y \le \ell$ are terminal, and let $(a_n)$ be the mex
sequence of $K^\ell$. Then $a_1 = \ell + 2$.

This is the least integer greater than $\ell$ other than $a_0 = \ell + 1$ and
$a_0 + \ell + 1 = 2\ell + 2$.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Theorem 17, equation (mexdef). -/
theorem wythoffMexA_one (ℓ : ℕ) (hℓ : 1 ≤ ℓ) : wythoffMexA ℓ 1 = ℓ + 2 := by
  rw [wythoffMexA]
  simp only [Fin.forall_fin_one, Fin.val_zero, wythoffMexA_zero]
  have hmem : ℓ + 2 ∈ {m : ℕ | ℓ < m ∧ m ≠ ℓ + 1 ∧ m ≠ ℓ + 1 + 0 + ℓ + 1} :=
    ⟨by omega, by omega, by omega⟩
  apply le_antisymm (Nat.sInf_le hmem)
  obtain ⟨h1, h2, h3⟩ := Nat.sInf_mem ⟨_, hmem⟩
  omega

/-- **The term $b_0$ of the companion sequence.** For every natural number $\ell$, the companion
sequence $(b_n)$ of the mex sequence of $K^\ell$ (Wythoff's game in which the positions $(x, y)$
with $x + y \le \ell$ are terminal) satisfies $b_0 = 2\ell + 2$.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Theorem 17 (`(a₀, b₀) = (ℓ + 1, 2ℓ + 2)`). -/
theorem wythoffMexB_zero (ℓ : ℕ) : wythoffMexB ℓ 0 = 2 * ℓ + 2 := by
  rw [wythoffMexB, wythoffMexA_zero]
  ring

/-- **Predicted P-positions of $K^\ell$.** Let $\ell$ be a natural number, let $a_n$ be the least
natural number $m > \ell$ with $m \ne a_i$ and $m \ne b_i$ for all $i < n$, where
$b_i = a_i + i + \ell + 1$ (the mex sequences of $K^\ell$). This is the set of positions
$(x, y)$ of natural numbers with $x + y \le \ell$ (the terminal positions of $K^\ell$),
together with the pairs $(a_n, b_n)$ and $(b_n, a_n)$ for $n \ge 0$.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Theorem 17. -/
def wythoffTerminalPSet (ℓ : ℕ) : Set (ℕ × ℕ) :=
  {p | p.1 + p.2 ≤ ℓ} ∪ {p | ∃ n, p = (wythoffMexA ℓ n, wythoffMexB ℓ n) ∨
    p = (wythoffMexB ℓ n, wythoffMexA ℓ n)}

/-- **Terminal positions lie in the predicted P-position set.** Let $\ell$ be a natural number.
Every position $(x, y) \in \mathbb{N} \times \mathbb{N}$ with $x + y \le \ell$ belongs to the
predicted P-position set of the game $K^\ell$ (Wythoff's game in which the positions with
$x + y \le \ell$ are terminal).

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Theorem 17. -/
theorem mem_wythoffTerminalPSet_of_terminal {ℓ : ℕ} {p : ℕ × ℕ} (hp : p.1 + p.2 ≤ ℓ) :
    p ∈ wythoffTerminalPSet ℓ :=
  Or.inl hp

/-- **The Komak sequence $g$.** Let $\varphi$ be the golden ratio. The sequence
$g : \mathbb{N} \to \mathbb{N}$ of Komak et al. is defined by recursion on $n$: if some
$m < n$ satisfies $\lfloor n\varphi \rfloor = \lfloor m\varphi^2 \rfloor + 1$, then
$g(n) = 1 - g(m)$ for the least such $m$; otherwise $g(n) = 1$.

Such an $m$ is unique when it exists, and every $m$ with
$\lfloor n\varphi \rfloor = \lfloor m\varphi^2 \rfloor + 1$ satisfies $m < n$, so this agrees
with the source's definition, which does not restrict $m$ (there $\varphi^2$ is written
$\varphi + 1$). In particular $g(0) = 1$ and $g(1) = 0$.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Definition `def:fg` (arXiv:2512.11601v1). -/
noncomputable def komakG (n : ℕ) : ℕ :=
  if h : ∃ m < n, ⌊(n : ℝ) * Real.goldenRatio⌋₊ = ⌊(m : ℝ) * Real.goldenRatio ^ 2⌋₊ + 1 then
    1 - komakG (Nat.find h)
  else 1
termination_by n
decreasing_by exact (Nat.find_spec h).1

/-- **Value of the Komak sequence at 0.** The sequence $g$ of Komak et al. satisfies
$g(0) = 1$.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Definition `def:fg`. -/
theorem komakG_zero : komakG 0 = 1 := by
  rw [komakG]
  split_ifs with h
  · obtain ⟨m, hm, -⟩ := h
    omega
  · rfl

/-- **Value of the Komak sequence at 1.** The sequence $g$ of Komak et al. satisfies
$g(1) = 0$: with $\varphi$ the golden ratio, $\lfloor \varphi \rfloor = 1 =
\lfloor 0 \cdot \varphi^2 \rfloor + 1$, so $g(1) = 1 - g(0) = 0$.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Definition `def:fg` and Table `tab:gh`. -/
theorem komakG_one : komakG 1 = 0 := by
  have hfloor : ⌊Real.goldenRatio⌋₊ = 1 := by
    rw [Nat.floor_eq_iff Real.goldenRatio_pos.le]
    constructor
    · exact_mod_cast Real.one_lt_goldenRatio.le
    · norm_num [Real.goldenRatio_lt_two]
  rw [komakG]
  split_ifs with h
  · have h0 : Nat.find h = 0 := by
      have := (Nat.find_spec h).1
      omega
    rw [h0, komakG_zero]
  · exact absurd ⟨0, by omega, by simp [hfloor]⟩ h

/-- **Greedy Fibonacci digits.** Let $F_0 = 1$, $F_1 = 2$ and $F_{i+2} = F_{i+1} + F_i$. For
$k, n \in \mathbb{N}$, the greedy digits of $n$ at positions $k - 1, \dots, 0$ are the list of
$k$ digits, most significant first, computed with a remainder $r$ that starts at $n$: for
$j = k - 1, \dots, 0$ in turn, the digit at position $j$ is $1$ if $F_j \le r$, in which case
$F_j$ is subtracted from $r$, and $0$ otherwise. The digits $1$ and $0$ are encoded as the
booleans true and false.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Definition `def:fib_rep` (greedy representation). -/
def fibGreedyDigits : ℕ → ℕ → List Bool
  | 0, _ => []
  | k + 1, n =>
      if Nat.fib (k + 2) ≤ n then true :: fibGreedyDigits k (n - Nat.fib (k + 2))
      else false :: fibGreedyDigits k n

/-- **Fibonacci digit count.** Let $F_0 = 1$, $F_1 = 2$ and $F_{i+2} = F_{i+1} + F_i$. For
$n, s, k_0 \in \mathbb{N}$, the digit count of $n$ searched from $k_0$ in at most $s$ steps is
the least $k$ with $k_0 \le k < k_0 + s$ and $n < F_k$ if there is one, and $k_0 + s$
otherwise.

With $k_0 = 0$ and $s = n + 1$ it is the number of digits of the greedy Fibonacci
representation of $n$, the least $k$ with $n < F_k$, which exists since $n < F_n$.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Definition `def:fib_rep` (greedy representation). -/
def fibDigitCount (n : ℕ) : ℕ → ℕ → ℕ
  | 0, k => k
  | fuel + 1, k => if n < Nat.fib (k + 2) then k else fibDigitCount n fuel (k + 1)

/-- **Greedy Fibonacci representation.** Let $F_0 = 1$, $F_1 = 2$ and $F_{i+2} = F_{i+1} + F_i$.
The greedy Fibonacci representation $\mathrm{rep}_F(n)$ of $n \in \mathbb{N}$ is the word of
digits $d_{k-1} \cdots d_0$, most significant first, where $k$ is the least integer with
$n < F_k$ and the digits are chosen greedily: starting from the remainder $n$, for
$j = k - 1, \dots, 0$ in turn, $d_j = 1$ and $F_j$ is subtracted from the remainder if $F_j$ is
at most the remainder, and $d_j = 0$ otherwise. It has no leading zero, and
$\mathrm{rep}_F(0)$ is the empty word. The digits $1$ and $0$ are encoded as the booleans true
and false.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Definition `def:fib_rep`. -/
def fibRep (n : ℕ) : List Bool :=
  (fibGreedyDigits (fibDigitCount n (n + 1) 0) n).dropWhile (· = false)

/-- **Greedy Fibonacci representations of 0, 2, 4, 7 and 12.** With $F_0 = 1$, $F_1 = 2$ and
$F_{i+2} = F_{i+1} + F_i$, the greedy Fibonacci representations are
$\mathrm{rep}_F(0) = \varepsilon$ (the empty word), $\mathrm{rep}_F(2) = 10$,
$\mathrm{rep}_F(4) = 101$, $\mathrm{rep}_F(7) = 1010$ and $\mathrm{rep}_F(12) = 10101$.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Definition `def:fib_rep` and Table `tab:K1`. -/
theorem fibRep_examples :
    fibRep 0 = [] ∧ fibRep 2 = [true, false] ∧ fibRep 4 = [true, false, true] ∧
      fibRep 7 = [true, false, true, false] ∧
      fibRep 12 = [true, false, true, false, true] := by
  decide

/-- **Fibonacci-automatic sequences.** A sequence $u : \mathbb{N} \to \mathbb{N}$ is
Fibonacci-automatic if there are a finite set $Q$ of states, a transition function
$\delta : Q \times \{0, 1\} \to Q$, an initial state $q_0 \in Q$ and an output map
$\tau : Q \to \mathbb{N}$ such that for every $n$, $u(n) = \tau(q)$, where $q$ is the state
reached from $q_0$ by reading the digits of the greedy Fibonacci representation
$\mathrm{rep}_F(n)$ with $\delta$, most significant digit first.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Section 2 (Fibonacci-automatic sequences, DFAO fed with `rep_F(n)`). -/
def IsFibonacciAutomatic (u : ℕ → ℕ) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (δ : Q → Bool → Q) (q₀ : Q) (τ : Q → ℕ),
    ∀ n, u n = τ ((fibRep n).foldl δ q₀)

/-- **Constant sequences are Fibonacci-automatic.** For every $c \in \mathbb{N}$, the constant
sequence $n \mapsto c$ is Fibonacci-automatic.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Section 2 (Fibonacci-automatic sequences). -/
theorem isFibonacciAutomatic_const (c : ℕ) : IsFibonacciAutomatic fun _ => c :=
  ⟨Unit, inferInstance, fun _ _ => (), (), fun _ => c, fun _ => rfl⟩

/-- **A prefix of the fourth iterate of $f_1$.** Let $f_1$ be the map on the alphabet
$\{0, 1, 2, 3, 4\}$ given by $0 \mapsto 01$, $1 \mapsto 2$, $2 \mapsto 34$, $3 \mapsto 31$ and
$4 \mapsto 2$, extended to finite words by concatenation. The first six letters of the word
$f_1^4(0)$ are $0, 1, 2, 3, 4, 3$.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, table after Proposition 22. -/
theorem morphIterate_wythoffTerminal_one_example :
    (morphIterate (![[0, 1], [2], [3, 4], [3, 1], [2]] : Fin 5 → List (Fin 5)) 4 [0]).take 6 =
      [0, 1, 2, 3, 4, 3] := by
  decide

/-- **Larsson's set $R_2$.** Let $\varphi = (1 + \sqrt{5})/2$ be the golden ratio. The set
$R_2 \subseteq \mathbb{N} \times \mathbb{N}$ consists of $(0, 0)$ together with, for every natural
number $n$, the pairs $(n, 2n + 1)$ and $(2n + 1, n)$ and the pairs
$(2\lfloor n\varphi \rfloor + 2, 2\lfloor n\varphi^2 \rfloor + 2)$ and
$(2\lfloor n\varphi^2 \rfloor + 2, 2\lfloor n\varphi \rfloor + 2)$.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Theorem 26. -/
def larssonSetTwo : Set (ℕ × ℕ) :=
  {(0, 0)} ∪ {p | ∃ n : ℕ, p = (n, 2 * n + 1) ∨ p = (2 * n + 1, n)} ∪
    {p | ∃ n : ℕ,
      p = (2 * ⌊(n : ℝ) * Real.goldenRatio⌋₊ + 2, 2 * ⌊(n : ℝ) * Real.goldenRatio ^ 2⌋₊ + 2) ∨
      p = (2 * ⌊(n : ℝ) * Real.goldenRatio ^ 2⌋₊ + 2, 2 * ⌊(n : ℝ) * Real.goldenRatio⌋₊ + 2)}

/-- **Sample positions in Larsson's set $R_2$.** The positions $(0, 0)$, $(0, 1)$ and
$(2, 2)$ belong to Larsson's set $R_2$.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Theorem 26. -/
theorem larssonSetTwo_examples :
    (0, 0) ∈ larssonSetTwo ∧ (0, 1) ∈ larssonSetTwo ∧ (2, 2) ∈ larssonSetTwo :=
  ⟨Or.inl (Or.inl rfl), Or.inl (Or.inr ⟨0, Or.inl rfl⟩), Or.inr ⟨0, Or.inl (by simp)⟩⟩

/-- **Larsson's set $R_3$.** Larsson's set $R_3 \subseteq \mathbb{N} \times \mathbb{N}$
consists of $(0, 0)$ together with the pairs $(n, 2n + 1)$, $(2n + 1, n)$, $(n, 2n + 2)$ and
$(2n + 2, n)$ for all $n \ge 0$.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Theorem 28. -/
def larssonSetThree : Set (ℕ × ℕ) :=
  {(0, 0)} ∪ {p | ∃ n : ℕ, p = (n, 2 * n + 1) ∨ p = (2 * n + 1, n) ∨
    p = (n, 2 * n + 2) ∨ p = (2 * n + 2, n)}

/-- **Sample positions in Larsson's set $R_3$.** The positions $(0, 0)$, $(0, 2)$ and
$(3, 1)$ belong to Larsson's set $R_3$.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Theorem 28. -/
theorem larssonSetThree_examples :
    (0, 0) ∈ larssonSetThree ∧ (0, 2) ∈ larssonSetThree ∧ (3, 1) ∈ larssonSetThree :=
  ⟨Or.inl rfl, Or.inr ⟨0, Or.inr (Or.inr (Or.inl rfl))⟩, Or.inr ⟨1, Or.inr (Or.inl rfl)⟩⟩

/-- **P-positions of Wythoff's game with terminal positions.** Let $\ell \ge 1$. Let $a_n$ be the
least natural number $m > \ell$ with $m \ne a_i$ and $m \ne b_i$ for all $i < n$, where
$b_i = a_i + i + \ell + 1$. Let $P$ be the set of positions $(x, y)$ with $x + y \le \ell$,
together with the pairs $(a_n, b_n)$ and $(b_n, a_n)$ for $n \ge 0$. Then $P$ is stable, meaning
no move of $K^\ell$ leads from a position of $P$ to a position of $P$, and absorbing, meaning
from every position outside $P$ some move of $K^\ell$ leads into $P$.

Since the move relation is well founded, a stable and absorbing set is the set of P-positions,
so the non-terminal P-positions of $K^\ell$ are exactly the pairs $(a_n, b_n)$ and $(b_n, a_n)$.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Theorem 17 (`jis-2026-26.1.6-thm-17`). -/
public theorem_wanted wythoffTerminal_pPositions (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (∀ x y, x ∈ wythoffTerminalPSet ℓ → wythoffTerminalMove ℓ x y →
        y ∉ wythoffTerminalPSet ℓ) ∧
      ∀ x, x ∉ wythoffTerminalPSet ℓ →
        ∃ y, wythoffTerminalMove ℓ x y ∧ y ∈ wythoffTerminalPSet ℓ

/-- **P-positions of $K^1$.** Let $a_n$ be the least natural number $m > 1$ with $m \ne a_i$ and
$m \ne b_i$ for all $i < n$, where $b_i = a_i + i + 2$; so $(a_0, b_0) = (2, 4)$. Let $P$ be the
set of positions $(x, y)$ with $x + y \le 1$, together with the pairs $(a_n, b_n)$ and
$(b_n, a_n)$ for $n \ge 0$. Then $P$ is stable, meaning no move of $K^1$ leads from a position
of $P$ to a position of $P$, and absorbing, meaning from every position outside $P$ some move
of $K^1$ leads into $P$.

This is the case $\ell = 1$ of Theorem 17. Since the move relation is well founded, a stable
and absorbing set is the set of P-positions, so $P$ is the set of P-positions of $K^1$.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Proposition 15 (`jis-2026-26.1.6-prop-15`). -/
public theorem_wanted wythoffTerminal_one_pPositions :
    (∀ x y, x ∈ wythoffTerminalPSet 1 → wythoffTerminalMove 1 x y →
        y ∉ wythoffTerminalPSet 1) ∧
      ∀ x, x ∉ wythoffTerminalPSet 1 →
        ∃ y, wythoffTerminalMove 1 x y ∧ y ∈ wythoffTerminalPSet 1

/-- **P-positions of Wythoff's game when positions of total at most 2 are terminal.** In the game
$K^2$ on two piles, a move from a position $(x, y)$ with $x + y > 2$ removes a positive number
of tokens from one pile or the same positive number from both piles, and no move is allowed
from a position with $x + y \le 2$. Let $a_n$ be the least integer $m > 2$ that differs from
$a_i$ and $b_i$ for every $i < n$, and let $b_n = a_n + n + 3$, so that $(a_0, b_0) = (3, 6)$.
Let $P$ consist of the positions $(x, y)$ with $x + y \le 2$ together with the pairs
$(a_n, b_n)$ and $(b_n, a_n)$ for $n \ge 0$. Then no move of $K^2$ leads from a position in $P$
to a position in $P$, and from every position not in $P$ some move of $K^2$ leads into $P$.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Proposition 16 (`jis-2026-26.1.6-prop-16`). -/
public theorem_wanted wythoffTerminal_two_pPositions :
    (∀ x y, x ∈ wythoffTerminalPSet 2 → wythoffTerminalMove 2 x y →
        y ∉ wythoffTerminalPSet 2) ∧
      ∀ x, x ∉ wythoffTerminalPSet 2 →
        ∃ y, wythoffTerminalMove 2 x y ∧ y ∈ wythoffTerminalPSet 2

/-- **Structure of the mex sequences of $K^\ell$.** Let $\ell \ge 1$. Let $a_n$ be the least
natural number $m > \ell$ with $m \ne a_i$ and $m \ne b_i$ for all $i < n$, where
$b_i = a_i + i + \ell + 1$ (the mex sequences of the game $K^\ell$). Then $(a_n)$ and $(b_n)$
are strictly increasing; a natural number $j$ satisfies $j > \ell$ if and only if $j = a_n$ or
$j = b_n$ for some $n$; $a_n \ne b_m$ for all $n$ and $m$; every $j > \ell$ equals $b_n - a_n$
for exactly one $n$; and for every $n$, $a_{n+1} - a_n \in \{1, 2\}$,
$b_{n+1} - b_n \in \{2, 3\}$ and $b_{n+1} - b_n = (a_{n+1} - a_n) + 1$.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Lemma 18 (`jis-2026-26.1.6-lem-18`). -/
public theorem_wanted wythoffMex_properties (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    StrictMono (wythoffMexA ℓ) ∧ StrictMono (wythoffMexB ℓ) ∧
    (∀ j, ℓ < j ↔ (∃ n, wythoffMexA ℓ n = j) ∨ ∃ n, wythoffMexB ℓ n = j) ∧
    (∀ n m, wythoffMexA ℓ n ≠ wythoffMexB ℓ m) ∧
    (∀ j, ℓ < j → ∃! n, j = wythoffMexB ℓ n - wythoffMexA ℓ n) ∧
    (∀ n, wythoffMexA ℓ (n + 1) - wythoffMexA ℓ n ∈ ({1, 2} : Set ℕ) ∧
      wythoffMexB ℓ (n + 1) - wythoffMexB ℓ n ∈ ({2, 3} : Set ℕ) ∧
      wythoffMexB ℓ (n + 1) - wythoffMexB ℓ n =
        wythoffMexA ℓ (n + 1) - wythoffMexA ℓ n + 1)

/-- **Golden-ratio formula for the mex sequences.** Let $\ell \ge 1$, let $\varphi$ be the golden
ratio, let $K^\ell$ be Wythoff's game in which the positions $(x, y)$ with $x + y \le \ell$ are
terminal, and let $(a_n)$ be the mex sequence of $K^\ell$ and $(b_n)$ its companion sequence.
Then there are integers $\lambda_n$ for $n \ge 0$ and an integer $C$ with $|\lambda_n| \le C$
for all $n$ such that, for every natural number $n$,
$a_n = \lfloor (n + \ell)\varphi \rfloor + \lambda_n$ and
$b_n = \lfloor (n + \ell)\varphi^2 \rfloor + \lambda_n + 1$.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Corollary 19 (`jis-2026-26.1.6-cor-19`). -/
public theorem_wanted wythoffMex_floor_goldenRatio (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ lam : ℕ → ℤ, (∃ C : ℤ, ∀ n, |lam n| ≤ C) ∧ ∀ n,
      (wythoffMexA ℓ n : ℤ) = ⌊((n + ℓ : ℕ) : ℝ) * Real.goldenRatio⌋ + lam n ∧
      (wythoffMexB ℓ n : ℤ) = ⌊((n + ℓ : ℕ) : ℝ) * Real.goldenRatio ^ 2⌋ + lam n + 1

/-- **Growth of the mex sequences of $K^\ell$.** Let $\ell \ge 1$. Let $a_n$ be the least natural
number $m > \ell$ with $m \ne a_i$ and $m \ne b_i$ for all $i < n$, where
$b_i = a_i + i + \ell + 1$ (the mex sequences of the game $K^\ell$), and let
$\varphi = (1 + \sqrt{5})/2$ be the golden ratio. Then $a_n / n \to \varphi$ and
$b_n / n \to \varphi^2$ as $n \to \infty$.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Corollary 20 (`jis-2026-26.1.6-cor-20`). -/
public theorem_wanted wythoffMex_tendsto_goldenRatio (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    Filter.Tendsto (fun n : ℕ => (wythoffMexA ℓ n : ℝ) / n) Filter.atTop
        (nhds Real.goldenRatio) ∧
      Filter.Tendsto (fun n : ℕ => (wythoffMexB ℓ n : ℝ) / n) Filter.atTop
        (nhds (Real.goldenRatio ^ 2))


/-- **Komak's description of the P-positions of $K^2$.** Let $\varphi$ be the golden ratio
and $g$ the sequence of Komak et al. Let $S$ be the set of pairs $(x, y)$ of natural numbers
with $x + y \le 2$, together with the pairs
$(\lfloor n\varphi \rfloor + g(n) - 1, \lfloor n\varphi^2 \rfloor + g(n))$ and
$(\lfloor n\varphi^2 \rfloor + g(n), \lfloor n\varphi \rfloor + g(n) - 1)$ for all $n \ge 0$.
In the game $K^2$ (Wythoff's game in which the positions with $x + y \le 2$ are terminal),
no move leads from a position in $S$ to a position in $S$, and from every position outside
$S$ some move leads to a position in $S$.

These two properties determine the set of P-positions, so the P-positions of $K^2$ are
exactly the positions in $S$. The source omits the terminal positions $(0, 0)$ and $(1, 1)$,
which are P-positions since no move leaves them; they are included here.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Theorem 2 (`jis-2026-26.1.6-thm-2`). -/
public theorem_wanted komak_pPositions :
    let S : Set (ℕ × ℕ) := {p | p.1 + p.2 ≤ 2} ∪ {p | ∃ n : ℕ,
      p = (⌊(n : ℝ) * Real.goldenRatio⌋₊ + komakG n - 1,
        ⌊(n : ℝ) * Real.goldenRatio ^ 2⌋₊ + komakG n) ∨
      p = (⌊(n : ℝ) * Real.goldenRatio ^ 2⌋₊ + komakG n,
        ⌊(n : ℝ) * Real.goldenRatio⌋₊ + komakG n - 1)}
    (∀ x y, x ∈ S → wythoffTerminalMove 2 x y → y ∉ S) ∧
      ∀ x, x ∉ S → ∃ y, wythoffTerminalMove 2 x y ∧ y ∈ S

/-- **Hofstadter recursion for the Komak sequence.** Let $h$ be Hofstadter's $G$-sequence
(OEIS A005206), given by $h(0) = 0$ and $h(n) = n - h(h(n - 1))$ for $n \ge 1$. The sequence
$g$ of Komak et al. satisfies $g(0) = 1$, $g(1) = 0$, and for every $n \ge 2$,
$g(n) = 1 - g(h(n - 1))$ if $h(n - 2) < h(n - 1)$, and $g(n) = 1$ otherwise.

The source prints $g(1) = 1$. With $\varphi$ the golden ratio, $\lfloor \varphi \rfloor = 1 =
\lfloor 0 \cdot \varphi^2 \rfloor + 1$, so the definition of $g$ gives $g(1) = 1 - g(0) = 0$,
as in the source's table of values; the value is corrected to $g(1) = 0$.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Proposition 4 (`jis-2026-26.1.6-prop-4`). -/
public theorem_wanted komakG_hofstadter :
    komakG 0 = 1 ∧ komakG 1 = 0 ∧ ∀ n, 2 ≤ n →
      komakG n = if hofstadterF 2 (n - 2) < hofstadterF 2 (n - 1) then
        1 - komakG (hofstadterF 2 (n - 1)) else 1

/-- **The Komak sequence $g$ is Fibonacci-automatic.** The sequence $g$ of Komak et al. is
Fibonacci-automatic.

Only the existence of an automaton is asserted; the explicit automaton that the source draws
for $g$ is not part of the statement.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Proposition 6 (`jis-2026-26.1.6-prop-6`). -/
public theorem_wanted isFibonacciAutomatic_komakG : IsFibonacciAutomatic komakG

/-- **Fibonacci characterization of the P-positions of $K^1$.** For a natural number $n$, let
$\operatorname{rep}_F(n)$ be its greedy Fibonacci representation for $F_0 = 1$, $F_1 = 2$,
$F_{i+2} = F_{i+1} + F_i$: a word over $\{0, 1\}$, most significant digit first, without leading
zeros, empty for $n = 0$. Let $S$ be the set of positions $(x, y)$ with $x + y \le 1$, together
with the pairs $(a, b)$ and $(b, a)$ for natural numbers $a \le b$ such that
$\operatorname{rep}_F(a)$ is nonempty and ends in $0$ and
$\operatorname{rep}_F(b) = \operatorname{rep}_F(a)\,1$. Then $S$ is stable, meaning no move of
$K^1$ leads from a position of $S$ to a position of $S$, and absorbing, meaning from every
position outside $S$ some move of $K^1$ leads into $S$.

Since the move relation is well founded, $S$ is therefore the set of P-positions of $K^1$. As
printed, the theorem imposes the condition on all pairs $a \le b$, which fails at the terminal
P-positions $(0, 0)$ and $(0, 1)$ because $\operatorname{rep}_F(0)$ is empty; the terminal
positions are therefore listed separately.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Theorem 12 (`jis-2026-26.1.6-thm-12`). -/
public theorem_wanted wythoffTerminal_one_fibRep :
    let S : Set (ℕ × ℕ) := {p | p.1 + p.2 ≤ 1} ∪ {p |
      (p.1 ≤ p.2 ∧ (fibRep p.1).getLast? = some false ∧ fibRep p.2 = fibRep p.1 ++ [true]) ∨
      (p.2 ≤ p.1 ∧ (fibRep p.2).getLast? = some false ∧ fibRep p.1 = fibRep p.2 ++ [true])}
    (∀ x y, x ∈ S → wythoffTerminalMove 1 x y → y ∉ S) ∧
      ∀ x, x ∉ S → ∃ y, wythoffTerminalMove 1 x y ∧ y ∈ S

/-- **Golden-ratio formula for Wythoff's game with terminal positions up to total 3.** Let
$\varphi$ be the golden ratio. Let $a_n$ be the least integer greater than $3$ that differs from
$a_i$ and $b_i$ for all $i < n$, and let $b_n = a_n + n + 4$. Then there is a Fibonacci-automatic
sequence $g_3 : \mathbb{N} \to \mathbb{N}$ with $g_3(n) \le 2$ for all $n$ such that, for every
$n \ge 0$, $a_n = \lfloor (n + 2)\varphi \rfloor + g_3(n + 1) - 1$ and
$b_n = \lfloor (n + 2)\varphi^2 \rfloor + g_3(n + 1) + 1$.

Here $(a_n, b_n)$ are the mex pairs of $K^3$, Wythoff's game in which every position $(x, y)$
with $x + y \le 3$ is terminal; by Theorem 17 of the source they are its non-terminal
P-positions with $a_n < b_n$.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Theorem 13 (`jis-2026-26.1.6-thm-13`). -/
public theorem_wanted exists_fibonacciAutomatic_wythoffTerminal_three :
    ∃ g₃ : ℕ → ℕ, IsFibonacciAutomatic g₃ ∧ (∀ n, g₃ n ≤ 2) ∧ ∀ n,
      (wythoffMexA 3 n : ℤ) = ⌊((n + 2 : ℕ) : ℝ) * Real.goldenRatio⌋ + g₃ (n + 1) - 1 ∧
      (wythoffMexB 3 n : ℤ) = ⌊((n + 2 : ℕ) : ℝ) * Real.goldenRatio ^ 2⌋ + g₃ (n + 1) + 1

/-- **Golden-ratio formula for Wythoff's game with terminal positions up to total 4.** Let
$\varphi$ be the golden ratio. Let $a_n$ be the least natural number greater than $4$ that
differs from $a_i$ and $b_i$ for all $i < n$, and let $b_n = a_n + n + 5$. Then there is a
Fibonacci-automatic sequence $g_4 : \mathbb{N} \to \mathbb{N}$ with $g_4(n) \le 2$ for all $n$
such that, for every $n \ge 0$, $a_n = \lfloor (n + 2)\varphi \rfloor + g_4(n + 1)$ and
$b_n = \lfloor (n + 2)\varphi^2 \rfloor + g_4(n + 1) + 3$.

Here $(a_n, b_n)$ are the mex pairs of $K^4$, Wythoff's game in which every position $(x, y)$
with $x + y \le 4$ is terminal; by Theorem 17 of the source they are its non-terminal
P-positions with $a_n < b_n$. The source defines $g_4$ through an infinite word generated by a
morphism $\mu_4$ from the letter $1$, which is not well defined as printed ($\mu_4(1) = 2$ does
not start with $1$); $g_4$ is therefore existentially quantified.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Theorem 14 (`jis-2026-26.1.6-thm-14`). -/
public theorem_wanted exists_fibonacciAutomatic_wythoffTerminal_four :
    ∃ g₄ : ℕ → ℕ, IsFibonacciAutomatic g₄ ∧ (∀ n, g₄ n ≤ 2) ∧ ∀ n,
      (wythoffMexA 4 n : ℤ) = ⌊((n + 2 : ℕ) : ℝ) * Real.goldenRatio⌋ + g₄ (n + 1) ∧
      (wythoffMexB 4 n : ℤ) = ⌊((n + 2 : ℕ) : ℝ) * Real.goldenRatio ^ 2⌋ + g₄ (n + 1) + 3

/-- **Morphic coding of the Wythoff mex pairs at level one.** Let $a_n$ be the least natural
number $m > 1$ that differs from $a_i$ and $b_i$ for every $i < n$, and let $b_n = a_n + n + 2$,
so that $(a_0, b_0) = (2, 4)$. Let $f_1$ be the morphism on the alphabet $\{0, 1, 2, 3, 4\}$
given by $0 \mapsto 0\,1$, $1 \mapsto 2$, $2 \mapsto 3\,4$, $3 \mapsto 3\,1$, $4 \mapsto 2$ and
extended to finite words by concatenation, and let $g_1$ send the letters $0, 1, 3$ to $a$ and
the letters $2, 4$ to $b$. Then there is an infinite word $w = w(0)\,w(1)\,w(2) \cdots$ over this
alphabet that is the limit of the iterates $f_1^k(0)$ (each $f_1^k(0)$ is a prefix of $w$, and
their lengths are unbounded), and for every such $w$ and every $n \ge 0$, $g_1(w(a_n - 2)) = a$
and $g_1(w(b_n - 2)) = b$.

By Theorem 17 of the source, the pairs $(a_n, b_n)$ and $(b_n, a_n)$ are the non-terminal
P-positions of $K^1$, Wythoff's game in which no move is allowed from a position $(x, y)$ with
$x + y \le 1$; indexing the letters of $w$ from $2$, the letter at $a_n$ is coded $a$ and the
letter at $b_n$ is coded $b$.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Proposition 22 (`jis-2026-26.1.6-prop-22`). -/
public theorem_wanted wythoffTerminal_one_morphic (n : ℕ) :
    let f₁ : Fin 5 → List (Fin 5) := ![[0, 1], [2], [3, 4], [3, 1], [2]]
    let g₁ : Fin 5 → Bool := fun c => decide (c ∈ ({0, 1, 3} : Finset (Fin 5)))
    (∃ w : ℕ → Fin 5, IsOmegaLimit f₁ 0 w) ∧
      ∀ w : ℕ → Fin 5, IsOmegaLimit f₁ 0 w →
        g₁ (w (wythoffMexA 1 n - 2)) = true ∧ g₁ (w (wythoffMexB 1 n - 2)) = false

/-- **Morphic coding of the Wythoff mex pairs at level two.** Let $a_n$ be the least integer
$m > 2$ that differs from $a_i$ and $b_i$ for every $i < n$, and let $b_n = a_n + n + 3$, so that
$(a_0, b_0) = (3, 6)$. Let $f_2$ be the morphism on the alphabet $\{0, 1, \dots, 15\}$ given by
$0 \mapsto 0\,1$, $1 \mapsto 2$, $2 \mapsto 3\,4$, $3 \mapsto 5\,6$, $4 \mapsto 7$,
$5 \mapsto 8\,9$, $6 \mapsto 10$, $7 \mapsto 11\,12$, $8 \mapsto 10\,13$, $9 \mapsto 14$,
$10 \mapsto 10\,13$, $11 \mapsto 5\,6$, $12 \mapsto 15$, $13 \mapsto 5$, $14 \mapsto 8\,9$,
$15 \mapsto 11\,12$ and extended to finite words by concatenation, and let $g_2$ send the
letters $3, 5, 7, 10$ to $b$ and every other letter to $a$. Then there is an infinite word
$w = w(0)\,w(1)\,w(2) \cdots$ over this alphabet that is the limit of the iterates $f_2^k(0)$
(each $f_2^k(0)$ is a prefix of $w$, and their lengths are unbounded), and for every such $w$
and every $n \ge 0$, $g_2(w(a_n - 3)) = a$ and $g_2(w(b_n - 3)) = b$.

By Theorem 17 of the source, the pairs $(a_n, b_n)$ and $(b_n, a_n)$ are the non-terminal
P-positions of $K^2$, Wythoff's game in which no move is allowed from a position $(x, y)$ with
$x + y \le 2$; indexing the letters of $w$ from $3$, the letter at $a_n$ is coded $a$ and the
letter at $b_n$ is coded $b$.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Proposition 23 (`jis-2026-26.1.6-prop-23`). -/
public theorem_wanted wythoffTerminal_two_morphic (n : ℕ) :
    let f₂ : Fin 16 → List (Fin 16) := ![[0, 1], [2], [3, 4], [5, 6], [7], [8, 9], [10],
      [11, 12], [10, 13], [14], [10, 13], [5, 6], [15], [5], [8, 9], [11, 12]]
    let g₂ : Fin 16 → Bool := fun c => decide (c ∉ ({3, 5, 7, 10} : Finset (Fin 16)))
    (∃ w : ℕ → Fin 16, IsOmegaLimit f₂ 0 w) ∧
      ∀ w : ℕ → Fin 16, IsOmegaLimit f₂ 0 w →
        g₂ (w (wythoffMexA 2 n - 3)) = true ∧ g₂ (w (wythoffMexB 2 n - 3)) = false

/-- **Morphic coding of the Wythoff mex pairs at level three.** Let $a_n$ be the least integer
$m > 3$ that differs from $a_i$ and $b_i$ for every $i < n$, and let $b_n = a_n + n + 4$, so that
$(a_0, b_0) = (4, 8)$. Let $f_3$ be the morphism on the alphabet $\{0, 1, \dots, 21\}$ given by
$0 \mapsto 0\,1$, $1 \mapsto 2$, $2 \mapsto 3\,4$, $3 \mapsto 5\,6$, $4 \mapsto 7$,
$5 \mapsto 8\,9$, $6 \mapsto 10$, $7 \mapsto 11\,12$, $8 \mapsto 13\,12$, $9 \mapsto 14$,
$10 \mapsto 15\,16$, $11 \mapsto 14\,17$, $12 \mapsto 18$, $13 \mapsto 14\,17$,
$14 \mapsto 19\,12$, $15 \mapsto 18\,20$, $16 \mapsto 21$, $17 \mapsto 18$, $18 \mapsto 13\,12$,
$19 \mapsto 19\,12$, $20 \mapsto 14$, $21 \mapsto 15\,16$ and extended to finite words by
concatenation, and let $g_3$ send the letters $4, 6, 8, 10, 13, 15, 17, 19, 20$ to $b$ and every
other letter to $a$. Then there is an infinite word $w = w(0)\,w(1)\,w(2) \cdots$ over this
alphabet that is the limit of the iterates $f_3^k(0)$ (each $f_3^k(0)$ is a prefix of $w$, and
their lengths are unbounded), and for every such $w$ and every $n \ge 0$,
$g_3(w(a_n - 4)) = a$ and $g_3(w(b_n - 4)) = b$.

By Theorem 17 of the source, the pairs $(a_n, b_n)$ and $(b_n, a_n)$ are the non-terminal
P-positions of $K^3$, Wythoff's game in which no move is allowed from a position $(x, y)$ with
$x + y \le 3$; indexing the letters of $w$ from $4$, the letter at $a_n$ is coded $a$ and the
letter at $b_n$ is coded $b$.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Proposition 24 (`jis-2026-26.1.6-prop-24`). -/
public theorem_wanted wythoffTerminal_three_morphic (n : ℕ) :
    let f₃ : Fin 22 → List (Fin 22) := ![[0, 1], [2], [3, 4], [5, 6], [7], [8, 9], [10],
      [11, 12], [13, 12], [14], [15, 16], [14, 17], [18], [14, 17], [19, 12], [18, 20], [21],
      [18], [13, 12], [19, 12], [14], [15, 16]]
    let g₃ : Fin 22 → Bool := fun c =>
      decide (c ∉ ({4, 6, 8, 10, 13, 15, 17, 19, 20} : Finset (Fin 22)))
    (∃ w : ℕ → Fin 22, IsOmegaLimit f₃ 0 w) ∧
      ∀ w : ℕ → Fin 22, IsOmegaLimit f₃ 0 w →
        g₃ (w (wythoffMexA 3 n - 4)) = true ∧ g₃ (w (wythoffMexB 3 n - 4)) = false

/-- **Larsson's P-positions of Blocking Wythoff Nim with one blocked option.** Let $\varphi$ be
the golden ratio, and let $R_2$ consist of $(0, 0)$ and, for every $n \ge 0$, the positions
$(n, 2n + 1)$, $(2n + 1, n)$, $(2\lfloor n\varphi \rfloor + 2, 2\lfloor n\varphi^2 \rfloor + 2)$
and $(2\lfloor n\varphi^2 \rfloor + 2, 2\lfloor n\varphi \rfloor + 2)$. A Wythoff move from a
position of two piles removes a positive number of tokens from one pile, or the same positive
number from both. Then every position in $R_2$ has at most one Wythoff move to a position in
$R_2$, and every position outside $R_2$ has at least two Wythoff moves to positions in $R_2$.

Hence $R_2$ is the set of P-positions of $W^2$, Wythoff's game in which the previous player may
forbid one option.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Theorem 26 (`jis-2026-26.1.6-thm-26`). -/
public theorem_wanted blockingWythoff_two_pPositions :
    (∀ x ∈ larssonSetTwo, {y | wythoffTerminalMove 0 x y ∧ y ∈ larssonSetTwo}.ncard ≤ 1) ∧
      ∀ x ∉ larssonSetTwo, 2 ≤ {y | wythoffTerminalMove 0 x y ∧ y ∈ larssonSetTwo}.ncard

/-- **Larsson's P-positions of Blocking Wythoff Nim with two blocked options.** Let $R_3$
consist of $(0, 0)$ and, for every $n \ge 0$, the positions $(n, 2n + 1)$, $(2n + 1, n)$,
$(n, 2n + 2)$ and $(2n + 2, n)$. A Wythoff move from a position of two piles removes a positive
number of tokens from one pile, or the same positive number from both. Then every position in
$R_3$ has at most two Wythoff moves to positions in $R_3$, and every position outside $R_3$ has
at least three Wythoff moves to positions in $R_3$.

Hence $R_3$ is the set of P-positions of $W^3$, Wythoff's game in which the previous player may
forbid two options.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Theorem 28 (`jis-2026-26.1.6-thm-28`). -/
public theorem_wanted blockingWythoff_three_pPositions :
    (∀ x ∈ larssonSetThree,
        {y | wythoffTerminalMove 0 x y ∧ y ∈ larssonSetThree}.ncard ≤ 2) ∧
      ∀ x ∉ larssonSetThree, 3 ≤ {y | wythoffTerminalMove 0 x y ∧ y ∈ larssonSetThree}.ncard

/-- **No redundant move in $K^\ell$ for $1 \le \ell \le 4$.** Let $1 \le \ell \le 4$. Let $a_n$ be
the least natural number $m > \ell$ with $m \ne a_i$ and $m \ne b_i$ for all $i < n$, where
$b_i = a_i + i + \ell + 1$, and let $P$ be the set of positions $(x, y)$ with $x + y \le \ell$
together with the pairs $(a_n, b_n)$ and $(b_n, a_n)$ for $n \ge 0$. Let $v$ be one of the move
vectors $(i, 0)$, $(0, i)$ or $(i, i)$ with $i > 0$. Then there is a position $p \notin P$ such
that every move of $K^\ell$ from $p$ to a position $q \in P$ satisfies $p = q + v$.

In other words, once the moves by $v$ are removed from $K^\ell$, the set $P$ is no longer
absorbing. Since $P$ is the set of P-positions of $K^\ell$ (Theorem 17) and stays stable when
moves are removed, removing the moves by $v$ changes the set of P-positions.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Theorem 30 (`jis-2026-26.1.6-thm-30`). -/
public theorem_wanted wythoffTerminal_no_redundant_move (ℓ : ℕ) (hℓ₁ : 1 ≤ ℓ) (hℓ₄ : ℓ ≤ 4)
    (v : ℕ × ℕ) (hv : ∃ i, 0 < i ∧ (v = (i, 0) ∨ v = (0, i) ∨ v = (i, i))) :
    ∃ x, x ∉ wythoffTerminalPSet ℓ ∧ ∀ y ∈ wythoffTerminalPSet ℓ,
      wythoffTerminalMove ℓ x y → y.1 + v.1 = x.1 ∧ y.2 + v.2 = x.2

/-- **Blocking Wythoff Nim with one or two blocked options has no redundant move.** Let
$\varphi$ be the golden ratio. Let $R_2$ consist of $(0, 0)$ and, for every $n \ge 0$, the
positions $(n, 2n + 1)$, $(2n + 1, n)$,
$(2\lfloor n\varphi \rfloor + 2, 2\lfloor n\varphi^2 \rfloor + 2)$ and
$(2\lfloor n\varphi^2 \rfloor + 2, 2\lfloor n\varphi \rfloor + 2)$, and let $R_3$ consist of
$(0, 0)$ and, for every $n \ge 0$, the positions $(n, 2n + 1)$, $(2n + 1, n)$, $(n, 2n + 2)$ and
$(2n + 2, n)$. A Wythoff move from a position $x$ of two piles to a position $y$ removes a
positive number of tokens from one pile, or the same positive number from both. Let $v$ be
$(i, 0)$, $(0, i)$ or $(i, i)$ for an integer $i > 0$. Then some position $x \notin R_2$ has
fewer than two Wythoff moves to positions $y \in R_2$ with $y + v \ne x$, and some position
$x \notin R_3$ has fewer than three Wythoff moves to positions $y \in R_3$ with $y + v \ne x$.

So once the moves by $v$ are removed, $R_2$ and $R_3$ are no longer the sets of P-positions of
$W^2$ and $W^3$, Wythoff's game in which the previous player may forbid one, respectively two,
options.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Theorem 31 (`jis-2026-26.1.6-thm-31`). -/
public theorem_wanted blockingWythoff_no_redundant_move (v : ℕ × ℕ)
    (hv : ∃ i, 0 < i ∧ (v = (i, 0) ∨ v = (0, i) ∨ v = (i, i))) :
    (∃ x ∉ larssonSetTwo, {y | wythoffTerminalMove 0 x y ∧ y ∈ larssonSetTwo ∧
        ¬(y.1 + v.1 = x.1 ∧ y.2 + v.2 = x.2)}.ncard < 2) ∧
      ∃ x ∉ larssonSetThree, {y | wythoffTerminalMove 0 x y ∧ y ∈ larssonSetThree ∧
        ¬(y.1 + v.1 = x.1 ∧ y.2 + v.2 = x.2)}.ncard < 3

end

end MetaMathlibExt
