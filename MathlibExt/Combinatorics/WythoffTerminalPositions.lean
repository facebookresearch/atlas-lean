/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Real.GoldenRatio
public import MathlibExt.Combinatorics.InfiniteWord.PureMorphicWord
import Mathlib.Data.List.Chain

/-!
# Wythoff's game with terminal positions

The theorem `wythoffTerminal_one_fibRep` characterizes the P-positions at terminal level one
by their greedy Fibonacci representations.
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
decreasing_by exact i.isLt

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

namespace wythoffTerminal_one_fibRep

-- The offset counts the number of places by which the word is shifted to the left.
private def value (i : ℕ) : List Bool → ℕ
  | [] => 0
  | b :: w => (if b then Nat.fib (w.length + i + 2) else 0) + value i w

private abbrev Valid (w : List Bool) := w.IsChain (fun a b => a = false ∨ b = false)

private theorem value_lt (i : ℕ) : ∀ {w : List Bool}, Valid w →
    value i w < Nat.fib (w.length + i + 2)
  | [], _ => by simp [value]
  | false :: w, h => by
    simpa [value] using (value_lt i (List.isChain_cons.mp h).2).trans_le
      (Nat.fib_mono (show w.length + i + 2 ≤ (false :: w).length + i + 2 by simp))
  | [true], _ => by
    simpa [value, Nat.add_comm 1 i, Nat.add_assoc] using
      Nat.fib_lt_fib_succ (n := i + 2) (by omega)
  | true :: false :: w, h => by
    have hw := value_lt i (List.isChain_cons.mp (List.isChain_cons.mp h).2).2
    simpa [value, Nat.add_right_comm _ 1 i, Nat.add_assoc] using
      (show Nat.fib (w.length + i + 3) + value i w < Nat.fib (w.length + i + 4) by
        rw [Nat.fib_add_two (n := w.length + i + 2), Nat.add_comm]
        exact Nat.add_lt_add_right hw _)
  | true :: true :: _, h => by
    simpa using (List.isChain_cons_cons.mp h).1

private theorem digits_length (k n : ℕ) : (fibGreedyDigits k n).length = k := by
  induction k generalizing n with
  | zero => rfl
  | succ k ih => simp only [fibGreedyDigits]; split <;> simp [ih]

private theorem digits_spec (k n : ℕ) (hn : n < Nat.fib (k + 2)) :
    Valid (fibGreedyDigits k n) ∧ value 0 (fibGreedyDigits k n) = n := by
  induction k generalizing n with
  | zero =>
    simp at hn
    simp [fibGreedyDigits, Valid, value, hn]
  | succ k ih =>
    simp only [fibGreedyDigits]
    split_ifs with h
    · have hsum : Nat.fib (k + 1 + 2) = Nat.fib (k + 1) + Nat.fib (k + 2) := Nat.fib_add_two
      have hrem : n - Nat.fib (k + 2) < Nat.fib (k + 1) := by omega
      obtain ⟨hv, he⟩ := ih _ (hrem.trans_le Nat.fib_le_fib_succ)
      refine ⟨List.isChain_cons.mpr ⟨?_, hv⟩, by simp [value, digits_length, he, h]⟩
      cases k with
      | zero => simp [fibGreedyDigits]
      | succ k => simp [fibGreedyDigits, Nat.not_le.mpr hrem]
    · obtain ⟨hv, he⟩ := ih n (Nat.lt_of_not_ge h)
      exact ⟨List.isChain_cons.mpr ⟨by simp, hv⟩, by simpa [value] using he⟩

private theorem digits_value {w : List Bool} (hw : Valid w) :
    fibGreedyDigits w.length (value 0 w) = w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    have hv := (List.isChain_cons.mp hw).2
    have hb := value_lt 0 hv
    cases b <;> simp [fibGreedyDigits, value, Nat.not_le.mpr hb, ih hv]

private abbrev trim (w : List Bool) := w.dropWhile (· = false)

private theorem trim_value (i : ℕ) (w : List Bool) : value i (trim w) = value i w := by
  induction w with
  | nil => rfl
  | cons b w ih => cases b <;> simp [trim, value, ← ih]

private theorem trim_valid {w : List Bool} (hw : Valid w) : Valid (trim w) := by
  induction w with
  | nil => exact hw
  | cons b w ih =>
    cases b
    · exact ih (List.isChain_cons.mp hw).2
    · exact hw

private theorem count_bound (n fuel k : ℕ) (h : n < Nat.fib (k + fuel + 2)) :
    n < Nat.fib (fibDigitCount n fuel k + 2) := by
  induction fuel generalizing k with
  | zero => exact h
  | succ fuel ih =>
    simp only [fibDigitCount]
    split
    · assumption
    · exact ih _ (by rwa [show k + 1 + fuel + 2 = k + (fuel + 1) + 2 by omega])

private theorem rep_bound (n : ℕ) : n < Nat.fib (fibDigitCount n (n + 1) 0 + 2) :=
  count_bound _ _ _ (by
    rw [Nat.zero_add]
    change n < Nat.fib (n + 3)
    have := Nat.le_fib_add_one (n + 3)
    omega)

private theorem rep_value (n : ℕ) : value 0 (fibRep n) = n :=
  (trim_value _ _).trans (digits_spec _ _ (rep_bound n)).2

private theorem rep_valid (n : ℕ) : Valid (fibRep n) :=
  trim_valid (digits_spec _ _ (rep_bound n)).1

private theorem trim_digits_eq {n k l : ℕ} (hk : n < Nat.fib (k + 2)) (hkl : k ≤ l) :
    trim (fibGreedyDigits l n) = trim (fibGreedyDigits k n) := by
  induction l, hkl using Nat.le_induction with
  | base => rfl
  | succ l hkl ih =>
    have hl := hk.trans_le (Nat.fib_mono (Nat.add_le_add_right hkl 2))
    simpa [fibGreedyDigits, Nat.not_le.mpr hl, trim] using ih

private theorem rep_digits {n k : ℕ} (hk : n < Nat.fib (k + 2)) :
    fibRep n = trim (fibGreedyDigits k n) := by
  unfold fibRep
  rcases le_total k (fibDigitCount n (n + 1) 0) with h | h
  · exact trim_digits_eq hk h
  · exact (trim_digits_eq (rep_bound n) h).symm

private theorem rep_of_word {w : List Bool} (hw : Valid w) :
    fibRep (value 0 w) = trim w := by
  rw [rep_digits (by simpa using value_lt 0 hw), digits_value hw]

-- Shifting the place values preserves the order of equal-width valid words.
private theorem value_lt_shift {w v : List Bool} (hw : Valid w) (hv : Valid v)
    (hlen : w.length = v.length) (hlt : value 0 w < value 0 v) : value 1 w < value 1 v := by
  induction w generalizing v with
  | nil => cases v <;> simp_all
  | cons b w ih =>
    cases v with
    | nil => simp at hlen
    | cons c v =>
      have he : w.length = v.length := by simpa using hlen
      have hw' := (List.isChain_cons.mp hw).2
      have hv' := (List.isChain_cons.mp hv).2
      cases b <;> cases c
      · simpa [value] using ih hw' hv' he (by simpa [value] using hlt)
      · have h := value_lt 1 hw'
        simp only [value, Bool.false_eq_true, ite_false, zero_add, ite_true, he] at h ⊢
        omega
      · have h := value_lt 0 hv'
        simp [value, he] at hlt
        simp at h
        omega
      · simpa [value, he] using ih hw' hv' he (by simpa [value, he] using hlt)

-- For positive n with word w, the two coordinates have words w0 and w01.
private def lower (n : ℕ) := value 1 (fibRep n)
private def upper (n : ℕ) := lower n + n + 1

private theorem lower_strictMono : StrictMono lower := by
  intro n m hnm
  let k := fibDigitCount m (m + 1) 0
  have hm : m < Nat.fib (k + 2) := rep_bound m
  have hn := hnm.trans hm
  obtain ⟨hvn, hen⟩ := digits_spec _ _ hn
  obtain ⟨hvm, hem⟩ := digits_spec _ _ hm
  simp only [lower, rep_digits hn, rep_digits hm, trim_value]
  exact value_lt_shift hvn hvm (by rw [digits_length, digits_length]) (by rwa [hen, hem])

private theorem value_append (i : ℕ) (w v : List Bool) :
    value i (w ++ v) = value (v.length + i) w + value i v := by
  induction w with
  | nil => simp [value]
  | cons b w ih => simp [value, ih, Nat.add_assoc]

private theorem value_add_two (i : ℕ) (w : List Bool) :
    value (i + 2) w = value i w + value (i + 1) w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    cases b
    · simpa only [value, Bool.false_eq_true, ite_false, zero_add] using ih
    · simp only [value, ite_true, ih]
      have h : Nat.fib (w.length + (i + 2) + 2) =
          Nat.fib (w.length + i + 2) + Nat.fib (w.length + (i + 1) + 2) := by
        simpa [Nat.add_assoc] using Nat.fib_add_two (n := w.length + i + 2)
      omega

private theorem rep_injective : Function.Injective fibRep :=
  fun a b h => by simpa only [rep_value] using congrArg (value 0) h

private theorem rep_head (n : ℕ) (hn : 0 < n) : (fibRep n).head? = some true := by
  have ne : fibRep n ≠ [] := by
    intro h
    have := rep_value n
    rw [h] at this
    exact hn.ne' this.symm
  have hd := List.head_dropWhile_not (fun b : Bool => decide (b = false)) ne
  change decide ((fibRep n).head ne = false) = false at hd
  simpa [List.head?_eq_some_head ne] using hd

private theorem trim_of_head {w : List Bool} (h : w.head? = some true) : trim w = w := by
  cases w with
  | nil => simp at h
  | cons b w => cases b <;> simp_all [trim]

private theorem suffix_values (n : ℕ) :
    value 0 (fibRep n ++ [false]) = lower n ∧
      value 0 (fibRep n ++ [false, true]) = upper n := by
  constructor
  · simp [value_append, value, lower]
  · simp [value_append, value, upper, value_add_two 0, rep_value, lower, Nat.add_comm]

private theorem suffix_reps {n : ℕ} (hn : 0 < n) :
    fibRep (lower n) = fibRep n ++ [false] ∧ fibRep (upper n) = fibRep n ++ [false, true] := by
  have h := rep_valid n
  have head := rep_head n hn
  obtain ⟨hl, hu⟩ := suffix_values n
  constructor
  · rw [← hl, rep_of_word, trim_of_head]
    · simp [head]
    · exact h.append (by simp) (by simp)
  · rw [← hu, rep_of_word, trim_of_head]
    · simp [head]
    · exact h.append (by decide) (by simp)

private theorem disjoint_coords {i j : ℕ} (hi : 0 < i) (hj : 0 < j) : lower i ≠ upper j := by
  intro h
  have := congrArg (fun n => (fibRep n).getLast?) h
  simp [(suffix_reps hi).1, (suffix_reps hj).2] at this

-- Removing a suffix beginning with zero leaves a nonempty canonical prefix.
private theorem prefix_index {n : ℕ} (hn : 0 < n) {w v : List Bool}
    (h : fibRep n = w ++ false :: v) : ∃ i, 0 < i ∧ fibRep i = w := by
  have hh := rep_head n hn
  rw [h] at hh
  have head : w.head? = some true := by
    cases w with
    | nil => simp at hh
    | cons b w => exact hh
  have valid := rep_valid n
  rw [h] at valid
  have he := (rep_of_word valid.left_of_append).trans (trim_of_head head)
  refine ⟨_, Nat.pos_of_ne_zero ?_, he⟩
  intro hz
  rw [hz, show fibRep 0 = [] by decide] at he
  simp [← he] at head

-- Every canonical word of length at least two ends with 0 or 01.
private theorem coord_cover {n : ℕ} (hn : 2 ≤ n) : ∃ i, 0 < i ∧ (n = lower i ∨ n = upper i) := by
  have val := rep_value n
  obtain h | ⟨w, b, h⟩ := List.eq_nil_or_concat (fibRep n)
  · rw [h] at val
    change 0 = n at val
    omega
  rw [List.concat_eq_append] at h
  cases b
  · obtain ⟨i, hi, rfl⟩ := prefix_index (by omega) h
    exact ⟨i, hi, Or.inl (rep_injective (h.trans (suffix_reps hi).1.symm))⟩
  · obtain hw | ⟨v, c, hw⟩ := List.eq_nil_or_concat w
    · rw [h, hw] at val
      change 1 = n at val
      omega
    rw [List.concat_eq_append] at hw
    rw [hw, List.append_assoc] at h
    cases c
    · obtain ⟨i, hi, rfl⟩ := prefix_index (by omega) h
      exact ⟨i, hi, Or.inr (rep_injective (h.trans (suffix_reps hi).2.symm))⟩
    · have hv := rep_valid n
      rw [h] at hv
      simpa [List.isChain_pair] using hv.right_of_append

private theorem pair_iff (a b : ℕ) :
    (a ≤ b ∧ (fibRep a).getLast? = some false ∧ fibRep b = fibRep a ++ [true]) ↔
      ∃ i, 0 < i ∧ a = lower i ∧ b = upper i := by
  constructor
  · rintro ⟨_, ha, hb⟩
    have h : 2 ≤ a := by
      by_contra! hs
      interval_cases a <;> contradiction
    obtain ⟨i, hi, rfl | rfl⟩ := coord_cover h
    · refine ⟨i, hi, rfl, rep_injective ?_⟩
      simpa [(suffix_reps hi).1, (suffix_reps hi).2] using hb
    · simp [(suffix_reps hi).2] at ha
  · rintro ⟨i, hi, rfl, rfl⟩
    simp [(suffix_reps hi).1, (suffix_reps hi).2, show lower i ≤ upper i by unfold upper; omega]

private def positions (p : ℕ × ℕ) : Prop :=
  p.1 + p.2 ≤ 1 ∨ ∃ i, 0 < i ∧ (p = (lower i, upper i) ∨ p = (upper i, lower i))

private theorem positions_swap (x y : ℕ) : positions (x, y) ↔ positions (y, x) := by
  simp [positions, Nat.add_comm, Prod.ext_iff, and_comm, or_comm]

private theorem move_swap (x y u v : ℕ) :
    wythoffTerminalMove 1 (x, y) (u, v) ↔ wythoffTerminalMove 1 (y, x) (v, u) := by
  simp only [wythoffTerminalMove, Nat.add_comm x y, @and_comm (u + _ = x)]
  tauto

private theorem min_lower {i : ℕ} (hi : 0 < i) : 2 ≤ lower i :=
  calc
    2 = lower 1 := by decide
    _ ≤ lower i := lower_strictMono.monotone hi

private theorem upper_strictMono : StrictMono upper :=
  fun _ _ h => by
    have := lower_strictMono h
    unfold upper
    omega

-- A one-pile move preserves a coordinate, and a diagonal move preserves the difference.
private theorem stable_sorted {i x y : ℕ} (hi : 0 < i)
    (h : wythoffTerminalMove 1 (lower i, upper i) (x, y)) : ¬positions (x, y) := by
  obtain ⟨_, hm⟩ := h
  have ha := min_lower hi
  change (y = upper i ∧ x < lower i) ∨ (x = lower i ∧ y < upper i) ∨
    (∃ k, 0 < k ∧ x + k = lower i ∧ y + k = upper i) at hm
  rintro (ht | ⟨j, hj, hxy | hxy⟩)
  · change x + y ≤ 1 at ht
    unfold upper at hm
    rcases hm with h | h | ⟨k, hk, hx, hy⟩ <;> omega
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy
    rcases hm with ⟨he, hl⟩ | ⟨he, hl⟩ | ⟨k, hk, hx, hy⟩
    · exact hl.ne (congrArg lower (upper_strictMono.injective he))
    · exact hl.ne (congrArg upper (lower_strictMono.injective he))
    · unfold upper at hy
      have he : i = j := by omega
      subst j
      omega
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hxy
    rcases hm with ⟨he, _⟩ | ⟨he, _⟩ | ⟨k, hk, hx, hy⟩
    · exact disjoint_coords hj hi he
    · exact disjoint_coords hi hj he.symm
    · unfold upper at hx hy
      omega

private theorem stable (p q : ℕ × ℕ) (hp : positions p) (hm : wythoffTerminalMove 1 p q) :
    ¬positions q := by
  obtain ⟨x, y⟩ := q
  rcases hp with ht | ⟨i, hi, rfl | rfl⟩
  · exact (ht.not_gt hm.1).elim
  · exact stable_sorted hi hm
  · exact fun hq => stable_sorted hi ((move_swap ..).mp hm) ((positions_swap ..).mp hq)

private theorem absorbing_sorted {x y : ℕ} (hxy : x ≤ y) (hp : ¬positions (x, y)) :
    ∃ q, wythoffTerminalMove 1 (x, y) q ∧ positions q := by
  have htotal : 1 < x + y := lt_of_not_ge (fun h => hp (Or.inl h))
  by_cases hs : x ≤ 1
  · exact ⟨(x, 0), ⟨htotal, Or.inr (Or.inl ⟨rfl, by dsimp; omega⟩)⟩, Or.inl (by simpa)⟩
  by_cases hd : y ≤ x + 1
  · exact ⟨(0, y - x), ⟨htotal, Or.inr (Or.inr ⟨x, by omega, Nat.zero_add x, by dsimp; omega⟩)⟩,
      Or.inl (by dsimp; omega)⟩
  obtain ⟨i, hi, hx | hx⟩ := coord_cover (show 2 ≤ x by omega)
  · subst x
    have hne : y ≠ upper i := fun he => hp (Or.inr ⟨i, hi, Or.inl (by rw [he])⟩)
    rcases lt_or_gt_of_ne hne with h | h
    · -- The pair with the same difference has a smaller index.
      let j := y - lower i - 1
      have hj : 0 < j := by dsimp [j]; omega
      have hji : j < i := by dsimp [j]; unfold upper at h; omega
      have hl := lower_strictMono hji
      refine ⟨(lower j, upper j), ⟨htotal, Or.inr (Or.inr ?_)⟩, Or.inr ⟨j, hj, Or.inl rfl⟩⟩
      refine ⟨lower i - lower j, by omega, by dsimp; omega, ?_⟩
      change lower j + j + 1 + (lower i - lower j) = y
      have : j = y - lower i - 1 := rfl
      omega
    · exact ⟨(lower i, upper i), ⟨htotal, Or.inr (Or.inl ⟨rfl, h⟩)⟩, Or.inr ⟨i, hi, Or.inl rfl⟩⟩
  · subst x
    have hl : lower i < y := by unfold upper at hxy; omega
    exact ⟨(upper i, lower i), ⟨htotal, Or.inr (Or.inl ⟨rfl, hl⟩)⟩, Or.inr ⟨i, hi, Or.inr rfl⟩⟩

private theorem absorbing (p : ℕ × ℕ) (hp : ¬positions p) :
    ∃ q, wythoffTerminalMove 1 p q ∧ positions q := by
  obtain ⟨x, y⟩ := p
  rcases le_total x y with h | h
  · exact absorbing_sorted h hp
  · obtain ⟨⟨v, u⟩, hm, hq⟩ := absorbing_sorted h (fun hy => hp ((positions_swap ..).mp hy))
    exact ⟨(u, v), (move_swap ..).mp hm, (positions_swap ..).mp hq⟩

end wythoffTerminal_one_fibRep

open wythoffTerminal_one_fibRep

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
public theorem wythoffTerminal_one_fibRep :
    let S : Set (ℕ × ℕ) := {p | p.1 + p.2 ≤ 1} ∪ {p |
      (p.1 ≤ p.2 ∧ (fibRep p.1).getLast? = some false ∧ fibRep p.2 = fibRep p.1 ++ [true]) ∨
      (p.2 ≤ p.1 ∧ (fibRep p.2).getLast? = some false ∧ fibRep p.1 = fibRep p.2 ++ [true])}
    (∀ x y, x ∈ S → wythoffTerminalMove 1 x y → y ∉ S) ∧
      ∀ x, x ∉ S → ∃ y, wythoffTerminalMove 1 x y ∧ y ∈ S := by
  intro S
  have mem_iff (p : ℕ × ℕ) : p ∈ S ↔ positions p := by
    simp only [S, Set.mem_union, Set.mem_ofPred_eq, pair_iff, positions, Prod.ext_iff]
    aesop
  constructor
  · intro x y hx hm hy
    exact stable x y ((mem_iff x).mp hx) hm ((mem_iff y).mp hy)
  · intro x hx
    obtain ⟨y, hm, hy⟩ := absorbing x (fun h => hx ((mem_iff x).mpr h))
    exact ⟨y, hm, (mem_iff y).mpr hy⟩

end

end MetaMathlibExt
