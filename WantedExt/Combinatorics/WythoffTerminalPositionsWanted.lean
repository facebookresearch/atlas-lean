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

/-- The move relation of `K^ℓ`: from a non-terminal position `p` (`ℓ < p.1 + p.2`) one may
move to `q` by removing a positive number of tokens from one pile, or the same positive
number from both piles.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6, the game
`K^ℓ` of Theorem 17 (`jis-2026-26.1.6-thm-17`): Wythoff's moves with terminal positions
`{(x, y) | x + y ≤ ℓ}`. -/
def wythoffTerminalMove (ℓ : ℕ) (p q : ℕ × ℕ) : Prop :=
  ℓ < p.1 + p.2 ∧
    ((q.2 = p.2 ∧ q.1 < p.1) ∨ (q.1 = p.1 ∧ q.2 < p.2) ∨
      (∃ k, 0 < k ∧ q.1 + k = p.1 ∧ q.2 + k = p.2))

/-- No move leaves a terminal position of `K^ℓ`.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, terminal positions of `K^ℓ` (Theorem 17). -/
theorem not_wythoffTerminalMove_of_terminal {ℓ : ℕ} {p : ℕ × ℕ} (hp : p.1 + p.2 ≤ ℓ)
    (q : ℕ × ℕ) : ¬wythoffTerminalMove ℓ p q := fun h => by
  have := h.1
  omega

/-- From `(1, 0)` one may move to `(0, 0)` in `K^0`.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Wythoff's moves (Theorem 17). -/
theorem wythoffTerminalMove_zero_one_zero : wythoffTerminalMove 0 (1, 0) (0, 0) :=
  ⟨by decide, Or.inl ⟨rfl, by decide⟩⟩

/-- The mex sequence `a_n` of `K^ℓ`:
`a_n = mex({a_i, b_i | i < n} ∪ {0, 1, …, ℓ})` with `b_i = a_i + i + ℓ + 1`, so
`(a₀, b₀) = (ℓ + 1, 2ℓ + 2)`.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Theorem 17, equation (mexdef) (`jis-2026-26.1.6-thm-17`). -/
noncomputable def wythoffMexA (ℓ : ℕ) (n : ℕ) : ℕ :=
  sInf {m : ℕ | ℓ < m ∧ ∀ i : Fin n,
    m ≠ wythoffMexA ℓ i ∧ m ≠ wythoffMexA ℓ i + i + ℓ + 1}
termination_by n
decreasing_by all_goals exact i.isLt

/-- The companion sequence `b_n = a_n + n + ℓ + 1` of `K^ℓ`.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Theorem 17, equation (mexdef). -/
noncomputable def wythoffMexB (ℓ n : ℕ) : ℕ := wythoffMexA ℓ n + n + ℓ + 1

/-- `a₀ = ℓ + 1`.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Theorem 17 (`(a₀, b₀) = (ℓ + 1, 2ℓ + 2)`). -/
theorem wythoffMexA_zero (ℓ : ℕ) : wythoffMexA ℓ 0 = ℓ + 1 := by
  rw [wythoffMexA]
  simp only [IsEmpty.forall_iff, and_true]
  apply le_antisymm
  · exact Nat.sInf_le (Nat.lt_succ_self ℓ)
  · exact Nat.sInf_mem (s := {m | ℓ < m}) ⟨ℓ + 1, Nat.lt_succ_self ℓ⟩

/-- `a₁ = ℓ + 2` for `ℓ ≥ 1` (the least integer above `ℓ` other than `a₀ = ℓ + 1` and
`b₀ = 2ℓ + 2`).

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

/-- `b₀ = 2ℓ + 2`.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Theorem 17 (`(a₀, b₀) = (ℓ + 1, 2ℓ + 2)`). -/
theorem wythoffMexB_zero (ℓ : ℕ) : wythoffMexB ℓ 0 = 2 * ℓ + 2 := by
  rw [wythoffMexB, wythoffMexA_zero]
  ring

/-- The P-position set of `K^ℓ` predicted by Theorem 17: the terminal positions together with
`(a_n, b_n)` and `(b_n, a_n)` for `n ≥ 0`.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Theorem 17. -/
def wythoffTerminalPSet (ℓ : ℕ) : Set (ℕ × ℕ) :=
  {p | p.1 + p.2 ≤ ℓ} ∪ {p | ∃ n, p = (wythoffMexA ℓ n, wythoffMexB ℓ n) ∨
    p = (wythoffMexB ℓ n, wythoffMexA ℓ n)}

/-- Terminal positions belong to `wythoffTerminalPSet ℓ`.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Theorem 17. -/
theorem mem_wythoffTerminalPSet_of_terminal {ℓ : ℕ} {p : ℕ × ℕ} (hp : p.1 + p.2 ≤ ℓ) :
    p ∈ wythoffTerminalPSet ℓ :=
  Or.inl hp

/-- The sequence `g` of Komak et al.: `g(0) = 1`, `g(1) = 0`, and `g(n) = 1 - g(m)` if
`⌊nφ⌋ = ⌊m(φ + 1)⌋ + 1` for some `m`, and `g(n) = 1` otherwise (`φ + 1 = φ²`; such an `m` is
unique and satisfies `m < n`, so the recursion is restricted to `m < n`).

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Definition `def:fg` (arXiv:2512.11601v1). -/
noncomputable def komakG (n : ℕ) : ℕ :=
  if h : ∃ m < n, ⌊(n : ℝ) * Real.goldenRatio⌋₊ = ⌊(m : ℝ) * Real.goldenRatio ^ 2⌋₊ + 1 then
    1 - komakG (Nat.find h)
  else 1
termination_by n
decreasing_by exact (Nat.find_spec h).1

/-- `g(0) = 1`.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Definition `def:fg`. -/
theorem komakG_zero : komakG 0 = 1 := by
  rw [komakG]
  split_ifs with h
  · obtain ⟨m, hm, -⟩ := h
    omega
  · rfl

/-- `g(1) = 0`, since `⌊φ⌋ = 1 = ⌊0 · φ²⌋ + 1`.

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

/-- Greedy digits of `n` for the Fibonacci numeration `F_i = fib (i + 2)` (`F_0 = 1`,
`F_1 = 2`) at the positions `k - 1, …, 0`, most significant first.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Definition `def:fib_rep` (greedy representation). -/
def fibGreedyDigits : ℕ → ℕ → List Bool
  | 0, _ => []
  | k + 1, n =>
      if Nat.fib (k + 2) ≤ n then true :: fibGreedyDigits k (n - Nat.fib (k + 2))
      else false :: fibGreedyDigits k n

/-- The number of digits of `rep_F(n)`: the least `k ≥ k₀` with `n < F_k = fib (k + 2)`,
searched upward from `k₀` with at most `fuel` steps, so the work is proportional to the
representation length. Called with `k₀ = 0` and `fuel = n + 1` (enough, as `n < fib (n + 2)`).

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Definition `def:fib_rep` (greedy representation). -/
def fibDigitCount (n : ℕ) : ℕ → ℕ → ℕ
  | 0, k => k
  | fuel + 1, k => if n < Nat.fib (k + 2) then k else fibDigitCount n fuel (k + 1)

/-- The greedy Fibonacci representation `rep_F(n)` (most significant digit first, no leading
zero, `rep_F(0)` empty), for `F_0 = 1`, `F_1 = 2`, `F_{i+2} = F_{i+1} + F_i`.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Definition `def:fib_rep`. -/
def fibRep (n : ℕ) : List Bool :=
  (fibGreedyDigits (fibDigitCount n (n + 1) 0) n).dropWhile (· = false)

/-- `rep_F(0) = ε`, `rep_F(2) = 10`, `rep_F(4) = 101`, `rep_F(7) = 1010`,
`rep_F(12) = 10101` (Table `tab:K1`).

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Definition `def:fib_rep` and Table `tab:K1`. -/
theorem fibRep_examples :
    fibRep 0 = [] ∧ fibRep 2 = [true, false] ∧ fibRep 4 = [true, false, true] ∧
      fibRep 7 = [true, false, true, false] ∧
      fibRep 12 = [true, false, true, false, true] := by
  decide

/-- A sequence `u : ℕ → ℕ` is Fibonacci-automatic if some deterministic finite automaton with
output reads `rep_F(n)` (most significant digit first) and outputs `u n`.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Section 2 (Fibonacci-automatic sequences, DFAO fed with `rep_F(n)`). -/
def IsFibonacciAutomatic (u : ℕ → ℕ) : Prop :=
  ∃ (Q : Type) (_ : Finite Q) (δ : Q → Bool → Q) (q₀ : Q) (τ : Q → ℕ),
    ∀ n, u n = τ ((fibRep n).foldl δ q₀)

/-- Constant sequences are Fibonacci-automatic.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Section 2 (Fibonacci-automatic sequences). -/
theorem isFibonacciAutomatic_const (c : ℕ) : IsFibonacciAutomatic fun _ => c :=
  ⟨Unit, inferInstance, fun _ _ => (), (), fun _ => c, fun _ => rfl⟩

/-- The prefix `f₁⁴(0)` of `f₁^ω(0)` for `f₁ : 0 ↦ 01, 1 ↦ 2, 2 ↦ 34, 3 ↦ 31, 4 ↦ 2` starts
`0, 1, 2, 3, 4, 3` (the table after Proposition 22), via the existing `morphIterate`.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, table after Proposition 22. -/
theorem morphIterate_wythoffTerminal_one_example :
    (morphIterate (![[0, 1], [2], [3, 4], [3, 1], [2]] : Fin 5 → List (Fin 5)) 4 [0]).take 6 =
      [0, 1, 2, 3, 4, 3] := by
  decide

/-- Larsson's set `R₂ = {(0,0)} ∪ {{n, 2n+1}} ∪ {{2⌊nφ⌋ + 2, 2⌊nφ²⌋ + 2}}` (unordered pairs,
`n ≥ 0`).

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Theorem 26. -/
def larssonSetTwo : Set (ℕ × ℕ) :=
  {(0, 0)} ∪ {p | ∃ n : ℕ, p = (n, 2 * n + 1) ∨ p = (2 * n + 1, n)} ∪
    {p | ∃ n : ℕ,
      p = (2 * ⌊(n : ℝ) * Real.goldenRatio⌋₊ + 2, 2 * ⌊(n : ℝ) * Real.goldenRatio ^ 2⌋₊ + 2) ∨
      p = (2 * ⌊(n : ℝ) * Real.goldenRatio ^ 2⌋₊ + 2, 2 * ⌊(n : ℝ) * Real.goldenRatio⌋₊ + 2)}

/-- `(0, 0)`, `(0, 1)` and `(2, 2)` lie in `R₂`.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Theorem 26. -/
theorem larssonSetTwo_examples :
    (0, 0) ∈ larssonSetTwo ∧ (0, 1) ∈ larssonSetTwo ∧ (2, 2) ∈ larssonSetTwo :=
  ⟨Or.inl (Or.inl rfl), Or.inl (Or.inr ⟨0, Or.inl rfl⟩), Or.inr ⟨0, Or.inl (by simp)⟩⟩

/-- Larsson's set `R₃ = {(0,0)} ∪ {{n, 2n+1}, {n, 2n+2}}` (unordered pairs, `n ≥ 0`).

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Theorem 28. -/
def larssonSetThree : Set (ℕ × ℕ) :=
  {(0, 0)} ∪ {p | ∃ n : ℕ, p = (n, 2 * n + 1) ∨ p = (2 * n + 1, n) ∨
    p = (n, 2 * n + 2) ∨ p = (2 * n + 2, n)}

/-- `(0, 0)`, `(0, 2)` and `(3, 1)` lie in `R₃`.

Source: Antoine Renard and Michel Rigo, Journal of Integer Sequences 29 (2026),
Article 26.1.6, Theorem 28. -/
theorem larssonSetThree_examples :
    (0, 0) ∈ larssonSetThree ∧ (0, 2) ∈ larssonSetThree ∧ (3, 1) ∈ larssonSetThree :=
  ⟨Or.inl rfl, Or.inr ⟨0, Or.inr (Or.inr (Or.inl rfl))⟩, Or.inr ⟨1, Or.inr (Or.inl rfl)⟩⟩

/-- Theorem 17: for `ℓ ≥ 1`, the non-terminal P-positions of `K^ℓ` are exactly the `(a_n, b_n)`
and `(b_n, a_n)` of the mex recursion; stated as: terminal positions plus these pairs form a
stable (no move inside) and absorbing (a move into it from outside) set of the move relation, which determines the P-positions
(`MetaMathlibExt.pPositions_unique`).

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Theorem 17 (`jis-2026-26.1.6-thm-17`). -/
public theorem_wanted wythoffTerminal_pPositions (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    (∀ x y, x ∈ wythoffTerminalPSet ℓ → wythoffTerminalMove ℓ x y →
        y ∉ wythoffTerminalPSet ℓ) ∧
      ∀ x, x ∉ wythoffTerminalPSet ℓ →
        ∃ y, wythoffTerminalMove ℓ x y ∧ y ∈ wythoffTerminalPSet ℓ

/-- Proposition 15: the case `ℓ = 1` of Theorem 17, with `(a₀, b₀) = (2, 4)` and
`b_n = a_n + n + 2`.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Proposition 15 (`jis-2026-26.1.6-prop-15`). -/
public theorem_wanted wythoffTerminal_one_pPositions :
    (∀ x y, x ∈ wythoffTerminalPSet 1 → wythoffTerminalMove 1 x y →
        y ∉ wythoffTerminalPSet 1) ∧
      ∀ x, x ∉ wythoffTerminalPSet 1 →
        ∃ y, wythoffTerminalMove 1 x y ∧ y ∈ wythoffTerminalPSet 1

/-- Proposition 16: the case `ℓ = 2` of Theorem 17, with `(a₀, b₀) = (3, 6)` and
`b_n = a_n + n + 3`.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Proposition 16 (`jis-2026-26.1.6-prop-16`). -/
public theorem_wanted wythoffTerminal_two_pPositions :
    (∀ x y, x ∈ wythoffTerminalPSet 2 → wythoffTerminalMove 2 x y →
        y ∉ wythoffTerminalPSet 2) ∧
      ∀ x, x ∉ wythoffTerminalPSet 2 →
        ∃ y, wythoffTerminalMove 2 x y ∧ y ∈ wythoffTerminalPSet 2

/-- Lemma 18: for `ℓ ≥ 1`, (1) `(a_n)` and `(b_n)` are strictly increasing; (2) they partition
`ℕ_{>ℓ}`; (3) every `j > ℓ` is `b_n - a_n` for a unique `n`; (4) `a_{n+1} - a_n ∈ {1, 2}`,
`b_{n+1} - b_n ∈ {2, 3}` and `b_{n+1} - b_n = a_{n+1} - a_n + 1`.

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

/-- Corollary 19: for `ℓ ≥ 1` there is a bounded `λ_ℓ : ℕ → ℤ` with
`a_n = ⌊(n + ℓ)φ⌋ + λ_ℓ(n)` and `b_n = ⌊(n + ℓ)φ²⌋ + λ_ℓ(n) + 1` for all `n`.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Corollary 19 (`jis-2026-26.1.6-cor-19`). -/
public theorem_wanted wythoffMex_floor_goldenRatio (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    ∃ lam : ℕ → ℤ, (∃ C : ℤ, ∀ n, |lam n| ≤ C) ∧ ∀ n,
      (wythoffMexA ℓ n : ℤ) = ⌊((n + ℓ : ℕ) : ℝ) * Real.goldenRatio⌋ + lam n ∧
      (wythoffMexB ℓ n : ℤ) = ⌊((n + ℓ : ℕ) : ℝ) * Real.goldenRatio ^ 2⌋ + lam n + 1

/-- Corollary 20: for `ℓ ≥ 1`, `a_n / n → φ` and `b_n / n → φ²`.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Corollary 20 (`jis-2026-26.1.6-cor-20`). -/
public theorem_wanted wythoffMex_tendsto_goldenRatio (ℓ : ℕ) (hℓ : 1 ≤ ℓ) :
    Filter.Tendsto (fun n : ℕ => (wythoffMexA ℓ n : ℝ) / n) Filter.atTop
        (nhds Real.goldenRatio) ∧
      Filter.Tendsto (fun n : ℕ => (wythoffMexB ℓ n : ℝ) / n) Filter.atTop
        (nhds (Real.goldenRatio ^ 2))


/-- Theorem 2 (Komak et al.): the P-positions of `K²` are the terminal positions together
with `(⌊nφ⌋ + g(n) - 1, ⌊nφ²⌋ + g(n))` and `(⌊nφ²⌋ + g(n), ⌊nφ⌋ + g(n) - 1)`, `n ≥ 0`;
stated as stability and absorption (`MetaMathlibExt.pPositions_unique`). The printed set
omits the terminal positions `(0, 0)` and `(1, 1)`, which are P-positions (no move leaves
them); they are added here.

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

/-- Proposition 4: with `h` Hofstadter's `G`-sequence (A005206, `hofstadterF 2`), `g(0) = 1`,
`g(1) = 0`, and for `n ≥ 2`, `g(n) = 1 - g(h(n - 1))` if `h(n - 2) < h(n - 1)` and
`g(n) = 1` otherwise. The printed value `g(1) = 1` is false for the `g` of Definition
`def:fg` (`⌊φ⌋ = 1 = ⌊0 · φ²⌋ + 1` gives `g(1) = 1 - g(0) = 0`, as in Table `tab:gh`) and
is replaced by `g(1) = 0`.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Proposition 4 (`jis-2026-26.1.6-prop-4`). -/
public theorem_wanted komakG_hofstadter :
    komakG 0 = 1 ∧ komakG 1 = 0 ∧ ∀ n, 2 ≤ n →
      komakG n = if hofstadterF 2 (n - 2) < hofstadterF 2 (n - 1) then
        1 - komakG (hofstadterF 2 (n - 1)) else 1

/-- Proposition 6 (first part): the sequence `g` is Fibonacci-automatic. The explicit DFA of
Figure `fig:automG` is given only as an image and is not stated.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Proposition 6 (`jis-2026-26.1.6-prop-6`). -/
public theorem_wanted isFibonacciAutomatic_komakG : IsFibonacciAutomatic komakG

/-- Theorem 12: the P-positions of `K¹` are the terminal positions together with the pairs
`(a, b)` and `(b, a)` with `a ≤ b`, `rep_F(a)` ending in `0` and `rep_F(b) = rep_F(a)1`;
stated as stability and absorption. As printed (for all `a ≤ b`) the statement fails at the
terminal P-positions `(0, 0)` and `(0, 1)`, since `rep_F(0)` is empty; the characterization
is stated for non-terminal positions.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Theorem 12 (`jis-2026-26.1.6-thm-12`). -/
public theorem_wanted wythoffTerminal_one_fibRep :
    let S : Set (ℕ × ℕ) := {p | p.1 + p.2 ≤ 1} ∪ {p |
      (p.1 ≤ p.2 ∧ (fibRep p.1).getLast? = some false ∧ fibRep p.2 = fibRep p.1 ++ [true]) ∨
      (p.2 ≤ p.1 ∧ (fibRep p.2).getLast? = some false ∧ fibRep p.1 = fibRep p.2 ++ [true])}
    (∀ x y, x ∈ S → wythoffTerminalMove 1 x y → y ∉ S) ∧
      ∀ x, x ∉ S → ∃ y, wythoffTerminalMove 1 x y ∧ y ∈ S

/-- Theorem 13: there is a Fibonacci-automatic `g₃ : ℕ → {0, 1, 2}` with
`a_n = ⌊(n + 2)φ⌋ + g₃(n + 1) - 1` and `b_n = ⌊(n + 2)φ²⌋ + g₃(n + 1) + 1` for the `n`-th
non-terminal P-position `(a_n, b_n)`, `a_n < b_n`, of `K³`; `(a_n, b_n)` is the mex pair
`(wythoffMexA 3 n, wythoffMexB 3 n)`, which Theorem 17 (`wythoffTerminal_pPositions`)
identifies with the `n`-th non-terminal P-position.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Theorem 13 (`jis-2026-26.1.6-thm-13`). -/
public theorem_wanted exists_fibonacciAutomatic_wythoffTerminal_three :
    ∃ g₃ : ℕ → ℕ, IsFibonacciAutomatic g₃ ∧ (∀ n, g₃ n ≤ 2) ∧ ∀ n,
      (wythoffMexA 3 n : ℤ) = ⌊((n + 2 : ℕ) : ℝ) * Real.goldenRatio⌋ + g₃ (n + 1) - 1 ∧
      (wythoffMexB 3 n : ℤ) = ⌊((n + 2 : ℕ) : ℝ) * Real.goldenRatio ^ 2⌋ + g₃ (n + 1) + 1

/-- Theorem 14: the non-terminal P-positions `(a_n, b_n)`, `a_n < b_n`, of `K⁴` satisfy
`a_n = ⌊(n + 2)φ⌋ + g₄(n + 1)` and `b_n = ⌊(n + 2)φ²⌋ + g₄(n + 1) + 3` (equation `eq:K4`)
for a Fibonacci-automatic `g₄ : ℕ → {0, 1, 2}`. The paper's `g₄` is the `n`-th letter of
`ρ₄(μ₄^ω(1))`, which is not well defined as printed (`μ₄(1) = 2` does not start with `1`);
`g₄` is therefore existentially quantified. `(a_n, b_n)` is the mex pair of Theorem 17.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Theorem 14 (`jis-2026-26.1.6-thm-14`). -/
public theorem_wanted exists_fibonacciAutomatic_wythoffTerminal_four :
    ∃ g₄ : ℕ → ℕ, IsFibonacciAutomatic g₄ ∧ (∀ n, g₄ n ≤ 2) ∧ ∀ n,
      (wythoffMexA 4 n : ℤ) = ⌊((n + 2 : ℕ) : ℝ) * Real.goldenRatio⌋ + g₄ (n + 1) ∧
      (wythoffMexB 4 n : ℤ) = ⌊((n + 2 : ℕ) : ℝ) * Real.goldenRatio ^ 2⌋ + g₄ (n + 1) + 3

/-- Proposition 22: the non-terminal P-positions `(a_n, b_n)` of `K¹` are coded by
`g₁(f₁^ω(0))` with letters indexed from `2`: the letter at index `a_n` has `g₁`-image `a`
(`true`) and the letter at index `b_n` has image `b` (`false`), where
`f₁ : 0 ↦ 01, 1 ↦ 2, 2 ↦ 34, 3 ↦ 31, 4 ↦ 2` and `g₁ : 0, 1, 3 ↦ a; 2, 4 ↦ b`.
`(a_n, b_n)` is the mex pair of Theorem 17. The infinite word is an `IsOmegaLimit` of the
iterates `morphIterate f n [0]`; its existence is part of the statement.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Proposition 22 (`jis-2026-26.1.6-prop-22`). -/
public theorem_wanted wythoffTerminal_one_morphic (n : ℕ) :
    let f₁ : Fin 5 → List (Fin 5) := ![[0, 1], [2], [3, 4], [3, 1], [2]]
    let g₁ : Fin 5 → Bool := fun c => decide (c ∈ ({0, 1, 3} : Finset (Fin 5)))
    (∃ w : ℕ → Fin 5, IsOmegaLimit f₁ 0 w) ∧
      ∀ w : ℕ → Fin 5, IsOmegaLimit f₁ 0 w →
        g₁ (w (wythoffMexA 1 n - 2)) = true ∧ g₁ (w (wythoffMexB 1 n - 2)) = false

/-- Proposition 23: the non-terminal P-positions `(a_n, b_n)` of `K²` are coded by
`g₂(f₂^ω(0))` with letters indexed from `3` (`a`, encoded `true`, at `a_n`; `b`, encoded
`false`, at `b_n`), for the 16-letter morphism `f₂` and coding `g₂` of the statement.
`(a_n, b_n)` is the mex pair of Theorem 17. The infinite word is an `IsOmegaLimit` of the
iterates `morphIterate f n [0]`; its existence is part of the statement.

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

/-- Proposition 24: the non-terminal P-positions `(a_n, b_n)` of `K³` are coded by
`g₃(f₃^ω(0))` with letters indexed from `4` (`a`, encoded `true`, at `a_n`; `b`, encoded
`false`, at `b_n`), for the 22-letter morphism `f₃` and coding `g₃` of the statement.
`(a_n, b_n)` is the mex pair of Theorem 17. The infinite word is an `IsOmegaLimit` of the
iterates `morphIterate f n [0]`; its existence is part of the statement.

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

/-- Theorem 26 (Larsson): the P-positions of `W²` (Wythoff's game in which the previous player
may forbid one option) are `R₂`: every position of `R₂` has at most one Wythoff option in
`R₂`, and every position outside `R₂` has at least two.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Theorem 26 (`jis-2026-26.1.6-thm-26`). -/
public theorem_wanted blockingWythoff_two_pPositions :
    (∀ x ∈ larssonSetTwo, {y | wythoffTerminalMove 0 x y ∧ y ∈ larssonSetTwo}.ncard ≤ 1) ∧
      ∀ x ∉ larssonSetTwo, 2 ≤ {y | wythoffTerminalMove 0 x y ∧ y ∈ larssonSetTwo}.ncard

/-- Theorem 28 (Larsson): the P-positions of `W³` (the previous player may forbid two options)
are `R₃`: every position of `R₃` has at most two Wythoff options in `R₃`, and every position
outside `R₃` has at least three.

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Theorem 28 (`jis-2026-26.1.6-thm-28`). -/
public theorem_wanted blockingWythoff_three_pPositions :
    (∀ x ∈ larssonSetThree,
        {y | wythoffTerminalMove 0 x y ∧ y ∈ larssonSetThree}.ncard ≤ 2) ∧
      ∀ x ∉ larssonSetThree, 3 ≤ {y | wythoffTerminalMove 0 x y ∧ y ∈ larssonSetThree}.ncard

/-- Theorem 30: for `ℓ ∈ {1, 2, 3, 4}`, `K^ℓ` has no redundant move: for every move vector
`v ∈ {(i, 0), (0, i), (i, i) | i > 0}`, the P-positions of `K^ℓ` (terminal positions and the
mex pairs, Theorem 17) are not absorbing once moves by `v` are removed, so removing `v`
changes the set of P-positions (stability is inherited, `MetaMathlibExt.pPositions_unique`).

Source: Antoine Renard and Michel Rigo, *Variants of Wythoff Game With Terminal Positions
or Blocking Maneuvers*, Journal of Integer Sequences 29 (2026), Article 26.1.6,
Theorem 30 (`jis-2026-26.1.6-thm-30`). -/
public theorem_wanted wythoffTerminal_no_redundant_move (ℓ : ℕ) (hℓ₁ : 1 ≤ ℓ) (hℓ₄ : ℓ ≤ 4)
    (v : ℕ × ℕ) (hv : ∃ i, 0 < i ∧ (v = (i, 0) ∨ v = (0, i) ∨ v = (i, i))) :
    ∃ x, x ∉ wythoffTerminalPSet ℓ ∧ ∀ y ∈ wythoffTerminalPSet ℓ,
      wythoffTerminalMove ℓ x y → y.1 + v.1 = x.1 ∧ y.2 + v.2 = x.2

/-- Theorem 31: `W²` and `W³` have no redundant move: for every move vector
`v ∈ {(i, 0), (0, i), (i, i) | i > 0}` some position outside `R_k` keeps fewer than `k` options
in `R_k` once moves by `v` are removed (`k = 2, 3`), so `R_k` stops being the P-position set.

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
