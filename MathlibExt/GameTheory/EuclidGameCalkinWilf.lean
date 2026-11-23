/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.GameTheory.SpragueGrundy

/-!
# Euclid on the Calkin–Wilf tree

Each arch top has a unique move to a child of the original position. From that child,
subtracting once returns to the original position.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Fuel-bounded Euclid classifier.** The fuel-bounded evaluation of the P-positions of Euclid is
the function $E(f, a, b)$ of natural numbers $f, a, b$ with Boolean values defined by recursion on
the fuel $f$. With no fuel, $E(0, a, b)$ is true. Otherwise $E(f + 1, a, b)$ is true when $a = b$,
$a = 0$ or $b = 0$; when $0 < a < b$ it is true iff $E(f, a, b - ja)$ is false for every $j \ge 1$
with $ja < b$; and when $0 < b < a$ it is true iff $E(f, a - jb, b)$ is false for every $j \ge 1$
with $jb < a$.

In Euclid a move replaces the larger entry by its difference with a positive multiple of the
smaller one, keeping both entries positive, and the player facing two equal entries (no move)
loses. With fuel at least $a + b$ the value is exact.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Section 4. -/
public def euclidPPositionAux : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => true
  | fuel + 1, a, b =>
    if a = b ∨ a = 0 ∨ b = 0 then true
    else if a < b then
      (List.range ((b - 1) / a)).all fun k => !euclidPPositionAux fuel a (b - (k + 1) * a)
    else
      (List.range ((a - 1) / b)).all fun k => !euclidPPositionAux fuel (a - (k + 1) * b) b

/-- **Euclid P-position test.** For natural numbers $a$ and $b$, the Euclid P-position test at
$(a, b)$ is the value at $(a, b)$ of the fuel-bounded evaluation of the P-positions of Euclid with
fuel $a + b$.

It is true exactly at the P-positions of Euclid, the positions from which every move leads to a
position that is not a P-position: each move lowers $a + b$, so fuel $a + b$ suffices.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Section 4. -/
public def euclidPPosition (a b : ℕ) : Bool :=
  euclidPPositionAux (a + b) a b

/-- **Euclid moves.** The moves of Euclid from a pair $(a, b)$ of natural numbers are as follows.
If $a = b$, $a = 0$ or $b = 0$, there are none. If $0 < a < b$, the moves are to the pairs
$(a, b - ja)$ for every integer $j \ge 1$ with $ja < b$; if $0 < b < a$, the moves are to the
pairs $(a - jb, b)$ for every integer $j \ge 1$ with $jb < a$.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Section 4. -/
public def euclidMoves (p : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  if p.1 = p.2 ∨ p.1 = 0 ∨ p.2 = 0 then ∅
  else if p.1 < p.2 then
    (Finset.range ((p.2 - 1) / p.1)).image fun k => (p.1, p.2 - (k + 1) * p.1)
  else
    (Finset.range ((p.1 - 1) / p.2)).image fun k => (p.1 - (k + 1) * p.2, p.2)

/-- **Euclid moves lower the sum.** If $(a', b')$ is a Euclid move from $(a, b)$, then
$a' + b' < a + b$.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Section 4. -/
public theorem euclidMoves_rank_lt (p q : ℕ × ℕ) (h : q ∈ euclidMoves p) :
    q.1 + q.2 < p.1 + p.2 := by
  obtain ⟨a, b⟩ := p
  simp only [euclidMoves] at h
  split_ifs at h with h1 h2
  · simp at h
  · simp only [Finset.mem_image, Finset.mem_range] at h
    obtain ⟨k, hk, rfl⟩ := h
    have ha : 0 < a := by omega
    have h3 : (k + 1) * a ≤ b - 1 := (Nat.le_div_iff_mul_le ha).mp hk
    have h4 : 0 < (k + 1) * a := Nat.mul_pos (Nat.succ_pos k) ha
    dsimp only
    omega
  · simp only [Finset.mem_image, Finset.mem_range] at h
    obtain ⟨k, hk, rfl⟩ := h
    have hb : 0 < b := by omega
    have h3 : (k + 1) * b ≤ a - 1 := (Nat.le_div_iff_mul_le hb).mp hk
    have h4 : 0 < (k + 1) * b := Nat.mul_pos (Nat.succ_pos k) hb
    dsimp only
    omega

/-- **The game Euclid.** Euclid as an impartial game: its positions are the pairs $(a, b)$ of
natural numbers, its moves from $(a, b)$ are the Euclid moves, the rank of $(a, b)$ is $a + b$,
and its starting position is $(1, 1)$.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Section 4. -/
public def euclidGame : SpragueGrundy.ImpartialGame where
  Pos := ℕ × ℕ
  eqDec := inferInstance
  moves := euclidMoves
  rank := fun p => p.1 + p.2
  rank_lt := euclidMoves_rank_lt
  start := (1, 1)

/-- **Correctness of the fuel-bounded Euclid classifier.** For all natural numbers $f$, $a$ and $b$
with $a + b \le f$, the fuel-bounded evaluation of the P-positions of Euclid with fuel $f$ returns
true at $(a, b)$ if and only if $(a, b)$ is a normal-play P-position of the Euclid game.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Section 4. -/
public theorem euclidPPositionAux_eq_true_iff :
    ∀ fuel a b : ℕ, a + b ≤ fuel →
      (euclidPPositionAux fuel a b = true ↔ SpragueGrundy.IsP euclidGame (a, b))
  | 0, a, b, h => by
    obtain rfl : a = 0 := by omega
    obtain rfl : b = 0 := by omega
    simp only [euclidPPositionAux, true_iff]
    refine (SpragueGrundy.isP_iff _ _).2 fun q hq => ?_
    change q ∈ euclidMoves (0, 0) at hq
    simp only [euclidMoves, true_or, ite_true] at hq
    exact (Finset.notMem_empty _ hq).elim
  | fuel + 1, a, b, h => by
    refine Iff.trans ?_ (SpragueGrundy.isP_iff _ _).symm
    change _ ↔ ∀ q (_ : q ∈ euclidMoves (a, b)), ¬SpragueGrundy.IsP euclidGame q
    simp only [euclidPPositionAux, euclidMoves]
    split_ifs with h1 h2
    · simp
    · rw [List.all_eq_true]
      simp only [List.mem_range, Finset.mem_image, Finset.mem_range, forall_exists_index,
        and_imp, forall_apply_eq_imp_iff₂, Bool.not_eq_true']
      refine forall_congr' fun k => imp_congr_right fun hk => ?_
      have ha : 0 < a := by omega
      have h3 : (k + 1) * a ≤ b - 1 := (Nat.le_div_iff_mul_le ha).mp hk
      have h4 : 0 < (k + 1) * a := Nat.mul_pos (Nat.succ_pos k) ha
      rw [← euclidPPositionAux_eq_true_iff fuel a (b - (k + 1) * a) (by omega)]
      simp
    · rw [List.all_eq_true]
      simp only [List.mem_range, Finset.mem_image, Finset.mem_range, forall_exists_index,
        and_imp, forall_apply_eq_imp_iff₂, Bool.not_eq_true']
      refine forall_congr' fun k => imp_congr_right fun hk => ?_
      have hb : 0 < b := by omega
      have h3 : (k + 1) * b ≤ a - 1 := (Nat.le_div_iff_mul_le hb).mp hk
      have h4 : 0 < (k + 1) * b := Nat.mul_pos (Nat.succ_pos k) hb
      rw [← euclidPPositionAux_eq_true_iff fuel (a - (k + 1) * b) b (by omega)]
      simp

/-- **The Euclid P-position test is correct.** For all natural numbers $a$ and $b$, the Euclid
P-position test returns true at $(a, b)$ if and only if $(a, b)$ is a normal-play P-position of
the Euclid game.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Section 4. -/
public theorem euclidPPosition_eq_true_iff (a b : ℕ) :
    euclidPPosition a b = true ↔ SpragueGrundy.IsP euclidGame (a, b) :=
  euclidPPositionAux_eq_true_iff (a + b) a b le_rfl

/-- **Small P-positions of Euclid.** The Euclid P-position test returns true at the pairs $(1, 1)$
and $(3, 2)$ and false at the pairs $(2, 1)$ and $(1, 2)$.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Section 4. -/
public theorem euclidPPosition_small :
    euclidPPosition 1 1 = true ∧ euclidPPosition 2 1 = false ∧
      euclidPPosition 1 2 = false ∧ euclidPPosition 3 2 = true := by
  decide

/-- **Rows of the Calkin–Wilf tree.** Row $k$ of the Calkin–Wilf tree is a list of
numerator–denominator pairs, the pair $(a, b)$ standing for $a/b$. Row $0$ is the single pair
$(1, 1)$, and row $k + 1$ is obtained from row $k$ by replacing each pair $(a, b)$, in order, by
its two children $(a, a + b)$ and $(a + b, b)$.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Section 2. -/
public def calkinWilfRow : ℕ → List (ℕ × ℕ)
  | 0 => [(1, 1)]
  | k + 1 => (calkinWilfRow k).flatMap fun p => [(p.1, p.1 + p.2), (p.1 + p.2, p.2)]

/-- **The first rows of the Calkin–Wilf tree.** As lists of numerator–denominator pairs, row $1$
of the Calkin–Wilf tree is $(1, 2), (2, 1)$ and row $2$ is $(1, 3), (3, 2), (2, 3), (3, 1)$, in
this order.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Section 2. -/
public theorem calkinWilfRow_one_two :
    calkinWilfRow 1 = [(1, 2), (2, 1)] ∧
      calkinWilfRow 2 = [(1, 3), (3, 2), (2, 3), (3, 1)] := by
  decide

namespace euclidPPosition_tops_of_arch

/-- A forced move to a position with a reply to a P-position starts at a P-position. -/
private theorem isP_of_forced_move {p q r : ℕ × ℕ} (hp : SpragueGrundy.IsP euclidGame p)
    (forced : euclidMoves r = {q}) (reply : p ∈ euclidMoves q) :
    SpragueGrundy.IsP euclidGame r := by
  apply (SpragueGrundy.isP_iff _ _).2
  change ∀ x : ℕ × ℕ, x ∈ euclidMoves r → ¬SpragueGrundy.IsP euclidGame x
  intro x hx
  rw [forced, Finset.mem_singleton] at hx
  subst x
  exact fun hq => (SpragueGrundy.isP_iff _ _).1 hq p reply hp

end euclidPPosition_tops_of_arch

/-- **Distinguishing the tops of arches.** Call a pair $(a, b)$ of natural numbers a P-position
when the Euclid P-position test returns true at $(a, b)$, and read it as the vertex $a/b$ of the
Calkin–Wilf tree, with son $a/(a+b)$ and daughter $(a+b)/b$. Let $m, n$ be positive integers. If
$m/n$ is a P-position, then so are its son's daughter $(2m+n)/(m+n)$ and its daughter's son
$(m+n)/(m+2n)$.

The statement covers all positive pairs; the tree vertices are the coprime ones.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 4.1. -/
public theorem euclidPPosition_tops_of_arch (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (h : euclidPPosition m n = true) :
    euclidPPosition (2 * m + n) (m + n) = true ∧ euclidPPosition (m + n) (m + 2 * n) = true := by
  have hp := (euclidPPosition_eq_true_iff m n).1 h
  have legal (a b : ℕ) (ha : 0 < a) (hab : a < b) : 0 < (b - 1) / a :=
    (Nat.one_le_div_iff ha).2 (by omega)
  rw [euclidPPosition_eq_true_iff, euclidPPosition_eq_true_iff]
  constructor
  · apply euclidPPosition_tops_of_arch.isP_of_forced_move (q := (m, m + n)) hp
    · have hdiv : (2 * m + n - 1) / (m + n) = 1 :=
        Nat.div_eq_of_lt_le (by omega) (by omega)
      rw [euclidMoves, ite_eq_right (by dsimp; omega), ite_eq_right (by dsimp; omega)]
      simp [hdiv, Finset.range_one]
      omega
    · rw [euclidMoves, ite_eq_right (by dsimp; omega), ite_eq_left (by dsimp; omega)]
      simp only [Finset.mem_image, Finset.mem_range]
      exact ⟨0, legal m (m + n) hm (by omega), by simp⟩
  · apply euclidPPosition_tops_of_arch.isP_of_forced_move (q := (m + n, n)) hp
    · have hdiv : (m + 2 * n - 1) / (m + n) = 1 :=
        Nat.div_eq_of_lt_le (by omega) (by omega)
      rw [euclidMoves, ite_eq_right (by dsimp; omega), ite_eq_left (by dsimp; omega)]
      simp [hdiv, Finset.range_one]
      omega
    · rw [euclidMoves, ite_eq_right (by dsimp; omega), ite_eq_right (by dsimp; omega)]
      simp only [Finset.mem_image, Finset.mem_range]
      exact ⟨0, legal n (m + n) hn (by omega), by simp⟩

end

end MetaMathlibExt
