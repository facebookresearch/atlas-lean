/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Data.Nat.Fib.Basic
public import MathlibExt.GameTheory.SpragueGrundy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Euclid on the Calkin–Wilf tree

Each arch top has a unique move to a child of the original position. From that child,
subtracting once returns to the original position. Counting the left arch tops row by row
gives `3 * Tₖ = 2 ^ (k - 2) + 2 * (-1) ^ k` for `2 ≤ k` (`count_arch_tops_calkinWilfRow`).
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

namespace euclidPPosition_aunt_xor_cousin

private theorem swap (a b : ℕ) : euclidPPosition a b = euclidPPosition b a := by
  suffices h : ∀ f a b, euclidPPositionAux f a b = euclidPPositionAux f b a by
    simpa only [euclidPPosition, Nat.add_comm b a] using h (a + b) a b
  intro f
  induction f with
  | zero => intros; rfl
  | succ f ih =>
    intro a b
    simp only [euclidPPositionAux]
    split_ifs <;> first | rfl | omega | (congr 1; funext k; rw [ih])

-- Subtracting the first copy of b leaves a; each further copy gives another option.
private theorem add_iff (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    euclidPPosition (a + b) b = true ↔
      ∀ k : ℕ, k * b < a → ¬euclidPPosition (a - k * b) b = true := by
  rw [euclidPPosition_eq_true_iff, SpragueGrundy.isP_iff euclidGame (a + b, b)]
  change (∀ q ∈ euclidMoves (a + b, b), ¬SpragueGrundy.IsP euclidGame q) ↔ _
  rw [euclidMoves, ite_eq_right (by dsimp; omega), ite_eq_right (by dsimp; omega)]
  simp only [Finset.mem_image, Finset.mem_range, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, euclidPPosition_eq_true_iff]
  refine forall_congr' fun k => ?_
  have bound : k < (a + b - 1) / b ↔ k * b < a := by
    change k + 1 ≤ (a + b - 1) / b ↔ _
    rw [Nat.le_div_iff_mul_le hb, Nat.add_one_mul]
    omega
  simp only [bound, Nat.add_one_mul, Nat.add_sub_add_right]

-- When a ≤ b, the only option of (a + b, b) is (a, b).
private theorem forced (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    euclidPPosition a b = true ↔ ¬euclidPPosition (a + b) b = true := by
  suffices h : euclidPPosition (a + b) b = true ↔ ¬euclidPPosition a b = true by
    simp only [h, not_not]
  rw [add_iff a b ha (by omega)]
  constructor
  · intro h
    simpa using h 0 (by simpa)
  · intro h k hk
    cases k with
    | zero => simpa using h
    | succ k => rw [Nat.succ_mul] at hk; omega

-- After two additions, the position can move to the intermediate position or any of its options.
private theorem twice (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    ¬euclidPPosition (a + b + b) b = true := by
  rw [add_iff (a + b) b (by omega) hb]
  intro h
  have hparent : ¬euclidPPosition (a + b) b = true := by
    simpa using h 0 (by simp; omega)
  apply hparent
  apply (add_iff a b ha hb).2
  intro k hk
  simpa only [Nat.succ_mul, Nat.add_sub_add_right] using
    h (k + 1) (by rw [Nat.succ_mul]; omega)

end euclidPPosition_aunt_xor_cousin

open euclidPPosition_aunt_xor_cousin in
/-- **Aunt or cousin of a P-position.** Call a pair $(a, b)$ of natural numbers a P-position when
the Euclid P-position test returns true at $(a, b)$, and let its son be $s(a, b) = (a, a + b)$ and
its daughter $d(a, b) = (a + b, b)$, as in the Calkin–Wilf tree. Let $x, y$ be positive integers,
let $r = (x, y)$, let $q$ be one of the two children $s(r)$ and $d(r)$ of $r$, and let $q'$ be the
other one. If the daughter $d(q)$ is a P-position, then exactly one of its aunt $q'$ and its male
cousin $s(q')$ is a P-position. If the son $s(q)$ is a P-position, then exactly one of its uncle
$q'$ and its female cousin $d(q')$ is a P-position.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 4.3. -/
public theorem euclidPPosition_aunt_xor_cousin (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    let s : ℕ × ℕ → ℕ × ℕ := fun p => (p.1, p.1 + p.2)
    let d : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + p.2, p.2)
    let P : ℕ × ℕ → Prop := fun p => euclidPPosition p.1 p.2 = true
    let r := (x, y)
    (P (d (s r)) → (P (d r) ↔ ¬P (s (d r)))) ∧ (P (d (d r)) → (P (s r) ↔ ¬P (s (s r)))) ∧
      (P (s (d r)) → (P (s r) ↔ ¬P (d (s r)))) ∧ (P (s (s r)) → (P (d r) ↔ ¬P (d (d r)))) := by
  dsimp only
  have left := forced x (x + y) hx (by omega)
  have right := forced y (x + y) hy (by omega)
  rw [swap y (x + y), Nat.add_comm y (x + y), swap (x + y + y) (x + y)] at right
  refine ⟨fun _ => right, fun h => (twice x y hx hy h).elim, fun _ => left, ?_⟩
  intro h
  rw [swap, Nat.add_comm x (x + y), Nat.add_comm x y] at h
  exact (twice y x hy hx h).elim

namespace euclidPPosition_branch_step

open euclidPPosition_aunt_xor_cousin

-- A positive pair with one entry at least twice the other has a winning move.
private theorem daughter_not_p_of_le (a b : ℕ) (hb : 0 < b) (h : b ≤ a) :
    ¬euclidPPosition (a + b) b = true := by
  rcases lt_or_eq_of_le h with hlt | rfl
  · simpa only [Nat.sub_add_cancel h] using twice (a - b) b (by omega) hb
  · apply (forced b b hb le_rfl).1
    unfold euclidPPosition
    cases b + b <;> simp [euclidPPositionAux]

private theorem niece (x y : ℕ) (hx : 0 < x) (hy : 0 < y)
    (hd : euclidPPosition (x + y) y = true) :
    euclidPPosition (x + (x + y)) (x + y) = true := by
  by_contra hn
  -- The niece can only move to the son, so the son and daughter would both be P-positions.
  have hs := (forced x (x + y) hx (by omega)).2 hn
  rcases le_total x y with h | h
  · rw [swap x (x + y), Nat.add_comm x y] at hs
    exact daughter_not_p_of_le y x hx h hs
  · exact daughter_not_p_of_le x y hy h hd

end euclidPPosition_branch_step

open euclidPPosition_branch_step euclidPPosition_aunt_xor_cousin in
/-- **Establishing branches: nieces and nephews of P-positions.** Call a pair $(a, b)$ of natural
numbers a P-position when the Euclid P-position test returns true at $(a, b)$, and read it as the
vertex $a/b$ of the Calkin–Wilf tree, with son $a/(a+b)$ and daughter $(a+b)/b$. Let $x, y$ be
positive integers. If the daughter $(x+y)/y$ of $x/y$ is a P-position, then so is its niece
$(2x+y)/(x+y)$, the daughter of its sibling $x/(x+y)$. If the son $x/(x+y)$ of $x/y$ is a
P-position, then so is its nephew $(x+y)/(x+2y)$, the son of its sibling $(x+y)/y$.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 4.2. -/
public theorem euclidPPosition_branch_step (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    (euclidPPosition (x + y) y = true → euclidPPosition (2 * x + y) (x + y) = true) ∧
      (euclidPPosition x (x + y) = true → euclidPPosition (x + y) (x + 2 * y) = true) := by
  constructor
  · simpa only [two_mul, Nat.add_assoc] using niece x y hx hy
  · rw [swap x (x + y), swap (x + y) (x + 2 * y)]
    simpa only [two_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using niece y x hy hx

namespace euclidPPosition_self_similar

open euclidPPosition_aunt_xor_cousin euclidPPosition_branch_step

private def child (p : ℕ × ℕ) (b : Bool) : ℕ × ℕ :=
  if b then (p.1 + p.2, p.2) else (p.1, p.1 + p.2)

private abbrev outcome (p : ℕ × ℕ) := euclidPPosition p.1 p.2

private theorem child_pos {p : ℕ × ℕ} (hp : 0 < p.1 ∧ 0 < p.2) (b : Bool) :
    0 < (child p b).1 ∧ 0 < (child p b).2 := by
  cases b <;> simp [child, hp.1, hp.2]

private theorem row_pos {k : ℕ} {p : ℕ × ℕ} (h : p ∈ calkinWilfRow k) :
    0 < p.1 ∧ 0 < p.2 := by
  induction k generalizing p with
  | zero =>
    simp only [calkinWilfRow, List.mem_singleton] at h
    subst p
    decide
  | succ k ih =>
    obtain ⟨q, hq, h⟩ := List.mem_flatMap.mp h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl
    · exact child_pos (ih hq) false
    · exact child_pos (ih hq) true

-- The daughter has a forced move to its parent when a ≤ b. Otherwise it is always N.
private theorem daughter_iff (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    euclidPPosition (a + b) b = true ↔ euclidPPosition a b = false ∧ a ≤ b := by
  by_cases hab : a ≤ b
  · have h := forced a b ha hab
    grind
  · simp [hab, daughter_not_p_of_le a b hb (by omega)]

private theorem child_iff {p : ℕ × ℕ} (hp : 0 < p.1 ∧ 0 < p.2) (b : Bool) :
    outcome (child p b) = true ↔ outcome p = false ∧
      (if b then p.1 ≤ p.2 else p.2 ≤ p.1) := by
  cases b with
  | false =>
    simp only [child, outcome, Bool.false_eq_true, ite_false]
    rw [swap, Nat.add_comm, daughter_iff _ _ hp.2 hp.1, swap p.2 p.1]
  | true => exact daughter_iff _ _ hp.1 hp.2

-- Repeating a direction gives N. Changing direction flips the intermediate outcome.
private theorem grandchild_iff {p : ℕ × ℕ} (hp : 0 < p.1 ∧ 0 < p.2) (b c : Bool) :
    outcome (child (child p b) c) = true ↔ outcome (child p b) = false ∧ b ≠ c := by
  rw [child_iff (child_pos hp b)]
  cases b <;> cases c <;> simp [child, hp.1.ne', hp.2.ne']

private theorem walk_congr (w : List Bool) {p q : ℕ × ℕ}
    (hp : 0 < p.1 ∧ 0 < p.2) (hq : 0 < q.1 ∧ 0 < q.2) (h : outcome p = outcome q)
    (hc : ∀ b, outcome (child p b) = outcome (child q b)) :
    outcome (w.foldl child p) = outcome (w.foldl child q) := by
  induction w generalizing p q with
  | nil => exact h
  | cons b w ih =>
    apply ih (child_pos hp b) (child_pos hq b) (hc b)
    intro c
    apply Bool.eq_iff_iff.mpr
    rw [grandchild_iff hp, grandchild_iff hq, hc b]

end euclidPPosition_self_similar

open euclidPPosition_self_similar in
/-- **Self-similarity of the P-positions of Euclid.** Call a pair $(a, b)$ of natural numbers a
P-position when the Euclid P-position test returns true at $(a, b)$, and read it as the vertex
$a/b$ of the Calkin–Wilf tree, with son $a/(a+b)$ and daughter $(a+b)/b$. Let $V$ be a vertex in
some row of the Calkin–Wilf tree that is a P-position. Then for every finite sequence $w$ of steps,
each step going to the son or to the daughter, the vertex reached from $V$ by following $w$ is a
P-position if and only if the vertex reached from the root $1/1$ by following $w$ is one.

In other words, below every P-position the P-positions sit exactly where they sit below the root.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Theorem 4.5. -/
public theorem euclidPPosition_self_similar (k : ℕ) (V : ℕ × ℕ)
    (hV : V ∈ calkinWilfRow k) (hP : euclidPPosition V.1 V.2 = true) (w : List Bool) :
    let walk : ℕ × ℕ → ℕ × ℕ := fun p =>
      w.foldl (fun q b => if b then (q.1 + q.2, q.2) else (q.1, q.1 + q.2)) p
    euclidPPosition (walk V).1 (walk V).2 = euclidPPosition (walk (1, 1)).1 (walk (1, 1)).2 := by
  have hp := row_pos hV
  have hr : 0 < (1 : ℕ) ∧ 0 < (1 : ℕ) := by decide
  apply walk_congr w hp hr (hP.trans euclidPPosition_small.1.symm)
  intro b
  apply Bool.eq_iff_iff.mpr
  simp [child_iff hp, child_iff (p := (1, 1)) hr, outcome, hP, euclidPPosition_small.1]

-- The formulas only need `b ≤ a` and `c ≤ d`; the statement keeps the hypotheses `hb` and `hc`.
set_option linter.unusedVariables false in
/-- **Levels of the branches of an arch.** On numerator–denominator pairs write
$s(x, y) = (x, x + y)$ for the son and $t(x, y) = (x + y, y)$ for the daughter of a vertex of the
Calkin–Wilf tree. Let $a, b, c, d, k$ be natural numbers with $0 < b < a$ and $0 < c < d$. Then
$t(s^k(a - b, b))$, the daughter of the $k$-fold son of $(a - b, b)$, has first entry
$(k+1)a - kb$ and second entry $ka - (k-1)b$, and $s(t^k(c, d - c))$, the son of the $k$-fold
daughter of $(c, d - c)$, has first entry $kd - (k-1)c$ and second entry $(k+1)d - kc$, the
right-hand sides computed in the integers.

When $a/b$ and $c/d$ are the left and right tops of an arch, these pairs are level $k$ (level $0$
the top) of its left branch, which descends by nieces, and of its right branch, which descends by
nephews; the formulas hold without the arch-top hypothesis.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Lemma 5.1. -/
public theorem arch_branch_levels (a b c d k : ℕ) (hb : 0 < b) (hab : b < a) (hc : 0 < c)
    (hcd : c < d) :
    let s : ℕ × ℕ → ℕ × ℕ := fun p => (p.1, p.1 + p.2)
    let t : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + p.2, p.2)
    let L := t (s^[k] (a - b, b))
    let R := s (t^[k] (c, d - c))
    ((L.1 : ℤ) = (k + 1) * a - k * b ∧ (L.2 : ℤ) = k * a - (k - 1) * b) ∧
      ((R.1 : ℤ) = k * d - (k - 1) * c ∧ (R.2 : ℤ) = (k + 1) * d - k * c) := by
  intro s t L R
  -- Iterating the son adds the first entry to the second, and the daughter the reverse.
  have hs (j x y : ℕ) : s^[j] (x, y) = (x, j * x + y) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      refine Prod.ext rfl ?_
      simp only [s]
      ring
  have ht (j x y : ℕ) : t^[j] (x, y) = (x + j * y, y) := by
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Function.iterate_succ_apply', ih]
      refine Prod.ext ?_ rfl
      simp only [t]
      ring
  simp only [L, R, hs, ht, s, t]
  push_cast [Nat.cast_sub hab.le, Nat.cast_sub hcd.le]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩ <;> ring

namespace fibonacci_arch_tops

-- Each successive Fibonacci pair is the son's daughter of the preceding pair.
private theorem fib_pair (i : ℕ) :
    euclidPPosition (Nat.fib (2 * i + 2)) (Nat.fib (2 * i + 1)) = true := by
  induction i with
  | zero => exact euclidPPosition_small.1
  | succ i ih =>
    have tops := (euclidPPosition_tops_of_arch _ _ (Nat.fib_pos.mpr (by omega))
      (Nat.fib_pos.mpr (by omega)) ih).1
    have h₃ : Nat.fib (2 * i + 3) = Nat.fib (2 * i + 1) + Nat.fib (2 * i + 2) :=
      Nat.fib_add_two (n := 2 * i + 1)
    have h₄ : Nat.fib (2 * i + 4) = Nat.fib (2 * i + 2) + Nat.fib (2 * i + 3) :=
      Nat.fib_add_two (n := 2 * i + 2)
    change euclidPPosition (Nat.fib (2 * i + 4)) (Nat.fib (2 * i + 3)) = true
    rw [h₄, h₃]
    convert tops using 2 <;> omega

open euclidPPosition_aunt_xor_cousin in
-- The only move subtracts the denominator and leaves (a, b + (k+1)a).
-- Subtracting (k+1)a from the second entry then returns to (a, b).
private theorem left_branch (a b k : ℕ) (ha : 0 < a) (hb : 0 < b)
    (hp : euclidPPosition a b = true) :
    euclidPPosition (a + (b + (k + 1) * a)) (b + (k + 1) * a) = true := by
  rw [Nat.add_one_mul, ← Nat.add_assoc b]
  have hle : a ≤ b + k * a + a := by omega
  by_contra hn
  have child := (forced a (b + k * a + a) ha hle).2 hn
  rw [swap, add_iff (b + k * a) a (by omega) ha] at child
  have reply := child k (by omega)
  rw [Nat.add_sub_cancel, swap] at reply
  exact reply hp

end fibonacci_arch_tops

open fibonacci_arch_tops in
/-- **Fibonacci arch tops.** Index the Fibonacci numbers as in the source, $F_0 = F_1 = 1$ and
$F_{j+2} = F_{j+1} + F_j$. Write $a/b$ for the position $(a, b)$ of Euclid, and call $a/(a+b)$
its son and $(a+b)/b$ its daughter. Let $n \ge 1$ and $k \ge 0$ be integers, and let
$X = (F_{2n+1} + kF_{2n-1})/(F_{2n+1} + (k-1)F_{2n-1})$ and
$Y = (F_{2n} + kF_{2n-2})/(F_{2n} + (k+1)F_{2n-2})$. Then $X$ is a P-position of Euclid, and so
are its son's daughter $(3F_{2n+1} + (3k-1)F_{2n-1})/(2F_{2n+1} + (2k-1)F_{2n-1})$ and its
daughter's son $(2F_{2n+1} + (2k-1)F_{2n-1})/(3F_{2n+1} + (3k-2)F_{2n-1})$. Likewise $Y$ is a
P-position of Euclid, and so are its son's daughter
$(3F_{2n} + (3k+1)F_{2n-2})/(2F_{2n} + (2k+1)F_{2n-2})$ and its daughter's son
$(2F_{2n} + (2k+1)F_{2n-2})/(3F_{2n} + (3k+2)F_{2n-2})$.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Corollary 5.3. -/
public theorem fibonacci_arch_tops (n k : ℕ) (hn : 1 ≤ n) :
    let F : ℕ → ℕ := fun j => Nat.fib (j + 1)
    let s : ℕ × ℕ → ℕ × ℕ := fun p => (p.1, p.1 + p.2)
    let t : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + p.2, p.2)
    let P : ℕ × ℕ → Prop := fun p => euclidPPosition p.1 p.2 = true
    let X := (F (2 * n + 1) + k * F (2 * n - 1),
      F (2 * n + 1) + k * F (2 * n - 1) - F (2 * n - 1))
    let Y := (F (2 * n) + k * F (2 * n - 2), F (2 * n) + (k + 1) * F (2 * n - 2))
    (P X ∧ P (t (s X)) ∧ P (s (t X)) ∧
      ((t (s X)).1 : ℤ) = 3 * F (2 * n + 1) + (3 * k - 1) * F (2 * n - 1) ∧
      ((t (s X)).2 : ℤ) = 2 * F (2 * n + 1) + (2 * k - 1) * F (2 * n - 1) ∧
      ((s (t X)).1 : ℤ) = 2 * F (2 * n + 1) + (2 * k - 1) * F (2 * n - 1) ∧
      ((s (t X)).2 : ℤ) = 3 * F (2 * n + 1) + (3 * k - 2) * F (2 * n - 1)) ∧
    (P Y ∧ P (t (s Y)) ∧ P (s (t Y)) ∧
      t (s Y) = (3 * F (2 * n) + (3 * k + 1) * F (2 * n - 2),
        2 * F (2 * n) + (2 * k + 1) * F (2 * n - 2)) ∧
      s (t Y) = (2 * F (2 * n) + (2 * k + 1) * F (2 * n - 2),
        3 * F (2 * n) + (3 * k + 2) * F (2 * n - 2))) := by
  obtain ⟨i, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  intro F s t P X Y
  let a := F (2 * (i + 1) - 1)
  let b := F (2 * (i + 1) - 2)
  have ha : a = Nat.fib (2 * i + 2) := congrArg Nat.fib (by omega)
  have hb : b = Nat.fib (2 * i + 1) := congrArg Nat.fib (by omega)
  have ha₀ : 0 < a := ha ▸ Nat.fib_pos.mpr (by omega)
  have hb₀ : 0 < b := hb ▸ Nat.fib_pos.mpr (by omega)
  have hp : euclidPPosition a b = true := ha ▸ hb ▸ fib_pair i
  have hsum : F (2 * (i + 1)) = a + b := by
    rw [ha, hb, Nat.add_comm (Nat.fib (2 * i + 2))]
    exact Nat.fib_add_two (n := 2 * i + 1)
  have htop : F (2 * (i + 1) + 1) = a + (a + b) := by
    rw [← hsum, ha]
    exact Nat.fib_add_two (n := 2 * i + 2)
  have hX : X = (a + (b + (k + 1) * a), b + (k + 1) * a) := by
    change (F _ + k * a, F _ + k * a - a) = _
    rw [htop, Nat.add_one_mul]
    congr 1 <;> omega
  have hY : Y = (a + (k + 1) * b, b + (a + (k + 1) * b)) := by
    change (F _ + k * b, F _ + (k + 1) * b) = _
    rw [hsum, Nat.add_one_mul]
    congr 1 <;> omega
  have pX : P X := by
    rw [hX]
    exact left_branch a b k ha₀ hb₀ hp
  have pY : P Y := by
    rw [hY]
    change euclidPPosition _ _ = true
    rw [euclidPPosition_aunt_xor_cousin.swap]
    apply left_branch b a k hb₀ ha₀
    rwa [euclidPPosition_aunt_xor_cousin.swap]
  have tops (p : ℕ × ℕ) (hm : 0 < p.1) (hn : 0 < p.2) (h : P p) :
      P (t (s p)) ∧ P (s (t p)) := by
    simpa only [P, s, t, two_mul, Nat.add_assoc] using
      euclidPPosition_tops_of_arch p.1 p.2 hm hn h
  obtain ⟨pXL, pXR⟩ := tops X (by rw [hX]; dsimp; omega) (by rw [hX]; dsimp; omega) pX
  obtain ⟨pYL, pYR⟩ := tops Y (by rw [hY]; dsimp; omega) (by rw [hY]; dsimp; omega) pY
  constructor
  · refine ⟨pX, pXL, pXR, ?_, ?_, ?_, ?_⟩ <;>
      rw [hX, htop] <;> dsimp only [t, s, a] <;> push_cast <;> ring
  · refine ⟨pY, pYL, pYR, ?_, ?_⟩ <;> ext <;> dsimp only [t, s, Y] <;> ring

namespace count_arch_tops_calkinWilfRow

open euclidPPosition_self_similar

private def children (p : ℕ × ℕ) : List (ℕ × ℕ) :=
  [(p.1, p.1 + p.2), (p.1 + p.2, p.2)]

private def grandchildren (p : ℕ × ℕ) : List (ℕ × ℕ) :=
  (children p).flatMap children

private theorem row_succ (k : ℕ) :
    calkinWilfRow (k + 1) = (calkinWilfRow k).flatMap children := rfl

private theorem row_two (k : ℕ) :
    calkinWilfRow (k + 2) = (calkinWilfRow k).flatMap grandchildren := by
  rw [row_succ, row_succ, List.flatMap_assoc]
  rfl

private theorem children_length (l : List (ℕ × ℕ)) :
    (l.flatMap children).length = 2 * l.length := by
  induction l with
  | nil => rfl
  | cons p l ih => simp [children, ih]; omega

private theorem row_length (k : ℕ) : (calkinWilfRow k).length = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [row_succ, children_length, ih, pow_succ]; omega

private theorem children_eq (p : ℕ × ℕ) : children p = [child p false, child p true] := by
  simp [children, child]

-- Repeating a direction gives N, and changing direction gives P exactly when the child is N
-- (`grandchild_iff`), so a vertex's children and grandchildren hold exactly two P-positions.
private theorem count_grandchildren {p : ℕ × ℕ} (hp : 0 < p.1 ∧ 0 < p.2) :
    (grandchildren p).countP outcome + (children p).countP outcome = 2 := by
  have g (b c : Bool) : outcome (child (child p b) c) = (!outcome (child p b) && b != c) := by
    apply Bool.eq_iff_iff.mpr
    rw [grandchild_iff hp]
    simp
  simp only [grandchildren, children_eq, List.flatMap_cons, List.flatMap_nil, List.cons_append,
    List.nil_append, List.countP_cons, List.countP_nil, g]
  cases outcome (child p false) <;> cases outcome (child p true) <;> rfl

private theorem count_two (l : List (ℕ × ℕ))
    (hl : ∀ p ∈ l, 0 < p.1 ∧ 0 < p.2) :
    (l.flatMap grandchildren).countP outcome + (l.flatMap children).countP outcome =
      2 * l.length := by
  induction l with
  | nil => rfl
  | cons p l ih =>
    have hp := count_grandchildren (hl p (by simp))
    have ht := ih (fun q hq => hl q (by simp [hq]))
    simp only [List.flatMap_cons, List.countP_append, List.length_cons]
    omega

private theorem row_count_step (k : ℕ) :
    (calkinWilfRow (k + 2)).countP outcome + (calkinWilfRow (k + 1)).countP outcome =
      2 * 2 ^ k := by
  rw [row_two, row_succ, ← row_length]
  exact count_two _ (fun _ h => row_pos h)

private theorem row_count_sum (k : ℕ) :
    (calkinWilfRow (k + 1)).countP outcome + (calkinWilfRow k).countP outcome = 2 ^ k := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h := row_count_step k
    change (calkinWilfRow (k + 2)).countP outcome +
      (calkinWilfRow (k + 1)).countP outcome = 2 ^ (k + 1)
    rw [pow_succ]
    omega

private theorem row_count_formula (k : ℕ) :
    3 * ((calkinWilfRow k).countP outcome : ℤ) = 2 ^ k + 2 * (-1) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have h := congrArg (fun n : ℕ => (n : ℤ)) (row_count_sum k)
    push_cast at h
    rw [pow_succ, pow_succ]
    linarith

private def archPredicate (l : List (ℕ × ℕ)) (p : ℕ × ℕ) : Bool :=
  l.any fun V => outcome V && p == (2 * V.1 + V.2, V.1 + V.2)

private theorem arch_iff (l : List (ℕ × ℕ)) (p : ℕ × ℕ) :
    archPredicate l p = true ↔
      ∃ V ∈ l, outcome V = true ∧ p = (2 * V.1 + V.2, V.1 + V.2) := by
  simp [archPredicate, List.any_eq_true]

private theorem arch_bounds (l : List (ℕ × ℕ))
    (hl : ∀ V ∈ l, 0 < V.1 ∧ 0 < V.2) (p : ℕ × ℕ)
    (hp : archPredicate l p = true) : p.2 < p.1 ∧ p.1 < 2 * p.2 := by
  obtain ⟨V, hV, _, rfl⟩ := (arch_iff l p).1 hp
  have hv := hl V hV
  dsimp
  omega

private theorem arch_grandchildren_count (l : List (ℕ × ℕ))
    (hl : ∀ V ∈ l, 0 < V.1 ∧ 0 < V.2) (p : ℕ × ℕ) (hp : p ∈ l) :
    (grandchildren p).countP (archPredicate l) = if outcome p then 1 else 0 := by
  obtain ⟨a, b⟩ := p
  have hab := hl (a, b) hp
  have excluded (q : ℕ × ℕ) (hq : q.1 ≤ q.2 ∨ 2 * q.2 ≤ q.1) :
      archPredicate l q = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hbound := arch_bounds l hl q h
    omega
  have hss := excluded (a, a + (a + b)) (by dsimp; omega)
  have hds := excluded (a + b, a + b + b) (by dsimp; omega)
  have hdd := excluded (a + b + b, b) (by dsimp; omega)
  have hsd : archPredicate l (a + (a + b), a + b) = outcome (a, b) := by
    apply Bool.eq_iff_iff.mpr
    rw [arch_iff]
    constructor
    · rintro ⟨V, _, hV, he⟩
      have h₁ := congrArg Prod.fst he
      have h₂ := congrArg Prod.snd he
      have hv : V = (a, b) := by
        apply Prod.ext <;> dsimp at h₁ h₂ ⊢ <;> omega
      simpa only [hv] using hV
    · intro h
      refine ⟨(a, b), hp, h, ?_⟩
      apply Prod.ext <;> dsimp; omega
  simp only [grandchildren, children, List.flatMap_cons, List.flatMap_nil,
    List.cons_append, List.nil_append, List.countP_cons, List.countP_nil]
  simp [hss, hds, hdd, hsd]

private theorem arch_flatMap_count (l r : List (ℕ × ℕ))
    (hl : ∀ V ∈ l, 0 < V.1 ∧ 0 < V.2) (hr : ∀ p ∈ r, p ∈ l) :
    (r.flatMap grandchildren).countP (archPredicate l) = r.countP outcome := by
  induction r with
  | nil => rfl
  | cons p r ih =>
    have hp := arch_grandchildren_count l hl p (hr p (by simp))
    have ht := ih (fun q hq => hr q (by simp [hq]))
    simp only [List.flatMap_cons, List.countP_append, List.countP_cons, hp, ht]
    omega

private theorem arch_count (k : ℕ) :
    (calkinWilfRow (k + 2)).countP (archPredicate (calkinWilfRow k)) =
      (calkinWilfRow k).countP outcome := by
  rw [row_two]
  exact arch_flatMap_count _ _ (fun _ h => row_pos h) (fun _ h => h)

end count_arch_tops_calkinWilfRow

open count_arch_tops_calkinWilfRow euclidPPosition_self_similar in
/-- **Number of arch tops in a row of the Calkin–Wilf tree.** For $k \ge 2$ let $T_k$ be the
number of vertices of row $k$ of the Calkin–Wilf tree of the form $(2m+n)/(m+n)$ with $m/n$ a
P-position of Euclid in row $k - 2$. Then $3T_k = 2^{k-2} + 2(-1)^k$, that is,
$T_k = 2^{k-2}/3 + 2(-1)^k/3$.

The vertex $(2m+n)/(m+n)$ is the son's daughter of $m/n$, the left top of the arch below $m/n$;
the daughter's son $(m+n)/(m+2n)$ is the right top, so $T_k$ counts the arches whose tops lie in
row $k$.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Corollary 4.7. -/
public theorem count_arch_tops_calkinWilfRow (k : ℕ) (hk : 2 ≤ k) :
    3 * (((calkinWilfRow k).countP fun p => (calkinWilfRow (k - 2)).any fun V =>
        euclidPPosition V.1 V.2 && p == (2 * V.1 + V.2, V.1 + V.2)) : ℤ) =
      2 ^ (k - 2) + 2 * (-1) ^ k
    := by
  have h : k = (k - 2) + 2 := by omega
  change 3 * ((calkinWilfRow k).countP (archPredicate (calkinWilfRow (k - 2))) : ℤ) = _
  have hc : (calkinWilfRow k).countP (archPredicate (calkinWilfRow (k - 2))) =
      (calkinWilfRow (k - 2)).countP outcome := by
    conv_lhs => arg 2; rw [h]
    exact arch_count (k - 2)
  have he : (-1 : ℤ) ^ k = (-1) ^ (k - 2) := by
    conv_lhs => rw [h, pow_add]
    norm_num
  rw [hc, row_count_formula, he]

end

end MetaMathlibExt
