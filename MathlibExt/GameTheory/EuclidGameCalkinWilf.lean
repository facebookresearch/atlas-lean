/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
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

end

end MetaMathlibExt
