/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.NumberTheory.Real.GoldenRatio
public import MathlibExt.GameTheory.SmithRemoteness

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

/-- **Number of P-positions of Euclid in a row of the Calkin–Wilf tree.** Let $L_k$ be the
number of P-positions of Euclid in row $k$ of the Calkin–Wilf tree. Then $L_0 = 1$, $L_1 = 0$,
$L_{k+2} = L_{k+1} + 2L_k$ for every $k$, and $3L_k = 2^k + 2(-1)^k$ for every $k$, that is,
$L_k = 2^k/3 + 2(-1)^k/3$.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Corollary 4.6. -/
public theorem_wanted count_euclidPPosition_calkinWilfRow :
    (calkinWilfRow 0).countP (fun p => euclidPPosition p.1 p.2) = 1 ∧
      (calkinWilfRow 1).countP (fun p => euclidPPosition p.1 p.2) = 0 ∧
      (∀ k, (calkinWilfRow (k + 2)).countP (fun p => euclidPPosition p.1 p.2) =
        (calkinWilfRow (k + 1)).countP (fun p => euclidPPosition p.1 p.2) +
          2 * (calkinWilfRow k).countP (fun p => euclidPPosition p.1 p.2)) ∧
      ∀ k, 3 * ((calkinWilfRow k).countP (fun p => euclidPPosition p.1 p.2) : ℤ) =
        2 ^ k + 2 * (-1) ^ k

/-- **Distinguishing the tops of arches.** Call a pair $(a, b)$ of natural numbers a P-position
when the Euclid P-position test returns true at $(a, b)$, and read it as the vertex $a/b$ of the
Calkin–Wilf tree, with son $a/(a+b)$ and daughter $(a+b)/b$. Let $m, n$ be positive integers. If
$m/n$ is a P-position, then so are its son's daughter $(2m+n)/(m+n)$ and its daughter's son
$(m+n)/(m+2n)$.

The statement covers all positive pairs; the tree vertices are the coprime ones.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 4.1. -/
public theorem_wanted euclidPPosition_tops_of_arch (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (h : euclidPPosition m n = true) :
    euclidPPosition (2 * m + n) (m + n) = true ∧ euclidPPosition (m + n) (m + 2 * n) = true

/-- **Establishing branches: nieces and nephews of P-positions.** Call a pair $(a, b)$ of natural
numbers a P-position when the Euclid P-position test returns true at $(a, b)$, and read it as the
vertex $a/b$ of the Calkin–Wilf tree, with son $a/(a+b)$ and daughter $(a+b)/b$. Let $x, y$ be
positive integers. If the daughter $(x+y)/y$ of $x/y$ is a P-position, then so is its niece
$(2x+y)/(x+y)$, the daughter of its sibling $x/(x+y)$. If the son $x/(x+y)$ of $x/y$ is a
P-position, then so is its nephew $(x+y)/(x+2y)$, the son of its sibling $(x+y)/y$.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 4.2. -/
public theorem_wanted euclidPPosition_branch_step (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    (euclidPPosition (x + y) y = true → euclidPPosition (2 * x + y) (x + y) = true) ∧
      (euclidPPosition x (x + y) = true → euclidPPosition (x + y) (x + 2 * y) = true)

/-- **Aunt or cousin of a P-position.** Call a pair $(a, b)$ of natural numbers a P-position when
the Euclid P-position test returns true at $(a, b)$, and let its son be $s(a, b) = (a, a + b)$ and
its daughter $d(a, b) = (a + b, b)$, as in the Calkin–Wilf tree. Let $x, y$ be positive integers,
let $r = (x, y)$, let $q$ be one of the two children $s(r)$ and $d(r)$ of $r$, and let $q'$ be the
other one. If the daughter $d(q)$ is a P-position, then exactly one of its aunt $q'$ and its male
cousin $s(q')$ is a P-position. If the son $s(q)$ is a P-position, then exactly one of its uncle
$q'$ and its female cousin $d(q')$ is a P-position.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 4.3. -/
public theorem_wanted euclidPPosition_aunt_xor_cousin (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    let s : ℕ × ℕ → ℕ × ℕ := fun p => (p.1, p.1 + p.2)
    let d : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + p.2, p.2)
    let P : ℕ × ℕ → Prop := fun p => euclidPPosition p.1 p.2 = true
    let r := (x, y)
    (P (d (s r)) → (P (d r) ↔ ¬P (s (d r)))) ∧ (P (d (d r)) → (P (s r) ↔ ¬P (s (s r)))) ∧
      (P (s (d r)) → (P (s r) ↔ ¬P (d (s r)))) ∧ (P (s (s r)) → (P (d r) ↔ ¬P (d (d r))))

/-- **Self-similarity of the P-positions of Euclid.** Call a pair $(a, b)$ of natural numbers a
P-position when the Euclid P-position test returns true at $(a, b)$, and read it as the vertex
$a/b$ of the Calkin–Wilf tree, with son $a/(a+b)$ and daughter $(a+b)/b$. Let $V$ be a vertex in
some row of the Calkin–Wilf tree that is a P-position. Then for every finite sequence $w$ of steps,
each step going to the son or to the daughter, the vertex reached from $V$ by following $w$ is a
P-position if and only if the vertex reached from the root $1/1$ by following $w$ is one.

In other words, below every P-position the P-positions sit exactly where they sit below the root.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Theorem 4.5. -/
public theorem_wanted euclidPPosition_self_similar (k : ℕ) (V : ℕ × ℕ)
    (hV : V ∈ calkinWilfRow k) (hP : euclidPPosition V.1 V.2 = true) (w : List Bool) :
    let walk : ℕ × ℕ → ℕ × ℕ := fun p =>
      w.foldl (fun q b => if b then (q.1 + q.2, q.2) else (q.1, q.1 + q.2)) p
    euclidPPosition (walk V).1 (walk V).2 = euclidPPosition (walk (1, 1)).1 (walk (1, 1)).2

/-- **Number of arch tops in a row of the Calkin–Wilf tree.** For $k \ge 2$ let $T_k$ be the
number of vertices of row $k$ of the Calkin–Wilf tree of the form $(2m+n)/(m+n)$ with $m/n$ a
P-position of Euclid in row $k - 2$. Then $3T_k = 2^{k-2} + 2(-1)^k$, that is,
$T_k = 2^{k-2}/3 + 2(-1)^k/3$.

The vertex $(2m+n)/(m+n)$ is the son's daughter of $m/n$, the left top of the arch below $m/n$;
the daughter's son $(m+n)/(m+2n)$ is the right top, so $T_k$ counts the arches whose tops lie in
row $k$.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Corollary 4.7. -/
public theorem_wanted count_arch_tops_calkinWilfRow (k : ℕ) (hk : 2 ≤ k) :
    3 * (((calkinWilfRow k).countP fun p => (calkinWilfRow (k - 2)).any fun V =>
        euclidPPosition V.1 V.2 && p == (2 * V.1 + V.2, V.1 + V.2)) : ℤ) =
      2 ^ (k - 2) + 2 * (-1) ^ k

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
public theorem_wanted arch_branch_levels (a b c d k : ℕ) (hb : 0 < b) (hab : b < a) (hc : 0 < c)
    (hcd : c < d) :
    let s : ℕ × ℕ → ℕ × ℕ := fun p => (p.1, p.1 + p.2)
    let t : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + p.2, p.2)
    let L := t (s^[k] (a - b, b))
    let R := s (t^[k] (c, d - c))
    ((L.1 : ℤ) = (k + 1) * a - k * b ∧ (L.2 : ℤ) = k * a - (k - 1) * b) ∧
      ((R.1 : ℤ) = k * d - (k - 1) * c ∧ (R.2 : ℤ) = (k + 1) * d - k * c)

/-- **The Fibonacci arches.** Let $F_j$ be the Fibonacci numbers with $F_0 = F_1 = 1$ and
$F_{j+2} = F_{j+1} + F_j$. Call a pair $(a, b)$ of natural numbers a P-position when the Euclid
P-position test returns true at $(a, b)$, read it as the vertex $a/b$ of the Calkin–Wilf tree, and
let $s(a/b) = a/(a+b)$ be its son and $d(a/b) = (a+b)/b$ its daughter; write $s^k$ and $d^k$ for
the $k$-fold iterates. Let $n \ge 1$ and $k \ge 0$, and let $V = F_{2n-1}/F_{2n-2}$. Then $V$ is a
P-position, its son's daughter $d(s(V))$ is $F_{2n+1}/F_{2n}$, and its daughter's son $s(d(V))$
is $F_{2n}/(F_{2n} + F_{2n-2})$. The vertex $L = d(s^k((F_{2n+1} - F_{2n})/F_{2n}))$ is a
P-position whose numerator is $F_{2n+1} + kF_{2n-1}$ and whose denominator is
$F_{2n+1} + (k-1)F_{2n-1}$, and the vertex $R = s(d^k(F_{2n}/F_{2n-2}))$ is the P-position
$(F_{2n} + kF_{2n-2})/(F_{2n} + (k+1)F_{2n-2})$.

Here $L$ and $R$ are level $k$ (level $0$ the top) of the left and right branches of the arch
topped by $d(s(V))$ and $s(d(V))$.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 5.2. -/
public theorem_wanted fibonacci_arch_positions (n k : ℕ) (hn : 1 ≤ n) :
    let F : ℕ → ℕ := fun j => Nat.fib (j + 1)
    let s : ℕ × ℕ → ℕ × ℕ := fun p => (p.1, p.1 + p.2)
    let t : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + p.2, p.2)
    let V := (F (2 * n - 1), F (2 * n - 2))
    let L := t (s^[k] (F (2 * n + 1) - F (2 * n), F (2 * n)))
    let R := s (t^[k] (F (2 * n), F (2 * n - 2)))
    euclidPPosition V.1 V.2 = true ∧ t (s V) = (F (2 * n + 1), F (2 * n)) ∧
      s (t V) = (F (2 * n), F (2 * n) + F (2 * n - 2)) ∧
      ((L.1 : ℤ) = F (2 * n + 1) + k * F (2 * n - 1) ∧
        (L.2 : ℤ) = F (2 * n + 1) + (k - 1) * F (2 * n - 1) ∧ euclidPPosition L.1 L.2 = true) ∧
      (R = (F (2 * n) + k * F (2 * n - 2), F (2 * n) + (k + 1) * F (2 * n - 2)) ∧
        euclidPPosition R.1 R.2 = true)

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
public theorem_wanted fibonacci_arch_tops (n k : ℕ) (hn : 1 ≤ n) :
    let F : ℕ → ℕ := fun j => Nat.fib (j + 1)
    let s : ℕ × ℕ → ℕ × ℕ := fun p => (p.1, p.1 + p.2)
    let t : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + p.2, p.2)
    let P : ℕ × ℕ → Prop := fun p => euclidPPosition p.1 p.2 = true
    let X := (F (2 * n + 1) + k * F (2 * n - 1), F (2 * n + 1) + k * F (2 * n - 1) - F (2 * n - 1))
    let Y := (F (2 * n) + k * F (2 * n - 2), F (2 * n) + (k + 1) * F (2 * n - 2))
    (P X ∧ P (t (s X)) ∧ P (s (t X)) ∧
      ((t (s X)).1 : ℤ) = 3 * F (2 * n + 1) + (3 * k - 1) * F (2 * n - 1) ∧
      ((t (s X)).2 : ℤ) = 2 * F (2 * n + 1) + (2 * k - 1) * F (2 * n - 1) ∧
      ((s (t X)).1 : ℤ) = 2 * F (2 * n + 1) + (2 * k - 1) * F (2 * n - 1) ∧
      ((s (t X)).2 : ℤ) = 3 * F (2 * n + 1) + (3 * k - 2) * F (2 * n - 1)) ∧
    (P Y ∧ P (t (s Y)) ∧ P (s (t Y)) ∧
      t (s Y) = (3 * F (2 * n) + (3 * k + 1) * F (2 * n - 2), 2 * F (2 * n) + (2 * k + 1) * F (2 * n - 2)) ∧
      s (t Y) = (2 * F (2 * n) + (2 * k + 1) * F (2 * n - 2), 3 * F (2 * n) + (3 * k + 2) * F (2 * n - 2)))

/-- **Positions of a Calkin–Wilf row with maximal optimal play in Euclid.** For every $k \ge 0$,
the number of positions in row $k$ of the Calkin–Wilf tree whose Smith remoteness in the Euclid
game is $k$ equals $2^{k/2}$ if $k$ is even and $2^{(k+1)/2}$ if $k$ is odd.

Smith remoteness is the length of optimal play when the winner hurries and the loser delays.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 6.1. -/
public theorem_wanted count_max_remoteness_calkinWilfRow (k : ℕ) :
    ((calkinWilfRow k).filter fun p =>
        SpragueGrundy.smithRemoteness euclidGame (show euclidGame.Pos from p) = k).length =
      if Even k then 2 ^ (k / 2) else 2 ^ ((k + 1) / 2)

/-- **Maximal-remoteness paths alternate in pairs.** In the Calkin–Wilf tree the vertex $a/b$ has
son $a/(a+b)$ and daughter $(a+b)/b$. Let $w = (w_0, \dots, w_{\ell-1})$ be a sequence of steps,
each "son" or "daughter", and let $a/b$ be the vertex reached from the root $1/1$ by following
$w$. If the Smith remoteness of the position $(a, b)$ of Euclid equals $\ell$, then
$w_{2i} \ne w_{2i+1}$ for every $i$ with $2i + 1 < \ell$; that is, steps $2i+1$ and $2i+2$ are
one son step and one daughter step, in either order.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 6.2. -/
public theorem_wanted max_remoteness_path_alternates (w : List Bool)
    (hw : SpragueGrundy.smithRemoteness euclidGame (show euclidGame.Pos from
      w.foldl (fun q b => if b then (q.1 + q.2, q.2) else (q.1, q.1 + q.2)) (1, 1)) = w.length)
    (i : ℕ) (hi : 2 * i + 1 < w.length) :
    w[2 * i]! ≠ w[2 * i + 1]!

/-- **Golden-ratio bounds for N-positions of maximal remoteness above 1.** Let $\varphi$ be the
golden ratio. If the pair $(m, n)$, read as the fraction $m/n$, lies in row $k$ of the Calkin–Wilf
tree, $n < m$, the position $(m, n)$ of Euclid is not a P-position, and its Smith remoteness in
Euclid equals $k$, then $\varphi < m/n < \varphi + 1$.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 6.3. -/
public theorem_wanted golden_bounds_of_max_remoteness_N (k m n : ℕ) (hk : (m, n) ∈ calkinWilfRow k)
    (hmn : n < m) (hN : euclidPPosition m n = false)
    (hr : SpragueGrundy.smithRemoteness euclidGame (show euclidGame.Pos from (m, n)) = k) :
    Real.goldenRatio < (m : ℝ) / n ∧ (m : ℝ) / n < Real.goldenRatio + 1

/-- **Golden-ratio bounds for N-positions of maximal remoteness below 1.** Let $\varphi$ be the
golden ratio. If the pair $(m, n)$, read as the fraction $m/n$, lies in row $k$ of the Calkin–Wilf
tree, $m < n$, the position $(m, n)$ of Euclid is not a P-position, and its Smith remoteness in
Euclid equals $k$, then $1/(\varphi + 1) < m/n < 1/\varphi$.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Corollary 6.4. -/
public theorem_wanted golden_bounds_of_max_remoteness_N_symm (k m n : ℕ)
    (hk : (m, n) ∈ calkinWilfRow k) (hmn : m < n) (hN : euclidPPosition m n = false)
    (hr : SpragueGrundy.smithRemoteness euclidGame (show euclidGame.Pos from (m, n)) = k) :
    1 / (Real.goldenRatio + 1) < (m : ℝ) / n ∧ (m : ℝ) / n < 1 / Real.goldenRatio

/-- **Golden-ratio bounds for P-positions of maximal remoteness.** Let $\varphi$ be the golden
ratio. If the pair $(m, n)$, read as the fraction $m/n$, lies in row $k$ of the Calkin–Wilf tree,
$m \ne n$, the position $(m, n)$ of Euclid is a P-position, and its Smith remoteness in Euclid
equals $k$, then $(\varphi + 2)/(\varphi + 1) < m/n < \varphi$ or
$1/\varphi < m/n < (\varphi + 1)/(\varphi + 2)$.

The hypothesis $m \ne n$ corrects the printed statement, which fails at the root $1/1$ (a
P-position with $0$ moves in row $0$, and $1$ lies in neither interval).

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 6.5. -/
public theorem_wanted golden_bounds_of_max_remoteness_P (k m n : ℕ)
    (hk : (m, n) ∈ calkinWilfRow k) (hmn : m ≠ n) (hP : euclidPPosition m n = true)
    (hr : SpragueGrundy.smithRemoteness euclidGame (show euclidGame.Pos from (m, n)) = k) :
    ((Real.goldenRatio + 2) / (Real.goldenRatio + 1) < (m : ℝ) / n ∧
        (m : ℝ) / n < Real.goldenRatio) ∨
      (1 / Real.goldenRatio < (m : ℝ) / n ∧
        (m : ℝ) / n < (Real.goldenRatio + 1) / (Real.goldenRatio + 2))

/-- **Continued fractions with maximal optimal play in Euclid.** For natural numbers
$a_0, \dots, a_r$ write $[a_0, \dots, a_r]$ for the continued fraction
$a_0 + 1/(a_1 + 1/(\cdots + 1/a_r))$, and $1^j$ for a block of $j$ ones; read a positive rational
$u/v$ in lowest terms as the position $(u, v)$ of the Euclid game. Let $n \ge 1$, $i$ and $k$ be
natural numbers. If the position of $[1^{n-1}, 2]$ lies in row $k$ of the Calkin–Wilf tree, its
Smith remoteness is $k$. If the position of $[1^{n-1}, 3]$ lies in row $k$, its Smith remoteness
is less than $k$. If $1 \le i \le n - 2$ and the position of $[1^i, 2, 1^{n-2-i}, 2]$ lies in
row $k$, its Smith remoteness is $k$ when $i \equiv n \pmod 2$ and less than $k$ when
$i \not\equiv n \pmod 2$.

Proposition 6.6 also identifies these pairs as the ones taking the most steps in the Euclidean
algorithm, a result of Hopkins and Tangboonduangjit; that half is not part of this statement.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 6.6. -/
public theorem_wanted continued_fraction_max_remoteness (n i k : ℕ) (hn : 1 ≤ n) :
    let cf : List ℕ → ℚ := fun l => l.foldr (fun a x => (a : ℚ) + x⁻¹) 0
    let pos : ℚ → euclidGame.Pos := fun q => (q.num.toNat, q.den)
    let rem := SpragueGrundy.smithRemoteness euclidGame
    let A := cf (List.replicate (n - 1) 1 ++ [2])
    let B := cf (List.replicate (n - 1) 1 ++ [3])
    let C := cf (List.replicate i 1 ++ [2] ++ List.replicate (n - 2 - i) 1 ++ [2])
    (((pos A).1, (pos A).2) ∈ calkinWilfRow k → rem (pos A) = k) ∧
      (((pos B).1, (pos B).2) ∈ calkinWilfRow k → rem (pos B) < k) ∧
      (1 ≤ i → i ≤ n - 2 → ((pos C).1, (pos C).2) ∈ calkinWilfRow k →
        (i % 2 = n % 2 → rem (pos C) = k) ∧ (i % 2 ≠ n % 2 → rem (pos C) < k))

end

end MetaMathlibExt
