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

/-- Fuel-bounded evaluation of the P-positions of the game Euclid on pairs of positive
integers: a move replaces the larger entry by its difference with a positive multiple of
the smaller one, keeping both entries positive, and the player facing two equal entries
(no move) loses. With fuel at least `a + b` the value is exact (`euclidPPosition`).

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

/-- `euclidPPosition a b` is `true` iff `(a, b)` (positive entries) is a P-position of
Euclid: every move leads to an N-position. Each move lowers `a + b`, so fuel `a + b`
suffices.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Section 4. -/
public def euclidPPosition (a b : ℕ) : Bool :=
  euclidPPositionAux (a + b) a b

/-- The moves of Euclid from `(a, b)`: when `0 < a < b`, replace `b` by `b - j a` for
`1 ≤ j` with `b - j a` still positive (and symmetrically when `0 < b < a`); a position
with equal or zero entries has no moves.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Section 4. -/
public def euclidMoves (p : ℕ × ℕ) : Finset (ℕ × ℕ) :=
  if p.1 = p.2 ∨ p.1 = 0 ∨ p.2 = 0 then ∅
  else if p.1 < p.2 then
    (Finset.range ((p.2 - 1) / p.1)).image fun k => (p.1, p.2 - (k + 1) * p.1)
  else
    (Finset.range ((p.1 - 1) / p.2)).image fun k => (p.1 - (k + 1) * p.2, p.2)

/-- Every move of Euclid lowers `a + b`.

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

/-- Euclid as a `SpragueGrundy.ImpartialGame` on pairs of naturals, ranked by `a + b` and
started at `(1, 1)`.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Section 4. -/
public def euclidGame : SpragueGrundy.ImpartialGame where
  Pos := ℕ × ℕ
  eqDec := inferInstance
  moves := euclidMoves
  rank := fun p => p.1 + p.2
  rank_lt := euclidMoves_rank_lt
  start := (1, 1)

/-- With fuel at least `a + b`, the executable classifier agrees with the normal-play
P-positions `SpragueGrundy.IsP euclidGame`.

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

/-- `euclidPPosition a b` holds exactly at the normal-play P-positions of `euclidGame`.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Section 4. -/
public theorem euclidPPosition_eq_true_iff (a b : ℕ) :
    euclidPPosition a b = true ↔ SpragueGrundy.IsP euclidGame (a, b) :=
  euclidPPositionAux_eq_true_iff (a + b) a b le_rfl

/-- Small values: `1/1` and `3/2` are P-positions, `2/1` and `1/2` are not.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Section 4. -/
public theorem euclidPPosition_small :
    euclidPPosition 1 1 = true ∧ euclidPPosition 2 1 = false ∧
      euclidPPosition 1 2 = false ∧ euclidPPosition 3 2 = true := by
  decide

/-- Row `k` of the Calkin–Wilf tree, as numerator–denominator pairs: row `0` is `1/1`, and
`a/b` has children `a/(a+b)` and `(a+b)/b`.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Section 2. -/
public def calkinWilfRow : ℕ → List (ℕ × ℕ)
  | 0 => [(1, 1)]
  | k + 1 => (calkinWilfRow k).flatMap fun p => [(p.1, p.1 + p.2), (p.1 + p.2, p.2)]

/-- Rows `1` and `2` of the Calkin–Wilf tree.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Section 2. -/
public theorem calkinWilfRow_one_two :
    calkinWilfRow 1 = [(1, 2), (2, 1)] ∧
      calkinWilfRow 2 = [(1, 3), (3, 2), (2, 3), (3, 1)] := by
  decide

/-- The number `L_k` of P-positions of Euclid in row `k` of the Calkin–Wilf tree satisfies
`L_0 = 1`, `L_1 = 0`, `L_{k+2} = L_{k+1} + 2L_k`, and `L_k = 2^k/3 + 2(-1)^k/3` (stated
as `3 L_k = 2^k + 2(-1)^k`). P-positions are counted with the executable `euclidPPosition`,
which agrees with `SpragueGrundy.IsP euclidGame` by `euclidPPosition_eq_true_iff`.

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

/-- Distinguishing the tops of arches. In the Calkin–Wilf tree the vertex `a/b` has son
`a/(a+b)` and daughter `(a+b)/b`. If the vertex `m/n` is a P-position of Euclid, then so are its
son's daughter `(2m+n)/(m+n)` and its daughter's son `(m+n)/(m+2n)`. Stated for all positive
pairs (tree vertices are the coprime ones).

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 4.1. -/
public theorem_wanted euclidPPosition_tops_of_arch (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (h : euclidPPosition m n = true) :
    euclidPPosition (2 * m + n) (m + n) = true ∧ euclidPPosition (m + n) (m + 2 * n) = true

/-- Establishing branches. For positive `x, y` (a tree vertex `x/y` when coprime): if its daughter `(x+y)/y` (a right/female
vertex) is a P-position, then so is that vertex's niece, the daughter `(2x+y)/(x+y)` of its
sibling `x/(x+y)`; if its son `x/(x+y)` (a left/male vertex) is a P-position, then so is that
vertex's nephew, the son `(x+y)/(x+2y)` of its sibling `(x+y)/y`.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 4.2. -/
public theorem_wanted euclidPPosition_branch_step (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    (euclidPPosition (x + y) y = true → euclidPPosition (2 * x + y) (x + y) = true) ∧
      (euclidPPosition x (x + y) = true → euclidPPosition (x + y) (x + 2 * y) = true)

/-- For positive `x, y` and `r = x/y` (a tree vertex when coprime), with son `s(a/b) = a/(a+b)` and daughter `d(a/b) = (a+b)/b`:
a right/female P-position `V = d(q)` with grandparent `r` has exactly one P-position among its
aunt (the sibling of `q`) and its male cousin (the son of the aunt); a left/male P-position
`V = s(q)` has exactly one P-position among its uncle (the sibling of `q`) and its female cousin
(the daughter of the uncle). Both cases `q = s(r)` and `q = d(r)` are stated.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 4.3. -/
public theorem_wanted euclidPPosition_aunt_xor_cousin (x y : ℕ) (hx : 0 < x) (hy : 0 < y) :
    let s : ℕ × ℕ → ℕ × ℕ := fun p => (p.1, p.1 + p.2)
    let d : ℕ × ℕ → ℕ × ℕ := fun p => (p.1 + p.2, p.2)
    let P : ℕ × ℕ → Prop := fun p => euclidPPosition p.1 p.2 = true
    let r := (x, y)
    (P (d (s r)) → (P (d r) ↔ ¬P (s (d r)))) ∧ (P (d (d r)) → (P (s r) ↔ ¬P (s (s r)))) ∧
      (P (s (d r)) → (P (s r) ↔ ¬P (d (s r)))) ∧ (P (s (s r)) → (P (d r) ↔ ¬P (d (d r))))

/-- Self-similarity of the P-positions of Euclid in the Calkin–Wilf tree: below every
P-position vertex `V`, the P-positions sit exactly where they sit below the root `1/1`. For every
finite left/right path `w` (`false` = son `a/(a+b)`, `true` = daughter `(a+b)/b`), the vertex
reached from `V` along `w` is a P-position iff the vertex reached from `1/1` along `w` is.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Theorem 4.5. -/
public theorem_wanted euclidPPosition_self_similar (k : ℕ) (V : ℕ × ℕ)
    (hV : V ∈ calkinWilfRow k) (hP : euclidPPosition V.1 V.2 = true) (w : List Bool) :
    let walk : ℕ × ℕ → ℕ × ℕ := fun p =>
      w.foldl (fun q b => if b then (q.1 + q.2, q.2) else (q.1, q.1 + q.2)) p
    euclidPPosition (walk V).1 (walk V).2 = euclidPPosition (walk (1, 1)).1 (walk (1, 1)).2

/-- The number `T_k` of arches whose tops lie in row `k ≥ 2` of the Calkin–Wilf tree satisfies
`T_k = 2^(k-2)/3 + 2(-1)^k/3`, stated as `3 T_k = 2^(k-2) + 2(-1)^k`. An arch top is the pair
(son's daughter, daughter's son) of a P-position two rows above; `T_k` counts the left tops, the
vertices `(2m+n)/(m+n)` of row `k` with `m/n` a P-position in row `k - 2`.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Corollary 4.7. -/
public theorem_wanted count_arch_tops_calkinWilfRow (k : ℕ) (hk : 2 ≤ k) :
    3 * (((calkinWilfRow k).countP fun p => (calkinWilfRow (k - 2)).any fun V =>
        euclidPPosition V.1 V.2 && p == (2 * V.1 + V.2, V.1 + V.2)) : ℤ) =
      2 ^ (k - 2) + 2 * (-1) ^ k

/-- Branches of an arch. If `a/b` (a right/female vertex, `a > b`) and `c/d` (a left/male
vertex, `c < d`) are the top left and right positions of an arch, the left branch descends by
nieces and the right branch by nephews: level `k` of the left branch (level `0` the top) is the
daughter of the `k`-fold son of the parent `(a-b)/b`, equal to `((k+1)a - kb)/(ka - (k-1)b)`, and
level `k` of the right branch is the son of the `k`-fold daughter of the parent `c/(d-c)`, equal
to `(kd - (k-1)c)/((k+1)d - kc)`. The arch-top hypothesis is dropped: the formulas hold for every
such pair.

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

/-- The Fibonacci arches. With the paper's Fibonacci numbers `F_j` (`F_0 = F_1 = 1`, here
`Nat.fib (j + 1)`), for `n ≥ 1`: `F_{2n+1}/F_{2n}` and `F_{2n}/(F_{2n} + F_{2n-2})` are the son's
daughter and daughter's son of the P-position `F_{2n-1}/F_{2n-2}` (so they top an arch), and for
every `k ≥ 0` (level `0` the top) level `k` of the left branch is the P-position
`(F_{2n+1} + kF_{2n-1})/(F_{2n+1} + (k-1)F_{2n-1})` and level `k` of the right branch is the
P-position `(F_{2n} + kF_{2n-2})/(F_{2n} + (k+1)F_{2n-2})`.

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

/-- Arch tops generated by the Fibonacci arch positions (paper's `F_0 = F_1 = 1`, here
`F_j = Nat.fib (j + 1)`; `n ≥ 1`, `k ≥ 0`). The P-position
`X = (F_{2n+1} + kF_{2n-1})/(F_{2n+1} + (k-1)F_{2n-1})` has son's daughter
`(3F_{2n+1} + (3k-1)F_{2n-1})/(2F_{2n+1} + (2k-1)F_{2n-1})` and daughter's son
`(2F_{2n+1} + (2k-1)F_{2n-1})/(3F_{2n+1} + (3k-2)F_{2n-1})`, the top of the arch below `X`; the
P-position `Y = (F_{2n} + kF_{2n-2})/(F_{2n} + (k+1)F_{2n-2})` has son's daughter
`(3F_{2n} + (3k+1)F_{2n-2})/(2F_{2n} + (2k+1)F_{2n-2})` and daughter's son
`(2F_{2n} + (2k+1)F_{2n-2})/(3F_{2n} + (3k+2)F_{2n-2})`. All six positions are P-positions.

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

/-- For `k ≥ 0`, the number of positions in row `k` of the Calkin–Wilf tree whose optimal play
takes `k` moves (the most possible from row `k`) is `2^(k/2)` for even `k` and `2^((k+1)/2)` for
odd `k`. Optimal-play length is Smith's remoteness (the winner hurries, the loser delays) of
`euclidGame`.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 6.1. -/
public theorem_wanted count_max_remoteness_calkinWilfRow (k : ℕ) :
    ((calkinWilfRow k).filter fun p =>
        SpragueGrundy.smithRemoteness euclidGame (show euclidGame.Pos from p) = k).length =
      if Even k then 2 ^ (k / 2) else 2 ^ ((k + 1) / 2)

/-- Every position requiring the maximum number of moves in optimal play lies on a path from
`1/1` whose steps `2n-1` and `2n` are `LR` or `RL`: if the vertex reached from `1/1` along
`w` (`false` = left/son, `true` = right/daughter) has Smith remoteness `|w|` (its row), then
`w[2i] ≠ w[2i+1]` whenever `2i + 1 < |w|`.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 6.2. -/
public theorem_wanted max_remoteness_path_alternates (w : List Bool)
    (hw : SpragueGrundy.smithRemoteness euclidGame (show euclidGame.Pos from
      w.foldl (fun q b => if b then (q.1 + q.2, q.2) else (q.1, q.1 + q.2)) (1, 1)) = w.length)
    (i : ℕ) (hi : 2 * i + 1 < w.length) :
    w[2 * i]! ≠ w[2 * i + 1]!

/-- If the player to move from the tree position `m/n` (row `k`), `m > n`, wins and optimal play
takes the maximum `k` moves (Smith remoteness `k`), then `φ < m/n < φ + 1`.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 6.3. -/
public theorem_wanted golden_bounds_of_max_remoteness_N (k m n : ℕ) (hk : (m, n) ∈ calkinWilfRow k)
    (hmn : n < m) (hN : euclidPPosition m n = false)
    (hr : SpragueGrundy.smithRemoteness euclidGame (show euclidGame.Pos from (m, n)) = k) :
    Real.goldenRatio < (m : ℝ) / n ∧ (m : ℝ) / n < Real.goldenRatio + 1

/-- If the player to move from the tree position `m/n` (row `k`), `n > m`, wins and optimal play
takes the maximum `k` moves (Smith remoteness `k`), then `1/(φ + 1) < m/n < 1/φ`.

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Corollary 6.4. -/
public theorem_wanted golden_bounds_of_max_remoteness_N_symm (k m n : ℕ)
    (hk : (m, n) ∈ calkinWilfRow k) (hmn : m < n) (hN : euclidPPosition m n = false)
    (hr : SpragueGrundy.smithRemoteness euclidGame (show euclidGame.Pos from (m, n)) = k) :
    1 / (Real.goldenRatio + 1) < (m : ℝ) / n ∧ (m : ℝ) / n < 1 / Real.goldenRatio

/-- A P-position `m/n ≠ 1/1` of row `k` of the Calkin–Wilf tree whose optimal play takes the
maximum `k` moves (Smith remoteness `k`) satisfies `(φ+2)/(φ+1) < m/n < φ` or
`1/φ < m/n < (φ+1)/(φ+2)`. The hypothesis `m ≠ n` corrects the printed statement, which fails at
the root `1/1` (a P-position with `0` moves in row `0`, and `1` lies in neither interval).

Source: Michael A. Jones and Brittany C. Ohlinger, *Self-Similar Structure of P-Positions
of the Game Euclid*, The Fibonacci Quarterly 62.1 (2024), Proposition 6.5. -/
public theorem_wanted golden_bounds_of_max_remoteness_P (k m n : ℕ)
    (hk : (m, n) ∈ calkinWilfRow k) (hmn : m ≠ n) (hP : euclidPPosition m n = true)
    (hr : SpragueGrundy.smithRemoteness euclidGame (show euclidGame.Pos from (m, n)) = k) :
    ((Real.goldenRatio + 2) / (Real.goldenRatio + 1) < (m : ℝ) / n ∧
        (m : ℝ) / n < Real.goldenRatio) ∨
      (1 / Real.goldenRatio < (m : ℝ) / n ∧
        (m : ℝ) / n < (Real.goldenRatio + 1) / (Real.goldenRatio + 2))

/-- Continued fractions and maximal optimal play. Write `[a_0, …, a_r]` for the continued
fraction `a_0 + 1/(a_1 + ⋯ + 1/a_r)` and `1^j` for `j` ones, and read its value `u/v` (lowest
terms) as the tree position `(u, v)` in its row `k`. For `n ≥ 1`, `[1^(n-1), 2]` and, for
`1 ≤ i ≤ n - 2` with `i ≡ n (mod 2)`, `[1^i, 2, 1^(n-2-i), 2]` give positions whose optimal play
takes the maximum `k` moves (Smith remoteness `k`); `[1^(n-1), 3]` and, for `1 ≤ i ≤ n - 2` with
`i ≢ n (mod 2)`, `[1^i, 2, 1^(n-2-i), 2]` give positions with Smith remoteness `< k`. The
proposition's other half, that these are the pairs taking the most steps in the Euclidean
algorithm, is the quoted result of Hopkins and Tangboonduangjit and is not stated.

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
