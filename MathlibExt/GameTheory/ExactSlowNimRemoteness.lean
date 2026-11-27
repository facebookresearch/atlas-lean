/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Nat.Find
public import MathlibExt.Computability.Complexity
public import MathlibExt.GameTheory.SlowANim
public import MathlibExt.GameTheory.SmithRemoteness

/-!
# Remoteness of Exact Slow `k`-NIM with `k + 1` piles

A position supported by a type (B) basic vector equals that vector, and each move lowers its
basic-vector value by one. At a position supported by a type (A1) basic vector, each move lowers the
basic-vector value by at most two, and the M-move lowers it by one. When `0 < k`, the basic-vector
value of every position equals its Smith remoteness. For positive even remoteness, critical
positions have uniform pile parity. Moves from an all-even critical position that lower every pile
of size equal to its remoteness give a critical position at the preceding parameter.
For odd-critical positions with `k ≥ 2`, the unique critical-lowering move keeps the unique even
pile. For `0 < k`, an all-odd position is a P-position exactly when it is a type (B) basic
vector for some parameter.

`NIM(k + 1, k)` is played on `k + 1` piles (a position is `x : Fin (k + 1) → ℕ`); a move removes
exactly one stone from each of `k` nonempty piles. This is the existing Slow`A`-Nim game
`slowANimGame (k + 1) {k}`, whose options are `slowANimMoves {k} x`. Smith's remoteness function
is `SpragueGrundy.smithRemoteness` (`MathlibExt/GameTheory/SmithRemoteness.lean`). The paper
compares positions after sorting their entries; since the game, the remoteness, and the
conditions below are invariant under permuting piles, "`R(y) ≠ m` for
every `y < x`" is equivalent to the same condition for the componentwise (`Pi`) order used here.

## References

* Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi,
  *On Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
  pp. 1–21, Theorem 1, Corollary 1 (i)–(ii), Proposition 1 (Sections 1.7 and 2), and Lemmas 1–4.
  Section 1.3 relates P-positions to even remoteness.
* The proof of Proposition 1 uses the option recursions `SpragueGrundy.isP_iff` and
  `SpragueGrundy.smithRemoteness_eq` from `MathlibExt.GameTheory.SpragueGrundy` and
  `MathlibExt.GameTheory.SmithRemoteness`, respectively. In this module it reuses
  `exactSlowNimBasicValue_eq_smithRemoteness`, `exactSlowNimBasicValue_of_supports_basicB`, and
  `odd_support_of_even_after`.
* Vladimir Gurvich and Nhan Bao Ho, *Slow k-Nim*, RUTCOR Research Report 3 (2015),
  arXiv:1508.05777 (introduction of exact slow Nim; reference [7] in the above paper).
* C. A. B. Smith, *Graphs and composite games*, Journal of Combinatorial Theory 1 (1966),
  pp. 51–81 (remoteness; reference [19] in the above paper).
* Charles L. Bouton, *Nim, a game with a complete mathematical theory*, Annals of Mathematics
  (2) 3 (1901–1902), pp. 35–39, and John von Neumann and Oskar Morgenstern,
  *Theory of Games and Economic Behavior*, Princeton University Press (1944)
  (earlier forms of the labeling algorithm; see Remark 2 in the above paper).
-/

namespace MetaMathlibExt

@[expose] public section

/-- **$m$-critical positions of exact slow $k$-NIM.** Let $k$ and $m$ be natural numbers and let
$\mathrm{NIM}(k + 1, k)$ be Slow$A$-Nim on $k + 1$ piles with $A = \{k\}$: a move chooses a
nonempty set of exactly $k$ nonempty piles and removes one stone from each. Let $R$ be Smith's
remoteness function of this game. A position $x = (x_0, \dots, x_k)$ is $m$-critical when
$R(x) = m$ and $R(y) \ne m$ for every position $y < x$, where $y < x$ means $y_i \le x_i$ for
every $i$ and $y \ne x$.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Theorem 1. -/
public def IsExactSlowNimCritical (k m : ℕ) (x : Fin (k + 1) → ℕ) : Prop :=
  SpragueGrundy.smithRemoteness (slowANimGame (k + 1) {k}) x = m ∧
    ∀ y : Fin (k + 1) → ℕ, y < x → SpragueGrundy.smithRemoteness (slowANimGame (k + 1) {k}) y ≠ m

/-- **The empty position is $0$-critical.** Let $k$ be a natural number and let
$\mathrm{NIM}(k + 1, k)$ be Slow$A$-Nim on $k + 1$ piles with $A = \{k\}$, in which a move
chooses a nonempty set of exactly $k$ nonempty piles and removes one stone from each. The
position $x$ of $\mathrm{NIM}(k + 1, k)$ in which all $k + 1$ piles are empty is $0$-critical:
its Smith remoteness is $0$, and no position $y$ with $y_i \le x_i$ for every $i$ and $y \ne x$
has remoteness $0$.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Theorem 1. -/
public theorem isExactSlowNimCritical_zero (k : ℕ) :
    IsExactSlowNimCritical k 0 (fun _ => 0) := by
  refine ⟨SpragueGrundy.smithRemoteness_of_moves_eq_empty _ _ (slowANimMoves_zero {k}), ?_⟩
  intro y hy
  exact absurd hy (not_lt_of_ge fun i => Nat.zero_le (y i))

/-- **Pile kept by the M-rule.** For a position $x \in \mathbb{N}^{n+1}$ with piles indexed by
$0, \dots, n$: if some entry of $x$ is even, the kept pile is the least index $i$ such that $x_i$
is even and $x_i \le x_j$ for every $j$ with $x_j$ even; otherwise it is the least index $i$
such that $x_j \le x_i$ for every $j$.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 2 (the index `e(x)`). Such a pile always exists, so the default `0` of `getD` is never
used. -/
public def exactSlowNimMRuleKept {n : ℕ} (x : Fin (n + 1) → ℕ) : Fin (n + 1) :=
  let piles := List.finRange (n + 1)
  if piles.any fun i => decide (Even (x i)) then
    (piles.find? fun i => decide (Even (x i) ∧ ∀ j, Even (x j) → x i ≤ x j)).getD 0
  else
    (piles.find? fun i => decide (∀ j, x j ≤ x i)).getD 0

/-- **The M-move.** For a position $x$ on $n + 1$ piles, the M-move keeps one pile, chosen by the
M-rule as the first pile holding the smallest even entry if some entry of $x$ is even, and
otherwise the first pile holding a largest entry. It removes one stone from every other pile,
where an empty pile stays empty.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Sections 1.2 and 2 (the M-rule). -/
public def exactSlowNimMRuleMove {n : ℕ} (x : Fin (n + 1) → ℕ) : Fin (n + 1) → ℕ :=
  slowANimAfter x (Finset.univ.erase (exactSlowNimMRuleKept x))

/-- **Terminal positions of exact slow $k$-NIM.** Let $n$ and $k$ be natural numbers and let
$x = (x_0, \dots, x_{n-1})$ be a position of Slow$A$-Nim on $n$ piles with $A = \{k\}$.
Then $x$ has no options if and only if $k = 0$ or fewer than $k$ of the piles are nonempty.

When $k = 0$ there is no move, since a move uses a nonempty set of exactly $k$ piles.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 1.1 (the moves of `NIM(n, k)`). -/
public theorem slowANimMoves_singleton_eq_empty_iff {n k : ℕ} (x : Fin n → ℕ) :
    slowANimMoves {k} x = ∅ ↔ k = 0 ∨ (Finset.univ.filter fun i => 0 < x i).card < k := by
  classical
  rw [slowANimMoves, Finset.image_eq_empty, Finset.filter_eq_empty_iff]
  constructor
  · intro h
    by_contra hc
    rw [not_or, not_lt] at hc
    obtain ⟨hk, hle⟩ := hc
    obtain ⟨S, hS, hcard⟩ := Finset.exists_subset_card_eq hle
    refine h (Finset.mem_univ S) ⟨Finset.card_pos.mp (by omega), by simp [hcard], fun i hi => ?_⟩
    have := (Finset.mem_filter.mp (hS hi)).2
    omega
  · rintro h S - ⟨hne, hcard, hp⟩
    rw [Finset.mem_singleton] at hcard
    rcases h with h | h
    · exact (Finset.card_pos.mpr hne).ne' (hcard.trans h)
    · have hsub : S ⊆ Finset.univ.filter fun i => 0 < x i := fun i hi =>
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp i hi⟩
      have := Finset.card_le_card hsub
      omega

/-- **Fuel-bounded length of M-rule play.** Let $k$ and $f$ be natural numbers and let $x$ be a
position on $k + 1$ piles. Call $x$ terminal when $k = 0$ or fewer than $k$ of its piles are
nonempty. The value at $f$ and $x$ is $0$ when $f = 0$ or $x$ is terminal; otherwise it is $1$
plus the value at $f - 1$ and the position reached from $x$ by the M-move. Thus it counts the
M-moves played from $x$, stopping at a terminal position or after $f$ moves.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 1.2 (the function `M`). -/
public def exactSlowNimMRuleLengthAux (k : ℕ) : ℕ → (Fin (k + 1) → ℕ) → ℕ
  | 0, _ => 0
  | f + 1, x =>
    if k = 0 ∨ (Finset.univ.filter fun i => 0 < x i).card < k then 0
    else 1 + exactSlowNimMRuleLengthAux k f (exactSlowNimMRuleMove x)

/-- **Successor step of the truncated M-rule length.** Let $k, f \in \mathbb{N}$ and
$x \in \mathbb{N}^{k+1}$, and write $M_f(x)$ for the number of M-rule steps from $x$ in
Slow$\{k\}$-Nim on $k + 1$ stacks, counted for at most $f$ steps. Then $M_{f+1}(x) = 0$ if $x$
has no options, and otherwise $M_{f+1}(x) = 1 + M_f(x')$, where $x'$ is the position obtained
from $x$ by the M-move.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 1.2 (the function `M`). -/
public theorem exactSlowNimMRuleLengthAux_succ (k f : ℕ) (x : Fin (k + 1) → ℕ) :
    exactSlowNimMRuleLengthAux k (f + 1) x =
      if slowANimMoves {k} x = ∅ then 0
      else 1 + exactSlowNimMRuleLengthAux k f (exactSlowNimMRuleMove x) := by
  rw [exactSlowNimMRuleLengthAux]
  exact if_congr (slowANimMoves_singleton_eq_empty_iff x).symm rfl rfl

/-- **M-rule length.** Let $k$ be a natural number and let $x = (x_0, \dots, x_k)$ be a position
on $k + 1$ piles. Then $M(x)$ is the number of M-moves played from $x$ until a terminal position
(one with $k = 0$ or fewer than $k$ nonempty piles) is reached, computed as the fuel-bounded
length of M-rule play with fuel $x_0 + \dots + x_k$.

For $0 < k$ every M-move from a nonterminal position removes $k$ stones, so this much fuel
suffices and $M(x)$ is the full length of the M-rule play from $x$.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 1.2 (the function `M`). -/
public def exactSlowNimMRuleLength (k : ℕ) (x : Fin (k + 1) → ℕ) : ℕ :=
  exactSlowNimMRuleLengthAux k (∑ i, x i) x

/-- **M-rule length of the position (3, 3, 3).** In exact slow $2$-NIM on three piles,
$\mathrm{NIM}(3, 2)$, where a move removes one stone from each of exactly two nonempty piles, the
M-rule length of the position $(3, 3, 3)$ is $M(3, 3, 3) = 4$.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 1.6 (example after Theorem 1). -/
public theorem exactSlowNimMRuleLength_three_three_three :
    exactSlowNimMRuleLength 2 ![3, 3, 3] = 4 := by
  decide +kernel

/-- **M-rule length of the position (3, 5, 5).** In exact slow $2$-NIM on three piles,
$\mathrm{NIM}(3, 2)$, where a move removes one stone from each of exactly two nonempty piles, the
M-rule length of the position $(3, 5, 5)$ is $M(3, 5, 5) = 6$.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 1.6 (example after Theorem 1). -/
public theorem exactSlowNimMRuleLength_three_five_five :
    exactSlowNimMRuleLength 2 ![3, 5, 5] = 6 := by
  decide +kernel

/-- **Basic vectors of type (A0).** Let $k$ and $b$ be natural numbers. A vector
$z = (z_0, \dots, z_k)$ of $k + 1$ natural numbers is basic of type (A0) for $b$ when
$z_0 + \dots + z_k = kb$, $z_i \le b$ for every $i$, $b$ is even, and every $z_i$ is even.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 2 (basic vectors). -/
public def IsExactSlowNimBasicA0 (k b : ℕ) (z : Fin (k + 1) → ℕ) : Prop :=
  ∑ i, z i = k * b ∧ (∀ i, z i ≤ b) ∧ Even b ∧ ∀ i, Even (z i)

/-- **Basic vectors of type (A1).** Let $k$ and $b$ be natural numbers. A vector
$z = (z_0, \dots, z_k)$ of $k + 1$ natural numbers is basic of type (A1) for $b$ when
$z_0 + \dots + z_k = kb$, $z_i \le b$ for every $i$, $b$ is odd, and exactly one $z_i$ is even.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 2 (basic vectors). -/
public def IsExactSlowNimBasicA1 (k b : ℕ) (z : Fin (k + 1) → ℕ) : Prop :=
  ∑ i, z i = k * b ∧ (∀ i, z i ≤ b) ∧ Odd b ∧ ∃! i, Even (z i)

/-- **Basic vectors of type (B).** Let $k$ and $b$ be natural numbers. A vector
$z = (z_0, \dots, z_k)$ of $k + 1$ natural numbers is basic of type (B) for $b$ when
$z_0 + \dots + z_k = kb + k - 1$, $z_i < b$ for every $i$, $b$ is even, and every $z_i$ is odd.
Here $kb + k - 1$ is computed in the natural numbers, so it is $0$ when $k = 0$.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 2 (basic vectors). -/
public def IsExactSlowNimBasicB (k b : ℕ) (z : Fin (k + 1) → ℕ) : Prop :=
  ∑ i, z i = k * b + k - 1 ∧ (∀ i, z i < b) ∧ Even b ∧ ∀ i, Odd (z i)

/-- **Basic-vector value.** For $k \in \mathbb{N}$ and $x \in \mathbb{N}^{k+1}$, the basic-vector
value $B(x)$ is the largest $b \le \sum_i x_i$ for which some $z \le x$ (componentwise) is a
basic vector of type (A0), (A1) or (B) with parameter $b$; such a $b$ exists, since $z = 0$ is
basic of type (A0) with parameter $0$. For $k \ge 1$ the bound is automatic, because every basic
$z \le x$ with parameter $b$ has $b \le k b \le \sum_i z_i \le \sum_i x_i$, so $B(x)$ is the
largest parameter of a basic vector $z \le x$.

For $k = 0$ that maximum does not exist ($z = 0$ is basic of type (A0) for every even $b$), and
the bound $b \le \sum_i x_i$ totalizes this degenerate case.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 2, equation (1). -/
public noncomputable def exactSlowNimBasicValue (k : ℕ) (x : Fin (k + 1) → ℕ) : ℕ :=
  open Classical in
  Nat.findGreatest (fun b => ∃ z ≤ x, IsExactSlowNimBasicA0 k b z ∨
    IsExactSlowNimBasicA1 k b z ∨ IsExactSlowNimBasicB k b z) (∑ i, x i)

/-- **The basic value is attained.** Let $k$ be a natural number, let $x$ be a position on
$k + 1$ piles, and let $b = B(x)$ be its basic value. Then some $z \le x$ (componentwise) is a
basic vector of type (A0), (A1) or (B) with parameter $b$, that is, $z$ supports $x$. Here type
(A0) means $\sum_i z_i = kb$, $z_i \le b$ for all $i$, and $b$ and every $z_i$ are even; type
(A1) means $\sum_i z_i = kb$, $z_i \le b$ for all $i$, $b$ is odd and exactly one $z_i$ is even;
and type (B) means $\sum_i z_i = kb + k - 1$ (truncated subtraction), $z_i < b$ for all $i$, $b$
is even and every $z_i$ is odd.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Section 2, equation (1). -/
public theorem exists_supports_exactSlowNimBasicValue (k : ℕ) (x : Fin (k + 1) → ℕ) :
    ∃ z ≤ x, IsExactSlowNimBasicA0 k (exactSlowNimBasicValue k x) z ∨
      IsExactSlowNimBasicA1 k (exactSlowNimBasicValue k x) z ∨
      IsExactSlowNimBasicB k (exactSlowNimBasicValue k x) z := by
  classical
  unfold exactSlowNimBasicValue
  exact Nat.findGreatest_spec (P := fun b => ∃ z ≤ x, IsExactSlowNimBasicA0 k b z ∨
    IsExactSlowNimBasicA1 k b z ∨ IsExactSlowNimBasicB k b z) (m := 0) (Nat.zero_le _)
    ⟨fun _ => 0, fun i => Nat.zero_le _,
    Or.inl ⟨by simp, fun _ => le_rfl, ⟨0, rfl⟩, fun _ => ⟨0, rfl⟩⟩⟩

namespace exactSlowNimBasicValue_of_supports_basicB

private theorem le_value_of_basicA1 {k b : ℕ} (hk : 0 < k) {x y : Fin (k + 1) → ℕ}
    (hyx : y ≤ x) (hy : IsExactSlowNimBasicA1 k b y) : b ≤ exactSlowNimBasicValue k x := by
  classical
  unfold exactSlowNimBasicValue
  refine Nat.le_findGreatest ?_ ⟨y, hyx, Or.inr (Or.inl hy)⟩
  calc
    b ≤ k * b := Nat.le_mul_of_pos_left _ hk
    _ = ∑ i, y i := hy.1.symm
    _ ≤ ∑ i, x i := Finset.sum_le_sum fun i _ => hyx i

private theorem mul_value_le_sum {k : ℕ} (hk : 0 < k) (x : Fin (k + 1) → ℕ) :
    k * exactSlowNimBasicValue k x ≤ ∑ i, x i := by
  obtain ⟨y, hyx, hy⟩ := exists_supports_exactSlowNimBasicValue k x
  refine le_trans ?_ (Finset.sum_le_sum fun i _ => hyx i)
  rcases hy with ha | ha | hb
  · exact ha.1.ge
  · exact ha.1.ge
  · have := hb.1
    omega

private theorem eq_of_supports {k : ℕ} (hk : 0 < k) {x z : Fin (k + 1) → ℕ} (hzx : z ≤ x)
    (hz : IsExactSlowNimBasicB k (exactSlowNimBasicValue k x) z) : x = z := by
  set b := exactSlowNimBasicValue k x
  obtain ⟨hsum, hlt, hb, hodd⟩ := hz
  funext j
  by_contra hne
  have hj : z j < x j := lt_of_le_of_ne (hzx j) (Ne.symm hne)
  -- A spare token on pile j gives a type (A1) vector with parameter b + 1.
  let y i := z i + if i = j then 1 else 0
  have hyx : y ≤ x := by
    intro i
    by_cases hi : i = j
    · simpa [y, hi] using Nat.succ_le_of_lt hj
    · simpa [y, hi] using hzx i
  have hy : IsExactSlowNimBasicA1 k (b + 1) y := by
    refine ⟨?_, ?_, hb.add_odd (by decide : Odd 1), j, ?_, ?_⟩
    · simp [y, Finset.sum_add_distrib, hsum, Nat.mul_succ]
      omega
    · intro i
      have := hlt i
      simp only [y]
      split <;> omega
    · simpa [y] using (hodd j).add_odd (by decide : Odd 1)
    · intro i hi
      by_contra hij
      exact (Nat.not_even_iff_odd.mpr (hodd i)) (by simpa [y, hij] using hi)
  exact (Nat.not_succ_le_self b) (le_value_of_basicA1 hk hyx hy)

private theorem sum_after_add_card {k : ℕ} (z : Fin (k + 1) → ℕ) (s : Finset (Fin (k + 1)))
    (hpos : ∀ i ∈ s, 1 ≤ z i) : (∑ i, slowANimAfter z s i) + s.card = ∑ i, z i := by
  calc
    _ = ∑ i, (slowANimAfter z s i + if i ∈ s then 1 else 0) := by
      simp [Finset.sum_add_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ s
      · simp [slowANimAfter, hi, Nat.sub_add_cancel (hpos i hi)]
      · simp [slowANimAfter, hi]

-- The other k piles each contain strictly fewer than b tokens.
private theorem le_pile_of_basicB {k b : ℕ} (hk : 0 < k) {z : Fin (k + 1) → ℕ}
    (hz : IsExactSlowNimBasicB k b z) (i : Fin (k + 1)) : k ≤ z i := by
  let rest := Finset.univ.erase i
  have hcard : rest.card = k := by simp [rest]
  have hne : rest.Nonempty := Finset.card_pos.mp (by simpa [hcard] using hk)
  have hlt := Finset.sum_lt_sum_of_nonempty hne
    (fun j (_ : j ∈ rest) => hz.2.1 j)
  have hbound : (∑ j ∈ rest, z j) < k * b := by simpa [hcard] using hlt
  have hsum := Finset.sum_erase_add Finset.univ z (Finset.mem_univ i)
  change (∑ j ∈ rest, z j) + z i = _ at hsum
  rw [hz.1] at hsum
  omega

private theorem value_after {k b : ℕ} (hk : 0 < k) {z : Fin (k + 1) → ℕ}
    (hz : IsExactSlowNimBasicB k b z) (s : Finset (Fin (k + 1))) (hcard : s.card = k)
    (hpos : ∀ i ∈ s, 1 ≤ z i) : exactSlowNimBasicValue k (slowANimAfter z s) = b - 1 := by
  let q := slowANimAfter z s
  have hsum : (∑ i, q i) + k = ∑ i, z i := by
    simpa only [hcard] using sum_after_add_card z s hpos
  rw [hz.1] at hsum
  apply le_antisymm
  · have hmass := mul_value_le_sum hk q
    have : k * exactSlowNimBasicValue k q < k * b := by omega
    exact Nat.le_pred_of_lt (Nat.lt_of_mul_lt_mul_left this)
  · obtain ⟨p, hp⟩ := Finset.card_pos.mp (hcard ▸ hk)
    -- Remove a second token from every played pile except p, the unique even pile.
    let t := s.erase p
    have ht : t.card = k - 1 := by simp [t, Finset.card_erase_of_mem hp, hcard]
    have htwo (i : Fin (k + 1)) (hi : i ∈ t) : 2 ≤ z i := by
      obtain ⟨hne, his⟩ := Finset.mem_erase.mp hi
      have := Finset.one_lt_card.mpr ⟨i, his, p, hp, hne⟩
      have := le_pile_of_basicB hk hz i
      omega
    have hqpos (i) (hi : i ∈ t) : 1 ≤ q i := by
      have := htwo i hi
      simp [q, slowANimAfter, (Finset.mem_erase.mp hi).2]
      omega
    let y := slowANimAfter q t
    have hyq : y ≤ q := by
      intro i
      simp [y, slowANimAfter]
      split <;> omega
    apply le_value_of_basicA1 hk hyq
    have hbpos : 0 < b := Nat.zero_lt_of_lt (hz.2.1 p)
    refine ⟨?_, ?_, ?_, p, ?_, ?_⟩
    · have hysum := sum_after_add_card q t hqpos
      change (∑ i, y i) + t.card = ∑ i, q i at hysum
      rw [ht] at hysum
      have hmul : k * (b - 1) + k = k * b := by
        rw [← Nat.mul_succ, show (b - 1).succ = b by omega]
      omega
    · intro i
      have hqi : q i ≤ z i := by
        simp [q, slowANimAfter]
        split <;> omega
      exact (hyq i).trans (hqi.trans (Nat.le_pred_of_lt (hz.2.1 i)))
    · have := Nat.even_iff.mp hz.2.2.1
      rw [Nat.odd_iff]
      omega
    · have := Nat.odd_iff.mp (hz.2.2.2 p)
      simp only [y, q, slowANimAfter, t, Finset.notMem_erase, ite_false, hp, ite_true, Nat.even_iff]
      omega
    · intro i hi
      by_contra hip
      have ho := Nat.odd_iff.mp (hz.2.2.2 i)
      by_cases his : i ∈ s
      · have hit : i ∈ t := Finset.mem_erase.mpr ⟨hip, his⟩
        have := htwo i hit
        simp only [y, q, slowANimAfter, hit, his, ite_true, Nat.even_iff] at hi
        omega
      · simp [y, q, t, slowANimAfter, his, Nat.even_iff] at hi
        omega

end exactSlowNimBasicValue_of_supports_basicB

open exactSlowNimBasicValue_of_supports_basicB

/-- **Positions supported by a (B) basic vector (Lemma 1).** Let $k \ge 1$, let $B$ be the
basic-vector value on $\mathbb{N}^{k+1}$, and let $x, z \in \mathbb{N}^{k+1}$ with $z \le x$
componentwise, where $z$ is a basic vector of type (B) with parameter $B(x)$. Then $x = z$, and
every option $x'$ of $x$ in Slow$\{k\}$-Nim on $k + 1$ stacks (a move removes one token from
each of exactly $k$ nonempty stacks) satisfies $B(x') = B(x) - 1$, where subtraction is
truncated at $0$.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Lemma 1. -/
public theorem exactSlowNimBasicValue_of_supports_basicB {k : ℕ} (hk : 0 < k)
    (x z : Fin (k + 1) → ℕ) (hzx : z ≤ x)
    (hz : IsExactSlowNimBasicB k (exactSlowNimBasicValue k x) z) :
    x = z ∧ ∀ x' ∈ slowANimMoves {k} x,
      exactSlowNimBasicValue k x' = exactSlowNimBasicValue k x - 1 := by
  obtain rfl := eq_of_supports hk hzx hz
  refine ⟨rfl, fun q hq => ?_⟩
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hq
  obtain ⟨_, _, hcard, hpos⟩ := Finset.mem_filter.mp hs
  exact value_after hk hz s (Finset.mem_singleton.mp hcard) hpos

local notation "Value" => exactSlowNimBasicValue

namespace exactSlowNim_critical_of_even

private abbrev Basic (k b : ℕ) (z : Fin (k + 1) → ℕ) :=
  IsExactSlowNimBasicA0 k b z ∨ IsExactSlowNimBasicA1 k b z ∨ IsExactSlowNimBasicB k b z

private abbrev after {k : ℕ} (x : Fin (k + 1) → ℕ) (j : Fin (k + 1)) :=
  slowANimAfter x (Finset.univ.erase j)

private theorem after_apply {k : ℕ} (x : Fin (k + 1) → ℕ) (j i : Fin (k + 1)) :
    after x j i = if i = j then x i else x i - 1 := by
  by_cases hi : i = j <;> simp [slowANimAfter, hi]

private theorem after_le {k : ℕ} (x : Fin (k + 1) → ℕ) (j : Fin (k + 1)) :
    after x j ≤ x := by
  intro i
  rw [after_apply]
  split_ifs
  · exact le_rfl
  · exact Nat.sub_le _ _

private theorem sub_one_le_after {k : ℕ} {x z : Fin (k + 1) → ℕ}
    (hzx : z ≤ x) (j i : Fin (k + 1)) : z i - 1 ≤ after x j i := by
  have h : z i ≤ x i := hzx i
  rw [after_apply]
  split_ifs <;> omega

private theorem after_sum {k : ℕ} (x : Fin (k + 1) → ℕ) (j : Fin (k + 1))
    (hpos : ∀ i, i ≠ j → 0 < x i) : (∑ i, after x j i) + k = ∑ i, x i := by
  simpa only [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
    Nat.add_sub_cancel] using
    sum_after_add_card x (Finset.univ.erase j) (fun i hi => hpos i (Finset.mem_erase.mp hi).1)

private theorem mem_moves_iff {k : ℕ} (hk : 0 < k) {x y : Fin (k + 1) → ℕ} :
    y ∈ slowANimMoves {k} x ↔ ∃ j, (∀ i, i ≠ j → 0 < x i) ∧ y = after x j := by
  simp only [slowANimMoves, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_singleton]
  constructor
  · rintro ⟨s, ⟨-, hc, hp⟩, rfl⟩
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := s) (t := Finset.univ) (by simp [hc])
    have hs : s = Finset.univ.erase j := by
      apply Finset.eq_of_subset_of_card_le
      · exact fun i hi => Finset.mem_erase.mpr ⟨fun h => hj (h ▸ hi), Finset.mem_univ _⟩
      · simp [hc]
    subst s
    exact ⟨j, fun i hi => hp i (by simp [hi]), rfl⟩
  · rintro ⟨j, hp, rfl⟩
    refine ⟨Finset.univ.erase j, ⟨Finset.card_pos.mp ?_, by simp, ?_⟩, rfl⟩
    · simpa using hk
    · intro i hi
      exact hp i (Finset.mem_erase.mp hi).1

private theorem sum_deficits {k b : ℕ} {z : Fin (k + 1) → ℕ}
    (hcap : ∀ i, z i ≤ b) (hsum : ∑ i, z i = k * b) :
    ∑ i, (b - z i) = b := by
  have h : (∑ i, (b - z i)) + ∑ i, z i = ∑ _i : Fin (k + 1), b := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hcap i)
  simp [hsum, Nat.succ_mul] at h
  omega

private theorem cap_of_other_zero {k b : ℕ} {z : Fin (k + 1) → ℕ}
    (hdef : ∑ i, (b - z i) = b) (hz : ∀ i, z i ≤ b) {p i : Fin (k + 1)}
    (hp : z p = 0) (hi : i ≠ p) : z i = b := by
  have h := Finset.sum_le_sum_of_subset (f := fun i => b - z i)
    (Finset.subset_univ ({i, p} : Finset (Fin (k + 1))))
  simp [hi, hp, hdef] at h
  have := hz i
  omega

private theorem a0_positive_away {k b : ℕ} {x z : Fin (k + 1) → ℕ} (hzx : z ≤ x)
    (hz : IsExactSlowNimBasicA0 k b z) {p : Fin (k + 1)} (hp : z p < b) :
    ∀ i, i ≠ p → 0 < x i := by
  intro i hi
  have hle : z i ≤ x i := hzx i
  by_contra! h
  have hzero : z i = 0 := by omega
  exact hp.ne (cap_of_other_zero (sum_deficits hz.2.1 hz.1) hz.2.1 hzero hi.symm)

private theorem exists_other_lt_cap {k b : ℕ} {z : Fin (k + 1) → ℕ}
    (hdef : ∑ i, (b - z i) = b) {p : Fin (k + 1)} (hp : 0 < z p) (hb : 0 < b) :
    ∃ q, q ≠ p ∧ z q < b := by
  by_contra! h
  have hrest : ∑ i ∈ Finset.univ.erase p, (b - z i) = 0 :=
    Finset.sum_eq_zero fun i hi => Nat.sub_eq_zero_of_le (h i (Finset.mem_erase.mp hi).1)
  have hs := Finset.sum_erase_add Finset.univ (fun i => b - z i) (Finset.mem_univ p)
  rw [hdef, hrest] at hs
  have hp' : b - z p = b := by simpa using hs
  omega

private theorem le_value {k b : ℕ} (hk : 0 < k) {x z : Fin (k + 1) → ℕ}
    (hzx : z ≤ x) (hz : Basic k b z) : b ≤ Value k x := by
  classical
  unfold exactSlowNimBasicValue
  refine Nat.le_findGreatest ?_ ⟨z, hzx, hz⟩
  have hmass : k * b ≤ ∑ i, z i := by
    rcases hz with ha | ha | hb
    · exact ha.1.ge
    · exact ha.1.ge
    · have := hb.1
      omega
  exact (Nat.le_mul_of_pos_left _ hk).trans (hmass.trans (Finset.sum_le_sum fun i _ => hzx i))

private theorem value_mono {k : ℕ} (hk : 0 < k) {x y : Fin (k + 1) → ℕ} (h : x ≤ y) :
    Value k x ≤ Value k y := by
  obtain ⟨z, hz, hb⟩ := exists_supports_exactSlowNimBasicValue k x
  exact le_value hk (hz.trans h) hb

private theorem kept_spec {k : ℕ} (x : Fin (k + 1) → ℕ) :
    let j := exactSlowNimMRuleKept x
    (Even (x j) ∧ ∀ i, Even (x i) → x j ≤ x i) ∨
      ((∀ i, ¬Even (x i)) ∧ ∀ i, x i ≤ x j) := by
  classical
  have find {P : Fin (k + 1) → Prop} [DecidablePred P] (h : ∃ i, P i) :
      P ((List.finRange (k + 1)).find? (fun i => decide (P i)) |>.getD 0) := by
    cases hfind : (List.finRange (k + 1)).find? (fun i => decide (P i)) with
    | none =>
      obtain ⟨i, hi⟩ := h
      exact (List.find?_eq_none.mp hfind i (List.mem_finRange _) (by simpa using hi)).elim
    | some i =>
      have hi := List.find?_some hfind
      simpa using hi
  dsimp only
  dsimp only [exactSlowNimMRuleKept]
  split_ifs with he
  · obtain ⟨i, -, hi⟩ := List.any_eq_true.mp he
    have hne : (Finset.univ.filter fun i => Even (x i)).Nonempty :=
      ⟨i, by simpa using hi⟩
    obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image _ x hne
    exact Or.inl (find (P := fun j => Even (x j) ∧ ∀ i, Even (x i) → x j ≤ x i)
      ⟨p, by simpa using hp, fun i hi => hmin i (by simpa using hi)⟩)
  · obtain ⟨p, -, hmax⟩ := Finset.exists_max_image Finset.univ x Finset.univ_nonempty
    exact Or.inr ⟨fun i hi => he (List.any_eq_true.mpr ⟨i, List.mem_finRange _, by simpa⟩),
      find (P := fun j => ∀ i, x i ≤ x j) ⟨p, fun i => hmax i (Finset.mem_univ _)⟩⟩

private theorem kept_legal {k : ℕ} {x : Fin (k + 1) → ℕ} {p : Fin (k + 1)}
    (hp : ∀ i, i ≠ p → 0 < x i) :
    ∀ i, i ≠ exactSlowNimMRuleKept x → 0 < x i := by
  intro i hi
  by_contra! hz
  have hzero : x i = 0 := Nat.eq_zero_of_le_zero hz
  have hei : Even (x i) := by simp [hzero]
  rcases kept_spec x with ⟨-, hmin⟩ | ⟨hn, -⟩
  · have hj := hmin i hei
    rw [hzero] at hj
    have hpi : i = p := by
      by_contra hne
      have := hp i hne
      omega
    have hpj : exactSlowNimMRuleKept x = p := by
      by_contra hne
      have := hp _ hne
      omega
    exact hi (hpi.trans hpj.symm)
  · exact hn i hei

-- A type (A0) support gives a type (A1) support after a move whenever a
-- sub-cap pile still has at least the number of stones in the support.
private theorem a1_of_a0_after {k b : ℕ} {x z : Fin (k + 1) → ℕ} (hzx : z ≤ x)
    (hz : IsExactSlowNimBasicA0 k b z) (j p : Fin (k + 1)) (hp : z p < b)
    (hp' : z p ≤ after x j p) : IsExactSlowNimBasicA1 k (b - 1) (after z p) ∧
      after z p ≤ after x j := by
  have ⟨hs, hcap, hb, he⟩ := hz
  have hb0 : 0 < b := Nat.zero_lt_of_lt hp
  have hpos := a0_positive_away le_rfl hz hp
  refine ⟨⟨?_, ?_, ?_, p, ?_, ?_⟩, ?_⟩
  · have h := after_sum z p hpos
    rw [hs] at h
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    omega
  · intro i
    have := hcap i
    rw [after_apply]
    split_ifs with hi
    · simpa [hi] using Nat.le_pred_of_lt hp
    · omega
  · rw [Nat.even_iff] at hb
    rw [Nat.odd_iff]
    omega
  · simpa [after_apply] using he p
  · intro i hi
    by_contra hne
    have := hpos i hne
    have := Nat.even_iff.mp (he i)
    simp only [after_apply, hne, ite_false, Nat.even_iff] at hi
    omega
  · intro i
    by_cases hi : i = p
    · simpa [hi, after_apply] using hp'
    · have hle : z i ≤ x i := hzx i
      simp only [after_apply, hi, ite_false]
      split_ifs <;> omega

private theorem sum_adjust {k : ℕ} {z w : Fin (k + 1) → ℕ} (p q : Fin (k + 1)) (c u v : ℕ)
    (h : ∀ i, w i + c = z i + (if i = p then u else 0) + (if i = q then v else 0)) :
    (∑ i, w i) + (k + 1) * c = (∑ i, z i) + u + v := by
  simpa [Finset.sum_add_distrib] using Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => h i)

-- Even basic vectors under an option can be extended to an odd one at its parent.
private theorem odd_support_of_even_after {k b : ℕ} (hk : 0 < k) {x z : Fin (k + 1) → ℕ}
    (j : Fin (k + 1)) (hj : ∀ i, i ≠ j → 0 < x i) (hzx : z ≤ after x j)
    (hz : IsExactSlowNimBasicA0 k b z ∨ IsExactSlowNimBasicB k b z) :
    ∃ w ≤ x, IsExactSlowNimBasicA1 k (b + 1) w := by
  rcases hz with ⟨hs, hcap, hb, he⟩ | ⟨hs, hcap, hb, ho⟩
  · let w (i : Fin (k + 1)) := z i + if i = j then 0 else 1
    have hw (i) : w i ≤ x i := by
      have h : z i ≤ after x j i := hzx i
      by_cases hi : i = j
      · simpa [w, after_apply, hi] using h
      · have := hj i hi
        simp [w, after_apply, hi] at h ⊢
        omega
    refine ⟨w, hw, ?_, ?_, hb.add_odd (by decide), j, ?_, ?_⟩
    · have h := sum_adjust j j 1 0 1 (z := w) (w := z) (by
        intro i
        by_cases hi : i = j <;> simp [w, hi])
      rw [Nat.mul_succ]
      omega
    · intro i
      have := hcap i
      dsimp [w]
      split_ifs <;> omega
    · simpa [w] using he j
    · intro i hi
      by_contra hne
      have := Nat.even_iff.mp (he i)
      simp [w, hne, Nat.even_iff] at hi
      omega
  · obtain ⟨p, hp⟩ := Finset.card_pos.mp (show (Finset.univ.erase j).card > 0 by
      simpa using hk)
    have hpj := (Finset.mem_erase.mp hp).1
    let w (i : Fin (k + 1)) := z i + if i = p then 1 else 0
    have hw (i) : w i ≤ x i := by
      have h : z i ≤ after x j i := hzx i
      by_cases hi : i = p
      · subst i
        have := hj p hpj
        simp [w, after_apply, hpj] at h ⊢
        omega
      · simp [w, hi, after_apply] at h ⊢
        split_ifs at h <;> omega
    refine ⟨w, hw, ?_, ?_, hb.add_odd (by decide), p, ?_, ?_⟩
    · simp [w, Finset.sum_add_distrib, hs, Nat.mul_succ]
      have := hcap j
      omega
    · intro i
      have := hcap i
      dsimp [w]
      split_ifs <;> omega
    · simpa [w] using (ho p).add_odd (show Odd 1 by decide)
    · intro i hi
      by_contra hne
      exact (Nat.not_even_iff_odd.mpr (ho i)) (by simpa [w, hne] using hi)

private theorem even_option_lt {k : ℕ} (hk : 0 < k) {x : Fin (k + 1) → ℕ}
    (j : Fin (k + 1)) (hj : ∀ i, i ≠ j → 0 < x i) (he : Even (Value k (after x j))) :
    Value k (after x j) < Value k x := by
  obtain ⟨z, hz, ha | ha | hb⟩ := exists_supports_exactSlowNimBasicValue k (after x j)
  · obtain ⟨w, hw, h⟩ := odd_support_of_even_after hk j hj hz (Or.inl ha)
    exact le_value hk hw (Or.inr (Or.inl h))
  · exact (Nat.not_even_iff_odd.mpr ha.2.2.1 he).elim
  · obtain ⟨w, hw, h⟩ := odd_support_of_even_after hk j hj hz (Or.inr hb)
    exact le_value hk hw (Or.inr (Or.inl h))

private theorem a0_bad_option {k b : ℕ} (hk : 0 < k) {x z : Fin (k + 1) → ℕ} (hzx : z ≤ x)
    (hz : IsExactSlowNimBasicA0 k b z) (j : Fin (k + 1)) (hb0 : 0 < b)
    (hbad : ∀ i, z i < b → after x j i < z i) (hlt : Value k (after x j) < b) :
    Odd (Value k (after x j)) := by
  let y := after x j
  obtain ⟨hs, hcap, hb, he⟩ := hz
  have hdef := sum_deficits hcap hs
  have hj : z j = b := by
    have h : z j ≤ x j := hzx j
    have h' := hbad j
    simp [after_apply] at h'
    have := hcap j
    omega
  have htwo (i) : 2 ≤ z i := by
    have h' := hbad i
    have := Nat.even_iff.mp (he i)
    omega
  obtain ⟨p, -, hpmin⟩ := Finset.exists_min_image Finset.univ z Finset.univ_nonempty
  obtain ⟨r, hr, hrlt⟩ := exists_other_lt_cap hdef (p := p) (by have := htwo p; omega) hb0
  have hp : z p < b := (hpmin r (Finset.mem_univ _)).trans_lt hrlt
  obtain ⟨q, hq, hqmin⟩ := Finset.exists_min_image (Finset.univ.erase p) z
    ⟨r, by simp [hr]⟩
  have hqp := (Finset.mem_erase.mp hq).1
  have hq' : z q < b := (hqmin r (by simp [hr])).trans_lt hrlt
  have hb4 : 4 ≤ b := by
    have := Nat.even_iff.mp hb
    have := Nat.even_iff.mp (he p)
    have := htwo p
    omega
  have hfour (i) (hip : i ≠ p) (hiq : i ≠ q) : 4 ≤ z i := by
    have hpi := hpmin i (Finset.mem_univ _)
    have hqi := hqmin i (by simp [hip])
    have h := Finset.sum_le_sum_of_subset (f := fun i => b - z i)
      (Finset.subset_univ ({i, q, p} : Finset (Fin (k + 1))))
    have := htwo i
    have := Nat.even_iff.mp (he i)
    simp [hip, hiq, hqp, hdef] at h
    omega
  -- Two sub-cap piles save three stones relative to taking three from every pile.
  let w (i : Fin (k + 1)) := z i - if i = p then 2 else if i = q then 1 else 3
  have hw : w ≤ y := by
    intro i
    change w i ≤ after x j i
    have := sub_one_le_after hzx j i
    dsimp [w]
    split_ifs <;> omega
  have ha : IsExactSlowNimBasicA1 k (b - 3) w := by
    refine ⟨?_, ?_, ?_, p, ?_, ?_⟩
    · have h := sum_adjust p q 3 1 2 (z := z) (w := w) (by
        intro i
        have := htwo i
        by_cases hip : i = p
        · subst i
          simp [w, hqp.symm]
          have := htwo p
          omega
        by_cases hiq : i = q
        · subst i
          simp [w, hqp]
          have := htwo q
          omega
        have := hfour i hip hiq
        simp [w, hip, hiq]
        omega)
      rw [Nat.mul_sub_left_distrib]
      omega
    · intro i
      have := hcap i
      have hp' := Nat.even_iff.mp (he p)
      have hq'' := Nat.even_iff.mp (he q)
      have hb' := Nat.even_iff.mp hb
      by_cases hip : i = p
      · simp [w, hip]
        omega
      by_cases hiq : i = q
      · subst i
        simp [w, hqp]
        omega
      simp [w, hip, hiq]
      omega
    · have := Nat.even_iff.mp hb
      rw [Nat.odd_iff]
      omega
    · have := Nat.even_iff.mp (he p)
      have := htwo p
      simp [w, Nat.even_iff]
      omega
    · intro i hi
      by_contra hip
      have := Nat.even_iff.mp (he i)
      have := htwo i
      by_cases hiq : i = q
      · subst i
        simp [w, Nat.even_iff, hqp] at hi
        omega
      · have := hfour i hip hiq
        simp [w, Nat.even_iff, hip, hiq] at hi
        omega
  have hle : b - 3 ≤ Value k y := le_value hk hw (Or.inr (Or.inl ha))
  by_contra! he'
  change Even (Value k y) at he'
  change Value k y < b at hlt
  have hb' := Nat.even_iff.mp hb
  have hy' := Nat.even_iff.mp he'
  have heq : Value k y = b - 2 := by omega
  have hmul : k * (b - 2) + k * 2 = k * b := by
    rw [← Nat.mul_add, Nat.sub_add_cancel (show 2 ≤ b by omega)]
  obtain ⟨v, hv, hA | hA | hB⟩ := exists_supports_exactSlowNimBasicValue k y
  · have hvz (i) : v i + 2 ≤ z i := by
      have hcap' := hA.2.1 i
      have hvi : v i ≤ y i := hv i
      have hev := Nat.even_iff.mp (hA.2.2.2 i)
      have hez := Nat.even_iff.mp (he i)
      have hm := hcap i
      have hlow := hbad i
      change z i < b → y i < z i at hlow
      rw [heq] at hcap'
      omega
    have hsum : (∑ i, v i) + (k + 1) * 2 ≤ ∑ i, z i := by
      simpa [Finset.sum_add_distrib] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => hvz i)
    rw [hA.1, heq, hs] at hsum
    omega
  · exact Nat.not_even_iff_odd.mpr hA.2.2.1 he'
  · have hvz (i) : v i + 1 ≤ z i := by
      have hcap' := hB.2.1 i
      have hvi : v i ≤ y i := hv i
      have hm := hcap i
      have hlow := hbad i
      change z i < b → y i < z i at hlow
      rw [heq] at hcap'
      omega
    have hj' := hB.2.1 j
    rw [heq] at hj'
    have hsum : (∑ i, v i) + (k + 1) < ∑ i, z i := by
      simpa [Finset.sum_add_distrib] using
        Finset.sum_lt_sum (s := Finset.univ) (fun i _ => hvz i)
          ⟨j, Finset.mem_univ _, show v j + 1 < z j by omega⟩
    rw [hB.1, heq, hs] at hsum
    omega

private theorem a1_option_lower {k b : ℕ} (hk : 0 < k) {x z : Fin (k + 1) → ℕ} (hzx : z ≤ x)
    (hz : IsExactSlowNimBasicA1 k b z) (j : Fin (k + 1)) : b - 2 ≤ Value k (after x j) := by
  by_cases hb : b ≤ 2
  · simp [Nat.sub_eq_zero_of_le hb]
  have hb3 : 3 ≤ b := by omega
  obtain ⟨hs, hcap, hbodd, p, hpe, hu⟩ := hz
  have hodd (i) (hi : i ≠ p) : Odd (z i) :=
    Nat.not_even_iff_odd.mp (fun h => hi (hu i h))
  have hdef := sum_deficits hcap hs
  have hb' : Odd (b - 2) := by
    have := Nat.odd_iff.mp hbodd
    rw [Nat.odd_iff]
    omega
  by_cases hp0 : z p = 0
  · let w (i : Fin (k + 1)) := z i - if i = p then 0 else 2
    have hw : w ≤ after x j := by
      intro i
      have := sub_one_le_after hzx j i
      by_cases hi : i = p
      · simp [w, hi, hp0]
      · simp [w, hi]
        omega
    apply le_value hk hw
    refine Or.inr (Or.inl ⟨?_, ?_, hb', p, by simpa [w] using hpe, ?_⟩)
    · have h := sum_adjust p p 2 2 0 (z := z) (w := w) (by
        intro i
        by_cases hi : i = p
        · simp [w, hi]
        · have := cap_of_other_zero hdef hcap hp0 hi
          simp [w, hi, this]
          omega)
      rw [Nat.mul_sub_left_distrib]
      omega
    · intro i
      by_cases hi : i = p
      · simp [w, hi, hp0]
      · simp [w, hi, cap_of_other_zero hdef hcap hp0 hi]
    · intro i hi
      by_contra hip
      have := Nat.odd_iff.mp hbodd
      simp [w, hip, cap_of_other_zero hdef hcap hp0 hip, Nat.even_iff] at hi
      omega
  obtain ⟨r, hr, hrl⟩ := exists_other_lt_cap hdef (p := p) (Nat.pos_of_ne_zero hp0) (by omega)
  obtain ⟨q, hq, hmin⟩ := Finset.exists_min_image (Finset.univ.erase p) z ⟨r, by simp [hr]⟩
  have hqp := (Finset.mem_erase.mp hq).1
  have hql : z q < b := (hmin r (by simp [hr])).trans_lt hrl
  have hqodd := Nat.odd_iff.mp (hodd q hqp)
  have hrest (i) (hip : i ≠ p) (hiq : i ≠ q) : 3 ≤ z i := by
    have hio := Nat.odd_iff.mp (hodd i hip)
    have hqi := hmin i (by simp [hip])
    have h := Finset.sum_le_sum_of_subset (f := fun i => b - z i)
      (Finset.subset_univ ({i, q} : Finset (Fin (k + 1))))
    simp [hiq, hdef] at h
    omega
  -- Exchange the even pile with the smallest odd one, subtracting two elsewhere.
  let w (i : Fin (k + 1)) := z i - if i = p ∨ i = q then 1 else 2
  have hw : w ≤ after x j := by
    intro i
    have := sub_one_le_after hzx j i
    dsimp [w]
    split_ifs <;> omega
  apply le_value hk hw
  refine Or.inr (Or.inl ⟨?_, ?_, hb', q, ?_, ?_⟩)
  · have h := sum_adjust p q 2 1 1 (z := z) (w := w) (by
      intro i
      by_cases hip : i = p
      · subst i
        simp [w, hqp.symm]
        omega
      by_cases hiq : i = q
      · subst i
        simp [w, hqp]
        omega
      have := hrest i hip hiq
      simp [w, hip, hiq]
      omega)
    rw [Nat.mul_sub_left_distrib]
    omega
  · intro i
    have := hcap i
    by_cases hip : i = p
    · subst i
      have := Nat.even_iff.mp hpe
      have := Nat.odd_iff.mp hbodd
      simp [w]
      omega
    by_cases hiq : i = q
    · subst i
      simp [w]
      omega
    simp [w, hip, hiq]
    omega
  · simp [w, Nat.even_iff]
    omega
  · intro i hi
    by_contra hiq
    by_cases hip : i = p
    · subst i
      have := Nat.even_iff.mp hpe
      simp [w, Nat.even_iff] at hi
      omega
    have := Nat.odd_iff.mp (hodd i hip)
    have := hrest i hip hiq
    simp [w, hip, hiq, Nat.even_iff] at hi
    omega

private theorem a0_support_mmove {k b : ℕ} {x z : Fin (k + 1) → ℕ} (hzx : z ≤ x)
    (hz : IsExactSlowNimBasicA1 k b z) :
    let j := exactSlowNimMRuleKept x
    ∃ w ≤ after x j, IsExactSlowNimBasicA0 k (b - 1) w := by
  let j := exactSlowNimMRuleKept x
  let y := after x j
  change ∃ w ≤ y, IsExactSlowNimBasicA0 k (b - 1) w
  obtain ⟨hs, hcap, hb, p, hp, hu⟩ := hz
  have hbodd := Nat.odd_iff.mp hb
  have hb0 : 0 < b := by omega
  have hodd (i) (hi : i ≠ p) : Odd (z i) :=
    Nat.not_even_iff_odd.mp (fun h => hi (hu i h))
  have hpcap : z p ≤ b - 1 := by
    have := hcap p
    have := Nat.even_iff.mp hp
    omega
  have hb' : Even (b - 1) := by rw [Nat.even_iff]; omega
  have hle (i) : z i - 1 ≤ y i := sub_one_le_after hzx j i
  by_cases hpy : z p ≤ y p
  · refine ⟨after z p, ?_, ?_, ?_, hb', ?_⟩
    · intro i
      by_cases hi : i = p
      · simpa [after_apply, hi] using hpy
      · simpa [after_apply, hi] using hle i
    · have h := after_sum z p (fun i hi => by
        have := Nat.odd_iff.mp (hodd i hi)
        omega)
      rw [hs] at h
      rw [Nat.mul_sub_left_distrib, Nat.mul_one]
      omega
    · intro i
      rw [after_apply]
      by_cases hi : i = p
      · simpa [hi] using hpcap
      · have := hcap i
        simp [hi]
        omega
    · intro i
      by_cases hi : i = p
      · simpa [after_apply, hi] using hp
      · have := Nat.odd_iff.mp (hodd i hi)
        simp [after_apply, hi, Nat.even_iff]
        omega
  have hpj : p ≠ j := by
    intro h
    have hpx : z p ≤ x p := hzx p
    exact hpy (by simpa [y, after_apply, h] using hpx)
  have hpx : z p = x p := by
    have h : z p ≤ x p := hzx p
    simp [y, after_apply, hpj] at hpy
    omega
  have hepx : Even (x p) := hpx ▸ hp
  have ⟨hej, hmin⟩ : Even (x j) ∧ ∀ i, Even (x i) → x j ≤ x i :=
    (kept_spec x).resolve_right (fun h => h.1 p hepx)
  have hzj : Odd (z j) := hodd j hpj.symm
  have hgap : z j + 1 ≤ x j := by
    have h : z j ≤ x j := hzx j
    have heven : x j % 2 = 0 := Nat.even_iff.mp hej
    have := Nat.odd_iff.mp hzj
    omega
  have hminp : x j ≤ x p := hmin p hepx
  have hp2 : 2 ≤ z p := by
    have := Nat.odd_iff.mp hzj
    omega
  let w (i : Fin (k + 1)) :=
    if i = p then z i - 2 else if i = j then z i + 1 else z i - 1
  refine ⟨w, ?_, ?_, ?_, hb', ?_⟩
  · intro i
    by_cases hip : i = p
    · subst i
      have := hle p
      simp [w]
      omega
    by_cases hij : i = j
    · subst i
      simpa [w, hpj.symm, y, after_apply] using hgap
    simpa [w, hip, hij] using hle i
  · have hpoint (i : Fin (k + 1)) :
        w i + 1 + (if i = p then 1 else 0) = z i + (if i = j then 2 else 0) := by
      by_cases hip : i = p
      · subst i
        simp [w, hpj]
        omega
      by_cases hij : i = j
      · subst i
        simp [w, hpj.symm]
      have := Nat.odd_iff.mp (hodd i hip)
      simp [w, hip, hij]
      omega
    have h := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hpoint i)
    simp [Finset.sum_add_distrib, hs] at h
    rw [Nat.mul_sub_left_distrib, Nat.mul_one]
    omega
  · intro i
    by_cases hip : i = p
    · subst i
      simp [w]
      omega
    by_cases hij : i = j
    · subst i
      simp [w, hpj.symm]
      omega
    have := hcap i
    simp [w, hip, hij]
    omega
  · intro i
    by_cases hip : i = p
    · subst i
      have := Nat.even_iff.mp hp
      simp [w, Nat.even_iff]
      omega
    have := Nat.odd_iff.mp (hodd i hip)
    simp only [w, hip, ite_false, Nat.even_iff]
    split_ifs <;> omega

-- An odd support under the M-option can be extended to an even support at its parent.
private theorem even_support_of_mmove {k b : ℕ} (hk : 0 < k) {x z : Fin (k + 1) → ℕ}
    (hj : ∀ i, i ≠ exactSlowNimMRuleKept x → 0 < x i)
    (hzx : z ≤ after x (exactSlowNimMRuleKept x)) (hz : IsExactSlowNimBasicA1 k b z) :
    b + 1 ≤ Value k x := by
  let j := exactSlowNimMRuleKept x
  obtain ⟨hs, hcap, hb, p, hp, hu⟩ := hz
  have ho (i) (hi : i ≠ p) : Odd (z i) :=
    Nat.not_even_iff_odd.mp (fun h => hi (hu i h))
  have hstep (i) (hi : i ≠ j) : z i + 1 ≤ x i := by
    have h := hj i hi
    have hle : z i ≤ after x j i := hzx i
    simp [after_apply, hi] at hle
    omega
  have hle (i) : z i ≤ x i := (hzx.trans (after_le x j)) i
  have hbe : Even (b + 1) := hb.add_odd (by decide)
  by_cases h : ∀ i, i ≠ p → z i + 1 ≤ x i
  · let w (i : Fin (k + 1)) := z i + if i = p then 0 else 1
    have hw (i) : w i ≤ x i := by
      by_cases hi : i = p
      · simpa [w, hi] using hle i
      · simpa [w, hi] using h i hi
    apply le_value hk (z := w) hw
    refine Or.inl ⟨?_, ?_, hbe, ?_⟩
    · have hsum := sum_adjust p p 1 0 1 (z := w) (w := z) (by
        intro i
        by_cases hi : i = p <;> simp [w, hi])
      rw [Nat.mul_succ]
      omega
    · intro i
      have := hcap i
      dsimp [w]
      split_ifs <;> omega
    · intro i
      by_cases hi : i = p
      · simpa [w, hi] using hp
      · simpa [w, hi] using (ho i hi).add_odd (show Odd 1 by decide)
  push Not at h
  obtain ⟨i, hip, hi⟩ := h
  have hij : i = j := by
    by_contra hij
    have := hstep i hij
    omega
  subst i
  have heq : x j = z j := by have := hle j; omega
  have hjodd : Odd (x j) := heq.symm ▸ ho j hip
  have ⟨hno, hmax⟩ : (∀ i, ¬Even (x i)) ∧ ∀ i, x i ≤ x j :=
    (kept_spec x).resolve_left (fun h => Nat.not_even_iff_odd.mpr hjodd h.1)
  -- With all x-piles odd and the largest one tight, raise each played odd pile by two.
  let w (i : Fin (k + 1)) := z i + if i = j then 0 else if i = p then 1 else 2
  have hw (i) : w i ≤ x i := by
    by_cases hi : i = j
    · simp [w, hi, heq]
    have hzi := hstep i hi
    by_cases hip' : i = p
    · simpa [w, hi, hip', hip.symm] using hzi
    have hxodd := Nat.odd_iff.mp (Nat.not_even_iff_odd.mp (hno i))
    have hzodd := Nat.odd_iff.mp (ho i hip')
    simp [w, hi, hip']
    omega
  apply le_value hk (z := w) hw
  refine Or.inr (Or.inr ⟨?_, ?_, hbe, ?_⟩)
  · have hsum := sum_adjust j p 2 2 1 (z := w) (w := z) (by
      intro i
      by_cases hi : i = j
      · subst i
        simp [w, hip]
      by_cases hp' : i = p
      · subst i
        simp [w, hip.symm]
      simp [w, hi, hp'])
    rw [Nat.mul_succ]
    omega
  · intro i
    exact Nat.lt_succ_of_le ((hw i).trans ((hmax i).trans (heq ▸ hcap j)))
  · intro i
    by_cases hi : i = j
    · simpa [w, hi, ← heq] using hjodd
    by_cases hp' : i = p
    · simpa [w, hi, hp', hip.symm] using hp.add_odd (show Odd 1 by decide)
    simpa [w, hi, hp'] using (ho i hp').add_even (show Even 2 by decide)

private theorem exists_lt_cap {k b : ℕ} {z : Fin (k + 1) → ℕ} (hb : 0 < b)
    (hs : ∑ i, z i = k * b) (hc : ∀ i, z i ≤ b) : ∃ i, z i < b := by
  by_contra! h
  have hzero : ∑ i, (b - z i) = 0 := Finset.sum_eq_zero fun i _ => Nat.sub_eq_zero_of_le (h i)
  rw [sum_deficits hc hs] at hzero
  omega

private theorem value_eq_pred_of_a1_after {k : ℕ} (hk : 0 < k) {x y : Fin (k + 1) → ℕ}
    (he : Even (Value k x)) (hy : y ∈ slowANimMoves {k} x)
    (hl : Value k x - 1 ≤ Value k y) : Value k y = Value k x - 1 := by
  obtain ⟨j, hj, rfl⟩ := (mem_moves_iff hk).mp hy
  have hle := value_mono hk (after_le x j)
  have hlt : Value k (after x j) < Value k x := by
    by_contra! h
    have heq := le_antisymm hle h
    have he' : Even (Value k (after x j)) := heq.symm ▸ he
    exact (Nat.ne_of_lt (even_option_lt hk j hj he')) heq
  omega

-- Lemma 3: at a position supported by a type (A1) basic vector, every option loses at most two,
-- and the M-move, which is legal, loses exactly one.
private theorem a1_support_moves {k : ℕ} (hk : 0 < k) {x z : Fin (k + 1) → ℕ} (hzx : z ≤ x)
    (hz : IsExactSlowNimBasicA1 k (Value k x) z) :
    (∀ j, Value k x - 2 ≤ Value k (after x j)) ∧
      (∀ i, i ≠ exactSlowNimMRuleKept x → 0 < x i) ∧
      Value k (after x (exactSlowNimMRuleKept x)) = Value k x - 1 := by
  obtain ⟨p, -, hp⟩ := hz.2.2.2
  have hpos (i) (hi : i ≠ p) : 0 < x i := by
    have ho' := Nat.not_even_iff_odd.mp (fun he => hi (hp i he))
    exact (show 0 < z i by have := Nat.odd_iff.mp ho'; omega).trans_le (hzx i)
  let j := exactSlowNimMRuleKept x
  have hj : ∀ i, i ≠ j → 0 < x i := kept_legal hpos
  obtain ⟨w, hw, hA⟩ := a0_support_mmove hzx hz
  have hlow : Value k x - 1 ≤ Value k (after x j) := le_value hk hw (Or.inl hA)
  have huv : Value k (after x j) < Value k x := by
    obtain ⟨v, hv, hvA | hvA | hvB⟩ := exists_supports_exactSlowNimBasicValue k (after x j)
    · exact even_option_lt hk j hj hvA.2.2.1
    · exact even_support_of_mmove hk hj hv hvA
    · exact even_option_lt hk j hj hvB.2.2.1
  refine ⟨fun j' => a1_option_lower hk hzx hz j', hj, ?_⟩
  change Value k (after x j) = Value k x - 1
  omega

-- These are the successor-value conditions in the defining recursion for remoteness.
private theorem option_profile {k : ℕ} (hk : 0 < k) (x : Fin (k + 1) → ℕ)
    (hb : 0 < Value k x) :
    (∃ y ∈ slowANimMoves {k} x, Value k y = Value k x - 1) ∧
    (Even (Value k x) → ∀ y ∈ slowANimMoves {k} x, Odd (Value k y) ∧ Value k y < Value k x) ∧
    (Odd (Value k x) → ∀ y ∈ slowANimMoves {k} x, Even (Value k y) →
      Value k x - 1 ≤ Value k y) := by
  obtain ⟨z, hzx, ha | ha | hB⟩ := exists_supports_exactSlowNimBasicValue k x
  · have he := ha.2.2.1
    obtain ⟨p, hp⟩ := exists_lt_cap hb ha.1 ha.2.1
    have hpos := a0_positive_away hzx ha hp
    have hmem : after x p ∈ slowANimMoves {k} x := (mem_moves_iff hk).mpr ⟨p, hpos, rfl⟩
    have pred_of_good (j) (hm : after x j ∈ slowANimMoves {k} x)
        (i) (hi : z i < Value k x) (hiy : z i ≤ after x j i) :
        Value k (after x j) = Value k x - 1 := by
      have ⟨hA, hle⟩ := a1_of_a0_after hzx ha j i hi hiy
      exact value_eq_pred_of_a1_after hk he hm (le_value hk hle (Or.inr (Or.inl hA)))
    refine ⟨⟨after x p, hmem, pred_of_good p hmem p hp (by simpa [after_apply] using hzx p)⟩,
      ?_, fun ho => (Nat.not_even_iff_odd.mpr ho he).elim⟩
    intro he' y hy
    obtain ⟨j, hj, rfl⟩ := (mem_moves_iff hk).mp hy
    have hle := value_mono hk (after_le x j)
    have hne : Value k (after x j) ≠ Value k x :=
      fun heq => (Nat.ne_of_lt (even_option_lt hk j hj (heq.symm ▸ he'))) heq
    have hlt := lt_of_le_of_ne hle hne
    refine ⟨?_, hlt⟩
    by_cases h : ∃ i, z i < Value k x ∧ z i ≤ after x j i
    · obtain ⟨i, hi, hiy⟩ := h
      rw [pred_of_good j hy i hi hiy, Nat.odd_iff]
      have := Nat.even_iff.mp he
      omega
    push Not at h
    exact a0_bad_option hk hzx ha j hb h hlt
  · have ho := ha.2.2.1
    obtain ⟨hlower, hj, hm⟩ := a1_support_moves hk hzx ha
    refine ⟨⟨after x (exactSlowNimMRuleKept x), (mem_moves_iff hk).mpr ⟨_, hj, rfl⟩, hm⟩,
      fun he => (Nat.not_even_iff_odd.mpr ho he).elim, ?_⟩
    intro ho' y hy he
    obtain ⟨j', -, rfl⟩ := (mem_moves_iff hk).mp hy
    have h : Value k x - 2 ≤ Value k (after x j') := hlower j'
    have := Nat.odd_iff.mp ho'
    have := Nat.even_iff.mp he
    omega
  · have he := hB.2.2.1
    have hpos (i) : 0 < x i :=
      (show 0 < z i by have := Nat.odd_iff.mp (hB.2.2.2 i); omega).trans_le (hzx i)
    have hs := (exactSlowNimBasicValue_of_supports_basicB hk x z hzx hB).2
    have hmem : after x 0 ∈ slowANimMoves {k} x :=
      (mem_moves_iff hk).mpr ⟨0, fun i _ => hpos i, rfl⟩
    refine ⟨⟨after x 0, hmem, hs _ hmem⟩, ?_, fun ho => (Nat.not_even_iff_odd.mpr ho he).elim⟩
    intro _ y hy
    rw [hs y hy, Nat.odd_iff]
    have := Nat.even_iff.mp he
    omega

-- Identify the basic-vector value with Smith's recursion by induction on the total pile size.
private theorem smith_eq_value {k : ℕ} (hk : 0 < k) (x : Fin (k + 1) → ℕ) :
    SpragueGrundy.smithRemoteness (slowANimGame (k + 1) {k}) x = Value k x := by
  classical
  induction x using (measure (fun y : Fin (k + 1) → ℕ => ∑ i, y i)).wf.induction with
  | h x ih =>
    let G := slowANimGame (k + 1) {k}
    change SpragueGrundy.smithRemoteness G x = Value k x
    let S := (slowANimMoves {k} x).image (Value k)
    have himage : (G.moves x).image (SpragueGrundy.smithRemoteness G) = S := by
      apply Finset.image_congr
      intro y hy
      exact ih y (sum_lt_of_mem_slowANimMoves _ _ _ hy)
    rw [SpragueGrundy.smithRemoteness_eq G x, himage]
    by_cases hb : 0 < Value k x
    · obtain ⟨⟨y, hy, hyv⟩, hev, hov⟩ := option_profile hk x hb
      have pred_mem : Value k x - 1 ∈ S := Finset.mem_image.mpr ⟨y, hy, hyv⟩
      have hS : S.Nonempty := ⟨_, pred_mem⟩
      by_cases he : Even (Value k x)
      · have hempty : ¬ (S.filter Even).Nonempty := by
          rintro ⟨v, hv⟩
          have hv' := Finset.mem_filter.mp hv
          obtain ⟨q, hq, hqv⟩ := Finset.mem_image.mp hv'.1
          exact (Nat.not_even_iff_odd.mpr (hev he q hq).1) (hqv.symm ▸ hv'.2)
        have hmax : S.max' hS = Value k x - 1 := by
          apply le_antisymm _ (Finset.le_max' _ _ pred_mem)
          obtain ⟨q, hq, hqv⟩ := Finset.mem_image.mp (Finset.max'_mem S hS)
          have := (hev he q hq).2
          omega
        rw [dite_eq_right hempty, dite_eq_left hS, hmax]
        omega
      · have ho := Nat.not_even_iff_odd.mp he
        have hprev : Even (Value k x - 1) := by
          have := Nat.odd_iff.mp ho
          rw [Nat.even_iff]
          omega
        have hmem := Finset.mem_filter.mpr ⟨pred_mem, hprev⟩
        have hE : (S.filter Even).Nonempty := ⟨_, hmem⟩
        have hmin : (S.filter Even).min' hE = Value k x - 1 := by
          apply le_antisymm (Finset.min'_le _ _ hmem)
          have hq' := Finset.mem_filter.mp (Finset.min'_mem _ hE)
          obtain ⟨q, hq, hqv⟩ := Finset.mem_image.mp hq'.1
          rw [← hqv]
          exact hov ho q hq (hqv.symm ▸ hq'.2)
        rw [dite_eq_left hE, hmin]
        omega
    · have hz : Value k x = 0 := by omega
      have hempty : ¬ S.Nonempty := by
        rintro ⟨v, hv⟩
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
        obtain ⟨j, hj, rfl⟩ := (mem_moves_iff hk).mp hy
        have hle := value_mono hk (after_le x j)
        have he : Even (Value k (after x j)) := by
          have hzero : Value k (after x j) = 0 := by omega
          simp [hzero]
        have := even_option_lt hk j hj he
        omega
      have hfilter : ¬ (S.filter Even).Nonempty :=
        fun h => hempty (h.mono (Finset.filter_subset _ _))
      rw [dite_eq_right hfilter, dite_eq_right hempty, hz]

private theorem basic_of_critical {k m : ℕ} (hk : 0 < k) {x : Fin (k + 1) → ℕ}
    (hx : IsExactSlowNimCritical k m x) : Basic k m x := by
  have hvalue : Value k x = m := (smith_eq_value hk x).symm.trans hx.1
  obtain ⟨z, hzx, hz⟩ := exists_supports_exactSlowNimBasicValue k x
  change Basic k (Value k x) z at hz
  rw [hvalue] at hz
  have hvalz : Value k z = m :=
    le_antisymm ((value_mono hk hzx).trans_eq hvalue) (le_value hk le_rfl hz)
  have hzx' : z = x := by
    by_contra hne
    have hlt : z < x := lt_of_le_of_ne hzx hne
    exact hx.2 z hlt ((smith_eq_value hk z).trans hvalz)
  subst z
  exact hz

private theorem critical_of_a1 {k b : ℕ} (hk : 0 < k) {y : Fin (k + 1) → ℕ}
    (hy : IsExactSlowNimBasicA1 k b y) : IsExactSlowNimCritical k b y := by
  refine ⟨?_, ?_⟩
  · rw [smith_eq_value hk]
    refine le_antisymm ?_ (le_value hk le_rfl (Or.inr (Or.inl hy)))
    exact Nat.le_of_mul_le_mul_left (by simpa only [hy.1] using mul_value_le_sum hk y) hk
  · intro z hz
    rw [smith_eq_value hk]
    have hsum := Fintype.sum_strictMono hz
    exact (Nat.lt_of_mul_lt_mul_left ((mul_value_le_sum hk z).trans_lt (hsum.trans_eq hy.1))).ne
end exactSlowNim_critical_of_even

open exactSlowNim_critical_of_even in
/-- **Basic-vector value equals Smith's remoteness (Lemma 4).** Let $k \ge 1$ and consider
Slow$\{k\}$-Nim on $k + 1$ stacks, in which a move removes one token from each of exactly $k$
nonempty stacks. For every position $x \in \mathbb{N}^{k+1}$, the basic-vector value $B(x)$
equals Smith's remoteness of $x$ in this game.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Lemma 4. -/
public theorem exactSlowNimBasicValue_eq_smithRemoteness {k : ℕ} (hk : 0 < k)
    (x : Fin (k + 1) → ℕ) :
    exactSlowNimBasicValue k x = SpragueGrundy.smithRemoteness (slowANimGame (k + 1) {k}) x :=
  (smith_eq_value hk x).symm

open exactSlowNim_critical_of_even in
/-- **Moves at a position supported by an (A1) basic vector (Lemma 3).** Let $k \ge 1$, let
$B$ be the basic-vector value on $\mathbb{N}^{k+1}$, and let $x, z \in \mathbb{N}^{k+1}$ with
$z \le x$ componentwise, where $z$ is a basic vector of type (A1) with parameter $B(x)$. Then
every option $x'$ of $x$ in Slow$\{k\}$-Nim on $k + 1$ stacks (a move removes one token from
each of exactly $k$ nonempty stacks) satisfies $B(x') \ge B(x) - 2$, and the position $x''$
obtained from $x$ by the M-move satisfies $B(x'') = B(x) - 1$, where subtraction is truncated
at $0$.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Lemma 3. -/
public theorem exactSlowNimBasicValue_of_supports_basicA1 {k : ℕ} (hk : 0 < k)
    (x z : Fin (k + 1) → ℕ) (hzx : z ≤ x)
    (hz : IsExactSlowNimBasicA1 k (exactSlowNimBasicValue k x) z) :
    (∀ x' ∈ slowANimMoves {k} x, exactSlowNimBasicValue k x - 2 ≤ exactSlowNimBasicValue k x') ∧
      exactSlowNimBasicValue k (exactSlowNimMRuleMove x) = exactSlowNimBasicValue k x - 1
    := by
  obtain ⟨hlower, -, hm⟩ := a1_support_moves hk hzx hz
  refine ⟨fun x' hx' => ?_, hm⟩
  obtain ⟨j, -, rfl⟩ := (mem_moves_iff hk).mp hx'
  exact hlower j

open exactSlowNim_critical_of_even in
/-- **Moves from critical positions with even parameter (Corollary 1 (i)).** Let $k \ge 1$, let
$m > 0$ be even, and let $x \in \mathbb{N}^{k+1}$ be an $m$-critical position of Slow$\{k\}$-Nim
on $k + 1$ stacks. Then the entries of $x$ are either all odd or all even. If they are all even,
then some entry satisfies $x_i < m$; every option $y$ of $x$ with $y_i < x_i$ for every $i$ such
that $x_i = m$ is $(m - 1)$-critical; and the position $x'$ obtained from $x$ by the M-move
satisfies $x'_i < x_i$ for every $i$ with $x_i = m$ and is $(m - 1)$-critical.

The hypothesis $m > 0$ and the restriction of the move claims to all-even $x$ are deviations from
the source.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Corollary 1 (i). -/
public theorem exactSlowNim_critical_of_even {k m : ℕ} (hk : 0 < k) (hm0 : 0 < m)
    (hm : Even m) (x : Fin (k + 1) → ℕ) (hx : IsExactSlowNimCritical k m x) :
    ((∀ i, Odd (x i)) ∨ (∀ i, Even (x i))) ∧
      ((∀ i, Even (x i)) →
        (∃ i, x i < m) ∧
          (∀ y ∈ slowANimMoves {k} x, (∀ i, x i = m → y i < x i) →
            IsExactSlowNimCritical k (m - 1) y) ∧
          (∀ i, x i = m → exactSlowNimMRuleMove x i < x i) ∧
          IsExactSlowNimCritical k (m - 1) (exactSlowNimMRuleMove x)) := by
  rcases basic_of_critical hk hx with ha | ha | hB
  · have hcap := ha.2.1
    have he := ha.2.2.2
    obtain ⟨p, hp⟩ := exists_lt_cap hm0 ha.1 hcap
    have hcritical (y : Fin (k + 1) → ℕ) (hy : y ∈ slowANimMoves {k} x)
        (hreduce : ∀ i, x i = m → y i < x i) : IsExactSlowNimCritical k (m - 1) y := by
      obtain ⟨j, -, rfl⟩ := (mem_moves_iff hk).mp hy
      have hj : x j < m := by
        apply lt_of_le_of_ne (hcap j)
        intro h
        simpa [after_apply] using hreduce j h
      have h := (a1_of_a0_after le_rfl ha j j hj (by simp [after_apply])).1
      exact critical_of_a1 hk h
    refine ⟨Or.inr he, fun _ => ⟨⟨p, hp⟩, hcritical, ?_⟩⟩
    let j := exactSlowNimMRuleKept x
    have hmin : ∀ i, x j ≤ x i := by
      rcases kept_spec x with ⟨-, h⟩ | ⟨h, -⟩
      · exact fun i => h i (he i)
      · exact (h p (he p)).elim
    have hjcap : x j < m := (hmin p).trans_lt hp
    have hpos := a0_positive_away le_rfl ha hjcap
    have hreduce (i) (hi : x i = m) : after x j i < x i := by
      have hne : i ≠ j := by
        intro h
        subst i
        omega
      simp only [after_apply, hne, ite_false]
      omega
    exact ⟨hreduce, hcritical _ ((mem_moves_iff hk).mpr ⟨j, hpos, rfl⟩) hreduce⟩
  · exact (Nat.not_even_iff_odd.mpr ha.2.2.1 hm).elim
  · exact ⟨Or.inl hB.2.2.2, fun h => (Nat.not_even_iff_odd.mpr (hB.2.2.2 0) (h 0)).elim⟩

open exactSlowNim_critical_of_even in
/-- **Unique critical-lowering move for odd parameter (Corollary 1 (ii)).** Let $k \ge 2$, let
$m$ be odd, and let $x \in \mathbb{N}^{k+1}$ be an $m$-critical position of Slow$\{k\}$-Nim on
$k + 1$ stacks. Then $x$ has exactly one even entry $x_i$. The position $x'$ obtained from $x$ by
removing one token from every pile other than $i$ is an option of $x$, it is the only option of
$x$ that is $(m - 1)$-critical, and it is the position reached from $x$ by the M-move.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Corollary 1 (ii). -/
public theorem exactSlowNim_critical_of_odd {k m : ℕ} (hk : 2 ≤ k) (hm : Odd m)
    (x : Fin (k + 1) → ℕ) (hx : IsExactSlowNimCritical k m x) :
    ∃ i, Even (x i) ∧ (∀ j, Even (x j) → j = i) ∧
      slowANimAfter x (Finset.univ.erase i) ∈ slowANimMoves {k} x ∧
      (∀ y ∈ slowANimMoves {k} x,
        IsExactSlowNimCritical k (m - 1) y ↔ y = slowANimAfter x (Finset.univ.erase i)) ∧
      exactSlowNimMRuleMove x = slowANimAfter x (Finset.univ.erase i) := by
  have hk0 : 0 < k := by omega
  have ha : IsExactSlowNimBasicA1 k m x := by
    rcases basic_of_critical hk0 hx with h | h | h
    · exact (Nat.not_even_iff_odd.mpr hm h.2.2.1).elim
    · exact h
    · exact (Nat.not_even_iff_odd.mpr hm h.2.2.1).elim
  obtain ⟨i, hi, hu⟩ := ha.2.2.2
  have hkept : exactSlowNimMRuleKept x = i :=
    hu _ ((kept_spec x).resolve_right (fun h => h.1 i hi)).1
  have hxval : Value k x = m := (smith_eq_value hk0 x).symm.trans hx.1
  obtain ⟨-, hpos, hval⟩ := a1_support_moves hk0 le_rfl (hxval.symm ▸ ha)
  rw [hkept] at hpos hval
  rw [hxval] at hval
  refine ⟨i, hi, hu, (mem_moves_iff hk0).mpr ⟨i, hpos, rfl⟩, ?_, ?_⟩
  · have hcritical : IsExactSlowNimCritical k (m - 1) (after x i) := by
      refine ⟨(smith_eq_value hk0 _).trans hval, fun z hz => ?_⟩
      have hsum := after_sum x i hpos
      rw [ha.1] at hsum
      have hsum' : ∑ p, after x i p = k * (m - 1) := by
        rw [Nat.mul_sub_left_distrib, Nat.mul_one]
        omega
      have hlt := (mul_value_le_sum hk0 z).trans_lt
        ((Fintype.sum_strictMono hz).trans_eq hsum')
      rw [smith_eq_value hk0]
      exact (Nat.lt_of_mul_lt_mul_left hlt).ne
    intro y hy
    refine ⟨fun hc => ?_, fun h => h.symm ▸ hcritical⟩
    obtain ⟨j, -, rfl⟩ := (mem_moves_iff hk0).mp hy
    by_cases hji : j = i
    · simp [hji]
    have hodd (p) (hp : p ≠ i) : Odd (x p) :=
      Nat.not_even_iff_odd.mp (fun h => hp (hu p h))
    have hjodd : Odd (after x j j) := by simpa [after_apply] using hodd j hji
    have hij : i ≠ j := Ne.symm hji
    obtain ⟨p, -, hp⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({i, j} : Finset (Fin (k + 1)))) (t := Finset.univ) (by
        simp [hij]
        omega)
    have hpi : p ≠ i := fun h => hp (by simp [h])
    have hpj : p ≠ j := fun h => hp (by simp [h])
    have hpe : Even (after x j p) := by
      have := Nat.odd_iff.mp (hodd p hpi)
      simp only [after_apply, hpj, ite_false, Nat.even_iff]
      omega
    have hme : Even (m - 1) := by
      have := Nat.odd_iff.mp hm
      rw [Nat.even_iff]
      omega
    -- The other legal move has mixed parity, incompatible with even criticality, including at 0.
    rcases basic_of_critical hk0 hc with h | h | h
    · exact (Nat.not_even_iff_odd.mpr hjodd (h.2.2.2 j)).elim
    · exact (Nat.not_even_iff_odd.mpr h.2.2.1 hme).elim
    · exact (Nat.not_even_iff_odd.mpr (h.2.2.2 p) hpe).elim
  · simp only [exactSlowNimMRuleMove, hkept]

/-- In an impartial game, a position is a P-position exactly when its Smith remoteness is even. -/
private theorem smithRemoteness_even_iff_isP (G : SpragueGrundy.ImpartialGame) (p : G.Pos) :
    Even (SpragueGrundy.smithRemoteness G p) ↔ SpragueGrundy.IsP G p := by
  classical
  induction p using (SpragueGrundy.wfRel G).induction with
  | h p ih =>
    let values := (G.moves p).image (SpragueGrundy.smithRemoteness G)
    have hfilter : ¬ (values.filter Even).Nonempty ↔ SpragueGrundy.IsP G p := by
      rw [SpragueGrundy.isP_iff]
      constructor
      · intro he q hq hp
        exact he ⟨_, Finset.mem_filter.mpr
          ⟨Finset.mem_image_of_mem _ hq, (ih q hq).mpr hp⟩⟩
      · rintro hp ⟨v, hv⟩
        obtain ⟨hv, hev⟩ := Finset.mem_filter.mp hv
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hv
        exact hp q hq ((ih q hq).mp hev)
    rw [← hfilter, SpragueGrundy.smithRemoteness_eq]
    split_ifs with he hne
    · have hmin := (Finset.mem_filter.mp (Finset.min'_mem _ he)).2
      exact iff_of_false (Nat.not_even_iff_odd.mpr ((by decide : Odd 1).add_even hmin))
        (not_not_intro he)
    · have hodd : Odd (values.max' hne) := Nat.not_even_iff_odd.mp fun h =>
        he ⟨_, Finset.mem_filter.mpr ⟨Finset.max'_mem _ hne, h⟩⟩
      exact iff_of_true ((by decide : Odd 1).add_odd hodd) he
    · exact iff_of_true (by decide) he

open exactSlowNim_critical_of_even in
/-- **Proposition 1 (odd P-positions of exact slow k-NIM).** Let $0 < k$ and let
$\mathrm{NIM}(k + 1, k)$ be Slow$A$-Nim on $k + 1$ stacks with $A = \{k\}$. A position
$x = (x_0, \dots, x_k)$ of $\mathrm{NIM}(k + 1, k)$ all of whose entries are odd is a P-position if
and only if there is a natural number $m$ such that $x_0 + \dots + x_k = km + k - 1$, $x_i < m$
for every $i$, and $m$ is even.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Proposition 1. -/
public theorem exactSlowNim_odd_isP_iff {k : ℕ} (hk : 0 < k) (x : Fin (k + 1) → ℕ)
    (hx : ∀ i, Odd (x i)) :
    SpragueGrundy.IsP (slowANimGame (k + 1) {k}) x ↔
      ∃ m, ∑ i, x i = k * m + k - 1 ∧ (∀ i, x i < m) ∧ Even m := by
  rw [← smithRemoteness_even_iff_isP (slowANimGame (k + 1) {k}) x,
    ← exactSlowNimBasicValue_eq_smithRemoteness hk x]
  constructor
  · intro hb
    obtain ⟨z, hzx, hA0 | hA1 | hB⟩ := exists_supports_exactSlowNimBasicValue k x
    · -- All piles have room for one more stone above an all-even vector.
      have hlt (i) : z i < x i :=
        lt_of_le_of_ne (hzx i) fun he => (Nat.not_even_iff_odd.mpr (hx i)) (he ▸ hA0.2.2.2 i)
      have hzAfter : z ≤ after x 0 := by
        intro i
        rw [after_apply]
        split_ifs
        · exact hzx i
        · exact Nat.le_pred_of_lt (hlt i)
      obtain ⟨w, hwx, hw⟩ := odd_support_of_even_after hk 0
        (fun i _ => Nat.zero_lt_of_lt (hlt i)) hzAfter (Or.inl hA0)
      exact (Nat.not_succ_le_self _ (le_value hk hwx (Or.inr (Or.inl hw)))).elim
    · exact (Nat.not_even_iff_odd.mpr hA1.2.2.1 hb).elim
    · obtain rfl := (exactSlowNimBasicValue_of_supports_basicB hk x z hzx hB).1
      exact ⟨_, hB.1, hB.2.1, hB.2.2.1⟩
  · rintro ⟨m, hsum, hlt, hm⟩
    have hB : IsExactSlowNimBasicB k m x := ⟨hsum, hlt, hm, hx⟩
    have hle : m ≤ Value k x := le_value hk le_rfl (Or.inr (Or.inr hB))
    have hsum_lt : (∑ i, x i) < k * (m + 1) := by
      rw [hsum, Nat.mul_succ]
      omega
    have hval : Value k x = m := le_antisymm
      (Nat.le_of_lt_succ (Nat.lt_of_mul_lt_mul_left ((mul_value_le_sum hk x).trans_lt hsum_lt))) hle
    simpa only [hval] using hm

/-- **Binary encoding of natural numbers.** The bitstring encoding of $\mathbb{N}$ that writes
$0$ as the empty string and a positive integer $n$ as its binary digits, least significant bit
first, together with Mathlib's decoding map, which recovers $n$ from its encoding. It is a
definition, not an instance; Theorem 3 installs it locally so that lists of piles are encoded as
self-delimiting binary blocks.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Theorem 3 ("integers are presented in binary"). -/
@[instance_reducible]
public def exactSlowNimBinaryNatEncoding : BitstringEncoding ℕ where
  toEncoding := Computability.encodingNatBool

/-- **Remoteness of exact slow k-NIM from a list of piles.** For a list $(x_0, \dots, x_{n-1})$
of natural numbers of length $n$, the value is Smith's remoteness of the position
$(x_0, \dots, x_{n-1})$ of Slow$A$-Nim on $n$ stacks with $A = \{n - 1\}$, where $0 - 1 = 0$. For
$n = k + 1$ this game is exact slow $k$-NIM $\mathrm{NIM}(k + 1, k)$, so $k$ is part of the input;
the empty list gives the game on no stacks.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Theorem 3. -/
public noncomputable def exactSlowNimRemotenessOfList (l : List ℕ) : ℕ :=
  SpragueGrundy.smithRemoteness (slowANimGame l.length {l.length - 1}) fun i => l.get i

end

end MetaMathlibExt
