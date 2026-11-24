/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Fin.VecNotation
public import MathlibExt.Computability.Complexity
public import MathlibExt.GameTheory.SmithRemoteness
public import WantedExt.Combinatorics.SlowANimWanted

/-!
# Remoteness of Exact Slow `k`-NIM with `k + 1` piles

Statements from Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi,
*On Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1
(arXiv:2304.06498).

`NIM(k + 1, k)` is played on `k + 1` piles (a position is `x : Fin (k + 1) → ℕ`); a move removes
exactly one stone from each of `k` nonempty piles. This is the existing Slow`A`-Nim game
`slowANimGame (k + 1) {k}`, whose options are `slowANimMoves {k} x`. Smith's remoteness function
is `SpragueGrundy.smithRemoteness` (`MathlibExt/GameTheory/SmithRemoteness.lean`). The paper
compares positions after sorting their entries; since the game, the remoteness, and the
conditions below are invariant under permuting piles, "`R(y) ≠ m` for
every `y < x`" is equivalent to the same condition for the componentwise (`Pi`) order used here.
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
    IsExactSlowNimBasicA1 k b z ∨ IsExactSlowNimBasicB k b z) (m := 0) (Nat.zero_le _) ⟨fun _ => 0, fun i => Nat.zero_le _,
    Or.inl ⟨by simp, fun _ => le_rfl, ⟨0, rfl⟩, fun _ => ⟨0, rfl⟩⟩⟩

/-- **$m$-critical positions of exact slow $k$-NIM with $k + 1$ piles (Theorem 1).** Let $k \ge 1$
and $m$ be natural numbers, and let $x = (x_0, \dots, x_k)$ be a position of
$\mathrm{NIM}(k + 1, k)$, the game on $k + 1$ piles in which a move removes one stone from each
of exactly $k$ nonempty piles. Call $x$ $m$-critical when its Smith remoteness is $m$ and no
position $y < x$ (that is, $y_i \le x_i$ for every $i$ and $y \ne x$) has remoteness $m$. Then
$x$ is $m$-critical if and only if either
(A) $x_0 + \dots + x_k = km$, $x_i \le m$ for every $i$, every $x_i$ is even if $m$ is even,
and exactly one $x_i$ is even if $m$ is odd; or
(B) $x_0 + \dots + x_k = km + k - 1$, $x_i < m$ for every $i$, $m$ is even, and every $x_i$ is
odd.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Theorem 1. -/
public theorem_wanted isExactSlowNimCritical_iff {k : ℕ} (hk : 0 < k) (m : ℕ)
    (x : Fin (k + 1) → ℕ) :
    IsExactSlowNimCritical k m x ↔
      (∑ i, x i = k * m ∧ (∀ i, x i ≤ m) ∧ (Even m → ∀ i, Even (x i)) ∧
          (Odd m → ∃! i, Even (x i))) ∨
        (∑ i, x i = k * m + k - 1 ∧ (∀ i, x i < m) ∧ Even m ∧ ∀ i, Odd (x i))

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
public theorem_wanted exactSlowNim_critical_of_even {k m : ℕ} (hk : 0 < k) (hm0 : 0 < m)
    (hm : Even m) (x : Fin (k + 1) → ℕ) (hx : IsExactSlowNimCritical k m x) :
    ((∀ i, Odd (x i)) ∨ (∀ i, Even (x i))) ∧
      ((∀ i, Even (x i)) →
        (∃ i, x i < m) ∧
          (∀ y ∈ slowANimMoves {k} x, (∀ i, x i = m → y i < x i) →
            IsExactSlowNimCritical k (m - 1) y) ∧
          (∀ i, x i = m → exactSlowNimMRuleMove x i < x i) ∧
          IsExactSlowNimCritical k (m - 1) (exactSlowNimMRuleMove x))

/-- **Unique critical-lowering move for odd parameter (Corollary 1 (ii)).** Let $k \ge 2$, let
$m$ be odd, and let $x \in \mathbb{N}^{k+1}$ be an $m$-critical position of Slow$\{k\}$-Nim on
$k + 1$ stacks. Then $x$ has exactly one even entry $x_i$. The position $x'$ obtained from $x$ by
removing one token from every pile other than $i$ is an option of $x$, it is the only option of
$x$ that is $(m - 1)$-critical, and it is the position reached from $x$ by the M-move.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Corollary 1 (ii). -/
public theorem_wanted exactSlowNim_critical_of_odd {k m : ℕ} (hk : 2 ≤ k) (hm : Odd m)
    (x : Fin (k + 1) → ℕ) (hx : IsExactSlowNimCritical k m x) :
    ∃ i, Even (x i) ∧ (∀ j, Even (x j) → j = i) ∧
      slowANimAfter x (Finset.univ.erase i) ∈ slowANimMoves {k} x ∧
      (∀ y ∈ slowANimMoves {k} x,
        IsExactSlowNimCritical k (m - 1) y ↔ y = slowANimAfter x (Finset.univ.erase i)) ∧
      exactSlowNimMRuleMove x = slowANimAfter x (Finset.univ.erase i)

/-- **Proposition 1 (odd P-positions of exact slow k-NIM).** Let $0 < k$ and let
$\mathrm{NIM}(k + 1, k)$ be Slow$A$-Nim on $k + 1$ stacks with $A = \{k\}$. A position
$x = (x_0, \dots, x_k)$ of $\mathrm{NIM}(k + 1, k)$ all of whose entries are odd is a P-position if
and only if there is a natural number $m$ such that $x_0 + \dots + x_k = km + k - 1$, $x_i < m$
for every $i$, and $m$ is even.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Proposition 1. -/
public theorem_wanted exactSlowNim_odd_isP_iff {k : ℕ} (hk : 0 < k) (x : Fin (k + 1) → ℕ)
    (hx : ∀ i, Odd (x i)) :
    SpragueGrundy.IsP (slowANimGame (k + 1) {k}) x ↔
      ∃ m, ∑ i, x i = k * m + k - 1 ∧ (∀ i, x i < m) ∧ Even m

/-- **Theorem 2 (the M-rule realizes Smith's remoteness).** Let $0 < k$ and let
$\mathrm{NIM}(k + 1, k)$ be exact slow $k$-NIM on $k + 1$ piles, that is, Slow$A$-Nim on $k + 1$
stacks with $A = \{k\}$, where a move removes one stone from each of exactly $k$ nonempty piles.
For every position $x$ of $\mathrm{NIM}(k + 1, k)$, the M-rule length $M(x)$ equals Smith's
remoteness $R(x)$ of $x$ in $\mathrm{NIM}(k + 1, k)$.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Theorem 2. -/
public theorem_wanted exactSlowNimMRuleLength_eq_smithRemoteness {k : ℕ} (hk : 0 < k)
    (x : Fin (k + 1) → ℕ) :
    exactSlowNimMRuleLength k x = SpragueGrundy.smithRemoteness (slowANimGame (k + 1) {k}) x

/-- **Positions supported by a (B) basic vector (Lemma 1).** Let $k \ge 1$, let $B$ be the
basic-vector value on $\mathbb{N}^{k+1}$, and let $x, z \in \mathbb{N}^{k+1}$ with $z \le x$
componentwise, where $z$ is a basic vector of type (B) with parameter $B(x)$. Then $x = z$, and
every option $x'$ of $x$ in Slow$\{k\}$-Nim on $k + 1$ stacks (a move removes one token from
each of exactly $k$ nonempty stacks) satisfies $B(x') = B(x) - 1$, where subtraction is
truncated at $0$.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Lemma 1. -/
public theorem_wanted exactSlowNimBasicValue_of_supports_basicB {k : ℕ} (hk : 0 < k)
    (x z : Fin (k + 1) → ℕ) (hzx : z ≤ x)
    (hz : IsExactSlowNimBasicB k (exactSlowNimBasicValue k x) z) :
    x = z ∧ ∀ x' ∈ slowANimMoves {k} x,
      exactSlowNimBasicValue k x' = exactSlowNimBasicValue k x - 1

/-- **Moves at a position supported by an (A0) basic vector (Lemma 2).** Let $k \ge 1$, let
$B$ be the basic-vector value on $\mathbb{N}^{k+1}$, and let $x, z \in \mathbb{N}^{k+1}$ with
$z \le x$ componentwise, where $z$ is a basic vector of type (A0) with parameter $B(x)$. Let $j$
be a pile with $x_i > 0$ for every $i \ne j$, and let $x'$ be obtained from $x$ by removing one
token from every pile other than $j$. Then $B(x') \le B(x) - 1$ and $B(x')$ is odd. Moreover, if
$z_j < B(x)$, or if $z_j = B(x)$ and $z_i < \min(B(x), x_i)$ for some $i$, then
$B(x') = B(x) - 1$. Here $B(x) - 1$ is truncated subtraction in $\mathbb{N}$.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Lemma 2. -/
public theorem_wanted exactSlowNimBasicValue_of_supports_basicA0 {k : ℕ} (hk : 0 < k)
    (x z : Fin (k + 1) → ℕ) (hzx : z ≤ x)
    (hz : IsExactSlowNimBasicA0 k (exactSlowNimBasicValue k x) z) (j : Fin (k + 1))
    (hj : ∀ i, i ≠ j → 0 < x i) :
    exactSlowNimBasicValue k (slowANimAfter x (Finset.univ.erase j)) ≤
        exactSlowNimBasicValue k x - 1 ∧
      Odd (exactSlowNimBasicValue k (slowANimAfter x (Finset.univ.erase j))) ∧
      (z j < exactSlowNimBasicValue k x ∨
          (z j = exactSlowNimBasicValue k x ∧
            ∃ i, z i < min (exactSlowNimBasicValue k x) (x i)) →
        exactSlowNimBasicValue k (slowANimAfter x (Finset.univ.erase j)) =
          exactSlowNimBasicValue k x - 1)

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
public theorem_wanted exactSlowNimBasicValue_of_supports_basicA1 {k : ℕ} (hk : 0 < k)
    (x z : Fin (k + 1) → ℕ) (hzx : z ≤ x)
    (hz : IsExactSlowNimBasicA1 k (exactSlowNimBasicValue k x) z) :
    (∀ x' ∈ slowANimMoves {k} x, exactSlowNimBasicValue k x - 2 ≤ exactSlowNimBasicValue k x') ∧
      exactSlowNimBasicValue k (exactSlowNimMRuleMove x) = exactSlowNimBasicValue k x - 1

/-- **Basic-vector value equals Smith's remoteness (Lemma 4).** Let $k \ge 1$ and consider
Slow$\{k\}$-Nim on $k + 1$ stacks, in which a move removes one token from each of exactly $k$
nonempty stacks. For every position $x \in \mathbb{N}^{k+1}$, the basic-vector value $B(x)$
equals Smith's remoteness of $x$ in this game.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Lemma 4. -/
public theorem_wanted exactSlowNimBasicValue_eq_smithRemoteness {k : ℕ} (hk : 0 < k)
    (x : Fin (k + 1) → ℕ) :
    exactSlowNimBasicValue k x = SpragueGrundy.smithRemoteness (slowANimGame (k + 1) {k}) x

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

/-- **Theorem 3 (Smith's remoteness of exact slow k-NIM is polynomial-time computable).** The map
sending a list $(x_0, \dots, x_{n-1})$ of natural numbers of length $n$ to Smith's remoteness of
the position $(x_0, \dots, x_{n-1})$ of Slow$A$-Nim on $n$ stacks with $A = \{n - 1\}$ (where
$0 - 1 = 0$) is polynomial-time computable. Here natural numbers, in the input and the output,
are encoded in binary, and a list is encoded as the concatenation of the self-delimiting forms
of the encodings of its entries. For $n = k + 1$ this is the game $\mathrm{NIM}(k + 1, k)$, so $k$
is part of the input.

Source: Vladimir Gurvich, Denis Martynov, Vladislav Maximchuk, and Michael Vyalyi, *On
Remoteness Functions of Exact Slow k-NIM with k+1 Piles*, INTEGERS 24 (2024), Article G1,
Theorem 3. -/
public theorem_wanted exactSlowNimRemoteness_isPolyTime :
    letI : BitstringEncoding ℕ := exactSlowNimBinaryNatEncoding
    ComplexityTheory.IsPolyTime exactSlowNimRemotenessOfList

end

end MetaMathlibExt
