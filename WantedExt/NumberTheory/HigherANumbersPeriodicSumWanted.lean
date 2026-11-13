/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# Higher `a`-numbers in `ℤ_p`-towers via lattice points

The periodic-sum lemmas of Section 2.2 of Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran,
James Upton, and Carol Wu, *Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*,
INTEGERS 26 (2026), Article A78. Sequences are indexed by `i ≥ 1`; the value at `0` is never used.
The record's `f̄` (overline lost in extraction) is the average of `f` over one period; it is the
only value for which the identity holds at `N = L`.

The remaining statements follow the paper's Sections 2-4: base-`p` digits of rationals and their
periods (`basePDigit`, `basePPeriod`, `basePDelay`), the rounding indicator `δ` and its variant
`δ₀`, sums of floors and of `δ`, and the expansion of the higher `a`-numbers. Statements about
`a^r(X_n)` use the lattice-point expression of Theorem 1 (`higherANumberLatticeCount`). Statements
follow the arXiv text (arXiv:2407.13969v3); Theorem 4 follows the journal version.
-/

open Finset

namespace MetaMathlibExt

@[expose] public section

/-- **Sum of a periodic sequence.** Let $K$ be a field of characteristic zero, let
$f : \mathbb{N} \to K$ and let $L \ge 1$ be a natural number such that $f(i + L) = f(i)$ for
all $i \ge 1$. Let $\bar f = \frac{1}{L} \sum_{k=1}^{L} f(k)$. Then for every natural number $N$,
$$\sum_{i=1}^{N} f(i) = N \bar f + \sum_{k=1}^{N \bmod L} \left(f(k) - \bar f\right).$$

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Lemma 1 (Sum of a periodic sequence) (`integers-2026-A78-lem-1`). -/
public theorem_wanted sum_Icc_of_periodic {K : Type*} [Field K] [CharZero K] (f : ℕ → K)
    {L : ℕ} (hL : 0 < L) (hf : ∀ i, 1 ≤ i → f (i + L) = f i) (N : ℕ) :
    ∑ i ∈ Icc 1 N, f i =
      N * ((∑ k ∈ Icc 1 L, f k) / L) +
        ∑ k ∈ Icc 1 (N % L), (f k - (∑ k ∈ Icc 1 L, f k) / L)

/-- **Sum of an eventually periodic sequence.** Let $K$ be a field of characteristic zero, let
$f : \mathbb{N} \to K$, and let $L \ge 1$ and $D \ge 1$ be natural numbers such that
$f(i + L) = f(i)$ for all $i \ge D$. Let $\bar f = \frac{1}{L} \sum_{k=D}^{D+L-1} f(k)$ be the
average over one period. Then for every natural number $N \ge D - 1$,
$$\sum_{i=1}^{N} f(i) = \sum_{i=1}^{D-1} f(i) + (N - D + 1) \bar f +
\sum_{k=1}^{(N-D+1) \bmod L} \left(f(k + D - 1) - \bar f\right).$$

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Corollary 1 (Sum of an eventually periodic sequence) (`integers-2026-A78-cor-1`). -/
public theorem_wanted sum_Icc_of_eventually_periodic {K : Type*} [Field K] [CharZero K]
    (f : ℕ → K) {L D : ℕ} (hL : 0 < L) (hD : 1 ≤ D) (hf : ∀ i, D ≤ i → f (i + L) = f i)
    {N : ℕ} (hN : D - 1 ≤ N) :
    ∑ i ∈ Icc 1 N, f i =
      ∑ i ∈ Icc 1 (D - 1), f i + ((N + 1 - D : ℕ) : K) * ((∑ k ∈ Ico D (D + L), f k) / L) +
        ∑ k ∈ Icc 1 ((N + 1 - D) % L), (f (k + D - 1) - (∑ k ∈ Ico D (D + L), f k) / L)


/-- **Base-$p$ digits of a rational number.** For a natural number $p$, a rational number $x$ and
an integer $k$, the $k$-th base-$p$ digit of $x$ is $[p^k](x) = \lfloor x / p^k \rfloor \bmod p$;
for $p \ge 1$ this is the residue of $\lfloor x / p^k \rfloor$ modulo $p$ in $\{0, \dots, p - 1\}$.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Section 2.2 (definition of `[p^k](x)`). -/
def basePDigit (p : ℕ) (x : ℚ) (k : ℤ) : ℤ := ⌊x / (p : ℚ) ^ k⌋ % p

/-- **Base-5 digits of 2/3.** Writing $[5^j](x)$ for the $j$-th base-$5$ digit of a rational
number $x$, we have $[5^{-1}](2/3) = 3$, $[5^{-2}](2/3) = 1$ and $[5^0](2/3) = 0$.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Section 2.2 (base-`5` example
`2/3 = .3131…`). -/
theorem basePDigit_five_two_thirds :
    basePDigit 5 (2 / 3) (-1) = 3 ∧ basePDigit 5 (2 / 3) (-2) = 1 ∧ basePDigit 5 (2 / 3) 0 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [basePDigit, zpow_neg]

/-- **Prime-to-$p$ part of the denominator.** For a natural number $p$ and a rational number
$x$ whose denominator in lowest terms is $b \ge 1$, $x_D$ is the natural number $b / p^k$, where
$p^k$ is the largest power of $p$ dividing $b$ (with $k = 0$ when $p = 1$).

For a prime $p$ and $x > 0$ this gives $x = p^{v_p(x)} x_N / x_D$ with $x_N$ and $x_D$ coprime to
$p$, where $x_N$ is the prime-to-$p$ part of the numerator (Notation 2).

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Notation 2 (`x_D`). -/
def primeToPDen (p : ℕ) (x : ℚ) : ℕ := x.den / p ^ padicValNat p x.den

/-- **Prime-to-$p$ part of the numerator.** For a natural number $p$ and a rational number $x$
whose numerator in lowest terms is $a$, $x_N$ is the natural number $|a| / p^k$, where $p^k$ is
the largest power of $p$ dividing $|a|$, with $k = 0$ when $p = 1$ or $a = 0$. In particular
$x_N = 0$ when $x = 0$.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Notation 2 (`x_N`). -/
def primeToPNum (p : ℕ) (x : ℚ) : ℕ := x.num.natAbs / p ^ padicValNat p x.num.natAbs

/-- **The prime-to-$p$ parts of $1$.** For every natural number $p$, the prime-to-$p$ part $x_D$
of the denominator and the prime-to-$p$ part $x_N$ of the numerator of $x = 1$ are both $1$.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Notation 2 (`x_N`, `x_D` of `1`). -/
theorem primeToPDen_one_primeToPNum_one (p : ℕ) : primeToPDen p 1 = 1 ∧ primeToPNum p 1 = 1 := by
  simp [primeToPDen, primeToPNum]

/-- **Period of the base-$p$ expansion.** For a natural number $p$ and a rational number $x$, let
$x_D$ be the denominator of $x$ in lowest terms divided by the largest power of $p$ dividing it.
The period $L_x$ of the base-$p$ expansion of $x$ is the multiplicative order of $p$ modulo $x_D$:
the least $n \ge 1$ with $p^n \equiv 1 \pmod{x_D}$, or $0$ if there is no such $n$. For prime $p$
this is the order of $p$ in $(\mathbb{Z}/x_D\mathbb{Z})^\times$.

For prime $p$ and $x > 0$, Lemma 2 of the source identifies $L_x$ with the minimal period of the
base-$p$ digits of $x$.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Definition of `L_x` and Lemma 2. -/
noncomputable def basePPeriod (p : ℕ) (x : ℚ) : ℕ := orderOf (p : ZMod (primeToPDen p x))

/-- **The base-$p$ expansion of $1$ has period $1$.** For every natural number $p$, the period
$L_1$ of the base-$p$ expansion of $1$ equals $1$.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Lemma 2 (`L_x = 1` when `x_D = 1`). -/
theorem basePPeriod_one (p : ℕ) : basePPeriod p 1 = 1 := by
  rw [basePPeriod, (primeToPDen_one_primeToPNum_one p).1]
  exact orderOf_eq_one_iff.mpr (Subsingleton.elim _ _)

/-- **Delay of the base-$p$ expansion.** For a natural number $p$ and a rational number $x$, the
delay of the base-$p$ expansion of $x$ is $D_x = -v_p(x)$, where $v_p$ is the $p$-adic valuation
(with $v_p(0) = 0$).

For prime $p$ and $x > 0$, Lemma 2 of the source identifies $D_x$ with the minimal delay of the
base-$p$ digits of $x$.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Definition of `D_x` and Lemma 2. -/
noncomputable def basePDelay (p : ℕ) (x : ℚ) : ℤ := -padicValRat p x

/-- **The delay of $1/p$ is $1$.** For every prime $p$, the delay of the base-$p$ expansion of
$1/p$ is $D_{1/p} = -v_p(1/p) = 1$, where $v_p$ is the $p$-adic valuation.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Lemma 2 (`D_{1/p} = 1`). -/
theorem basePDelay_inv_self (p : ℕ) [Fact p.Prime] : basePDelay p (p : ℚ)⁻¹ = 1 := by
  simp [basePDelay, padicValRat.inv]

/-- **Average repeating digit.** For a natural number $p$ and a rational number $x$, let $D_x$ be
the delay and $L_x$ the period of the base-$p$ expansion of $x$, and let $[p^k](x)$ be its
$k$-th base-$p$ digit. The average repeating digit of $x$ is
$$\bar{x} = \frac{1}{L_x} \sum_{k=D_x+1}^{D_x+L_x} [p^{-k}](x),$$
with $\bar{x} = 0$ when $L_x = 0$.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Definition of `x̄`. -/
noncomputable def basePDigitAverage (p : ℕ) (x : ℚ) : ℚ :=
  (∑ k ∈ Icc (basePDelay p x + 1) (basePDelay p x + basePPeriod p x), (basePDigit p x (-k) : ℚ)) /
    basePPeriod p x

/-- **The ratio $\tau = (p + 1)/d$.** For natural numbers $p$ and $d$, $\tau$ is the rational
number $(p + 1)/d$, which is $0$ when $d = 0$.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Notation 1 (i). -/
def towerTau (p d : ℕ) : ℚ := ((p : ℚ) + 1) / d

/-- **The constant $\gamma$.** For natural numbers $p$, $d$ and $r$,
$\gamma = ((p - 1) r + (p + 1))/d$, a rational number (taken to be $0$ when $d = 0$).

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Notation 1 (ii). -/
def towerGamma (p d r : ℕ) : ℚ := (((p : ℚ) - 1) * r + (p + 1)) / d

/-- **Values of $\tau$ and $\gamma$ for $p = 5$, $d = 4$, $r = 2$.** With $\tau = (p + 1)/d$ and
$\gamma = ((p - 1)r + (p + 1))/d$, taking $p = 5$, $d = 4$ and $r = 2$ gives $\tau = 3/2$ and
$\gamma = 7/2$.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Notation 1 (`p = 5`, `d = 4`,
`r = 2`). -/
theorem towerTau_towerGamma_five_four : towerTau 5 4 = 3 / 2 ∧ towerGamma 5 4 2 = 7 / 2 := by
  constructor <;> norm_num [towerTau, towerGamma]

/-- **Lexicographic order on integer sequences.** For sequences
$a, b \colon \mathbb{N} \to \mathbb{Z}$, $a$ is lexicographically larger than $b$ when there is
an index $m$ with $a_j = b_j$ for all $j < m$ and $a_m > b_m$. This is the order used in
Definition 1.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Equation (1). -/
def SeqLexGt (a b : ℕ → ℤ) : Prop := ∃ m, (∀ j < m, a j = b j) ∧ b m < a m

/-- **The rounding indicator $\delta$.** Let $p$, $d$ and $i$ be natural numbers and let
$\tau = (p + 1)/d$. For a rational $x$ and an integer $k$, write $[p^k](x)$ for the residue of
$\lfloor x / p^k \rfloor$ modulo $p$, the $k$-th base-$p$ digit of $x$. Then $\delta(i) = 0$ if
the integer-part digits $([p^n](\tau i))_{n \ge 0}$ are lexicographically larger than the
fractional digits $([p^{-1-n}](\tau i))_{n \ge 0}$, that is, the two sequences agree at every
index below some $m$ and the first is larger at $m$; otherwise $\delta(i) = 1$.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Definition of `δ`. -/
noncomputable def higherANumberDelta (p d i : ℕ) : ℕ :=
  open Classical in
  if SeqLexGt (fun n => basePDigit p (towerTau p d * i) n)
      (fun n => basePDigit p (towerTau p d * i) (-1 - n)) then 0 else 1

/-- **Two values of $\delta$ for $p = 5$ and $d = 4$.** For $p = 5$ and $d = 4$, so that
$\tau = (p + 1)/d = 3/2$, the rounding indicator satisfies $\delta(1) = 1$ and $\delta(2) = 0$.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78, Table 1 (`δ(1) = 1`, `δ(2) = 0` for
`p = 5`, `d = 4`). -/
theorem higherANumberDelta_five_four :
    higherANumberDelta 5 4 1 = 1 ∧ higherANumberDelta 5 4 2 = 0 := by
  constructor
  · unfold higherANumberDelta
    split_ifs with h
    · obtain ⟨m, hm, hlt⟩ := h
      rcases m with _ | m
      · norm_num [basePDigit, towerTau, zpow_neg] at hlt
      · have := hm 0 (by omega)
        norm_num [basePDigit, towerTau, zpow_neg] at this
    · rfl
  · unfold higherANumberDelta
    split_ifs with h
    · rfl
    · exact absurd ⟨0, by simp, by norm_num [basePDigit, towerTau, zpow_neg]⟩ h

/-- **The denominator $\tau_D$.** For natural numbers $p$ and $d$, $\tau_D$ is the denominator in
lowest terms of the rational number $\tau = (p + 1)/d$ (when $d = 0$, $\tau$ is taken to be $0$,
so $\tau_D = 1$).

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Notation 2 (`τ_D`). -/
def tauDen (p d : ℕ) : ℕ := (towerTau p d).den

/-- **$\tau_D = 1$ when $d = 1$.** For every natural number $p$, the denominator $\tau_D$ of
$\tau = (p + 1)/d$ in lowest terms equals $1$ when $d = 1$.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Notation 2 (`τ_D = 1` when `d = 1`). -/
theorem tauDen_one (p : ℕ) : tauDen p 1 = 1 := by
  simp only [tauDen, towerTau, Nat.cast_one, div_one]
  exact_mod_cast Rat.den_natCast (p + 1)

/-- **The variant $\delta_0$ of the rounding indicator.** For natural numbers $p$, $d$ and $i$, with
$\delta$ the rounding indicator for $p$ and $d$, the value $\delta_0(i)$ is $0$ if $p \mid i$, and
$\delta(i)$ otherwise.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Definition of `δ₀`. -/
noncomputable def higherANumberDeltaZero (p d i : ℕ) : ℕ :=
  if p ∣ i then 0 else higherANumberDelta p d i

/-- **The indicator $\delta_0$ vanishes at $0$.** For all natural numbers $p$ and $d$, the variant
$\delta_0$ of the rounding indicator for $p$ and $d$ satisfies $\delta_0(0) = 0$.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Definition of `δ₀` (`δ₀(0) = 0`). -/
theorem higherANumberDeltaZero_zero (p d : ℕ) : higherANumberDeltaZero p d 0 = 0 := by
  simp [higherANumberDeltaZero]

/-- **The lattice boundary $\mu$.** Let $p$, $d$ and $i$ be natural numbers and let
$\tau = (p + 1)/d$, taken to be $0$ when $d = 0$. For a rational $x$ and an integer $k$, write
$[p^k](x)$ for the residue of $\lfloor x/p^k \rfloor$ modulo $p$, the $k$-th base-$p$ digit
of $x$. Then $\mu(i)$ is $\lfloor \tau i \rfloor$ if the integer-part digit sequence
$([p^n](\tau i))_{n \ge 0}$ is lexicographically larger than the fractional digit sequence
$([p^{-1-n}](\tau i))_{n \ge 0}$, that is, the two sequences agree at every index below some
$m$ and the first is larger at $m$; otherwise $\mu(i) = \lceil \tau i \rceil$.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Definition 1 (`μ`). -/
noncomputable def towerMu (p d i : ℕ) : ℤ :=
  open Classical in
  if SeqLexGt (fun n => basePDigit p (towerTau p d * i) n)
      (fun n => basePDigit p (towerTau p d * i) (-1 - n)) then ⌊towerTau p d * i⌋
  else ⌈towerTau p d * i⌉

/-- **$\mu(2) = 3$ for $p = 5$ and $d = 4$.** For $p = 5$ and $d = 4$ the lattice boundary
$\mu(2)$ equals $3$; here $\tau = (p + 1)/d = 3/2$, so $\tau \cdot 2 = 3$ is an integer and
its floor and ceiling agree.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Definition 1 (`μ(2) = 3` for `p = 5`, `d = 4`, where `τ · 2 = 3`). -/
theorem towerMu_five_four_two : towerMu 5 4 2 = 3 := by
  unfold towerMu
  split_ifs <;> norm_num [towerTau]

/-- **The lattice-point count of Theorem 1.** For natural numbers $p$, $d$, $r$ and $n$, put
$\tau = (p + 1)/d$, $\gamma = ((p - 1) r + (p + 1))/d$ and $t_n = \lfloor \gamma^{-1} p^n \rfloor$
(a floor in $\mathbb{N}$, so $0$ for negative arguments), with the convention that division by
$0$ gives $0$; thus $\tau = \gamma = 0$ when $d = 0$, and $t_n = 0$ when $\gamma = 0$. For a
rational $x$ and an integer $k$ let $[p^k](x) = \lfloor x / p^k \rfloor \bmod p$, the base-$p$
digit of $x$ at $p^k$ when $p \ge 2$ (reduction mod $0$ is the identity). Let $\mu(i)$ be the
lattice boundary of Definition 1: $\mu(i) = \lfloor \tau i \rfloor$ if the sequence
$([p^k](\tau i))_{k \ge 0}$ is lexicographically larger than the sequence
$([p^{-1-k}](\tau i))_{k \ge 0}$, and $\mu(i) = \lceil \tau i \rceil$ otherwise. Let $\Delta_n$
be the set of pairs of integers $(i, j)$ with $t_n < i \le p^n$, $1 \le j \le p^n - 1$ and
$\mu(i) \le j$. The lattice-point count is the rational number
$r (p - 1) t_n (t_n + 1)/(2d) + |\Delta_n|$ (which is $|\Delta_n|$ when $d = 0$).

Theorem 1 (Booher, Cais, Kramer-Miller, Upton) identifies it with the higher $a$-number
$a^r(X_n)$ of a $\mathbb{Z}_p$-tower with minimal break ratios and ramification invariant
$d \mid p - 1$. Bounding $i$ by $p^n$ loses nothing when $\tau \ge 1$, since then
$\mu(i) \ge \lfloor \tau i \rfloor \ge i$.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Definition 2 and Theorem 1. -/
noncomputable def higherANumberLatticeCount (p d r n : ℕ) : ℚ :=
  (r : ℚ) * ((p : ℚ) - 1) * ⌊(p : ℚ) ^ n / towerGamma p d r⌋₊ *
      (⌊(p : ℚ) ^ n / towerGamma p d r⌋₊ + 1) / (2 * d) +
    (((Icc 1 (p ^ n) ×ˢ Icc 1 (p ^ n - 1)).filter fun ij : ℕ × ℕ =>
        ⌊(p : ℚ) ^ n / towerGamma p d r⌋₊ < ij.1 ∧ towerMu p d ij.1 ≤ ij.2).card : ℚ)

/-- **The lattice-point count at $p = 3$, $d = 2$, $r = 1$, $n = 0$.** Let
$\gamma = ((p - 1) r + (p + 1))/d$ and $t_n = \lfloor \gamma^{-1} p^n \rfloor$, and let $\Delta_n$
be the set of pairs of integers $(i, j)$ with $t_n < i \le p^n$, $1 \le j \le p^n - 1$ and
$\mu(i) \le j$, where $\mu$ is the lattice boundary of Definition 1. For $p = 3$, $d = 2$,
$r = 1$ and $n = 0$ the lattice-point count $r (p - 1) t_n (t_n + 1)/(2d) + |\Delta_n|$ of
Theorem 1 equals $0$: here $\gamma = 3$ and $t_0 = 0$, and $\Delta_0$ is empty because
$1 \le j \le p^0 - 1 = 0$ is impossible.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Definition 2 (`n = 0`, `p = 3`, `d = 2`, `r = 1`: no lattice points). -/
theorem higherANumberLatticeCount_three_two_one_zero : higherANumberLatticeCount 3 2 1 0 = 0 := by
  have h0 : ⌊(1 : ℚ) / 3⌋₊ = 0 := Nat.floor_eq_zero.mpr (by norm_num)
  have h1 : Icc 1 (3 ^ 0 - 1) = (∅ : Finset ℕ) := by decide
  norm_num [higherANumberLatticeCount, towerGamma]
  rw [h0, h1]
  simp

/-- **The correction term $A_{x^{-1}}$ for sums of floors.** For a natural number $p$, a rational
$x$ and a natural number $n$, let $x_D$ be the prime-to-$p$ part of the denominator of $x$, write
$\lbrace t \rbrace = t - \lfloor t \rfloor$ for the fractional part of $t$, and put
$y = x^{-1} p^n$ (with $y = 0$ when $x = 0$). Define
$$A_{x^{-1}}(n) = \frac12 \left(-\left(1 - \frac1{x_D}\right) + x (1 - \lbrace y \rbrace)\right)
\lbrace y \rbrace + \sum_{k=1}^{\lfloor y \rfloor \bmod x_D}
\left(\lbrace x k \rbrace - \frac12 \left(1 - \frac1{x_D}\right)\right),$$
where $\lfloor y \rfloor$ is read as $0$ when $y < 0$.

This is the periodic correction term of Proposition 4.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Proposition 4 (`A_{x^{-1}}`). -/
noncomputable def floorSumCorrection (p : ℕ) (x : ℚ) (n : ℕ) : ℚ :=
  1 / 2 * (-(1 - 1 / (primeToPDen p x : ℚ)) + x * (1 - Int.fract ((p : ℚ) ^ n / x))) *
      Int.fract ((p : ℚ) ^ n / x) +
    ∑ k ∈ Icc 1 (⌊(p : ℚ) ^ n / x⌋₊ % primeToPDen p x),
      (Int.fract (x * k) - 1 / 2 * (1 - 1 / (primeToPDen p x : ℚ)))

/-- **The correction $A_{x^{-1}}$ vanishes at $x = 1$.** For all natural numbers $p$ and $n$, the
periodic correction $A_{x^{-1}}(n)$ of Proposition 4 satisfies $A_1(n) = 0$.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Proposition 4 (`A_1 = 0`). -/
theorem floorSumCorrection_one (p n : ℕ) : floorSumCorrection p 1 n = 0 := by
  have h := (primeToPDen_one_primeToPNum_one p).1
  simp only [floorSumCorrection, h]
  simp only [div_one, Nat.cast_one, one_mul, sub_self, neg_zero, zero_add]
  have hf : Int.fract ((p : ℚ) ^ n) = 0 := by exact_mod_cast Int.fract_natCast (p ^ n)
  have hm : ⌊(p : ℚ) ^ n⌋₊ % 1 = 0 := Nat.mod_one _
  simp [hf, hm]

/-- **The correction term $F_y$ for sums of $\delta_0$.** For natural numbers $p$, $d$ and $e$
and a rational number $y$, let $\delta_0$ be the variant of the rounding indicator for $p$ and
$d$, let $\tau_D$ be the denominator in lowest terms of $\tau = (p + 1)/d$ (with $\tau = 0$ when
$d = 0$), and let $m = \lfloor y p^e \rfloor \bmod \tau_D p$, where $\lfloor y p^e \rfloor$ is
read as $0$ when $y p^e < 0$. Define
$$F_y(e) = \sum_{k=1}^{m} \left(\delta_0(k) - \frac12 \left(1 - \frac1p\right)
\left(1 - \frac1{\tau_D}\right)\right),$$
with the conventions that $1/0 = 0$ and that reduction modulo $0$ is the identity (both matter
only when $p = 0$).

In Lemma 9 this is used with $y = x^{-1}$, written $F_{x^{-1}}$.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Lemma 9 (`F_{x^{-1}}`). -/
noncomputable def deltaZeroSumCorrection (p d : ℕ) (y : ℚ) (e : ℕ) : ℚ :=
  ∑ k ∈ Icc 1 (⌊y * (p : ℚ) ^ e⌋₊ % (tauDen p d * p)),
    ((higherANumberDeltaZero p d k : ℚ) - 1 / 2 * (1 - 1 / (p : ℚ)) * (1 - 1 / (tauDen p d : ℚ)))

/-- **The correction $F_y$ vanishes at $y = 0$.** For all natural numbers $p$, $d$ and $e$, the
correction $F_y(e)$ of Lemma 9, taken at $y = 0$, is $0$.

Source: Booher, Hsieh, Rivera, Tran, Upton, and Wu, *Higher a-Numbers in `ℤ_p`-Towers via
Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Lemma 9 (`F_0 = 0`). -/
theorem deltaZeroSumCorrection_zero (p d e : ℕ) : deltaZeroSumCorrection p d 0 e = 0 := by
  simp [deltaZeroSumCorrection]

/-- **Digits of $m/d$ after the radix point are constant.** Let $p$ be a prime, $d$ a divisor of
$p - 1$, and write $[p^j](x)$ for the $j$-th base-$p$ digit of a rational number $x$. For every
positive integer $m$ and every integer $k \ge 1$, $[p^{-(k+1)}](m/d) = [p^{-k}](m/d)$; that is,
the base-$p$ expansion of $m/d$ is periodic with period $1$ right after the radix point.

The source assumes $p$ odd; for $p = 2$ only $d = 1$ occurs.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Corollary 2 (`integers-2026-A78-cor-2`). -/
public theorem_wanted basePDigit_div_periodic_one (p d : ℕ) [Fact p.Prime] (hd : d ∣ p - 1)
    (m : ℕ) (hm : 0 < m) (k : ℤ) (hk : 1 ≤ k) :
    basePDigit p ((m : ℚ) / d) (-(k + 1)) = basePDigit p ((m : ℚ) / d) (-k)

/-- **Minimal period and delay of base-$p$ digits.** Let $p$ be a prime and $x > 0$ a rational
number, write $[p^j](x)$ for the $j$-th base-$p$ digit of $x$, and let $L_x$ be the period and
$D_x = -v_p(x)$ the delay of the base-$p$ expansion of $x$. For every integer $D$ and every
natural number $L > 0$, the identity $[p^{-(k+L)}](x) = [p^{-k}](x)$ holds for all integers
$k \ge D + 1$ if and only if $L_x$ divides $L$ and $D_x \le D$. Thus $L_x$ is the minimal period
and $D_x$ the minimal delay of the digit sequence $k \mapsto [p^{-k}](x)$.

For $v_p(x) > 0$ the delay $D_x$ is negative.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Lemma 2 (`integers-2026-A78-lem-2`). -/
public theorem_wanted basePDigit_eventually_periodic_iff (p : ℕ) [Fact p.Prime] {x : ℚ}
    (hx : 0 < x) (D : ℤ) {L : ℕ} (hL : 0 < L) :
    (∀ k : ℤ, D + 1 ≤ k → basePDigit p x (-(k + L)) = basePDigit p x (-k)) ↔
      basePPeriod p x ∣ L ∧ basePDelay p x ≤ D

/-- **Digits of $\tau i$ next to the radix point.** Let $p$ be a prime, $d$ a divisor of $p - 1$
and $\tau = (p + 1)/d$, and write $[p^j](x)$ for the $j$-th base-$p$ digit of a rational number
$x$. For every natural number $i$, $[p^{-1}](\tau i) = [p^0](\tau i)$ if and only if $p$ divides
$i$.

The source's positivity assumption on $i$ is dropped (the claim holds at $i = 0$), and $p$ is any
prime.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Lemma 3 (`integers-2026-A78-lem-3`). -/
public theorem_wanted basePDigit_towerTau_neg_one_eq_zero_iff (p d : ℕ) [Fact p.Prime]
    (hd : d ∣ p - 1) (i : ℕ) :
    basePDigit p (towerTau p d * i) (-1) = basePDigit p (towerTau p d * i) 0 ↔ p ∣ i

/-- **A digit criterion for $\delta(i) = 1$.** Let $p$ be a prime, $d$ a divisor of $p - 1$ and
$\tau = (p + 1)/d$. For a rational $t$ and an integer $k$ write $[p^k](t)$ for the $k$-th base-$p$
digit of $t$, the residue of $\lfloor t / p^k \rfloor$ modulo $p$ in
$\lbrace 0, \dots, p - 1 \rbrace$, and let $\delta$ be the rounding indicator. If $i$ is a natural
number not divisible by $p$, then $[p^0](\tau i) < [p^{-1}](\tau i)$ if and only if $\delta(i) = 1$.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Lemma 4 (`integers-2026-A78-lem-4`). -/
public theorem_wanted higherANumberDelta_eq_one_iff (p d : ℕ) [Fact p.Prime] (hd : d ∣ p - 1)
    {i : ℕ} (hi : ¬ p ∣ i) :
    basePDigit p (towerTau p d * i) 0 < basePDigit p (towerTau p d * i) (-1) ↔
      higherANumberDelta p d i = 1

/-- **Reflection symmetry of the rounding indicator.** Let $p$ be a prime, let $d$ be a natural
number dividing $p - 1$, let $\tau_D$ be the denominator of $(p + 1)/d$ in lowest terms, and let
$\delta$ be the rounding indicator for $p$ and $d$. For every natural number $i < \tau_D p$ with
$p \nmid i$: (i) if $\tau_D \nmid i$, then $\delta(i) + \delta(\tau_D p - i) = 1$; (ii) if
$\tau_D \mid i$, then $\delta(i) = \delta(\tau_D p - i) = 0$. For every natural number $j < d$
with $p \nmid j$: (iii) if $\tau_D \nmid j$, then $\delta(j) + \delta(d - j) = 1$; (iv) if
$\tau_D \mid j$, then $\delta(j) = 0$.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Proposition 1 (`integers-2026-A78-prop-1`). -/
public theorem_wanted higherANumberDelta_reflection (p d : ℕ) [Fact p.Prime] (hd : d ∣ p - 1) :
    (∀ i < tauDen p d * p, ¬ p ∣ i → ¬ tauDen p d ∣ i →
        higherANumberDelta p d i + higherANumberDelta p d (tauDen p d * p - i) = 1) ∧
      (∀ i < tauDen p d * p, ¬ p ∣ i → tauDen p d ∣ i →
        higherANumberDelta p d i = 0 ∧ higherANumberDelta p d (tauDen p d * p - i) = 0) ∧
      (∀ j < d, ¬ p ∣ j → ¬ tauDen p d ∣ j →
        higherANumberDelta p d j + higherANumberDelta p d (d - j) = 1) ∧
      (∀ j < d, ¬ p ∣ j → tauDen p d ∣ j → higherANumberDelta p d j = 0)

/-- **Periodicity and reflection of $\delta$ and $\delta_0$.** Let $p$ be a prime and $d$ a divisor
of $p - 1$, let $\tau_D$ be the denominator of $\tau = (p + 1)/d$ in lowest terms, let $\delta$ be
the rounding indicator, and let $\delta_0(i)$ be $0$ if $p \mid i$ and $\delta(i)$ otherwise. Then
for all natural numbers $i$ and $n$: (i) $\delta(p^n i) = \delta(i)$;
(ii) $\delta_0(i) = \delta_0(i + \tau_D p)$; (iii) if $i \le \tau_D p$, $\tau_D \nmid i$ and
$p \nmid i$, then $\delta_0(i) + \delta_0(\tau_D p - i) = 1$; (iv) if $i \le \tau_D p$ and
at least one of $\tau_D \mid i$ and $p \mid i$ holds, then $\delta_0(i) = 0$ and
$\delta_0(\tau_D p - i) = 0$.

The bound $i \le \tau_D p$ in (iii) and (iv) makes $\tau_D p - i$ the natural number the
paper means; the paper's positivity of $i$ and $n$ is dropped (the claims hold at $0$).

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Theorem 3 (`integers-2026-A78-thm-3`). -/
public theorem_wanted higherANumberDelta_periodicity (p d : ℕ) [Fact p.Prime] (hd : d ∣ p - 1) :
    (∀ i n : ℕ, higherANumberDelta p d (p ^ n * i) = higherANumberDelta p d i) ∧
      (∀ i : ℕ, higherANumberDeltaZero p d i = higherANumberDeltaZero p d (i + tauDen p d * p)) ∧
      (∀ i ≤ tauDen p d * p, ¬ tauDen p d ∣ i → ¬ p ∣ i →
        higherANumberDeltaZero p d i + higherANumberDeltaZero p d (tauDen p d * p - i) = 1) ∧
      (∀ i ≤ tauDen p d * p, (tauDen p d ∣ i ∨ p ∣ i) →
        higherANumberDeltaZero p d i = 0 ∧ higherANumberDeltaZero p d (tauDen p d * p - i) = 0)

/-- **Average of the indicator $\delta_0$.** Let $p$ be a prime, let $d$ be a natural number
dividing $p - 1$, let $\tau_D$ be the denominator of $(p + 1)/d$ in lowest terms, and let
$\delta_0$ be the variant of the rounding indicator for $p$ and $d$. Then
$$\frac{1}{\tau_D p} \sum_{i=1}^{\tau_D p} \delta_0(i) =
\frac{1}{2} \left(1 - \frac{1}{p}\right) \left(1 - \frac{1}{\tau_D}\right).$$

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Proposition 2 (`integers-2026-A78-prop-2`). -/
public theorem_wanted higherANumberDeltaZero_average (p d : ℕ) [Fact p.Prime] (hd : d ∣ p - 1) :
    (∑ i ∈ Icc 1 (tauDen p d * p), (higherANumberDeltaZero p d i : ℚ)) / (tauDen p d * p) =
      1 / 2 * (1 - 1 / (p : ℚ)) * (1 - 1 / (tauDen p d : ℚ))

/-- **Periodicity and average of the fractional parts of $x p^n$.** Let $p$ be a prime and $x$ a
positive rational. Write $\lbrace t \rbrace$ for the fractional part of $t$, $D_x = -v_p(x)$ for
the delay and $L_x$ for the period of the base-$p$ expansion of $x$ (the order of $p$ modulo the
prime-to-$p$ part of the denominator of $x$), and $\bar x$ for the average of its repeating
base-$p$ digits. Then $\lbrace x p^{n + L_x} \rbrace = \lbrace x p^n \rbrace$ for every integer
$n \ge D_x$, and
$$\frac{1}{L_x} \sum_{n = D_x}^{D_x + L_x - 1} \lbrace x p^n \rbrace = \frac{\bar x}{p - 1}.$$

Here $n$ ranges over the integers, since $D_x$ can be negative.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Lemma 6 (`integers-2026-A78-lem-6`). -/
public theorem_wanted fract_mul_pow_periodic (p : ℕ) [Fact p.Prime] {x : ℚ} (hx : 0 < x) :
    (∀ n : ℤ, basePDelay p x ≤ n →
        Int.fract (x * (p : ℚ) ^ (n + basePPeriod p x)) = Int.fract (x * (p : ℚ) ^ n)) ∧
      (∑ n ∈ Ico (basePDelay p x) (basePDelay p x + basePPeriod p x), Int.fract (x * (p : ℚ) ^ n)) /
          basePPeriod p x = basePDigitAverage p x / ((p : ℚ) - 1)

/-- **Periodicity of $\lfloor x p^n \rfloor$ modulo $x_N$ and modulo $p$.** Let $p$ be a prime and
$x$ a positive rational. Write $x_N$ for the prime-to-$p$ part of the numerator of $x$,
$D_x = -v_p(x)$ for the delay of its base-$p$ expansion, and $L_x$ for its period, the order of
$p$ modulo the prime-to-$p$ part of the denominator of $x$. Then for every integer $n$:
(i) if $n \ge D_x$, then $\lfloor x p^n \rfloor \equiv \lfloor x p^{n + L_x} \rfloor \pmod{x_N}$;
(ii) if $n \ge D_x + 1$, then $\lfloor x p^n \rfloor \equiv \lfloor x p^{n + L_x} \rfloor \pmod p$.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Lemma 7 (`integers-2026-A78-lem-7`). -/
public theorem_wanted floor_mul_pow_modEq (p : ℕ) [Fact p.Prime] {x : ℚ} (hx : 0 < x) :
    (∀ n : ℤ, basePDelay p x ≤ n →
        ⌊x * (p : ℚ) ^ n⌋ ≡ ⌊x * (p : ℚ) ^ (n + basePPeriod p x)⌋ [ZMOD primeToPNum p x]) ∧
      (∀ n : ℤ, basePDelay p x + 1 ≤ n →
        ⌊x * (p : ℚ) ^ n⌋ ≡ ⌊x * (p : ℚ) ^ (n + basePPeriod p x)⌋ [ZMOD p])

/-- **Splitting the sum of $\delta$ by powers of $p$.** Let $p$ be a prime, $d$ a natural number
dividing $p - 1$, $x \ge 1$ a rational number and $n$ a natural number. With $\tau = (p + 1)/d$,
let $\delta(i)$ be $0$ if the sequence of base-$p$ digits of $\tau i$ at $p^0, p^1, p^2, \ldots$
is lexicographically larger than its sequence of digits at $p^{-1}, p^{-2}, \ldots$, and $1$
otherwise, and let $\delta_0(i)$ be $0$ if $p \mid i$ and $\delta(i)$ otherwise. Then
$$
\sum_{i=1}^{\lfloor x^{-1} p^n \rfloor} \delta(i) =
\sum_{e=0}^{n} \sum_{1 \le i \le \lfloor x^{-1} p^e \rfloor, p \nmid i} \delta(i) =
\sum_{e=0}^{n} \sum_{i=1}^{\lfloor x^{-1} p^e \rfloor} \delta_0(i).
$$

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Lemma 8 (`integers-2026-A78-lem-8`). -/
public theorem_wanted sum_higherANumberDelta_by_exponent (p d : ℕ) [Fact p.Prime]
    (hd : d ∣ p - 1) {x : ℚ} (hx : 1 ≤ x) (n : ℕ) :
    ∑ i ∈ Icc 1 ⌊(p : ℚ) ^ n / x⌋₊, higherANumberDelta p d i =
        ∑ e ∈ range (n + 1), ∑ i ∈ (Icc 1 ⌊(p : ℚ) ^ e / x⌋₊).filter (fun i => ¬ p ∣ i),
          higherANumberDelta p d i ∧
      ∑ e ∈ range (n + 1), ∑ i ∈ (Icc 1 ⌊(p : ℚ) ^ e / x⌋₊).filter (fun i => ¬ p ∣ i),
          higherANumberDelta p d i =
        ∑ e ∈ range (n + 1), ∑ i ∈ Icc 1 ⌊(p : ℚ) ^ e / x⌋₊, higherANumberDeltaZero p d i

/-- **Sum of $p^n - \lfloor x i \rfloor$.** Let $p$ be a prime and $x$ a positive rational with
$v_p(x) \ge 0$. Let $x_D$ be the prime-to-$p$ part of the denominator of $x$, let $D_{x^{-1}}$
and $L_{x^{-1}}$ be the delay and the period of the base-$p$ expansion of $x^{-1}$, and let
$A_{x^{-1}}(n)$ be the periodic correction of Proposition 4. Then for every natural number $n$,
$$\sum_{i=1}^{\lfloor p^n/x \rfloor} \left(p^n - \lfloor x i \rfloor\right) =
\frac{1}{2} x^{-1} p^{2n} +
\frac{1}{2} \left(x^{-1} \left(1 - \frac{1}{x_D}\right) - 1\right) p^n + A_{x^{-1}}(n),$$
and $A_{x^{-1}}(n + L_{x^{-1}}) = A_{x^{-1}}(n)$ for every natural number $n \ge D_{x^{-1}}$.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Proposition 4 (`integers-2026-A78-prop-4`). -/
public theorem_wanted sum_pow_sub_floor (p : ℕ) [Fact p.Prime] {x : ℚ} (hx : 0 < x)
    (hv : 0 ≤ padicValRat p x) :
    (∀ n : ℕ, ∑ i ∈ Icc 1 ⌊(p : ℚ) ^ n / x⌋₊, ((p : ℚ) ^ n - ⌊x * i⌋) =
        1 / 2 * x⁻¹ * (p : ℚ) ^ (2 * n) +
          1 / 2 * (x⁻¹ * (1 - 1 / (primeToPDen p x : ℚ)) - 1) * (p : ℚ) ^ n +
          floorSumCorrection p x n) ∧
      ∀ n : ℕ, basePDelay p x⁻¹ ≤ n →
        floorSumCorrection p x (n + basePPeriod p x⁻¹) = floorSumCorrection p x n

/-- **Difference of the floor sums for $\tau$ and $\gamma$.** Let $p$ be a prime, $d$ a natural
number dividing $p - 1$, and $r$ and $n$ natural numbers. Put $\tau = (p + 1)/d$ and
$\gamma = ((p - 1) r + (p + 1))/d$, let $\tau_D$ be the denominator of $\tau$ in lowest terms,
and for a rational $x$ let $A_{x^{-1}}(n)$ be the periodic correction of Proposition 4. Then
$$
\sum_{i=1}^{\lfloor \tau^{-1} p^n \rfloor} (p^n - \lfloor \tau i \rfloor) -
\sum_{i=1}^{\lfloor \gamma^{-1} p^n \rfloor} (p^n - \lfloor \gamma i \rfloor) =
\tfrac12 (\tau^{-1} - \gamma^{-1}) p^{2n} +
\tfrac12 (\tau^{-1} - \gamma^{-1})(1 - 1/\tau_D) p^n + (A_{\tau^{-1}}(n) - A_{\gamma^{-1}}(n)).
$$

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Corollary 3 (`integers-2026-A78-cor-3`). -/
public theorem_wanted sum_floor_difference (p d : ℕ) [Fact p.Prime] (hd : d ∣ p - 1) (r n : ℕ) :
    ∑ i ∈ Icc 1 ⌊(p : ℚ) ^ n / towerTau p d⌋₊, ((p : ℚ) ^ n - ⌊towerTau p d * i⌋) -
        ∑ i ∈ Icc 1 ⌊(p : ℚ) ^ n / towerGamma p d r⌋₊, ((p : ℚ) ^ n - ⌊towerGamma p d r * i⌋) =
      1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d r)⁻¹) * (p : ℚ) ^ (2 * n) +
        1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d r)⁻¹) * (1 - 1 / (tauDen p d : ℚ)) *
          (p : ℚ) ^ n +
        (floorSumCorrection p (towerTau p d) n - floorSumCorrection p (towerGamma p d r) n)

/-- **Higher $a$-numbers as sums of floors and of $\delta$.** Let $p$ be a prime, let $d$ be a
natural number dividing $p - 1$, let $r$ and $n$ be natural numbers, let $\tau = (p + 1)/d$ and
$\gamma = ((p - 1) r + (p + 1))/d$, let $\delta$ be the rounding indicator for $p$ and $d$, and let
$A_r(n)$ be the lattice-point count for the $r$-th higher $a$-number at level $n$. Put
$t_n = \lfloor \gamma^{-1} p^n \rfloor$ and $s_n = \lfloor \tau^{-1} p^n \rfloor$. Then
$$A_r(n) = \sum_{i=1}^{t_n} (\gamma - \tau) i +
\sum_{i=t_n+1}^{s_n} (p^n - \lfloor \tau i \rfloor) - \sum_{i=t_n+1}^{s_n} \delta(i)$$
and
$$A_r(n) = \left(\sum_{i=1}^{s_n} (p^n - \lfloor \tau i \rfloor) -
\sum_{i=1}^{t_n} (p^n - \lfloor \gamma i \rfloor)\right) -
\left(\sum_{i=1}^{s_n} \delta(i) - \sum_{i=1}^{t_n} \delta(i)\right).$$

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Proposition 3 (`integers-2026-A78-prop-3`). -/
public theorem_wanted higherANumberLatticeCount_eq_sums (p d : ℕ) [Fact p.Prime] (hd : d ∣ p - 1)
    (r n : ℕ) :
    higherANumberLatticeCount p d r n =
        ∑ i ∈ Icc 1 ⌊(p : ℚ) ^ n / towerGamma p d r⌋₊, (towerGamma p d r - towerTau p d) * i +
          ∑ i ∈ Ioc ⌊(p : ℚ) ^ n / towerGamma p d r⌋₊ ⌊(p : ℚ) ^ n / towerTau p d⌋₊,
            ((p : ℚ) ^ n - ⌊towerTau p d * i⌋) -
          ∑ i ∈ Ioc ⌊(p : ℚ) ^ n / towerGamma p d r⌋₊ ⌊(p : ℚ) ^ n / towerTau p d⌋₊,
            (higherANumberDelta p d i : ℚ) ∧
      higherANumberLatticeCount p d r n =
        (∑ i ∈ Icc 1 ⌊(p : ℚ) ^ n / towerTau p d⌋₊, ((p : ℚ) ^ n - ⌊towerTau p d * i⌋) -
            ∑ i ∈ Icc 1 ⌊(p : ℚ) ^ n / towerGamma p d r⌋₊,
              ((p : ℚ) ^ n - ⌊towerGamma p d r * i⌋)) -
          (∑ i ∈ Icc 1 ⌊(p : ℚ) ^ n / towerTau p d⌋₊, (higherANumberDelta p d i : ℚ) -
            ∑ i ∈ Icc 1 ⌊(p : ℚ) ^ n / towerGamma p d r⌋₊, (higherANumberDelta p d i : ℚ))

/-- **Sum of $\delta$ up to $\lfloor p^n/x \rfloor$.** Let $p$ be a prime and $d$ a divisor of
$p - 1$; let $\delta$ be the rounding indicator, $\tau_D$ the denominator of $\tau = (p + 1)/d$
in lowest terms, and $F_y(e)$ the $\delta_0$ correction sum of Lemma 9. For every rational
$x \ge 1$ and every natural number $n$,
$$\sum_{i=1}^{\lfloor p^n/x \rfloor} \delta(i) =
\frac{1}{2} \left(1 - \frac{1}{\tau_D}\right) \left(p^n - \frac{1}{p}\right) x^{-1} -
\frac{1}{2} \left(1 - \frac{1}{p}\right) \left(1 - \frac{1}{\tau_D}\right)
\sum_{e=0}^{n} \left(x^{-1} p^e - \lfloor x^{-1} p^e \rfloor\right) +
\sum_{e=0}^{n} F_{x^{-1}}(e).$$

The paper's positivity of $n$ is dropped (the identity holds at $n = 0$).

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Corollary 4 (`integers-2026-A78-cor-4`). -/
public theorem_wanted sum_higherANumberDelta_eq (p d : ℕ) [Fact p.Prime] (hd : d ∣ p - 1)
    {x : ℚ} (hx : 1 ≤ x) (n : ℕ) :
    ∑ i ∈ Icc 1 ⌊(p : ℚ) ^ n / x⌋₊, (higherANumberDelta p d i : ℚ) =
      1 / 2 * (1 - 1 / (tauDen p d : ℚ)) * ((p : ℚ) ^ n - 1 / p) * x⁻¹ -
        1 / 2 * (1 - 1 / (p : ℚ)) * (1 - 1 / (tauDen p d : ℚ)) *
          ∑ e ∈ range (n + 1), Int.fract (x⁻¹ * (p : ℚ) ^ e) +
        ∑ e ∈ range (n + 1), deltaZeroSumCorrection p d x⁻¹ e

/-- **Eventual periodicity of the $\delta$ sums.** Let $p$ be a prime and $d$ a divisor of
$p - 1$; let $\delta$ be the rounding indicator, $\tau_D$ the denominator of $\tau = (p + 1)/d$
in lowest terms, and $F_y(e)$ the $\delta_0$ correction sum of Lemma 9. Let $x$ be a positive
rational such that the prime-to-$p$ part $x_D$ of the denominator of $x$ equals $\tau_D$, and
write $D = D_{x^{-1}}$, $L = L_{x^{-1}}$ and $\overline{x^{-1}}$ for the delay, the period and
the average repeating digit of the base-$p$ expansion of $x^{-1}$. Then
$F_{x^{-1}}(e + L) = F_{x^{-1}}(e)$ for every natural number $e \ge D + 1$. Moreover, with
$s = \max(D + 1, 0)$ and $\bar F = \frac{1}{L} \sum_{e=s}^{s+L-1} F_{x^{-1}}(e)$, there is a
function $B : \mathbb{N} \to \mathbb{Q}$ with $B(n + L) = B(n)$ for every natural number
$n \ge D$ such that for every natural number $n \ge D$,
$$\sum_{i=1}^{\lfloor p^n/x \rfloor} \delta(i) =
\frac{1}{2} x^{-1} \left(1 - \frac{1}{\tau_D}\right) p^n +
\left(\bar F - \frac{\overline{x^{-1}}}{2p} \left(1 - \frac{1}{\tau_D}\right)\right) n + B(n).$$

The paper's explicit $B$ (Equation (6)) is replaced by an existential.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Proposition 5 (`integers-2026-A78-prop-5`). -/
public theorem_wanted sum_higherANumberDelta_periodic (p d : ℕ) [Fact p.Prime] (hd : d ∣ p - 1)
    {x : ℚ} (hx : 0 < x) (hxD : primeToPDen p x = tauDen p d) :
    (∀ e : ℕ, basePDelay p x⁻¹ + 1 ≤ e →
        deltaZeroSumCorrection p d x⁻¹ (e + basePPeriod p x⁻¹) =
          deltaZeroSumCorrection p d x⁻¹ e) ∧
      ∃ B : ℕ → ℚ, (∀ n : ℕ, basePDelay p x⁻¹ ≤ n → B (n + basePPeriod p x⁻¹) = B n) ∧
        ∀ n : ℕ, basePDelay p x⁻¹ ≤ n →
          ∑ i ∈ Icc 1 ⌊(p : ℚ) ^ n / x⌋₊, (higherANumberDelta p d i : ℚ) =
            1 / 2 * x⁻¹ * (1 - 1 / (tauDen p d : ℚ)) * (p : ℚ) ^ n +
              ((∑ e ∈ Ico (basePDelay p x⁻¹ + 1).toNat
                    ((basePDelay p x⁻¹ + 1).toNat + basePPeriod p x⁻¹),
                    deltaZeroSumCorrection p d x⁻¹ e) / basePPeriod p x⁻¹ -
                basePDigitAverage p x⁻¹ / (2 * p) * (1 - 1 / (tauDen p d : ℚ))) * n +
              B n

/-- **The linear coefficient of Proposition 5 vanishes at $\tau$.** Let $p$ be a prime and $d$ a
divisor of $p - 1$, let $\tau = (p + 1)/d$, and let $\tau_D$ be the denominator of $\tau$ in
lowest terms. Let $L$ be the order of $p$ modulo the prime-to-$p$ part of the denominator of
$\tau^{-1}$ (the period of the base-$p$ expansion of $\tau^{-1}$), and let $\overline{\tau^{-1}}$
be the average of the repeating base-$p$ digits of $\tau^{-1}$. For $e \ge 0$ let
$F_{\tau^{-1}}(e) = \sum_{k=1}^{\lfloor \tau^{-1} p^e \rfloor \bmod \tau_D p}
(\delta_0(k) - \frac12 (1 - 1/p)(1 - 1/\tau_D))$, where $\delta_0(k)$ is $0$ if $p \mid k$ and
$\delta(k)$ otherwise, $\delta$ being the rounding indicator. Then
$$\frac1L \sum_{e=1}^{L} F_{\tau^{-1}}(e) - \frac{\overline{\tau^{-1}}}{2p} (1 - 1/\tau_D) = 0.$$

This says that the linear coefficient in Proposition 5 vanishes at $\tau$; the delay of
$\tau^{-1}$ is $0$, so the average of $F_{\tau^{-1}}$ is taken over $1 \le e \le L$.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Proposition 6 (`integers-2026-A78-prop-6`). -/
public theorem_wanted deltaZeroSumCorrection_average_towerTau (p d : ℕ) [Fact p.Prime]
    (hd : d ∣ p - 1) :
    (∑ e ∈ Icc 1 (basePPeriod p (towerTau p d)⁻¹),
          deltaZeroSumCorrection p d (towerTau p d)⁻¹ e) / basePPeriod p (towerTau p d)⁻¹ -
        basePDigitAverage p (towerTau p d)⁻¹ / (2 * p) * (1 - 1 / (tauDen p d : ℚ)) = 0

/-- **Sum of $\delta$ between the $\gamma$- and $\tau$-cutoffs.** Let $p$ be a prime, let $d$
be a divisor of $p - 1$ and let $r \ge 1$ be an integer. Write $\tau = (p + 1)/d$,
$\gamma = ((p - 1) r + (p + 1))/d$ and $\tau_D$ for the denominator of $\tau$ in lowest terms;
let $\delta$ be the rounding indicator, and for a rational $y$ let $L_y$ be the period, $D_y$
the delay and $\bar y$ the average repeating digit of the base-$p$ expansion of $y$, and let
$F_y(e)$ be the $\delta_0$ correction sum of Lemma 9. Put $D = D_{\gamma^{-1}}$,
$L = L_{\gamma^{-1}}$, $s = \max(D + 1, 0)$ and
$\bar F = \frac{1}{L} \sum_{e=s}^{s+L-1} F_{\gamma^{-1}}(e)$. Then there is a function
$C : \mathbb{N} \to \mathbb{Q}$ such that $C(n + \operatorname{lcm}(L_{\tau^{-1}}, L)) = C(n)$
for every natural number $n \ge D$, and for every natural number $n \ge D$,
$$\sum_{\lfloor p^n/\gamma \rfloor < i \le \lfloor p^n/\tau \rfloor} \delta(i) =
\frac{1}{2} (\tau^{-1} - \gamma^{-1}) \left(1 - \frac{1}{\tau_D}\right) p^n +
\left(\frac{\overline{\gamma^{-1}}}{2p} \left(1 - \frac{1}{\tau_D}\right) - \bar F\right) n +
C(n).$$

The paper's explicit $B$ functions are replaced by the existential $C$.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Corollary 5 (`integers-2026-A78-cor-5`). -/
public theorem_wanted sum_higherANumberDelta_difference (p d : ℕ) [Fact p.Prime] (hd : d ∣ p - 1)
    (r : ℕ) (hr : 0 < r) :
    ∃ C : ℕ → ℚ,
      (∀ n : ℕ, basePDelay p (towerGamma p d r)⁻¹ ≤ n →
        C (n + Nat.lcm (basePPeriod p (towerTau p d)⁻¹) (basePPeriod p (towerGamma p d r)⁻¹)) =
          C n) ∧
      ∀ n : ℕ, basePDelay p (towerGamma p d r)⁻¹ ≤ n →
        ∑ i ∈ Ioc ⌊(p : ℚ) ^ n / towerGamma p d r⌋₊ ⌊(p : ℚ) ^ n / towerTau p d⌋₊,
            (higherANumberDelta p d i : ℚ) =
          1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d r)⁻¹) * (1 - 1 / (tauDen p d : ℚ)) *
              (p : ℚ) ^ n +
            (basePDigitAverage p (towerGamma p d r)⁻¹ / (2 * p) * (1 - 1 / (tauDen p d : ℚ)) -
              (∑ e ∈ Ico (basePDelay p (towerGamma p d r)⁻¹ + 1).toNat
                    ((basePDelay p (towerGamma p d r)⁻¹ + 1).toNat +
                      basePPeriod p (towerGamma p d r)⁻¹),
                  deltaZeroSumCorrection p d (towerGamma p d r)⁻¹ e) /
                basePPeriod p (towerGamma p d r)⁻¹) * n +
            C n

/-- **Asymptotic formula for higher $a$-numbers.** Let $p$ be a prime, let $d$ be a natural number
dividing $p - 1$, let $r \ge 1$, and for each natural number $n$ let $A_r(n)$ be the lattice-point
count for the $r$-th higher $a$-number at level $n$. Let $D_r$ be the prime-to-$p$ part of the
denominator of $d/((p - 1) r + (p + 1))$, and let
$M_r = \operatorname{lcm}(2, \operatorname{ord}_{D_r} p)$, where $\operatorname{ord}_{D_r} p$ is
the multiplicative order of $p$ modulo $D_r$. Then there are a positive integer $N_r$, a rational
number $\lambda_r$ and a function $\nu_r$ from the natural numbers to the rationals such that
$\nu_r(n + M_r) = \nu_r(n)$ for every $n \ge N_r$, and
$$A_r(n) = \frac{r}{r + (p + 1)/(p - 1)} \cdot \frac{d}{2(p + 1)} \cdot p^{2n} + \lambda_r n +
\nu_r(n)$$
for every $n \ge N_r$.

By Theorem 1 of the source, $A_r(n)$ is the higher $a$-number $a^r(X_n)$ of the $n$-th layer of
a $\mathbb{Z}_p$-tower with minimal break ratios and ramification invariant $d$; the source
states the periodicity as: the minimal period of $\nu_r$ divides $M_r$.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Theorem 2 (`integers-2026-A78-thm-2`). -/
public theorem_wanted higherANumberLatticeCount_asymptotic (p d : ℕ) [Fact p.Prime]
    (hd : d ∣ p - 1) (r : ℕ) (hr : 0 < r) :
    ∃ N : ℕ, 0 < N ∧ ∃ lam : ℚ, ∃ ν : ℕ → ℚ,
      (∀ n ≥ N, ν (n + Nat.lcm 2
          (orderOf (p : ZMod (primeToPDen p ((d : ℚ) / (((p : ℚ) - 1) * r + (p + 1))))))) = ν n) ∧
      ∀ n ≥ N, higherANumberLatticeCount p d r n =
        r / (r + ((p : ℚ) + 1) / ((p : ℚ) - 1)) * (d / (2 * ((p : ℚ) + 1))) * (p : ℚ) ^ (2 * n) +
          lam * n + ν n

/-- **Explicit linear term and period for higher $a$-numbers.** Let $p$ be a prime, let $d$ be a
natural number dividing $p - 1$, let $r \ge 1$, let $\tau = (p + 1)/d$ and
$\gamma = ((p - 1) r + (p + 1))/d$, let $\tau_D$ be the denominator of $\tau$ in lowest terms, let
$\delta_0$ be the variant of the rounding indicator for $p$ and $d$, and for each natural number
$n$ let $A_r(n)$ be the lattice-point count for the $r$-th higher $a$-number at level $n$. Put
$x = \gamma^{-1}$. Let $L$ be the period of the base-$p$ expansion of $x$ (the order of $p$
modulo the prime-to-$p$ part of the denominator of $x$), let $D = -v_p(x)$ be its delay, let
$\bar{x}$ be the average of its repeating digits, put $e_0 = \max(D + 1, 0)$, and for a natural
number $e$ let
$$F(e) = \sum_{k=1}^{\lfloor x p^e \rfloor \bmod \tau_D p}
\left(\delta_0(k) - \tfrac{1}{2} (1 - 1/p)(1 - 1/\tau_D)\right).$$
With
$$\lambda_r = \frac{1}{L} \sum_{e=e_0}^{e_0 + L - 1} F(e) -
\frac{\bar{x}}{2p} \left(1 - \frac{1}{\tau_D}\right),$$
there is a function $\nu_r$ from the natural numbers to the rationals such that
$A_r(n) = \frac{1}{2} (\tau^{-1} - \gamma^{-1}) p^{2n} + \lambda_r n + \nu_r(n)$ for every natural
number $n$, $\nu_r(n + \operatorname{lcm}(L, 2)) = \nu_r(n)$ for every natural number $n \ge D$,
and $\operatorname{lcm}(L, 2) \mid 2L'$ for every $L' > 0$ such that $\nu_r(n + L') = \nu_r(n)$
for all natural numbers $n \ge D$.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Theorem 4 (`integers-2026-A78-thm-4`). -/
public theorem_wanted higherANumberLatticeCount_eq_explicit_linear_add_periodic (p d : ℕ)
    [Fact p.Prime] (hd : d ∣ p - 1) (r : ℕ) (hr : 0 < r) :
    ∃ ν : ℕ → ℚ,
      (∀ n : ℕ, higherANumberLatticeCount p d r n =
        1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d r)⁻¹) * (p : ℚ) ^ (2 * n) +
          ((∑ e ∈ Ico (basePDelay p (towerGamma p d r)⁻¹ + 1).toNat
                  ((basePDelay p (towerGamma p d r)⁻¹ + 1).toNat +
                    basePPeriod p (towerGamma p d r)⁻¹),
                deltaZeroSumCorrection p d (towerGamma p d r)⁻¹ e) /
              basePPeriod p (towerGamma p d r)⁻¹ -
            basePDigitAverage p (towerGamma p d r)⁻¹ / (2 * p) * (1 - 1 / (tauDen p d : ℚ))) * n +
          ν n) ∧
      (∀ n : ℕ, basePDelay p (towerGamma p d r)⁻¹ ≤ n →
        ν (n + Nat.lcm (basePPeriod p (towerGamma p d r)⁻¹) 2) = ν n) ∧
      ∀ L' : ℕ, 0 < L' → (∀ n : ℕ, basePDelay p (towerGamma p d r)⁻¹ ≤ n → ν (n + L') = ν n) →
        Nat.lcm (basePPeriod p (towerGamma p d r)⁻¹) 2 ∣ 2 * L'

/-- **Period of higher $a$-numbers for $d = 1$ or $d = 2$.** Let $p$ be a prime, let $d$ be $1$
or $2$ with $d \mid p - 1$, let $r \ge 1$, let $\tau = (p + 1)/d$ and
$\gamma = ((p - 1) r + (p + 1))/d$, and for each natural number $n$ let $A_r(n)$ be the
lattice-point count for the $r$-th higher $a$-number at level $n$ and
$R(n) = A_r(n) - \frac{1}{2} (\tau^{-1} - \gamma^{-1}) p^{2n}$. Let $L$ be the period and $D$ the
delay of the base-$p$ expansion of $\gamma^{-1}$. Then $R(n + L) = R(n)$ for every natural number
$n \ge D$, and $L \mid 2L'$ for all natural numbers $L' > 0$ and $N$ such that
$R(n + L') = R(n)$ for every $n \ge N$.

In particular $R$ has no linear term in $n$, and its minimal eventual period is $L$ when $L$ is
odd and $L$ or $L/2$ when $L$ is even.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Corollary 6 (`integers-2026-A78-cor-6`). -/
public theorem_wanted higherANumberLatticeCount_period_small_d (p d : ℕ) [Fact p.Prime]
    (hd : d ∣ p - 1) (hd12 : d = 1 ∨ d = 2) (r : ℕ) (hr : 0 < r) :
    (∀ n : ℕ, basePDelay p (towerGamma p d r)⁻¹ ≤ n →
        higherANumberLatticeCount p d r (n + basePPeriod p (towerGamma p d r)⁻¹) -
            1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d r)⁻¹) *
              (p : ℚ) ^ (2 * (n + basePPeriod p (towerGamma p d r)⁻¹)) =
          higherANumberLatticeCount p d r n -
            1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d r)⁻¹) * (p : ℚ) ^ (2 * n)) ∧
      ∀ L' N : ℕ, 0 < L' → (∀ n ≥ N,
          higherANumberLatticeCount p d r (n + L') -
              1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d r)⁻¹) * (p : ℚ) ^ (2 * (n + L')) =
            higherANumberLatticeCount p d r n -
              1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d r)⁻¹) * (p : ℚ) ^ (2 * n)) →
        basePPeriod p (towerGamma p d r)⁻¹ ∣ 2 * L'

/-- **The lattice-point count for $r = p + 1$.** Let $p$ be a prime and $d$ a natural number
dividing $p - 1$. Put $\tau = (p + 1)/d$ and $\gamma = ((p - 1)(p + 1) + (p + 1))/d$, the value
at $r = p + 1$ of $\gamma = ((p - 1) r + (p + 1))/d$, and write $a^{p+1}(X_n)$ for the
lattice-point expression of Theorem 1 with $r = p + 1$. Then for every $n \ge 1$,
$$
a^{p+1}(X_n) = \tfrac12 (\tau^{-1} - \gamma^{-1}) p^{2n} + \tfrac12 (p - 1)(\tau^{-1} - 1).
$$

In the paper's terms: for $r = p + 1$ the linear coefficient $\lambda_r$ vanishes, and the
periodic part $\nu_r(n) = \tfrac12 (p - 1)(\tau^{-1} - 1)$ is constant (minimal period $1$) for
$n \ge 1$.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Corollary 7 (`integers-2026-A78-cor-7`). -/
public theorem_wanted higherANumberLatticeCount_r_eq_succ (p d : ℕ) [Fact p.Prime]
    (hd : d ∣ p - 1) (n : ℕ) (hn : 1 ≤ n) :
    higherANumberLatticeCount p d (p + 1) n =
      1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d (p + 1))⁻¹) * (p : ℚ) ^ (2 * n) +
        1 / 2 * ((p : ℚ) - 1) * ((towerTau p d)⁻¹ - 1)

/-- **The linear coefficient times a period is an integer.** Let $p$ be a prime, let $d$ be a
natural number dividing $p - 1$, let $r \ge 1$, let $\tau = (p + 1)/d$ and
$\gamma = ((p - 1) r + (p + 1))/d$, and for each natural number $n$ let $A_r(n)$ be the
lattice-point count for the $r$-th higher $a$-number at level $n$. Let $\lambda$ be a rational
number, $\nu$ a function from the natural numbers to the rationals, and $N$ and $L > 0$ natural
numbers such that, for every $n \ge N$, $\nu(n + L) = \nu(n)$ and
$A_r(n) = \frac{1}{2} (\tau^{-1} - \gamma^{-1}) p^{2n} + \lambda n + \nu(n)$. Then $\lambda L$ is
an integer.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Corollary 8 (`integers-2026-A78-cor-8`). -/
public theorem_wanted higherANumberLatticeCount_linear_coeff_mul_period (p d : ℕ) [Fact p.Prime]
    (hd : d ∣ p - 1) (r : ℕ) (hr : 0 < r) (lam : ℚ) (ν : ℕ → ℚ) (N L : ℕ) (hL : 0 < L)
    (hν : ∀ n ≥ N, ν (n + L) = ν n)
    (hexp : ∀ n ≥ N, higherANumberLatticeCount p d r n =
      1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d r)⁻¹) * (p : ℚ) ^ (2 * n) + lam * n + ν n) :
    ∃ z : ℤ, lam * L = z

/-- **Passing from $r_0$ to $(r_0 + 1)p + 1$.** Let $p$ be a prime, $d$ a natural number
dividing $p - 1$ and $r_0$ a natural number, and put $r_1 = (r_0 + 1)p + 1$. Write
$\tau = (p + 1)/d$, $\gamma_k = ((p - 1) r_k + (p + 1))/d$ for $k = 0, 1$, and $a^r(X_n)$ for
the lattice-point expression of Theorem 1. For a rational $\lambda$ and $k = 0, 1$ let
$f_k(n) = a^{r_k}(X_n) - \tfrac12 (\tau^{-1} - \gamma_k^{-1}) p^{2n} - \lambda n$. Then for every
rational $\lambda$: if there are $N$ and $L > 0$ with $f_0(n + L) = f_0(n)$ for all $n \ge N$,
then there are $N'$ and $L' > 0$ with $f_1(n + L') = f_1(n)$ for all $n \ge N'$. Moreover
$D_{\gamma_1^{-1}} = D_{\gamma_0^{-1}} + 1$, where $D_x = -v_p(x)$ is the delay of the base-$p$
expansion of a rational $x$.

The first part is the paper's statement that the linear coefficients agree, $\lambda_1 = \lambda_0$.

Source: Jeremy Booher, Jack Hsieh, Rakesh Rivera, Vincent Tran, James Upton, and Carol Wu,
*Higher a-Numbers in `ℤ_p`-Towers via Counting Lattice Points*, INTEGERS 26 (2026), Article A78,
Proposition 7 (`integers-2026-A78-prop-7`). -/
public theorem_wanted higherANumberLatticeCount_shift (p d : ℕ) [Fact p.Prime] (hd : d ∣ p - 1)
    (r₀ : ℕ) :
    (∀ lam : ℚ,
        (∃ N L : ℕ, 0 < L ∧ ∀ n ≥ N,
          higherANumberLatticeCount p d r₀ (n + L) -
              1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d r₀)⁻¹) * (p : ℚ) ^ (2 * (n + L)) -
              lam * (n + L : ℕ) =
            higherANumberLatticeCount p d r₀ n -
              1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d r₀)⁻¹) * (p : ℚ) ^ (2 * n) - lam * n) →
        ∃ N L : ℕ, 0 < L ∧ ∀ n ≥ N,
          higherANumberLatticeCount p d ((r₀ + 1) * p + 1) (n + L) -
              1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d ((r₀ + 1) * p + 1))⁻¹) *
                (p : ℚ) ^ (2 * (n + L)) - lam * (n + L : ℕ) =
            higherANumberLatticeCount p d ((r₀ + 1) * p + 1) n -
              1 / 2 * ((towerTau p d)⁻¹ - (towerGamma p d ((r₀ + 1) * p + 1))⁻¹) *
                (p : ℚ) ^ (2 * n) - lam * n) ∧
      basePDelay p (towerGamma p d ((r₀ + 1) * p + 1))⁻¹ = basePDelay p (towerGamma p d r₀)⁻¹ + 1

end

end MetaMathlibExt
