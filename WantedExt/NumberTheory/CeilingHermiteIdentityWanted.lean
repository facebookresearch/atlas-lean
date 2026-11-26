/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.InclExclLikeSumBounds
public import MathlibExt.NumberTheory.InclExclLikeSumRelations
public import MathlibExt.NumberTheory.TverbergSumPeriodic
public import MathlibExt.Algebra.Order.Floor.HalfShift
public import MathlibExt.NumberTheory.CeilingHermiteIdentityTverbergSumRoundBounds
public import MathlibExt.NumberTheory.CeilingHermiteIdentityInclExclLikeSumFloorExtrema

/-!
# Inclusion-exclusion-like sums with floor, ceiling and nearest-integer functions (statements)

Mathlib proves Hermite's identity for the floor function as `Int.sum_floor_add_div`
(`∑_{0 ≤ i < n} ⌊x + i/n⌋ = ⌊n x⌋`). The ceiling analogue uses the shifted range `1 ≤ k ≤ n`.
This file states the sharp bounds of Onphaeng, Khemaratchatakumthorn and Pongsriiam for the sums
`g^(F)`, `f^(F)` and the partial sums `S^(F)`, `T^(F)` of Jacobsthal and Tverberg type,
where `F` is one of `⌊·⌋` (`j = 1`), `⌈·⌉` (`j = 2`),
`r⁺(x) = ⌊x + 1/2⌋` (`j = 3`, Mathlib's `round`, see `round_eq`) and
`r⁻(x) = ⌈x - 1/2⌉` (`j = 4`). The sharp bounds for `f^(r⁺)`, `tverbergSum_round_bounds`, are
proved in `MathlibExt.NumberTheory.CeilingHermiteIdentityTverbergSumRoundBounds`, and the extrema
of `g^(⌊·⌋)`, `inclExclLikeSum_floor_extrema`, are proved in
`MathlibExt.NumberTheory.CeilingHermiteIdentityInclExclLikeSumFloorExtrema`.

Conventions: the multiset `C = {a_1, …, a_ℓ}` is a tuple `a : Fin ℓ → ℤ`; the modulus `m` is a
natural number, and at `m = 0` Lean's `x / 0 = 0` makes every term `F 0 = 0`, so statements whose
value is then trivially correct carry no positivity hypothesis on `m`. The partial sums are written
inline: `S^(F)(C, m, K) = ∑ k ∈ Finset.range (K + 1), tverbergSum F a m k` and
`T^(F)(C, m, K) = ∑ k ∈ Finset.Icc 1 K, tverbergSum F a m k`. `⌊m/2⌋` is the natural-number
quotient `m / 2`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Tverberg's sum in terms of the inclusion-exclusion-like sum.** Let $F$ be one of
$\lfloor \cdot \rfloor$, $\lceil \cdot \rceil$, $r^+(y) = \lfloor y + 1/2 \rfloor$ and
$r^-(y) = \lceil y - 1/2 \rceil$. For real numbers $x_1, \dots, x_n$ let
$g(x_1, \dots, x_n) =
\sum_{\emptyset \ne U \subseteq \{1, \dots, n\}} (-1)^{|U| - 1} F(\sum_{i \in U} x_i)$
be the inclusion-exclusion-like sum of $F$. For every natural number $\ell$, integers
$a_1, \dots, a_\ell$, a natural number $m$ and an integer $k$, let
$f(a, m, k) =
\sum_{U \subseteq \{1, \dots, \ell\}} (-1)^{\ell - |U|} F((k + \sum_{i \in U} a_i)/m)$
be Tverberg's sum of $F$, with $x/0 = 0$. Then
$f(a, m, 0) = (-1)^{\ell+1} g(a_1/m, \dots, a_\ell/m)$ and
$f(a, m, k) = (-1)^{\ell} g(a_1/m, \dots, a_\ell/m, k/m) + (-1)^{\ell+1} g(a_1/m, \dots, a_\ell/m)$.

The paper assumes $\ell \ge 2$ and $m \ge 1$; the identities hold without these hypotheses.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Lemma 2. -/
public theorem_wanted tverbergSum_eq_inclExclLikeSum {ℓ : ℕ} (F : ℝ → ℤ)
    (hF : F ∈ ({Int.floor, Int.ceil, round, fun y : ℝ => ⌈y - 1 / 2⌉} : Set (ℝ → ℤ)))
    (a : Fin ℓ → ℤ) (m : ℕ) :
    tverbergSum F a m 0 = (-1) ^ (ℓ + 1) * inclExclLikeSum F (fun i => (a i : ℝ) / m) ∧
      ∀ k : ℤ, tverbergSum F a m k =
        (-1) ^ ℓ * inclExclLikeSum F (Fin.snoc (fun i => (a i : ℝ) / m) ((k : ℝ) / m)) +
          (-1) ^ (ℓ + 1) * inclExclLikeSum F (fun i => (a i : ℝ) / m)

/-- **Sharp bounds for Tverberg's floor sum.** Let $\ell \ge 2$ and let $F = \lfloor \cdot \rfloor$.
For integers $a_1, \dots, a_\ell$, a natural number $m$ and an integer $k$, let
$f(a, m, k) =
\sum_{U \subseteq \{1, \dots, \ell\}} (-1)^{\ell - |U|} F((k + \sum_{i \in U} a_i)/m)$
be Tverberg's sum of $F$, with $x/0 = 0$. Then $-2^{\ell-2} \le f(a, m, k) \le 2^{\ell-2}$ for
all such $a$, $m$ and $k$. Both bounds are attained: for every integer $r \ge 1$, if $a_i = r$
for all $i$ and $m = 2r$, then $f(a, m, 0) = (-1)^{\ell} 2^{\ell-2}$ and
$f(a, m, r) = (-1)^{\ell+1} 2^{\ell-2}$.

This bound is due to Onphaeng and Pongsriiam. The paper states the equality cases separately for
odd and even $\ell$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Lemma 4. -/
public theorem_wanted tverbergSum_floor_bounds {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    (∀ (a : Fin ℓ → ℤ) (m : ℕ) (k : ℤ),
      -2 ^ (ℓ - 2) ≤ tverbergSum Int.floor a m k ∧ tverbergSum Int.floor a m k ≤ 2 ^ (ℓ - 2)) ∧
      ∀ r : ℕ, 0 < r →
        tverbergSum Int.floor (fun _ : Fin ℓ => (r : ℤ)) (2 * r) 0 = (-1) ^ ℓ * 2 ^ (ℓ - 2) ∧
          tverbergSum Int.floor (fun _ : Fin ℓ => (r : ℤ)) (2 * r) r = (-1) ^ (ℓ + 1) * 2 ^ (ℓ - 2)

/-- **Extrema of the round-half-up inclusion-exclusion-like sum.** Let $n \ge 2$ and let $g_3$ be
the inclusion-exclusion-like sum $g^{(F)}$ in $n$ real variables with
$F(y) = \lfloor y + 1/2 \rfloor$, the nearest integer to $y$ with ties rounded up. Then
$-2^{n-2} \le g_3(x) \le 2^{n-2}$ for every $x \in \mathbb{R}^n$; the minimum $-2^{n-2}$ is
attained at the point with all coordinates $1/2 - 1/n^2$, and the maximum $2^{n-2}$ at the point
with all coordinates $1/2$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Theorem 2. -/
public theorem_wanted inclExclLikeSum_round_extrema {n : ℕ} (hn : 2 ≤ n) :
    (∀ x : Fin n → ℝ, -2 ^ (n - 2) ≤ inclExclLikeSum round x ∧
      inclExclLikeSum round x ≤ 2 ^ (n - 2)) ∧
      inclExclLikeSum round (fun _ : Fin n => 1 / 2 - 1 / (n : ℝ) ^ 2) = -2 ^ (n - 2) ∧
      inclExclLikeSum round (fun _ : Fin n => (1 / 2 : ℝ)) = 2 ^ (n - 2)

/-- **Extrema of the round-half-down inclusion-exclusion-like sum.** Let $n \ge 2$ and let $g_4$
be the inclusion-exclusion-like sum $g^{(F)}$ in $n$ real variables with
$F(y) = \lceil y - 1/2 \rceil$, the nearest integer to $y$ with ties rounded down. Then
$-2^{n-2} \le g_4(x) \le 2^{n-2}$ for every $x \in \mathbb{R}^n$; the minimum $-2^{n-2}$ is
attained at the point with all coordinates $1/2$, and the maximum $2^{n-2}$ at the point with all
coordinates $1/2 + 1/n^2$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Theorem 3. -/
public theorem_wanted inclExclLikeSum_roundDown_extrema {n : ℕ} (hn : 2 ≤ n) :
    (∀ x : Fin n → ℝ, -2 ^ (n - 2) ≤ inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) x ∧
      inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) x ≤ 2 ^ (n - 2)) ∧
      inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) (fun _ : Fin n => (1 / 2 : ℝ)) = -2 ^ (n - 2) ∧
      inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) (fun _ : Fin n => 1 / 2 + 1 / (n : ℝ) ^ 2) =
        2 ^ (n - 2)

/-- **Sharp bounds for Tverberg's ceiling sum.** Let $\ell \ge 2$ and let $F = \lceil \cdot \rceil$.
For integers $a_1, \dots, a_\ell$, a natural number $m$ and an integer $k$, let
$f(a, m, k) =
\sum_{U \subseteq \{1, \dots, \ell\}} (-1)^{\ell - |U|} F((k + \sum_{i \in U} a_i)/m)$
be Tverberg's sum of $F$, with $x/0 = 0$. Then $-2^{\ell-2} \le f(a, m, k) \le 2^{\ell-2}$ for
all such $a$, $m$ and $k$. Both bounds are attained: for every integer $r \ge 1$, if $a_i = r$
for all $i$ and $m = 2r$, then $f(a, m, 0) = (-1)^{\ell+1} 2^{\ell-2}$ and
$f(a, m, r) = (-1)^{\ell} 2^{\ell-2}$.

The paper states the equality cases separately for odd and even $\ell$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Theorem 4. -/
public theorem_wanted tverbergSum_ceil_bounds {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    (∀ (a : Fin ℓ → ℤ) (m : ℕ) (k : ℤ),
      -2 ^ (ℓ - 2) ≤ tverbergSum Int.ceil a m k ∧ tverbergSum Int.ceil a m k ≤ 2 ^ (ℓ - 2)) ∧
      ∀ r : ℕ, 0 < r →
        tverbergSum Int.ceil (fun _ : Fin ℓ => (r : ℤ)) (2 * r) 0 = (-1) ^ (ℓ + 1) * 2 ^ (ℓ - 2) ∧
          tverbergSum Int.ceil (fun _ : Fin ℓ => (r : ℤ)) (2 * r) r = (-1) ^ ℓ * 2 ^ (ℓ - 2)

/-- **Sharp bounds for Tverberg's sum with rounding half down.** Let $\ell \ge 2$ and let $F$ be
rounding to the nearest integer with ties rounded down, $F(y) = \lceil y - 1/2 \rceil$.
For integers $a_1, \dots, a_\ell$, a natural number $m$ and an integer $k$, let
$f(a, m, k) =
\sum_{U \subseteq \{1, \dots, \ell\}} (-1)^{\ell - |U|} F((k + \sum_{i \in U} a_i)/m)$
be Tverberg's sum of $F$, with $x/0 = 0$. Then $-2^{\ell-2} \le f(a, m, k) \le 2^{\ell-2}$ for
all such $a$, $m$ and $k$. Both bounds are attained: for every integer $r \ge 1$, if $a_i = r$
for all $i$ and $m = 2r$, then $f(a, m, 0) = (-1)^{\ell} 2^{\ell-2}$ and
$f(a, m, r) = (-1)^{\ell+1} 2^{\ell-2}$.

The paper states the equality cases separately for odd and even $\ell$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Theorem 6. -/
public theorem_wanted tverbergSum_roundDown_bounds {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    (∀ (a : Fin ℓ → ℤ) (m : ℕ) (k : ℤ),
      -2 ^ (ℓ - 2) ≤ tverbergSum (fun y : ℝ => ⌈y - 1 / 2⌉) a m k ∧
        tverbergSum (fun y : ℝ => ⌈y - 1 / 2⌉) a m k ≤ 2 ^ (ℓ - 2)) ∧
      ∀ r : ℕ, 0 < r →
        tverbergSum (fun y : ℝ => ⌈y - 1 / 2⌉) (fun _ : Fin ℓ => (r : ℤ)) (2 * r) 0 =
            (-1) ^ ℓ * 2 ^ (ℓ - 2) ∧
          tverbergSum (fun y : ℝ => ⌈y - 1 / 2⌉) (fun _ : Fin ℓ => (r : ℤ)) (2 * r) r =
            (-1) ^ (ℓ + 1) * 2 ^ (ℓ - 2)

/-- **Sharp bounds for two-term tail sums of Tverberg's ceiling sum.** For integers $a, b$ and
natural numbers $m, K$, let
$T(a, b, m, K) = \sum_{k=1}^{K} f^{(\lceil \cdot \rceil)}((a, b), m, k)$, where
$f^{(\lceil \cdot \rceil)}$ is Tverberg's sum with $F$ the ceiling function. Then
$0 \le T(a, b, m, K) \le \lfloor m/2 \rfloor$ for all such $a, b, m, K$. Moreover, for every
natural number $r$, $T(r, r, 2r, 2r) = 0$ and $T(r, r, 2r, r) = r$.

The paper assumes $m, K \ge 1$; for $m = 0$ or $K = 0$ the sum is $0$, so these hypotheses are
not needed.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Theorem 7. -/
public theorem_wanted tverbergTailSum_ceil_two_bounds :
    (∀ (a b : ℤ) (m K : ℕ), 0 ≤ ∑ k ∈ Finset.Icc 1 K, tverbergSum Int.ceil ![a, b] m k ∧
      ∑ k ∈ Finset.Icc 1 K, tverbergSum Int.ceil ![a, b] m k ≤ ((m / 2 : ℕ) : ℤ)) ∧
      ∀ r : ℕ, ∑ k ∈ Finset.Icc 1 (2 * r), tverbergSum Int.ceil ![(r : ℤ), r] (2 * r) k = 0 ∧
        ∑ k ∈ Finset.Icc 1 r, tverbergSum Int.ceil ![(r : ℤ), r] (2 * r) k = r

/-- **Bounds for tail sums of Tverberg's ceiling sum.** Let $\ell \ge 2$. For a tuple
$a = (a_1, \dots, a_\ell)$ of integers and natural numbers $m, K$, let
$T(a, m, K) = \sum_{k=1}^{K} f^{(\lceil \cdot \rceil)}(a, m, k)$, where $f^{(\lceil \cdot \rceil)}$
is Tverberg's sum with $F$ the ceiling function. Then
$-2^{\ell-2} \lfloor m/2 \rfloor \le T(a, m, K) \le 2^{\ell-2} \lfloor m/2 \rfloor$ for all such
$a, m, K$. Moreover, for every natural number $r$, if $a_i = r$ for every $i$, then
$T(a, 2r, r) = (-1)^\ell \, 2^{\ell-2} \, r$.

Theorem 8 as recorded asserts this equality for every $K$, which is false: for $\ell = 3$, $m = 2$,
$a_i = 1$ and $K = 2$ the sum is $0$, not $-2$. The paper's proof establishes it at $K = m/2$,
which is what is stated here.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Theorem 8. -/
public theorem_wanted tverbergTailSum_ceil_bounds {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    (∀ (a : Fin ℓ → ℤ) (m K : ℕ),
      -(2 ^ (ℓ - 2) * ((m / 2 : ℕ) : ℤ)) ≤ ∑ k ∈ Finset.Icc 1 K, tverbergSum Int.ceil a m k ∧
        ∑ k ∈ Finset.Icc 1 K, tverbergSum Int.ceil a m k ≤ 2 ^ (ℓ - 2) * ((m / 2 : ℕ) : ℤ)) ∧
      ∀ r : ℕ, ∑ k ∈ Finset.Icc 1 r, tverbergSum Int.ceil (fun _ : Fin ℓ => (r : ℤ)) (2 * r) k =
        (-1) ^ ℓ * 2 ^ (ℓ - 2) * r

/-- **Bounds for partial Tverberg sums of two integers under rounding half up.** Let
$r^+(y) = \lfloor y + 1/2 \rfloor$ be rounding to the nearest integer with ties rounded up. For
integers $a, b, k$ and a natural number $m$, let
$f(a, b; m, k) = r^+(k/m) - r^+((k + a)/m) - r^+((k + b)/m) + r^+((k + a + b)/m)$ be
Tverberg's sum of $r^+$ at $(a, b)$, with $x/0 = 0$. For all integers $a, b$ and natural
numbers $m, K$,
$-\lfloor m/2 \rfloor \le \sum_{k=0}^{K} f(a, b; m, k) \le \lfloor m/2 \rfloor$. The lower bound
is attained: for every natural number $r$,
$\sum_{k=0}^{r} f(r + 1, r + 1; 2(r + 1), k) = -(r + 1)$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Theorem 9. -/
public theorem_wanted tverbergPartialSum_round_two_bounds :
    (∀ (a b : ℤ) (m K : ℕ),
      -((m / 2 : ℕ) : ℤ) ≤ ∑ k ∈ Finset.range (K + 1), tverbergSum round ![a, b] m k ∧
        ∑ k ∈ Finset.range (K + 1), tverbergSum round ![a, b] m k ≤ ((m / 2 : ℕ) : ℤ)) ∧
      ∀ r : ℕ, ∑ k ∈ Finset.range (r + 1),
        tverbergSum round ![((r + 1 : ℕ) : ℤ), ((r + 1 : ℕ) : ℤ)] (2 * (r + 1)) k =
          -((r + 1 : ℕ) : ℤ)

/-- **Bounds for two-term tail sums of Tverberg's sum with half-down rounding.** Let
$r^-(x) = \lceil x - 1/2 \rceil$. For integers $a, b$ and natural numbers $m, K$, let
$T(a, b, m, K) = \sum_{k=1}^{K} f^{(r^-)}((a, b), m, k)$, where $f^{(r^-)}$ is Tverberg's sum
with $F = r^-$. Then $-\lfloor m/2 \rfloor \le T(a, b, m, K) \le \lfloor m/2 \rfloor$ for all
such $a, b, m, K$, and the lower bound is attained: for every natural number $r$,
$T(r, r, 2r, r) = -r$.

The paper assumes $m, K \ge 1$ and states attainment as an existence claim; here it is stated
through the witness of the paper's proof, and the claims hold trivially at $m = 0$ or $K = 0$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Theorem 10. -/
public theorem_wanted tverbergTailSum_roundDown_two_bounds :
    (∀ (a b : ℤ) (m K : ℕ),
      -((m / 2 : ℕ) : ℤ) ≤
          ∑ k ∈ Finset.Icc 1 K, tverbergSum (fun y : ℝ => ⌈y - 1 / 2⌉) ![a, b] m k ∧
        ∑ k ∈ Finset.Icc 1 K, tverbergSum (fun y : ℝ => ⌈y - 1 / 2⌉) ![a, b] m k ≤
          ((m / 2 : ℕ) : ℤ)) ∧
      ∀ r : ℕ,
        ∑ k ∈ Finset.Icc 1 r, tverbergSum (fun y : ℝ => ⌈y - 1 / 2⌉) ![(r : ℤ), r] (2 * r) k =
          -(r : ℤ)

end

end MetaMathlibExt
