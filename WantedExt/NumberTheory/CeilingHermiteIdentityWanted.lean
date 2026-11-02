/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Order.Floor.BigOperators
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.Order.Round
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Interval.Finset.Nat

/-!
# Inclusion-exclusion-like sums with floor, ceiling and nearest-integer functions (statements)

Mathlib proves Hermite's identity for the floor function as `Int.sum_floor_add_div`
(`∑_{0 ≤ i < n} ⌊x + i/n⌋ = ⌊n x⌋`). This file states the ceiling analogue with the shifted
range `1 ≤ k ≤ n` used by Onphaeng, Khemaratchatakumthorn and Pongsriiam, and the paper's sharp
bounds for the sums `g^(F)`, `f^(F)` and the partial sums `S^(F)`, `T^(F)` of Jacobsthal and
Tverberg type, where `F` is one of `⌊·⌋` (`j = 1`), `⌈·⌉` (`j = 2`),
`r⁺(x) = ⌊x + 1/2⌋` (`j = 3`, Mathlib's `round`, see `round_eq`) and
`r⁻(x) = ⌈x - 1/2⌉` (`j = 4`).

Conventions: the multiset `C = {a_1, …, a_ℓ}` is a tuple `a : Fin ℓ → ℤ`; the modulus `m` is a
natural number, and at `m = 0` Lean's `x / 0 = 0` makes every term `F 0 = 0`, so statements whose
value is then trivially correct carry no positivity hypothesis on `m`. The partial sums are written
inline: `S^(F)(C, m, K) = ∑ k ∈ Finset.range (K + 1), tverbergSum F a m k` and
`T^(F)(C, m, K) = ∑ k ∈ Finset.Icc 1 K, tverbergSum F a m k`. `⌊m/2⌋` is the natural-number
quotient `m / 2`.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Ceiling analogue of Hermite's identity.** For every real number $x$ and every natural
number $n$, $\sum_{k=1}^{n} \lceil x + k/n \rceil = \lceil n x \rceil + n$.

The paper assumes $n \ge 1$; for $n = 0$ both sides are $0$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Lemma 6. -/
public theorem_wanted sum_ceil_add_div_eq_ceil_mul_add (x : ℝ) (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, ⌈x + (k : ℝ) / n⌉ = ⌈(n : ℝ) * x⌉ + n

/-- **Inclusion-exclusion-like sum.** For a function $F : \mathbb{R} \to \mathbb{Z}$ and real
numbers $x_1, \dots, x_n$, the inclusion-exclusion-like sum is the integer
$g^{(F)}(x_1, \dots, x_n) = \sum_T (-1)^{|T| - 1} F\left(\sum_{i \in T} x_i\right)$, where $T$
ranges over the nonempty subsets of $\{1, \dots, n\}$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Definitions 2 and 3. -/
public def inclExclLikeSum {n : ℕ} (F : ℝ → ℤ) (x : Fin n → ℝ) : ℤ :=
  ∑ T : Finset (Fin n) with T.Nonempty, (-1) ^ (T.card - 1) * F (∑ i ∈ T, x i)

/-- **The inclusion-exclusion-like sum in one variable.** For every function
$F : \mathbb{R} \to \mathbb{Z}$ and every real $x$, the inclusion-exclusion-like sum of $F$ in the
single variable $x$ is $g^{(F)}(x) = F(x)$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Definitions 2 and 3. -/
public theorem inclExclLikeSum_one (F : ℝ → ℤ) (x : ℝ) : inclExclLikeSum F ![x] = F x := by
  have h : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  rw [inclExclLikeSum, h, Finset.sum_filter, Finset.sum_insert (by decide), Finset.sum_singleton]
  simp

/-- **The inclusion-exclusion-like sum in two variables.** For every function
$F : \mathbb{R} \to \mathbb{Z}$ and all real numbers $x$ and $y$,
$g^{(F)}(x, y) = F(x) + F(y) - F(x + y)$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Definitions 2 and 3. -/
public theorem inclExclLikeSum_two (F : ℝ → ℤ) (x y : ℝ) :
    inclExclLikeSum F ![x, y] = F x + F y - F (x + y) := by
  have h : (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [inclExclLikeSum, h, Finset.sum_filter, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp
  ring

/-- **Tverberg's sum.** Let $F : \mathbb{R} \to \mathbb{Z}$, let $a = (a_1, \dots, a_\ell)$ be a
tuple of integers, let $m$ be a natural number and let $k$ be an integer. Tverberg's sum is
$f^{(F)}(a, m, k) = \sum_{T \subseteq \{1, \dots, \ell\}} (-1)^{\ell - |T|}
F((k + \sum_{i \in T} a_i) / m)$, where the division is in $\mathbb{R}$ (with $x / 0 = 0$).

The paper takes $F = \lfloor \cdot \rfloor$ in Definition 1, and $F = \lceil \cdot \rceil$,
$x \mapsto \lfloor x + 1/2 \rfloor$ or $x \mapsto \lceil x - 1/2 \rceil$ in Section 1 and
Definition 3.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Definitions 1 and 3. -/
public noncomputable def tverbergSum {ℓ : ℕ} (F : ℝ → ℤ) (a : Fin ℓ → ℤ) (m : ℕ) (k : ℤ) : ℤ :=
  ∑ T : Finset (Fin ℓ), (-1) ^ (ℓ - T.card) * F (((k + ∑ i ∈ T, a i : ℤ) : ℝ) / m)

/-- **Tverberg's sum of the empty tuple.** For every function $F : \mathbb{R} \to \mathbb{Z}$,
every natural number $m$ and every integer $k$, Tverberg's sum of the empty tuple of integers is
$f^{(F)}(\emptyset, m, k) = F(k / m)$, where $k / m$ is division in $\mathbb{R}$ (with $x / 0 = 0$).

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Definitions 1 and 3. -/
public theorem tverbergSum_zero (F : ℝ → ℤ) (a : Fin 0 → ℤ) (m : ℕ) (k : ℤ) :
    tverbergSum F a m k = F (k / m) := by
  simp [tverbergSum, Finset.univ_unique, Finset.eq_empty_of_isEmpty]

/-- **Tverberg's sum of a single integer.** For every function $F : \mathbb{R} \to \mathbb{Z}$,
all integers $a$ and $k$ and every natural number $m$, Tverberg's sum of $F$ for the one-element
family $(a)$, modulus $m$ and shift $k$ equals $F((k + a)/m) - F(k/m)$, with $x/0 = 0$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Definitions 1 and 3. -/
public theorem tverbergSum_one (F : ℝ → ℤ) (a : ℤ) (m : ℕ) (k : ℤ) :
    tverbergSum F ![a] m k = F ((k + a : ℤ) / m) - F (k / m) := by
  have h : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
  simp [tverbergSum, h]
  ring

/-- **Relations and periodicity of the inclusion-exclusion-like sums.** Let $n \ge 2$ and write
$g_1$, $g_2$, $g_3$, $g_4$ for the inclusion-exclusion-like sums $g^{(F)}$ with $F$ the floor
function $\lfloor y \rfloor$, the ceiling function $\lceil y \rceil$, the nearest-integer function
$\lfloor y + 1/2 \rfloor$ (ties rounded up) and $\lceil y - 1/2 \rceil$ (ties rounded down),
respectively. For every $x = (x_1, \dots, x_n) \in \mathbb{R}^n$:
(i) $g_3(x) = g_1(x) - g_1(x_1, \dots, x_n, 1/2)$;
(ii) $g_4(x) = g_2(x) - g_2(x_1, \dots, x_n, -1/2)$;
(iii) for each $j \in \{1, 2, 3, 4\}$, each index $i$ and each integer $q$, adding $q$ to $x_i$
does not change $g_j(x)$.

Parts (i) and (ii) also hold for $n < 2$; part (iii) fails for $n = 1$, where
$g_1(x) = \lfloor x \rfloor$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Lemma 1. -/
public theorem_wanted inclExclLikeSum_relations_and_periodic {n : ℕ} (hn : 2 ≤ n)
    (x : Fin n → ℝ) :
    inclExclLikeSum round x =
        inclExclLikeSum Int.floor x - inclExclLikeSum Int.floor (Fin.snoc x (1 / 2 : ℝ)) ∧
      inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) x =
        inclExclLikeSum Int.ceil x - inclExclLikeSum Int.ceil (Fin.snoc x (-1 / 2 : ℝ)) ∧
      ∀ F ∈ ({Int.floor, Int.ceil, round, fun y : ℝ => ⌈y - 1 / 2⌉} : Set (ℝ → ℤ)),
        ∀ (i : Fin n) (q : ℤ),
        inclExclLikeSum F (Function.update x i (x i + q)) = inclExclLikeSum F x

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

/-- **Periodicity of Tverberg's sum.** Let $\ell \ge 2$ and let $F$ be one of
$\lfloor \cdot \rfloor$, $\lceil \cdot \rceil$, $r^+(y) = \lfloor y + 1/2 \rfloor$ and
$r^-(y) = \lceil y - 1/2 \rceil$.
For integers $a_1, \dots, a_\ell$, a natural number $m$ and an integer $k$, let
$f(a, m, k) =
\sum_{U \subseteq \{1, \dots, \ell\}} (-1)^{\ell - |U|} F((k + \sum_{i \in U} a_i)/m)$
be Tverberg's sum of $F$, with $x/0 = 0$. For every index $i$ and every integer $q$, replacing
$a_i$ by $a_i + q m$ does not change $f(a, m, k)$, and $f(a, m, k + q m) = f(a, m, k)$.

The hypothesis $\ell \ge 2$ is needed: for $\ell = 1$, $F = \lfloor \cdot \rfloor$ and $m \ge 1$,
$f((a), m, k) = \lfloor (k + a)/m \rfloor - \lfloor k/m \rfloor$ increases by $q$ when $a$ is
replaced by $a + q m$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Lemma 3. -/
public theorem_wanted tverbergSum_periodic {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (F : ℝ → ℤ)
    (hF : F ∈ ({Int.floor, Int.ceil, round, fun y : ℝ => ⌈y - 1 / 2⌉} : Set (ℝ → ℤ)))
    (a : Fin ℓ → ℤ) (m : ℕ) (k : ℤ) (i : Fin ℓ) (q : ℤ) :
    tverbergSum F (Function.update a i (a i + q * m)) m k = tverbergSum F a m k ∧
      tverbergSum F a m (k + q * m) = tverbergSum F a m k

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

/-- **Extrema of the floor inclusion-exclusion-like sum.** Let $n \ge 2$ and let $g_1$ be the
inclusion-exclusion-like sum $g^{(F)}$ in $n$ real variables with $F$ the floor function. Then
$-2^{n-2} \le g_1(x) \le 2^{n-2} - 1$ for every $x \in \mathbb{R}^n$; the minimum $-2^{n-2}$ is
attained at the point with all coordinates $1/2$, and the maximum $2^{n-2} - 1$ at the point with
all coordinates $1/2 - 1/n^2$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Lemma 5. -/
public theorem_wanted inclExclLikeSum_floor_extrema {n : ℕ} (hn : 2 ≤ n) :
    (∀ x : Fin n → ℝ, -2 ^ (n - 2) ≤ inclExclLikeSum Int.floor x ∧
      inclExclLikeSum Int.floor x ≤ 2 ^ (n - 2) - 1) ∧
      inclExclLikeSum Int.floor (fun _ : Fin n => (1 / 2 : ℝ)) = -2 ^ (n - 2) ∧
      inclExclLikeSum Int.floor (fun _ : Fin n => 1 / 2 - 1 / (n : ℝ) ^ 2) = 2 ^ (n - 2) - 1

/-- **Vanishing and periodicity of partial Tverberg sums.** Let $\ell \ge 2$, let
$a = (a_1, \dots, a_\ell)$ be integers and let $m$ be a natural number. Let $F$ be one of
$\lfloor \cdot \rfloor$, $\lceil \cdot \rceil$, $r^+(y) = \lfloor y + 1/2 \rfloor$ and
$r^-(y) = \lceil y - 1/2 \rceil$, and for an integer $k$ let
$f^F(a, k) =
\sum_{U \subseteq \{1, \dots, \ell\}} (-1)^{\ell - |U|} F((k + \sum_{i \in U} a_i)/m)$
be Tverberg's sum, with $x/0 = 0$. For natural $K$ put $S^F(a, K) = \sum_{k=0}^{K} f^F(a, k)$
and $T^F(a, K) = \sum_{k=1}^{K} f^F(a, k)$, and for an index $i$ and an integer $p$ let $a'$ be
$a$ with $a_i$ replaced by $a_i + p m$. Then:
(i) $\sum_{k=0}^{m-1} f^F(a, k) = 0$ (an empty sum when $m = 0$);
(ii) $S^F(a, K + q m) = S^F(a, K)$ for all natural $K$ and $q$, and $S^F(a', K) = S^F(a, K)$
for every natural $K$, every index $i$ and every integer $p$;
(iii) if $F$ is $\lceil \cdot \rceil$ or $r^-$, then $T^F(a, m) = 0$,
$T^F(a, K + q m) = T^F(a, K)$ for all natural $K$ and $q$, and $T^F(a', K) = T^F(a, K)$ for
every natural $K$, every index $i$ and every integer $p$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Lemma 7. -/
public theorem_wanted tverbergPartialSum_vanish_and_periodic {ℓ : ℕ} (hℓ : 2 ≤ ℓ)
    (a : Fin ℓ → ℤ) (m : ℕ) :
    (∀ F ∈ ({Int.floor, Int.ceil, round, fun y : ℝ => ⌈y - 1 / 2⌉} : Set (ℝ → ℤ)),
      ∑ k ∈ Finset.range m, tverbergSum F a m k = 0 ∧
        ∀ K q : ℕ, ∑ k ∈ Finset.range (K + q * m + 1), tverbergSum F a m k =
          ∑ k ∈ Finset.range (K + 1), tverbergSum F a m k ∧
        ∀ (K : ℕ) (i : Fin ℓ) (q : ℤ),
          ∑ k ∈ Finset.range (K + 1), tverbergSum F (Function.update a i (a i + q * m)) m k =
            ∑ k ∈ Finset.range (K + 1), tverbergSum F a m k) ∧
      ∀ F ∈ ({Int.ceil, fun y : ℝ => ⌈y - 1 / 2⌉} : Set (ℝ → ℤ)),
        ∑ k ∈ Finset.Icc 1 m, tverbergSum F a m k = 0 ∧
          ∀ K q : ℕ, ∑ k ∈ Finset.Icc 1 (K + q * m), tverbergSum F a m k =
            ∑ k ∈ Finset.Icc 1 K, tverbergSum F a m k ∧
          ∀ (K : ℕ) (i : Fin ℓ) (q : ℤ),
            ∑ k ∈ Finset.Icc 1 K, tverbergSum F (Function.update a i (a i + q * m)) m k =
              ∑ k ∈ Finset.Icc 1 K, tverbergSum F a m k

/-- **Floor and ceiling of a quotient plus one half.** For every integer $q$ and every positive
integer $m$, $\lfloor q/m + 1/2 \rfloor = \lfloor (q + \lfloor m/2 \rfloor)/m \rfloor$ and
$\lceil q/m + 1/2 \rceil = \lceil (q + \lceil m/2 \rceil)/m \rceil$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Lemma 8. -/
public theorem_wanted floor_ceil_div_add_half (q : ℤ) (m : ℕ) (hm : 0 < m) :
    ⌊(q : ℝ) / m + 1 / 2⌋ = ⌊((q + (m / 2 : ℕ) : ℤ) : ℝ) / m⌋ ∧
      ⌈(q : ℝ) / m + 1 / 2⌉ = ⌈((q + ((m + 1) / 2 : ℕ) : ℤ) : ℝ) / m⌉

/-- **Extrema of the ceiling inclusion-exclusion-like sum.** Let $n \ge 2$ and let $g_2$ be the
inclusion-exclusion-like sum $g^{(F)}$ in $n$ real variables with $F$ the ceiling function. Then
$-2^{n-2} + 1 \le g_2(x) \le 2^{n-2}$ for every $x \in \mathbb{R}^n$; the minimum $-2^{n-2} + 1$
is attained at the point with all coordinates $1/2 + 1/n^2$, and the maximum $2^{n-2}$ at the
point with all coordinates $1/2$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Theorem 1. -/
public theorem_wanted inclExclLikeSum_ceil_extrema {n : ℕ} (hn : 2 ≤ n) :
    (∀ x : Fin n → ℝ, -2 ^ (n - 2) + 1 ≤ inclExclLikeSum Int.ceil x ∧
      inclExclLikeSum Int.ceil x ≤ 2 ^ (n - 2)) ∧
      inclExclLikeSum Int.ceil (fun _ : Fin n => 1 / 2 + 1 / (n : ℝ) ^ 2) = -2 ^ (n - 2) + 1 ∧
      inclExclLikeSum Int.ceil (fun _ : Fin n => (1 / 2 : ℝ)) = 2 ^ (n - 2)

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

/-- **Bounds for the four inclusion-exclusion-like sums.** Let $n \ge 2$ and write $g_1$, $g_2$,
$g_3$, $g_4$ for the inclusion-exclusion-like sums $g^{(F)}$ in $n$ real variables with $F$ the
floor function $\lfloor y \rfloor$, the ceiling function $\lceil y \rceil$, the nearest-integer
function $\lfloor y + 1/2 \rfloor$ (ties rounded up) and $\lceil y - 1/2 \rceil$ (ties rounded
down), respectively. Then for every $x \in \mathbb{R}^n$,
$-2^{n-2} \le g_1(x) \le 2^{n-2} - 1$, $-2^{n-2} + 1 \le g_2(x) \le 2^{n-2}$,
$-2^{n-2} \le g_3(x) \le 2^{n-2}$ and $-2^{n-2} \le g_4(x) \le 2^{n-2}$. At the point with all
coordinates $1/2$, $g_1 = g_4 = -2^{n-2}$ and $g_2 = g_3 = 2^{n-2}$. At the point with all
coordinates $1/2 - 1/n^2$, $g_1 = 2^{n-2} - 1 = -g_3 - 1$. At the point with all coordinates
$1/2 + 1/n^2$, $g_2 = -2^{n-2} + 1 = -g_4 + 1$.

Source: Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Prapanpong Pongsriiam,
*Inequalities for Inclusion-Exclusion-Like Sums Involving the Ceiling and the Nearest Integer
Functions*, INTEGERS 25 (2025), Article A45, Corollary 1. -/
public theorem_wanted inclExclLikeSum_bounds_summary {n : ℕ} (hn : 2 ≤ n) :
    (∀ x : Fin n → ℝ,
      (-2 ^ (n - 2) ≤ inclExclLikeSum Int.floor x ∧
        inclExclLikeSum Int.floor x ≤ 2 ^ (n - 2) - 1) ∧
      (-2 ^ (n - 2) + 1 ≤ inclExclLikeSum Int.ceil x ∧
        inclExclLikeSum Int.ceil x ≤ 2 ^ (n - 2)) ∧
      (-2 ^ (n - 2) ≤ inclExclLikeSum round x ∧ inclExclLikeSum round x ≤ 2 ^ (n - 2)) ∧
      (-2 ^ (n - 2) ≤ inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) x ∧
        inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) x ≤ 2 ^ (n - 2))) ∧
    (inclExclLikeSum Int.floor (fun _ : Fin n => (1 / 2 : ℝ)) = -2 ^ (n - 2) ∧
      inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) (fun _ : Fin n => (1 / 2 : ℝ)) = -2 ^ (n - 2) ∧
      inclExclLikeSum Int.ceil (fun _ : Fin n => (1 / 2 : ℝ)) = 2 ^ (n - 2) ∧
      inclExclLikeSum round (fun _ : Fin n => (1 / 2 : ℝ)) = 2 ^ (n - 2)) ∧
    (inclExclLikeSum Int.floor (fun _ : Fin n => 1 / 2 - 1 / (n : ℝ) ^ 2) = 2 ^ (n - 2) - 1 ∧
      inclExclLikeSum Int.floor (fun _ : Fin n => 1 / 2 - 1 / (n : ℝ) ^ 2) =
        -inclExclLikeSum round (fun _ : Fin n => 1 / 2 - 1 / (n : ℝ) ^ 2) - 1) ∧
    (inclExclLikeSum Int.ceil (fun _ : Fin n => 1 / 2 + 1 / (n : ℝ) ^ 2) = -2 ^ (n - 2) + 1 ∧
      inclExclLikeSum Int.ceil (fun _ : Fin n => 1 / 2 + 1 / (n : ℝ) ^ 2) =
        -inclExclLikeSum (fun y : ℝ => ⌈y - 1 / 2⌉) (fun _ : Fin n => 1 / 2 + 1 / (n : ℝ) ^ 2) + 1)

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

/-- **Sharp bounds for Tverberg's sum with rounding half up.** Let $\ell \ge 2$ and let $F$ be
rounding to the nearest integer with ties rounded up, $F(y) = \lfloor y + 1/2 \rfloor$.
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
Functions*, INTEGERS 25 (2025), Article A45, Theorem 5. -/
public theorem_wanted tverbergSum_round_bounds {ℓ : ℕ} (hℓ : 2 ≤ ℓ) :
    (∀ (a : Fin ℓ → ℤ) (m : ℕ) (k : ℤ),
      -2 ^ (ℓ - 2) ≤ tverbergSum round a m k ∧ tverbergSum round a m k ≤ 2 ^ (ℓ - 2)) ∧
      ∀ r : ℕ, 0 < r →
        tverbergSum round (fun _ : Fin ℓ => (r : ℤ)) (2 * r) 0 = (-1) ^ (ℓ + 1) * 2 ^ (ℓ - 2) ∧
          tverbergSum round (fun _ : Fin ℓ => (r : ℤ)) (2 * r) r = (-1) ^ ℓ * 2 ^ (ℓ - 2)

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
