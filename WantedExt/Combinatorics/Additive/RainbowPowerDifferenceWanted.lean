/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.ZMod.Basic
public import Mathlib.Basic.Real.Basic

/-! # Rainbow-free colorings for `x - y = z ^ k`

Statement-only requests from Ansaldi, Cowley, Green, Kim and Rapp. A coloring `c` is
rainbow-free for `x - y = z ^ k` when no solution has `c x`, `c y`, `c z` pairwise distinct,
and exact when every color is used (`Function.Surjective c`). The digraph `G^k_p` has vertex
set `ZMod p` and edges `a → a ^ k`; two vertices lie in the same (weak) component exactly when
`a ^ k ^ m = b ^ k ^ n` for some `m n : ℕ`. Color-class sizes are `Nat.card`s of subtypes.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Rainbow-free 3-colorings modulo a prime have a singleton color class.** Let $p$ be a prime
and $k$ a natural number, and let $c$ be a coloring of $\mathbb{Z}/p\mathbb{Z}$ with three colors
that uses every color and is rainbow-free for $x - y = z^k$: no $x, y, z \in \mathbb{Z}/p\mathbb{Z}$
with $x - y = z^k$ have $c(x), c(y), c(z)$ pairwise distinct. Then some color is taken by exactly
one element of $\mathbb{Z}/p\mathbb{Z}$.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Corollary 1
(`integers-2024-A105-cor-1`). -/
public theorem_wanted exists_card_colorClass_eq_one_of_rainbowFree_powDiff
    (p k : ℕ) [Fact p.Prime] (c : ZMod p → Fin 3) (hc : Function.Surjective c)
    (hrf : ∀ x y z : ZMod p, x - y = z ^ k → ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z)) :
    ∃ i : Fin 3, Nat.card {a : ZMod p // c a = i} = 1

/-- **Zero has a color class of its own.** Let $p$ be a prime and $k$ a natural number, and let $c$
be a coloring of $\mathbb{Z}/p\mathbb{Z}$ with three colors that uses every color and is
rainbow-free for $x - y = z^k$: no $x, y, z \in \mathbb{Z}/p\mathbb{Z}$ with $x - y = z^k$ have
$c(x), c(y), c(z)$ pairwise distinct. If $a \in \mathbb{Z}/p\mathbb{Z}$ satisfies $c(a) = c(0)$,
then $a = 0$.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Corollary 2
(`integers-2024-A105-cor-2`). -/
public theorem_wanted eq_zero_of_color_eq_color_zero_of_rainbowFree_powDiff
    (p k : ℕ) [Fact p.Prime] (c : ZMod p → Fin 3) (hc : Function.Surjective c)
    (hrf : ∀ x y z : ZMod p, x - y = z ^ k → ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z))
    (a : ZMod p) (ha : c a = c 0) : a = 0

/-- **Rainbow-free colorings of $\mathbb{Z}/n\mathbb{Z}$ lift to the positive integers.** Let $n$
and $k$ be natural numbers and let $c$ be a coloring of $\mathbb{Z}/n\mathbb{Z}$ with three colors
that is rainbow-free for $x - y = z^k$: there are no $x, y, z \in \mathbb{Z}/n\mathbb{Z}$ with
$x - y = z^k$ whose colors $c(x)$, $c(y)$, $c(z)$ are pairwise distinct. Then the coloring
$i \mapsto c(i \bmod n)$ of the positive integers is rainbow-free for $x - y = z^k$: for all
positive integers $x, y, z$ with $x = y + z^k$, the colors $c(x \bmod n)$, $c(y \bmod n)$ and
$c(z \bmod n)$ are not pairwise distinct. (For $n = 0$, $\mathbb{Z}/0\mathbb{Z}$ is $\mathbb{Z}$
and $i \bmod 0 = i$.)

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 7
(`integers-2024-A105-lem-7`). -/
public theorem_wanted rainbowFree_powDiff_lift_of_zmod
    (n k : ℕ) (c : ZMod n → Fin 3)
    (hrf : ∀ x y z : ZMod n, x - y = z ^ k → ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z))
    (x y z : ℕ) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) (h : x = y + z ^ k) :
    ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z)

/-- **Coprime representatives at a coprime distance.** Let $n$ be a natural number and let $c$ be a
coloring of $\mathbb{Z}/n\mathbb{Z}$ with three colors, used to color every positive integer by its
residue modulo $n$. If $i_1, i_2$ are positive integers with $\gcd(|i_1 - i_2|, n) = 1$, then there
are coprime positive integers $j_1, j_2$ with $|j_1 - j_2| = |i_1 - i_2|$ such that $j_1$ has the
color of $i_1$ and $j_2$ has the color of $i_2$.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 8
(`integers-2024-A105-lem-8`). -/
public theorem_wanted exists_coprime_same_colors_of_coprime_dist
    (n : ℕ) (c : ZMod n → Fin 3) (i₁ i₂ : ℕ) (hi₁ : 0 < i₁) (hi₂ : 0 < i₂)
    (hd : Nat.Coprime ((i₁ : ℤ) - i₂).natAbs n) :
    ∃ j₁ j₂ : ℕ, 0 < j₁ ∧ 0 < j₂ ∧ Nat.Coprime j₁ j₂ ∧ c j₁ = c i₁ ∧ c j₂ = c i₂ ∧
      ((j₁ : ℤ) - j₂).natAbs = ((i₁ : ℤ) - i₂).natAbs

/-- **Rainbow-free colorings modulo a prime are symmetric under negation.** Let $p$ be a prime and
$k$ a natural number, and let $c$ be a coloring of $\mathbb{Z}/p\mathbb{Z}$ with three colors that
uses every color and is rainbow-free for $x - y = z^k$: no $x, y, z \in \mathbb{Z}/p\mathbb{Z}$
with $x - y = z^k$ have $c(x), c(y), c(z)$ pairwise distinct. Then $c(-a) = c(a)$ for every
$a \in \mathbb{Z}/p\mathbb{Z}$.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 10
(`integers-2024-A105-lem-10`). -/
public theorem_wanted color_neg_eq_of_rainbowFree_powDiff
    (p k : ℕ) [Fact p.Prime] (c : ZMod p → Fin 3) (hc : Function.Surjective c)
    (hrf : ∀ x y z : ZMod p, x - y = z ^ k → ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z))
    (a : ZMod p) : c (-a) = c a

/-- **Each component of the power digraph has exactly one cycle.** Let $p$ be a prime and $k$ a
natural number, and let $G^k_p$ be the digraph on $\mathbb{Z}/p\mathbb{Z}$ with edges
$a \to a^k$, so that $m$ steps lead from $a$ to $a^{k^m}$. Call $a$ a cycle vertex if
$a^{k^r} = a$ for some $r > 0$, and say that $a$ and $b$ lie in the same component if
$a^{k^m} = b^{k^n}$ for some $m, n \ge 0$. Then every $a$ has a cycle vertex $a^{k^m}$ among its
iterates, and if two cycle vertices $a$ and $b$ lie in the same component, then $b = a^{k^m}$
for some $m \ge 0$. Thus every component of $G^k_p$ contains exactly one cycle.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 12
(`integers-2024-A105-lem-12`). -/
public theorem_wanted powMap_component_unique_cycle (p k : ℕ) [Fact p.Prime] :
    (∀ a : ZMod p, ∃ m : ℕ, ∃ r : ℕ, 0 < r ∧ (a ^ k ^ m) ^ k ^ r = a ^ k ^ m) ∧
      ∀ a b : ZMod p, (∃ r : ℕ, 0 < r ∧ a ^ k ^ r = a) → (∃ r : ℕ, 0 < r ∧ b ^ k ^ r = b) →
        (∃ m n : ℕ, a ^ k ^ m = b ^ k ^ n) → ∃ m : ℕ, a ^ k ^ m = b

/-- **Power digraphs modulo a prime with two components.** Let $p$ be a prime and $k > 0$ an even
natural number, and let $G^k_p$ be the directed graph on $\mathbb{Z}/p\mathbb{Z}$ with an edge
$a \to a^k$ from every vertex $a$. Its (weak) components are the classes of the equivalence
relation "$a^{k^m} = b^{k^n}$ for some natural numbers $m, n$". Then $G^k_p$ has exactly two
components if and only if every prime factor of $p - 1$ divides $k$.

In the source, writing the prime factorization of $k$ as
$k = 2^{\alpha_0} q_1^{\alpha_1} \cdots q_\ell^{\alpha_\ell}$ with distinct odd primes
$q_1, \dots, q_\ell$, the condition reads
$p - 1 = 2^{\beta_0} q_1^{\beta_1} \cdots q_\ell^{\beta_\ell}$ with all $\beta_i \ge 0$.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Proposition 1
(`integers-2024-A105-prop-1`). -/
public theorem_wanted card_powMap_components_eq_two_iff_of_even
    (p k : ℕ) [Fact p.Prime] (hk : Even k) (hk0 : 0 < k) :
    Nat.card (Quot fun a b : ZMod p => ∃ m n : ℕ, a ^ k ^ m = b ^ k ^ n) = 2 ↔
      ∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ k

/-- **Power digraphs modulo a prime with three components.** Let $p$ be a prime and $k \ge 3$ an
odd natural number, and let $G^k_p$ be the directed graph on $\mathbb{Z}/p\mathbb{Z}$ with an edge
$a \to a^k$ from every vertex $a$. Its (weak) components are the classes of the equivalence
relation "$a^{k^m} = b^{k^n}$ for some natural numbers $m, n$". Then $G^k_p$ has exactly three
components if and only if $p - 1 = 2m$ for some natural number $m$ every prime factor of which
divides $k$.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Proposition 2
(`integers-2024-A105-prop-2`). -/
public theorem_wanted card_powMap_components_eq_three_iff_of_odd
    (p k : ℕ) [Fact p.Prime] (hk : Odd k) (hk3 : 3 ≤ k) :
    Nat.card (Quot fun a b : ZMod p => ∃ m n : ℕ, a ^ k ^ m = b ^ k ^ n) = 3 ↔
      ∃ m : ℕ, p - 1 = 2 * m ∧ ∀ q : ℕ, q.Prime → q ∣ m → q ∣ k

/-- **Large multiples of the gcd are nonnegative combinations.** Let $i$ and $j$ be positive
integers. There is an $n_0$ such that every integer $m > n_0$ divisible by $\gcd(i, j)$ can be
written as $m = ui + vj$ with nonnegative integers $u$ and $v$.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Theorem 2
(`integers-2024-A105-thm-2`). -/
public theorem_wanted exists_forall_gcd_dvd_eq_add_mul (i j : ℕ) (hi : 0 < i) (hj : 0 < j) :
    ∃ n₀ : ℕ, ∀ m : ℕ, n₀ < m → Nat.gcd i j ∣ m → ∃ u v : ℕ, m = u * i + v * j

/-- **Upper density threshold for rainbow solutions of $x - y = z^k$.** Let $k \ge 2$ be an
integer, let $s = \lfloor k / 2 \rfloor$ and $\delta = (4^s - 1) / (3 \cdot 4^s)$, and let $c$ be
a coloring of the positive integers by three colors. Suppose that for each color $e$ there is
an $\varepsilon > 0$ such that, for arbitrarily large $N$, more than $(\delta + \varepsilon) N$
of the integers $x \in \{1, \dots, N\}$ have $c(x) = e$; that is, every color class has upper
density greater than $\delta$. Then there are positive integers $x, y, z$ with $x = y + z^k$
such that $c(x)$, $c(y)$, $c(z)$ are pairwise distinct.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Theorem 3
(`integers-2024-A105-thm-3`). -/
public theorem_wanted exists_rainbow_powDiff_of_upperDensity (k : ℕ) (hk : 2 ≤ k)
    (c : ℕ → Fin 3)
    (hdens : ∀ i : Fin 3, ∃ ε : ℝ, 0 < ε ∧ ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      ((4 : ℝ) ^ (k / 2) - 1) / (3 * 4 ^ (k / 2)) + ε <
        (((Finset.Icc 1 N).filter fun x => c x = i).card : ℝ) / N) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x = y + z ^ k ∧
      c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z

/-- **Small color classes in rainbow-free 3-colorings modulo an odd integer.** Let $n$ be an odd
natural number, let $r_1$ be its smallest prime factor (with $r_1 = 1$ when $n = 1$), let $k$ be a
natural number, and let $c$ be a coloring of $\mathbb{Z}/n\mathbb{Z}$ with three colors that uses
every color and is rainbow-free for $x - y = z^k$: no $x, y, z \in \mathbb{Z}/n\mathbb{Z}$ with
$x - y = z^k$ have $c(x), c(y), c(z)$ pairwise distinct. Then some color class has at most
$n / r_1$ elements.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Theorem 4
(`integers-2024-A105-thm-4`). -/
public theorem_wanted exists_card_colorClass_le_div_minFac_of_rainbowFree_powDiff
    (n k : ℕ) (hn : Odd n) (c : ZMod n → Fin 3) (hc : Function.Surjective c)
    (hrf : ∀ x y z : ZMod n, x - y = z ^ k → ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z)) :
    ∃ i : Fin 3, Nat.card {a : ZMod n // c a = i} ≤ n / n.minFac

/-- **Rainbow-free colorings of $\mathbb{Z}/p\mathbb{Z}$ for $x - y = z^k$.** Let $p$ be a prime,
$k$ a natural number, and $c$ a coloring of $\mathbb{Z}/p\mathbb{Z}$ by three colors that uses
all three. Then $c$ has no solution of $x - y = z^k$ in $\mathbb{Z}/p\mathbb{Z}$ with $c(x)$,
$c(y)$, $c(z)$ pairwise distinct if and only if the following three conditions hold: $0$ is the
only element of its color class; $c(a) = c(b)$ whenever $a^{k^m} = b^{k^n}$ for some
$m, n \ge 0$, that is, every component of the digraph $a \mapsto a^k$ is monochromatic; and
$c(-a) = c(a)$ for every $a$.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Theorem 5
(`integers-2024-A105-thm-5`). -/
public theorem_wanted rainbowFree_powDiff_iff
    (p k : ℕ) [Fact p.Prime] (c : ZMod p → Fin 3) (hc : Function.Surjective c) :
    (∀ x y z : ZMod p, x - y = z ^ k → ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z)) ↔
      (∀ a : ZMod p, c a = c 0 → a = 0) ∧
        (∀ a b : ZMod p, (∃ m n : ℕ, a ^ k ^ m = b ^ k ^ n) → c a = c b) ∧
        ∀ a : ZMod p, c (-a) = c a

/-- **Rainbow number of the power-difference equation modulo a prime, even exponent.** Let $p$ be
a prime and $k$ an even natural number. A coloring of $\mathbb{Z}/p\mathbb{Z}$ with $r$ colors is
exact if it uses every color, and a solution of $x - y = z^k$ in $\mathbb{Z}/p\mathbb{Z}$ is
rainbow if $x$, $y$ and $z$ receive pairwise distinct colors. Then the least $r \ge 3$ such that
every exact coloring of $\mathbb{Z}/p\mathbb{Z}$ with $r$ colors has a rainbow solution of
$x - y = z^k$ is $3$ if every prime factor of $p - 1$ divides $k$, and $4$ otherwise.

The bound $r \ge 3$ is part of the definition: a rainbow solution needs three colors, and for
$r = 0$ the condition would hold vacuously, as $\mathbb{Z}/p\mathbb{Z}$ has no coloring with no
colors.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Theorem 7
(`integers-2024-A105-thm-7`). -/
public theorem_wanted rainbowNumber_powDiff_of_even (p k : ℕ) [Fact p.Prime] (hk : Even k) :
    ((∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ k) →
      sInf {r : ℕ | 3 ≤ r ∧ ∀ c : ZMod p → Fin r, Function.Surjective c →
        ∃ x y z : ZMod p, x - y = z ^ k ∧ c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z} = 3) ∧
    (¬ (∀ q : ℕ, q.Prime → q ∣ p - 1 → q ∣ k) →
      sInf {r : ℕ | 3 ≤ r ∧ ∀ c : ZMod p → Fin r, Function.Surjective c →
        ∃ x y z : ZMod p, x - y = z ^ k ∧ c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z} = 4)

/-- **Rainbow number of the power-difference equation modulo a prime, odd exponent.** Let $p$ be
an odd prime and $k \ge 3$ an odd natural number. A coloring of $\mathbb{Z}/p\mathbb{Z}$ with $r$
colors is exact if it uses every color, and a solution of $x - y = z^k$ in $\mathbb{Z}/p\mathbb{Z}$
is rainbow if $x$, $y$ and $z$ receive pairwise distinct colors. Then the least $r \ge 3$ such
that every exact coloring of $\mathbb{Z}/p\mathbb{Z}$ with $r$ colors has a rainbow solution of
$x - y = z^k$ is $3$ if $p - 1 = 2m$ for a natural number $m$ all of whose prime factors divide
$k$, and $4$ otherwise.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Theorem 8
(`integers-2024-A105-thm-8`). -/
public theorem_wanted rainbowNumber_powDiff_of_odd (p k : ℕ) [Fact p.Prime] (hp : p ≠ 2)
    (hk : Odd k) (hk3 : 3 ≤ k) :
    ((∃ m : ℕ, p - 1 = 2 * m ∧ ∀ q : ℕ, q.Prime → q ∣ m → q ∣ k) →
      sInf {r : ℕ | 3 ≤ r ∧ ∀ c : ZMod p → Fin r, Function.Surjective c →
        ∃ x y z : ZMod p, x - y = z ^ k ∧ c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z} = 3) ∧
    (¬ (∃ m : ℕ, p - 1 = 2 * m ∧ ∀ q : ℕ, q.Prime → q ∣ m → q ∣ k) →
      sInf {r : ℕ | 3 ≤ r ∧ ∀ c : ZMod p → Fin r, Function.Surjective c →
        ∃ x y z : ZMod p, x - y = z ^ k ∧ c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z} = 4)


/-- **The color of one dominates bichromatic strings.** Let $r$ and $k$ be natural numbers and let
$c$ be a coloring of the positive integers with $r$ colors that uses every color on some positive
integer and is rainbow-free for $x - y = z^k$: no positive integers $x, y, z$ with $x = y + z^k$
have $c(x), c(y), c(z)$ pairwise distinct. Then for every positive integer $i$ and every natural
number $\ell$, if $c$ takes exactly two colors on $i, i + 1, \dots, i + \ell - 1$, one of these
integers has the color $c(1)$.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 1
(`integers-2024-A105-lem-1`). -/
public theorem_wanted color_one_dominant_of_rainbowFree_powDiff (r k : ℕ) (c : ℕ → Fin r)
    (hc : ∀ j : Fin r, ∃ i : ℕ, 0 < i ∧ c i = j)
    (hrf : ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → x = y + z ^ k →
      ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z))
    (i ℓ : ℕ) (hi : 0 < i) (hbi : ((Finset.Ico i (i + ℓ)).image c).card = 2) :
    c 1 ∈ (Finset.Ico i (i + ℓ)).image c

/-- **Shifting monochromatic strings by $k$-th powers.** Let $k$ be a natural number and let $c$
be a coloring of the positive integers by three distinct colors $R$, $B$, $G$ with no rainbow
solution of $x - y = z^k$: there are no positive integers $x, y, z$ with $x = y + z^k$ and
$c(x)$, $c(y)$, $c(z)$ pairwise distinct. Assume that $R$ is dominant: for all positive integers
$i$ and all $\ell \ge 0$, if $c$ takes exactly two colors on $\{i, i + 1, \dots, i + \ell - 1\}$,
then one of them is $R$. Let $j$ be a positive integer with $c(j) = B$, and let $i \ge 1$ and
$\ell \ge 0$ be such that $c(i + t) = G$ for all $0 \le t < \ell$. Then there is a color
$e \in \{B, G\}$ with $c(i + j^k + t) = e$ for all $0 \le t < \ell$, and, if $j^k < i$, there
is a color $e' \in \{B, G\}$ with $c(i - j^k + t) = e'$ for all $0 \le t < \ell$.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 2
(`integers-2024-A105-lem-2`). -/
public theorem_wanted monochromatic_shift_of_rainbowFree_powDiff (k : ℕ) (c : ℕ → Fin 3)
    (hrf : ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → x = y + z ^ k →
      ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z))
    (R B G : Fin 3) (hRB : R ≠ B) (hRG : R ≠ G) (hBG : B ≠ G)
    (hdom : ∀ i ℓ : ℕ, 0 < i → ((Finset.Ico i (i + ℓ)).image c).card = 2 →
      R ∈ (Finset.Ico i (i + ℓ)).image c)
    (j : ℕ) (hj : 0 < j) (hcj : c j = B) (i ℓ : ℕ) (hi : 0 < i)
    (hG : ∀ t < ℓ, c (i + t) = G) :
    (∃ e : Fin 3, (e = B ∨ e = G) ∧ ∀ t < ℓ, c (i + j ^ k + t) = e) ∧
      (j ^ k < i → ∃ e : Fin 3, (e = B ∨ e = G) ∧ ∀ t < ℓ, c (i - j ^ k + t) = e)

/-- **Zhan's small-gap lemma.** Let $S$ be a set of natural numbers, let $n_0 \ge 2$ be an
integer, and write $S(n)$ for the number of elements of $S \cap \{1, \dots, n\}$. If
$\limsup_{n \to \infty} (S(n) - n / n_0) = \infty$, that is, for every real $M$ there are
arbitrarily large $n$ with $S(n) - n / n_0 > M$, then there is an integer $d$ with
$1 \le d \le n_0 - 1$ such that $j$ and $j + d$ both lie in $S$ for arbitrarily large $j$.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 3
(`integers-2024-A105-lem-3`). -/
public theorem_wanted exists_small_gap_of_limsup_count (S : Set ℕ) [DecidablePred (· ∈ S)]
    (n₀ : ℕ) (hn₀ : 2 ≤ n₀)
    (hS : ∀ M : ℝ, ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧
      M < (((Finset.Icc 1 n).filter (· ∈ S)).card : ℝ) - n / n₀) :
    ∃ d : ℕ, 1 ≤ d ∧ d ≤ n₀ - 1 ∧ ∀ i : ℕ, ∃ j : ℕ, i < j ∧ j ∈ S ∧ j + d ∈ S

/-- **Non-dominant monochromatic strings have bounded length.** Let $k$ be a natural number, let
$n_0 \ge 2$ be an integer, and let $c$ be a coloring of the positive integers by three colors
with no rainbow solution of $x - y = z^k$: there are no positive integers $x, y, z$ with
$x = y + z^k$ and $c(x)$, $c(y)$, $c(z)$ pairwise distinct. For a color $e$ write $N_e(n)$ for
the number of $x \in \{1, \dots, n\}$ with $c(x) = e$, and assume that for every real $M$ there
are arbitrarily large $n$ with $N_e(n) - n / n_0 > M$ for all three colors $e$, that is,
$\limsup_{n \to \infty} \bigl(\min_e N_e(n) - n / n_0\bigr) = \infty$. Let $d$ be a dominant
color: for all positive integers $i$ and all $\ell \ge 0$, if $c$ takes exactly two colors on
$\{i, i + 1, \dots, i + \ell - 1\}$, then one of them is $d$. Then there is an $L$ such that for
all positive integers $i$ and all $\ell \ge 0$, if $c(i) \ne d$ and $c(i + t) = c(i)$ for all
$0 \le t < \ell$, then $\ell \le L$.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 4
(`integers-2024-A105-lem-4`). -/
public theorem_wanted nondominant_string_length_bounded (k : ℕ) (c : ℕ → Fin 3)
    (hrf : ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → x = y + z ^ k →
      ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z))
    (n₀ : ℕ) (hn₀ : 2 ≤ n₀)
    (hdens : ∀ M : ℝ, ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧ ∀ e : Fin 3,
      M < (((Finset.Icc 1 n).filter fun x => c x = e).card : ℝ) - n / n₀)
    (d : Fin 3) (hdom : ∀ i ℓ : ℕ, 0 < i → ((Finset.Ico i (i + ℓ)).image c).card = 2 →
      d ∈ (Finset.Ico i (i + ℓ)).image c) :
    ∃ L : ℕ, ∀ i ℓ : ℕ, 0 < i → c i ≠ d → (∀ t < ℓ, c (i + t) = c i) → ℓ ≤ L

/-- **Coprime numbers of a non-dominant color cannot both have the $A$-property.** Let $k$ be a
natural number, let $n_0 \ge 2$ be an integer, and let $c$ be a coloring of the positive
integers by three distinct colors $R$, $B$, $G$ with no rainbow solution of $x - y = z^k$: there
are no positive integers $x, y, z$ with $x = y + z^k$ and $c(x)$, $c(y)$, $c(z)$ pairwise
distinct. For a color $e$ write $N_e(n)$ for the number of $x \in \{1, \dots, n\}$ with
$c(x) = e$, and assume that for every real $M$ there are arbitrarily large $n$ with
$N_e(n) - n / n_0 > M$ for all three colors $e$. Assume that $R$ is dominant: for all positive
integers $i$ and all $\ell \ge 0$, if $c$ takes exactly two colors on
$\{i, i + 1, \dots, i + \ell - 1\}$, then one of them is $R$. Say that a positive integer $j$
has the $A$-property if there is a positive integer $i$ with $c(i + t j^k) = B$ for all
$t \ge 0$. If $j_1$ and $j_2$ are coprime positive integers with $c(j_1) = c(j_2) = G$, then
$j_1$ and $j_2$ do not both have the $A$-property.

The density hypothesis comes from Lemma 4 of the source; it is added because the source's proof
of this lemma ends by contradicting Lemma 4.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 5
(`integers-2024-A105-lem-5`); `A`-property as defined before Lemma 5 in arXiv:2305.15133. -/
public theorem_wanted not_both_aProperty_of_coprime (k : ℕ) (c : ℕ → Fin 3)
    (hrf : ∀ x y z : ℕ, 0 < x → 0 < y → 0 < z → x = y + z ^ k →
      ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z))
    (n₀ : ℕ) (hn₀ : 2 ≤ n₀)
    (hdens : ∀ M : ℝ, ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧ ∀ e : Fin 3,
      M < (((Finset.Icc 1 n).filter fun x => c x = e).card : ℝ) - n / n₀)
    (R B G : Fin 3) (hRB : R ≠ B) (hRG : R ≠ G) (hBG : B ≠ G)
    (hdom : ∀ i ℓ : ℕ, 0 < i → ((Finset.Ico i (i + ℓ)).image c).card = 2 →
      R ∈ (Finset.Ico i (i + ℓ)).image c)
    (j₁ j₂ : ℕ) (hj₁ : 0 < j₁) (hj₂ : 0 < j₂) (hcop : Nat.Coprime j₁ j₂)
    (hc₁ : c j₁ = G) (hc₂ : c j₂ = G) :
    ¬ ((∃ i : ℕ, 0 < i ∧ ∀ t : ℕ, c (i + t * j₁ ^ k) = B) ∧
      ∃ i : ℕ, 0 < i ∧ ∀ t : ℕ, c (i + t * j₂ ^ k) = B)

/-- **Coprime pairs in both non-dominant colors force a rainbow solution of $x - y = z^k$.**
Let $k \ge 2$ and $n_0 \ge 2$ be integers, and let $c$ be a coloring of the positive integers
by three distinct colors $R$, $B$, $G$. For a color $e$ write $N_e(n)$ for the number of
$x \in \{1, \dots, n\}$ with $c(x) = e$. Assume that for every real $M$ there are arbitrarily
large $n$ with $N_e(n) - n / n_0 > M$ for all three colors $e$, that is,
$\limsup_{n \to \infty} \bigl(\min_e N_e(n) - n / n_0\bigr) = \infty$. Assume also that $R$ is
dominant: for all positive integers $i$ and all $\ell \ge 0$, if $c$ takes exactly two colors on
$\{i, i + 1, \dots, i + \ell - 1\}$, then one of them is $R$. If there are coprime positive
integers $i_1, i_2$ with $c(i_1) = c(i_2) = B$ and coprime positive integers $j_1, j_2$ with
$c(j_1) = c(j_2) = G$, then there are positive integers $x, y, z$ with $x = y + z^k$ such that
$c(x)$, $c(y)$, $c(z)$ are pairwise distinct.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Theorem 1
(`integers-2024-A105-thm-1`). -/
public theorem_wanted exists_rainbow_powDiff_of_coprime_pairs (k : ℕ) (hk : 2 ≤ k)
    (c : ℕ → Fin 3) (n₀ : ℕ) (hn₀ : 2 ≤ n₀)
    (hdens : ∀ M : ℝ, ∀ N₀ : ℕ, ∃ n : ℕ, N₀ ≤ n ∧ ∀ e : Fin 3,
      M < (((Finset.Icc 1 n).filter fun x => c x = e).card : ℝ) - n / n₀)
    (R B G : Fin 3) (hRB : R ≠ B) (hRG : R ≠ G) (hBG : B ≠ G)
    (hdom : ∀ i ℓ : ℕ, 0 < i → ((Finset.Ico i (i + ℓ)).image c).card = 2 →
      R ∈ (Finset.Ico i (i + ℓ)).image c)
    (hB : ∃ i₁ i₂ : ℕ, 0 < i₁ ∧ 0 < i₂ ∧ Nat.Coprime i₁ i₂ ∧ c i₁ = B ∧ c i₂ = B)
    (hG : ∃ j₁ j₂ : ℕ, 0 < j₁ ∧ 0 < j₂ ∧ Nat.Coprime j₁ j₂ ∧ c j₁ = G ∧ c j₂ = G) :
    ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ x = y + z ^ k ∧
      c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z

/-- **Dominant colors on power-step strings modulo a prime.** Let $p$ be a prime and $k$ a natural
number, and let $c$ be a coloring of $\mathbb{Z}/p\mathbb{Z}$ with three colors that uses every
color and is rainbow-free for $x - y = z^k$: no $x, y, z \in \mathbb{Z}/p\mathbb{Z}$ with
$x - y = z^k$ have $c(x), c(y), c(z)$ pairwise distinct. Let $a \ne 0$ and $i$ be elements of
$\mathbb{Z}/p\mathbb{Z}$ and let $\ell$ be a natural number. If the elements $(i + t)a^k$ for
$0 \le t < \ell$ take exactly two colors, then one of these elements has the color $c(a)$.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 9
(`integers-2024-A105-lem-9`). -/
public theorem_wanted color_dominant_powStrings_of_rainbowFree_zmod (p k : ℕ) [Fact p.Prime]
    (c : ZMod p → Fin 3) (hc : Function.Surjective c)
    (hrf : ∀ x y z : ZMod p, x - y = z ^ k → ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z))
    (a : ZMod p) (ha : a ≠ 0) (i : ZMod p) (ℓ : ℕ)
    (hbi : ((Finset.range ℓ).image fun t : ℕ => c ((i + t) * a ^ k)).card = 2) :
    c a ∈ (Finset.range ℓ).image fun t : ℕ => c ((i + t) * a ^ k)

/-- **Components avoiding the color of zero are monochromatic.** Let $n$ and $t$ be natural
numbers, let $f$ be a map from $\mathbb{Z}/n\mathbb{Z}$ to itself, and let $c$ be a coloring of
$\mathbb{Z}/n\mathbb{Z}$ with $t$ colors that uses every color and is rainbow-free for
$x - y = f(z)$: no $x, y, z \in \mathbb{Z}/n\mathbb{Z}$ with $x - y = f(z)$ have $c(x), c(y), c(z)$
pairwise distinct. For $v \in \mathbb{Z}/n\mathbb{Z}$, call the set of $a$ with
$f^m(a) = f^{m'}(v)$ for some natural numbers $m, m'$ the component of $v$, where $f^m$ is the
$m$-th iterate of $f$. If no element of the component of $v$ has the color $c(0)$, then all its
elements have the same color.

The source record prints the equation as $x - y = f(x)$; the paper's proof uses the solution
$(f(a), 0, a)$ of $x - y = f(z)$, and the reading $x - y = f(x)$ fails on small examples.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Lemma 11
(`integers-2024-A105-lem-11`). -/
public theorem_wanted component_monochromatic_of_rainbowFree (n t : ℕ) (f : ZMod n → ZMod n)
    (c : ZMod n → Fin t) (hc : Function.Surjective c)
    (hrf : ∀ x y z : ZMod n, x - y = f z → ¬ (c x ≠ c y ∧ c y ≠ c z ∧ c x ≠ c z))
    (v : ZMod n)
    (h0 : ∀ a : ZMod n, (∃ m m' : ℕ, f^[m] a = f^[m'] v) → c a ≠ c 0)
    (a b : ZMod n) (ha : ∃ m m' : ℕ, f^[m] a = f^[m'] v)
    (hb : ∃ m m' : ℕ, f^[m] b = f^[m'] v) :
    c a = c b

/-- **Cycle vertices of the $k$-th power map modulo $p$.** Let $p$ be an odd prime, $k$ a natural
number, and $t$ the largest divisor of $p - 1$ that is coprime to $k$. A nonzero
$a \in \mathbb{Z}/p\mathbb{Z}$ lies on a cycle of the map $x \mapsto x^k$, that is,
$a^{k^m} = a$ for some $m \ge 1$, if and only if the multiplicative order of $a$ divides $t$.

Only this characterization is stated; the source's further claims (there are $t + 1$ cycle
vertices, and two components exactly when $t = 1$) are not.

Source: Katie Ansaldi, Gabriel Cowley, Eric Green, Kihyun Kim and JT Rapp, *Rainbow-Free
Colorings and Rainbow Numbers for x-y=z^k*, INTEGERS 24 (2024), Article A105, Theorem 6 (after Lucheta, Miller and Reiter)
(`integers-2024-A105-thm-6`). -/
public theorem_wanted isCycleVertex_powMap_iff_orderOf_dvd (p k : ℕ) [Fact p.Prime]
    (hp : p ≠ 2) (t : ℕ) (ht : t ∣ p - 1) (htk : Nat.Coprime t k)
    (htmax : ∀ s : ℕ, s ∣ p - 1 → Nat.Coprime s k → s ≤ t) (a : ZMod p) (ha : a ≠ 0) :
    (∃ m : ℕ, 1 ≤ m ∧ a ^ (k ^ m) = a) ↔ orderOf a ∣ t

end

end MetaMathlibExt
