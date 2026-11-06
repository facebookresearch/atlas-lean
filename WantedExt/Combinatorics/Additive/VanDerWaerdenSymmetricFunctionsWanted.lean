/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Van der Waerden-type vanishing for sum-plus-product families

Statements from Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden
Theorem to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25 (arXiv:2502.07921).
Labels follow the journal numbering (Lemmas 1-9); the arXiv version calls Lemmas 1-5 and
7-9 Propositions 1-5 and 7-9, and Lemma 6 Proposition 6.

A family `F = {f^(l)}_{l ≥ 2}` of functions `f^(l) : (ℤ/n)^l → M` is `m`-vanishing when
every sequence over `ℤ/n` contains `m` consecutive blocks of a common length `l > 1` on which
`f^(l)` vanishes, and vanishing when it is `m`-vanishing for every `m > 0`. Sequences are
indexed from `0` rather than `1`, which does not affect either property. Values of `f^(l)`
at `l < 2` never enter the definitions.
-/
module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.ZMod.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **$m$-vanishing family.** Let $n$ be a natural number and let $F = (f^{(l)})_{l \ge 0}$ be a
family of functions $f^{(l)} : (\mathbb{Z}/n\mathbb{Z})^l \to M$ into a type $M$ with a zero
element. For a natural number $m$, $F$ is $m$-vanishing if for every sequence
$a_0, a_1, a_2, \dots$ of elements of $\mathbb{Z}/n\mathbb{Z}$ there are a length $l > 1$ and a
start $s \ge 0$ such that $f^{(l)}(a_{s+jl}, a_{s+jl+1}, \dots, a_{s+jl+l-1}) = 0$ for every
$j < m$; that is, the sequence contains $m$ consecutive blocks of a common length $l > 1$ on each
of which $f^{(l)}$ vanishes.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Section 2 (definition of
`m`-vanishing). -/
public def IsMVanishingFamily {n : ℕ} {M : Type*} [Zero M] (m : ℕ)
    (F : (l : ℕ) → (Fin l → ZMod n) → M) : Prop :=
  ∀ a : ℕ → ZMod n, ∃ l, 1 < l ∧ ∃ s, ∀ j < m, F l (fun i => a (s + j * l + i)) = 0

/-- **Vanishing family.** Let $n$ be a natural number. A family $F$ of functions on blocks over
$\mathbb{Z}/n\mathbb{Z}$ with values in a type with a zero is vanishing if it is $m$-vanishing for
every positive integer $m$.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Section 2 (definition of
vanishing). -/
public def IsVanishingFamily {n : ℕ} {M : Type*} [Zero M]
    (F : (l : ℕ) → (Fin l → ZMod n) → M) : Prop :=
  ∀ m, 0 < m → IsMVanishingFamily m F

/-- **The sum-plus-product family $F_c$.** For $c \in \mathbb{Z}/n$, the family $F_c$ over
$\mathbb{Z}/n$ sends a block $(b_1, \dots, b_l)$ of elements of $\mathbb{Z}/n$, of any length
$l \ge 0$, to $b_1 + \dots + b_l + c\, b_1 b_2 \cdots b_l$, where an empty sum is $0$ and an
empty product is $1$.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Section 2 (the family
`F_c`). -/
public def sumAddMulProdFamily {n : ℕ} (c : ZMod n) (l : ℕ) (b : Fin l → ZMod n) :
    ZMod n :=
  ∑ i, b i + c * ∏ i, b i

/-- **Monotonicity of $m$-vanishing.** Let $F$ be a family of functions on blocks over
$\mathbb{Z}/n$ with values in a type $M$ with a zero. If $F$ is $m$-vanishing and $m' \le m$,
then $F$ is $m'$-vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Section 2 (definition of
`m`-vanishing). -/
public theorem IsMVanishingFamily.mono {n : ℕ} {M : Type*} [Zero M]
    {F : (l : ℕ) → (Fin l → ZMod n) → M} {m m' : ℕ} (h : IsMVanishingFamily m F)
    (hm : m' ≤ m) : IsMVanishingFamily m' F := by
  intro a
  obtain ⟨l, hl, s, hs⟩ := h a
  exact ⟨l, hl, s, fun j hj => hs j (lt_of_lt_of_le hj hm)⟩

/-- **Every family is $0$-vanishing.** For every natural number $n$ and every family $F$ of
functions $f^{(l)} : (\mathbb{Z}/n\mathbb{Z})^l \to M$, $l \ge 0$, into a type $M$ with a zero
element, $F$ is $0$-vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Section 2 (definition of
`m`-vanishing). -/
public theorem isMVanishingFamily_zero {n : ℕ} {M : Type*} [Zero M]
    (F : (l : ℕ) → (Fin l → ZMod n) → M) : IsMVanishingFamily 0 F :=
  fun _ => ⟨2, Nat.one_lt_two, 0, fun _ hj => absurd hj (Nat.not_lt_zero _)⟩

/-- **The sum-plus-product family on blocks of length two.** For $c \in \mathbb{Z}/n$ and
$b_0, b_1 \in \mathbb{Z}/n$, the sum-plus-product family $F_c$ over $\mathbb{Z}/n$ satisfies
$F_c(b_0, b_1) = b_0 + b_1 + c\, b_0 b_1$.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Section 2 (the family
`F_c`). -/
public theorem sumAddMulProdFamily_two {n : ℕ} (c : ZMod n) (b : Fin 2 → ZMod n) :
    sumAddMulProdFamily c 2 b = b 0 + b 1 + c * (b 0 * b 1) := by
  simp [sumAddMulProdFamily, Fin.sum_univ_two, Fin.prod_univ_two]

/-- **Zero-sum van der Waerden theorem.** For every positive integer $n$, the family over
$\mathbb{Z}/n\mathbb{Z}$ sending a block $(b_1, \dots, b_l)$ to $\sum_i b_i$ is vanishing: for
every $m > 0$, every sequence over $\mathbb{Z}/n\mathbb{Z}$ contains $m$ consecutive blocks of a
common length $l > 1$, each with sum zero.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Theorem 1
(`integers-2026-A25-thm-1`). -/
public theorem_wanted isVanishingFamily_sum {n : ℕ} (hn : 0 < n) :
    IsVanishingFamily (fun (l : ℕ) (b : Fin l → ZMod n) => ∑ i, b i)

/-- **$F_c$ with $c \notin \{0, \pm 1\}$ is not $m$-vanishing for $m > 0$.** Let $n > 1$ and let
$c \in \mathbb{Z}/n$ with $c \ne 0$, $c \ne 1$ and $c \ne -1$. Then for every $m > 0$ the
sum-plus-product family $F_c$ over $\mathbb{Z}/n$,
$F_c(b_1, \dots, b_l) = b_1 + \dots + b_l + c\, b_1 \cdots b_l$, is not $m$-vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Theorem 2
(`integers-2026-A25-thm-2`). -/
public theorem_wanted not_isMVanishingFamily_sumAddMulProd_of_ne {n : ℕ} (hn : 1 < n)
    (c : ZMod n) (hc0 : c ≠ 0) (hc1 : c ≠ 1) (hcm1 : c ≠ -1) {m : ℕ} (hm : 0 < m) :
    ¬ IsMVanishingFamily m (sumAddMulProdFamily c)

/-- **Classification of vanishing for the sum-plus-product family $F_1$.** Let $n > 1$ and let
$F_1$ be the family over $\mathbb{Z}/n$ given by
$F_1(b_1, \dots, b_l) = b_1 + \dots + b_l + b_1 \cdots b_l$. If $n \notin \{2, 3, 4, 6, 8\}$,
then $F_1$ is not $m$-vanishing for any $m > 0$. If $n \in \{2, 3, 4, 8\}$, then $F_1$ is
vanishing. If $n = 6$, then $F_1$ is $1$-vanishing but not $m$-vanishing for any $m > 1$.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Theorem 3
(`integers-2026-A25-thm-3`). -/
public theorem_wanted sumAddMulProd_one_classification {n : ℕ} (hn : 1 < n) :
    (n ∉ ({2, 3, 4, 6, 8} : Finset ℕ) →
      ∀ m, 0 < m → ¬ IsMVanishingFamily m (sumAddMulProdFamily (1 : ZMod n))) ∧
    (n ∈ ({2, 3, 4, 8} : Finset ℕ) → IsVanishingFamily (sumAddMulProdFamily (1 : ZMod n))) ∧
    (n = 6 → IsMVanishingFamily 1 (sumAddMulProdFamily (1 : ZMod n)) ∧
      ∀ m, 1 < m → ¬ IsMVanishingFamily m (sumAddMulProdFamily (1 : ZMod n)))

/-- **The sum-plus-product family is vanishing over $\mathbb{Z}/3\mathbb{Z}$.** Let $F_1$ be the
family over $\mathbb{Z}/3\mathbb{Z}$ sending a block $(b_1, \dots, b_l)$ to
$\sum_i b_i + \prod_i b_i$. Then $F_1$ is vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 1
(`integers-2026-A25-lem-1`). -/
public theorem_wanted isVanishingFamily_sumAddMulProd_one_three :
    IsVanishingFamily (sumAddMulProdFamily (1 : ZMod 3))

/-- **The sum-plus-product family is vanishing over $\mathbb{Z}/4\mathbb{Z}$ and
$\mathbb{Z}/8\mathbb{Z}$.** Let $n \in \{4, 8\}$ and let $F_1$ be the family over
$\mathbb{Z}/n\mathbb{Z}$ sending a block $(b_1, \dots, b_l)$ to $\sum_i b_i + \prod_i b_i$. Then
$F_1$ is vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 2
(`integers-2026-A25-lem-2`). -/
public theorem_wanted isVanishingFamily_sumAddMulProd_one_four_eight {n : ℕ}
    (hn : n = 4 ∨ n = 8) : IsVanishingFamily (sumAddMulProdFamily (1 : ZMod n))

/-- **The sum-plus-product family is $1$-vanishing over $\mathbb{Z}/6\mathbb{Z}$.** Let $F_1$ be
the family over $\mathbb{Z}/6\mathbb{Z}$ sending a block $(b_1, \dots, b_l)$ to
$\sum_i b_i + \prod_i b_i$. Then $F_1$ is $1$-vanishing: every sequence over
$\mathbb{Z}/6\mathbb{Z}$ contains a block of consecutive terms, of some length $l > 1$, on which
$F_1$ vanishes.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 3
(`integers-2026-A25-lem-3`). -/
public theorem_wanted isMVanishingFamily_one_sumAddMulProd_one_six :
    IsMVanishingFamily 1 (sumAddMulProdFamily (1 : ZMod 6))

/-- **$F_{\pm 1}$ over $\mathbb{Z}/6$ is not $m$-vanishing for $m > 1$.** For every $m > 1$,
neither of the sum-plus-product families $F_{-1}$ and $F_1$ over $\mathbb{Z}/6$, where
$F_c(b_1, \dots, b_l) = b_1 + \dots + b_l + c\, b_1 \cdots b_l$, is $m$-vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 4
(`integers-2026-A25-lem-4`). -/
public theorem_wanted not_isMVanishingFamily_sumAddMulProd_six {m : ℕ} (hm : 1 < m) :
    ¬ IsMVanishingFamily m (sumAddMulProdFamily (-1 : ZMod 6)) ∧
      ¬ IsMVanishingFamily m (sumAddMulProdFamily (1 : ZMod 6))

/-- **$F_1$ modulo a prime $n \equiv 1 \pmod 4$ is not $m$-vanishing for $m > 0$.** Let $n$ be
a prime with $n \equiv 1 \pmod 4$. Then for every $m > 0$ the sum-plus-product family $F_1$
over $\mathbb{Z}/n$, $F_1(b_1, \dots, b_l) = b_1 + \dots + b_l + b_1 \cdots b_l$, is not
$m$-vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 5
(`integers-2026-A25-lem-5`), quoting Theorem 3.6 of Bialostocki and Dierker. -/
public theorem_wanted not_isMVanishingFamily_sumAddMulProd_one_prime_one_mod_four {n : ℕ}
    (hp : n.Prime) (h4 : n % 4 = 1) {m : ℕ} (hm : 0 < m) :
    ¬ IsMVanishingFamily m (sumAddMulProdFamily (1 : ZMod n))

/-- **Nonzero solutions of a two-equation system modulo primes greater than 3 congruent to 3
mod 4.** Let $n > 3$ be a prime with $n \equiv 3 \pmod 4$. Then there are nonzero
$x, y \in \mathbb{Z}/n\mathbb{Z}$ and an integer $r \in \{2, 3\}$ such that $x + ry = 0$ and
$xy^r = 1$ in $\mathbb{Z}/n\mathbb{Z}$.

The source prints the second equation as $xy r = 1$; it is read as $xy^r = 1$, as in the proof,
whose first case computes $xy^2 = x^3/4 = 1$.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 6
(`integers-2026-A25-lem-6`). -/
public theorem_wanted exists_add_mul_eq_zero_mul_pow_eq_one {n : ℕ} (hp : n.Prime)
    (h3 : 3 < n) (h4 : n % 4 = 3) :
    ∃ x y : ZMod n, x ≠ 0 ∧ y ≠ 0 ∧ ∃ r : ℕ, (r = 2 ∨ r = 3) ∧
      x + r * y = 0 ∧ x * y ^ r = 1

/-- **$F_1$ modulo a prime $n > 3$ with $n \equiv 3 \pmod 4$ is not $m$-vanishing for $m > 0$.**
Let $n > 3$ be a prime with $n \equiv 3 \pmod 4$. Then for every $m > 0$ the sum-plus-product
family $F_1$ over $\mathbb{Z}/n$, $F_1(b_1, \dots, b_l) = b_1 + \dots + b_l + b_1 \cdots b_l$, is
not $m$-vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 7
(`integers-2026-A25-lem-7`). -/
public theorem_wanted not_isMVanishingFamily_sumAddMulProd_one_prime_three_mod_four
    {n : ℕ} (hp : n.Prime) (h3 : 3 < n) (h4 : n % 4 = 3) {m : ℕ} (hm : 0 < m) :
    ¬ IsMVanishingFamily m (sumAddMulProdFamily (1 : ZMod n))

/-- **$F_1$ modulo $8u$ with $u > 1$ is not $m$-vanishing for $m > 0$.** Let $u > 1$ be a natural
number and $n = 8u$. Then for every $m > 0$ the sum-plus-product family $F_1$ over $\mathbb{Z}/n$,
$F_1(b_1, \dots, b_l) = b_1 + \dots + b_l + b_1 \cdots b_l$, is not $m$-vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 8
(`integers-2026-A25-lem-8`). -/
public theorem_wanted not_isMVanishingFamily_sumAddMulProd_one_eight_mul {u : ℕ}
    (hu : 1 < u) {m : ℕ} (hm : 0 < m) :
    ¬ IsMVanishingFamily m (sumAddMulProdFamily (1 : ZMod (8 * u)))

/-- **$F_1$ modulo $9u$ with $u > 0$ is not $m$-vanishing for $m > 0$.** Let $u > 0$ be a natural
number and $n = 9u$. Then for every $m > 0$ the sum-plus-product family $F_1$ over $\mathbb{Z}/n$,
$F_1(b_1, \dots, b_l) = b_1 + \dots + b_l + b_1 \cdots b_l$, is not $m$-vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Lemma 9
(`integers-2026-A25-lem-9`). -/
public theorem_wanted not_isMVanishingFamily_sumAddMulProd_one_nine_mul {u : ℕ}
    (hu : 0 < u) {m : ℕ} (hm : 0 < m) :
    ¬ IsMVanishingFamily m (sumAddMulProdFamily (1 : ZMod (9 * u)))

/-- **The sum-minus-product family is vanishing modulo prime powers.** Let $p$ be a prime,
$k > 0$ and $n = p^k$, and let $F_{-1}$ be the family over $\mathbb{Z}/n\mathbb{Z}$ sending a
block $(b_1, \dots, b_l)$ to $\sum_i b_i - \prod_i b_i$. Then $F_{-1}$ is vanishing.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Theorem 4
(`integers-2026-A25-thm-4`). -/
public theorem_wanted isVanishingFamily_sumAddMulProd_neg_one_prime_pow {p k : ℕ}
    (hp : p.Prime) (hk : 0 < k) :
    IsVanishingFamily (sumAddMulProdFamily (-1 : ZMod (p ^ k)))

/-- **Vanishing of families of sums of transformed entries.** Let $n$ be a positive integer, $d$ a
natural number and $g_1, \dots, g_d : \mathbb{Z}/n\mathbb{Z} \to \mathbb{Z}/n\mathbb{Z}$ maps.
Then the family over $\mathbb{Z}/n\mathbb{Z}$ sending a block $(b_1, \dots, b_l)$ to the vector
$\left(\sum_i g_1(b_i), \dots, \sum_i g_d(b_i)\right) \in (\mathbb{Z}/n\mathbb{Z})^d$ is
vanishing, where a block counts as vanishing when all $d$ coordinates of this vector are zero.

The source assumes $d > 0$; for $d = 0$ the statement is trivial.

Source: Arie Bialostocki and Vladyslav Oles, *On Generalizing the Van Der Waerden Theorem
to Some Symmetric Functions*, INTEGERS 26 (2026), Article A25, Theorem 6
(`integers-2026-A25-thm-6`). -/
public theorem_wanted isVanishingFamily_transformation_sums {n d : ℕ} (hn : 0 < n)
    (g : Fin d → ZMod n → ZMod n) :
    IsVanishingFamily (fun (l : ℕ) (b : Fin l → ZMod n) (t : Fin d) => ∑ i, g t (b i))

end

end MetaMathlibExt
