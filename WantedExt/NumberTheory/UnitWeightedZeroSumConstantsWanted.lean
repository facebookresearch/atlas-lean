/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Coset.Defs
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Padics.PadicVal.Defs

/-!
# Unit-weighted zero-sum constants of `ℤ_n`: wishlist

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38 (arXiv:2203.02665).

Definitions follow the paper. For an `R`-module `M` and `A ⊆ R`, a subsequence of
`(x_1, …, x_k)` indexed by a nonempty `I` is `A`-weighted zero-sum if `∑_{i ∈ I} a_i x_i = 0`
for some `a_i ∈ A`. `D_A(M)` (resp. `C_A(M)`) is the least positive `k` such that every length-`k`
sequence has such a subsequence (resp. one of consecutive terms); both are stated with
`IsLeast` on the sets below (local notation), so no new definition is introduced. `D(M)`,
`C(M)` are the case `A = {1}`. `U(n)` is the unit group of `ℤ_n`, `Ω` is
`ArithmeticFunction.cardFactors`, `v_2` is `padicValNat 2`, and `f_{n,m}` is the natural map.
Vectors of `ℤ_2^m` are functions `Fin m → ZMod 2`. Several statements of the Drive extraction
print `2a` where the paper (arXiv:2203.02665v2) has `2^a`; the exponent is restored (see the
audit table).
-/

open scoped ArithmeticFunction.Omega

namespace MetaMathlibExt

@[expose] public section

set_option quotPrecheck false in
/-- The set of positive `k` such that every length-`k` sequence in `M` has an `A`-weighted
zero-sum subsequence; `D_A(M)` is its least element. -/
local notation "davenportSet" R:max M:max A:max => {k : ℕ | 0 < k ∧ ∀ x : Fin k → M,
  ∃ I : Finset (Fin k), I.Nonempty ∧
    ∃ a : Fin k → R, (∀ i ∈ I, a i ∈ A) ∧ ∑ i ∈ I, a i • x i = 0}

set_option quotPrecheck false in
/-- The set of positive `k` such that every length-`k` sequence in `M` has an `A`-weighted
zero-sum subsequence of consecutive terms; `C_A(M)` is its least element. -/
local notation "consecutiveSet" R:max M:max A:max => {k : ℕ | 0 < k ∧ ∀ x : Fin k → M,
  ∃ s t : Fin k, s ≤ t ∧
    ∃ a : Fin k → R, (∀ i ∈ Finset.Icc s t, a i ∈ A) ∧ ∑ i ∈ Finset.Icc s t, a i • x i = 0}

set_option quotPrecheck false in
/-- `x : Fin k → ZMod n` is a `U(n)`-weighted zero-sum sequence (all terms used). -/
local notation "IsUnitWeightedZeroSum" n:max x:max =>
  ∃ a : _ → ZMod n, (∀ i, IsUnit (a i)) ∧ ∑ i, a i * x i = 0

set_option quotPrecheck false in
/-- `x : Fin k → ZMod n` has a `U(n)`-weighted zero-sum subsequence of length `L`. -/
local notation "HasUnitWeightedZeroSumOfCard" n:max L:max x:max =>
  ∃ I : Finset _, I.card = L ∧
    ∃ a : _ → ZMod n, (∀ i ∈ I, IsUnit (a i)) ∧ ∑ i ∈ I, a i * x i = 0

set_option quotPrecheck false in
/-- The `ℕ`-indexed sequence `x` of length `L` in `ℤ_n` has no `U(n)`-weighted zero-sum
subsequence of consecutive terms. -/
local notation "NoConsecutiveUnitWeightedZeroSum" n:max L:max x:max =>
  ¬ ∃ s t : ℕ, s ≤ t ∧ t < L ∧ ∃ a : ℕ → ZMod n,
    (∀ i ∈ Finset.Icc s t, IsUnit (a i)) ∧ ∑ i ∈ Finset.Icc s t, a i * x i = 0

/-- **Weighted Davenport constant of a product with product weights.** Let $R$ and $R'$ be rings,
$M$ an $R$-module, $N$ an $R'$-module, $A \subseteq R$ and $B \subseteq R'$. Let $D_A(M)$ be the
least positive integer $k$, if one exists, such that every sequence $x_1, \dots, x_k$ in $M$ has
a nonempty set of indices $I$ and weights $a_i \in A$ for $i \in I$ with
$\sum_{i \in I} a_i x_i = 0$, and define $D_B(N)$ in the same way. Let $D_{A \times B}(M \times N)$
be the least positive integer $k$, if one exists, such that every sequence
$(y_1, z_1), \dots, (y_k, z_k)$ in $M \times N$ has a nonempty set of indices $I$ and weights
$(a_i, b_i) \in A \times B$ for $i \in I$ with $\sum_{i \in I} (a_i y_i, b_i z_i) = 0$. If all
three constants exist, then $D_{A \times B}(M \times N) \ge D_A(M) + D_B(N) - 1$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 2.1 (`integers-2024-A38-thm-2-1`). -/
public theorem_wanted davenport_prod_ring_ge {R R' M N : Type*} [Ring R] [Ring R']
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R' N] (A : Set R) (B : Set R')
    {dA dB d : ℕ} (hA : IsLeast (davenportSet R M A) dA)
    (hB : IsLeast (davenportSet R' N B) dB)
    (h : IsLeast {k : ℕ | 0 < k ∧ ∀ x : Fin k → M × N, ∃ I : Finset (Fin k), I.Nonempty ∧
      ∃ a : Fin k → R × R', (∀ i ∈ I, a i ∈ A ×ˢ B) ∧
        ∑ i ∈ I, ((a i).1 • (x i).1, (a i).2 • (x i).2) = 0} d) :
    dA + dB - 1 ≤ d

/-- **Weighted Davenport constant of a product of modules.** Let $R$ be a ring and
$A \subseteq R$. For an $R$-module $P$, let $D_A(P)$ be the least positive integer $k$, if one
exists, such that every sequence $x_1, \dots, x_k$ in $P$ has a nonempty set of indices $I$ and
weights $a_i \in A$ for $i \in I$ with $\sum_{i \in I} a_i x_i = 0$. If $M$ and $N$ are
$R$-modules for which $D_A(M)$, $D_A(N)$ and $D_A(M \times N)$ all exist, then
$D_A(M \times N) \ge D_A(M) + D_A(N) - 1$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 2.2 (`integers-2024-A38-thm-2-2`). -/
public theorem_wanted davenport_prod_ge {R M N : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (A : Set R) {dM dN d : ℕ}
    (hM : IsLeast (davenportSet R M A) dM) (hN : IsLeast (davenportSet R N A) dN)
    (h : IsLeast (davenportSet R (M × N) A) d) :
    dM + dN - 1 ≤ d

/-- **Consecutive weighted zero-sum constant of a product with product weights.** Let $R$ and
$R'$ be rings, $M$ an $R$-module, $N$ an $R'$-module, $A \subseteq R$ and $B \subseteq R'$. Let
$C_A(M)$ be the least positive integer $k$, if one exists, such that every sequence
$x_1, \dots, x_k$ in $M$ has indices $s \le t$ and weights $a_s, \dots, a_t \in A$ with
$a_s x_s + \dots + a_t x_t = 0$, and define $C_B(N)$ in the same way. Let
$C_{A \times B}(M \times N)$ be the least positive integer $k$, if one exists, such that every
sequence $(y_1, z_1), \dots, (y_k, z_k)$ in $M \times N$ has indices $s \le t$ and weights
$(a_i, b_i) \in A \times B$ for $s \le i \le t$ with $\sum_{i=s}^{t} (a_i y_i, b_i z_i) = 0$. If
all three constants exist, then $C_{A \times B}(M \times N) \ge C_A(M) \, C_B(N)$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 2.3 (`integers-2024-A38-thm-2-3`). -/
public theorem_wanted consecutive_prod_ring_ge {R R' M N : Type*} [Ring R] [Ring R']
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R' N] (A : Set R) (B : Set R')
    {cA cB c : ℕ} (hA : IsLeast (consecutiveSet R M A) cA)
    (hB : IsLeast (consecutiveSet R' N B) cB)
    (h : IsLeast {k : ℕ | 0 < k ∧ ∀ x : Fin k → M × N, ∃ s t : Fin k, s ≤ t ∧
      ∃ a : Fin k → R × R', (∀ i ∈ Finset.Icc s t, a i ∈ A ×ˢ B) ∧
        ∑ i ∈ Finset.Icc s t, ((a i).1 • (x i).1, (a i).2 • (x i).2) = 0} c) :
    cA * cB ≤ c

/-- **Consecutive weighted zero-sum constant of a product of modules.** Let $R$ be a ring and
$A \subseteq R$. For an $R$-module $P$, let $C_A(P)$ be the least positive integer $k$, if one
exists, such that every sequence $x_1, \dots, x_k$ in $P$ has indices $s \le t$ and weights
$a_s, \dots, a_t \in A$ with $a_s x_s + \dots + a_t x_t = 0$. If $M$ and $N$ are $R$-modules
for which $C_A(M)$, $C_A(N)$ and $C_A(M \times N)$ all exist, then
$C_A(M \times N) \ge C_A(M) \, C_A(N)$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 2.4 (`integers-2024-A38-thm-2-4`). -/
public theorem_wanted consecutive_prod_ge {R M N : Type*} [Ring R] [AddCommGroup M]
    [Module R M] [AddCommGroup N] [Module R N] (A : Set R) {cM cN c : ℕ}
    (hM : IsLeast (consecutiveSet R M A) cM) (hN : IsLeast (consecutiveSet R N A) cN)
    (h : IsLeast (consecutiveSet R (M × N) A) c) :
    cM * cN ≤ c

/-- **Consecutive zero-sum constant of a finite abelian group.** Let $G$ be a finite abelian
group and let $C(G)$ be the least positive integer $k$ such that every sequence
$x_1, \dots, x_k$ in $G$ has a block of consecutive terms $x_s, \dots, x_t$ with $s \le t$ and
$x_s + \dots + x_t = 0$. Then $C(G) = |G|$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 3.1 (`integers-2024-A38-thm-3-1`). -/
public theorem_wanted consecutive_constant_eq_card (G : Type*) [AddCommGroup G] [Fintype G] :
    IsLeast (consecutiveSet ℤ G ({1} : Set ℤ)) (Fintype.card G)

/-- **A block of consecutive coordinates orthogonal to $a$ vectors of $\mathbb{Z}_2^m$.** Let
$\mathbb{Z}_2 = \mathbb{Z}/2\mathbb{Z}$, let $2^a \le m$ and let
$v_1, \dots, v_a \in \mathbb{Z}_2^m$, with coordinates indexed by $\{0, \dots, m - 1\}$. Then there
are indices $s \le t$ in $\{0, \dots, m - 1\}$ such that $\sum_{j = s}^{t} (v_i)_j = 0$ in
$\mathbb{Z}_2$ for every $i$; that is, the nonzero vector whose ones occupy exactly the positions
$s, \dots, t$ is orthogonal to every $v_i$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 3.2 (`integers-2024-A38-lem-3-2`). -/
public theorem_wanted exists_consecutive_orthogonal {a m : ℕ} (hm : 2 ^ a ≤ m)
    (v : Fin a → Fin m → ZMod 2) :
    ∃ s t : Fin m, s ≤ t ∧ ∀ i, ∑ j ∈ Finset.Icc s t, v i j = 0

/-- **A block of consecutive integers meeting $a$ given sets evenly.** Let $2^a \le m$ and let
$X_1, \dots, X_a$ be finite sets of natural numbers. Then there are integers $s, t$ with
$1 \le s \le t \le m$ such that $|\{s, s + 1, \dots, t\} \cap X_i|$ is even for every $i$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 3.3 (`integers-2024-A38-lem-3-3`). -/
public theorem_wanted exists_consecutive_even_inter {a m : ℕ} (hm : 2 ^ a ≤ m)
    (X : Fin a → Finset ℕ) :
    ∃ s t : ℕ, 1 ≤ s ∧ s ≤ t ∧ t ≤ m ∧ ∀ i, Even (Finset.Icc s t ∩ X i).card

/-- **Griffiths' criterion for unit-weighted zero sums modulo a prime power.** Let $p$ be a prime,
let $r$ and $k$ be natural numbers, put $n = p^r$, and let
$x_1, \dots, x_k \in \mathbb{Z}/n\mathbb{Z}$. Suppose that for each $i \in [1, r]$ the set
$X_i = \{j : x_j \not\equiv 0 \pmod{p^i}\}$ has an even number of elements. Then there are units
$a_1, \dots, a_k$ of $\mathbb{Z}/n\mathbb{Z}$ with $a_1 x_1 + \dots + a_k x_k = 0$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 3.5 (`integers-2024-A38-lem-3-5`). -/
public theorem_wanted unitWeightedZeroSum_of_even_nonDivisible {p r k : ℕ} (hp : p.Prime)
    (x : Fin k → ZMod (p ^ r))
    (h : ∀ i ∈ Finset.Icc 1 r, Even (Finset.univ.filter fun j => ¬ p ^ i ∣ (x j).val).card) :
    IsUnitWeightedZeroSum (p ^ r) x

/-- **Davenport constant of $\mathbb{Z}_2^a$.** Let $\mathbb{Z}_2 = \mathbb{Z}/2\mathbb{Z}$. For
every natural number $a$, the least positive integer $k$ such that every sequence of $k$ elements
of the group $\mathbb{Z}_2^a$ has a nonempty subsequence with sum zero is $a + 1$; that is, the
Davenport constant of $\mathbb{Z}_2^a$ is $a + 1$.

The paper states this for positive $a$; for $a = 0$ both sides equal $1$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 4.1 (`integers-2024-A38-thm-4-1`). -/
public theorem_wanted davenport_zmod_two_pow (a : ℕ) :
    IsLeast (davenportSet (ZMod 2) (Fin a → ZMod 2) ({1} : Set (ZMod 2))) (a + 1)

/-- **A nonzero vector of $\mathbb{Z}_2^m$ orthogonal to $a$ vectors when $a < m$.** Let
$\mathbb{Z}_2 = \mathbb{Z}/2\mathbb{Z}$, let $a + 1 \le m$ and let
$v_1, \dots, v_a \in \mathbb{Z}_2^m$. Then there is a nonzero $w \in \mathbb{Z}_2^m$ with
$w \cdot v_i = \sum_j w_j (v_i)_j = 0$ in $\mathbb{Z}_2$ for every $i$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 4.2 (`integers-2024-A38-lem-4-2`). -/
public theorem_wanted exists_ne_zero_orthogonal {a m : ℕ} (hm : a + 1 ≤ m)
    (v : Fin a → Fin m → ZMod 2) :
    ∃ w : Fin m → ZMod 2, w ≠ 0 ∧ ∀ i, ∑ j, w j * v i j = 0

/-- **A nonempty subset of $\{1, \dots, m\}$ meeting $a$ given sets evenly.** Let $a + 1 \le m$
and let $X_1, \dots, X_a$ be finite sets of natural numbers. Then there is a nonempty set
$Y \subseteq \{1, \dots, m\}$ such that $|Y \cap X_i|$ is even for every $i$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 4.3 (`integers-2024-A38-lem-4-3`). -/
public theorem_wanted exists_nonempty_even_inter {a m : ℕ} (hm : a + 1 ≤ m)
    (X : Fin a → Finset ℕ) :
    ∃ Y : Finset ℕ, Y.Nonempty ∧ Y ⊆ Finset.Icc 1 m ∧ ∀ i, Even (Y ∩ X i).card

/-- **Zero-sum subsequences of length $m$ in $\mathbb{Z}_2^a$.** Let $a$ and $m$ be natural numbers
with $m$ even and $2^a \le m$, and write $\mathbb{Z}_2 = \mathbb{Z}/2\mathbb{Z}$. Every sequence
$(x_1, \dots, x_{m+a})$ of length $m + a$ in $\mathbb{Z}_2^a$ has a zero-sum subsequence of length
$m$: there is a set $I$ of exactly $m$ indices with $\sum_{i \in I} x_i = 0$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 5.2 (`integers-2024-A38-thm-5-2`). -/
public theorem_wanted exists_zeroSum_card_zmod_two_pow {a m : ℕ} (hme : Even m) (hm : 2 ^ a ≤ m)
    (x : Fin (m + a) → Fin a → ZMod 2) :
    ∃ I : Finset (Fin (m + a)), I.card = m ∧ ∑ i ∈ I, x i = 0

/-- **A weight-$m$ vector orthogonal to given vectors of $\mathbb{Z}_2^{m+a}$.** Let $a$ and $m$ be
natural numbers with $m$ even and $2^a \le m$, write $\mathbb{Z}_2 = \mathbb{Z}/2\mathbb{Z}$, and
let $v_1, \dots, v_a$ be vectors in $\mathbb{Z}_2^{m+a}$. Then there is a vector
$w \in \mathbb{Z}_2^{m+a}$ with exactly $m$ coordinates equal to $1$ such that
$w \cdot v_i = \sum_j w_j (v_i)_j = 0$ for every $i$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 5.3 (`integers-2024-A38-lem-5-3`). -/
public theorem_wanted exists_weight_orthogonal {a m : ℕ} (hme : Even m) (hm : 2 ^ a ≤ m)
    (v : Fin a → Fin (m + a) → ZMod 2) :
    ∃ w : Fin (m + a) → ZMod 2, (Finset.univ.filter fun j => w j = 1).card = m ∧
      ∀ i, ∑ j, w j * v i j = 0

/-- **An $m$-subset of $\{1, \dots, m + a\}$ meeting $a$ given sets evenly.** Let $m$ be even with
$2^a \le m$, and let $X_1, \dots, X_a$ be finite sets of natural numbers. Then there is a set
$Y \subseteq \{1, \dots, m + a\}$ with $|Y| = m$ such that $|Y \cap X_i|$ is even for every $i$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 5.4 (`integers-2024-A38-lem-5-4`). -/
public theorem_wanted exists_card_even_inter {a m : ℕ} (hme : Even m) (hm : 2 ^ a ≤ m)
    (X : Fin a → Finset ℕ) :
    ∃ Y : Finset ℕ, Y ⊆ Finset.Icc 1 (m + a) ∧ Y.card = m ∧ ∀ i, Even (Y ∩ X i).card

/-- **Unit-weighted zero sums of even length in $\mathbb{Z}_n$.** Let $n \ge 1$, let $\Omega(n)$ be
the number of prime factors of $n$ counted with multiplicity, and let $m$ be even with
$2^{\Omega(n)} \le m$. Then every sequence $x_1, \dots, x_{m + \Omega(n)}$ in
$\mathbb{Z}_n = \mathbb{Z}/n\mathbb{Z}$ has a unit-weighted zero-sum subsequence of length $m$:
there are a set $I \subseteq \{1, \dots, m + \Omega(n)\}$ with $|I| = m$ and units $a_i$ of
$\mathbb{Z}_n$ for $i \in I$ such that $\sum_{i \in I} a_i x_i = 0$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 5.5 (`integers-2024-A38-thm-5-5`). -/
public theorem_wanted exists_unitWeightedZeroSum_card {n m : ℕ} (hn : 0 < n) (hme : Even m)
    (hm : 2 ^ Ω n ≤ m) (x : Fin (m + Ω n) → ZMod n) :
    HasUnitWeightedZeroSumOfCard n m x

/-- **Every $m$-dimensional subspace of $\mathbb{Z}_2^{m+a}$ has a vector of weight $m$.** Let
$\mathbb{Z}_2 = \mathbb{Z}/2\mathbb{Z}$ and let $m$ be even with $2^a \le m$. Then every subspace
$W$ of $\mathbb{Z}_2^{m+a}$ of dimension $m$ contains a vector with exactly $m$ coordinates equal
to $1$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Corollary 5.7 (`integers-2024-A38-cor-5-7`). -/
public theorem_wanted exists_weight_mem_subspace {a m : ℕ} (hme : Even m) (hm : 2 ^ a ≤ m)
    (W : Submodule (ZMod 2) (Fin (m + a) → ZMod 2)) (hW : Module.finrank (ZMod 2) W = m) :
    ∃ v ∈ W, (Finset.univ.filter fun j => v j = 1).card = m

/-- **Largest subspaces of $\mathbb{Z}_2^{m+a}$ with no vector of weight $m$.** Let $a$ and $m$ be
natural numbers with $m$ even and $2^a \le m$, and write $\mathbb{Z}_2 = \mathbb{Z}/2\mathbb{Z}$.
The largest dimension of a subspace of $\mathbb{Z}_2^{m+a}$ containing no vector with exactly $m$
coordinates equal to $1$ is $m - 1$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Corollary 5.9 (`integers-2024-A38-cor-5-9`). -/
public theorem_wanted max_finrank_avoiding_weight {a m : ℕ} (hme : Even m) (hm : 2 ^ a ≤ m) :
    IsGreatest {d : ℕ | ∃ W : Submodule (ZMod 2) (Fin (m + a) → ZMod 2),
      Module.finrank (ZMod 2) W = d ∧
        ∀ v ∈ W, (Finset.univ.filter fun j => v j = 1).card ≠ m} (m - 1)

/-- **Unit-weighted Erdős–Ginzburg–Ziv constant of $\mathbb{Z}_n$ for even $n$.** Let $n$ be a
positive even integer, let $U(n)$ be the set of units of $\mathbb{Z}_n = \mathbb{Z}/n\mathbb{Z}$,
and let $\Omega(n)$ be the number of prime factors of $n$ counted with multiplicity. Then
$E_{U(n)}(n) = n + \Omega(n)$, where $E_{U(n)}(n)$ is the least positive integer $k$ such that
for every sequence $(x_1, \dots, x_k)$ in $\mathbb{Z}_n$ there are a set $I$ of exactly $n$
indices and units $a_i \in U(n)$ for $i \in I$ with $\sum_{i \in I} a_i x_i = 0$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 6.3 (`integers-2024-A38-thm-6-3`). -/
public theorem_wanted gao_unit_constant_of_even {n : ℕ} (hn : 0 < n) (he : Even n) :
    IsLeast {k : ℕ | 0 < k ∧ ∀ x : Fin k → ZMod n, HasUnitWeightedZeroSumOfCard n n x}
      (n + Ω n)

/-- **Sequences equivalent to the extremal profile have no unit-weighted zero sum of length
$2^r$.** Let $r \ge 1$, $n = 2^r$ and $L = n + r - 1$, and let $U(n)$ be the unit group of
$\mathbb{Z}_n = \mathbb{Z}/n\mathbb{Z}$. Let $y_1, \dots, y_L \in \mathbb{Z}_n$ be a sequence in
which, for each $i \in \{0, \dots, r - 2\}$, exactly one term equals $2^i$, an odd number of
terms equal $2^{r-1}$, and every term is $0$ or $2^i$ for some $i < r$. Let
$x_1, \dots, x_L \in \mathbb{Z}_n$ be $U(n)$-equivalent to $y$: there are $c \in U(n)$,
$b_1, \dots, b_L \in U(n)$ and a permutation $\sigma$ of $\{1, \dots, L\}$ with
$c \, y_{\sigma(i)} = b_i x_i$ for all $i$. Then $x$ has no $U(n)$-weighted zero-sum subsequence
of length $n$: there is no set $I \subseteq \{1, \dots, L\}$ with $|I| = n$ together with
$a_i \in U(n)$ for $i \in I$ such that $\sum_{i \in I} a_i x_i = 0$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 6.4 (`integers-2024-A38-thm-6-4`). -/
public theorem_wanted eExtremal_of_unitEquiv_profile {r : ℕ} (hr : 1 ≤ r)
    (x y : Fin (2 ^ r + r - 1) → ZMod (2 ^ r))
    (hy : (∀ i < r - 1, (Finset.univ.filter fun j => y j = 2 ^ i).card = 1) ∧
      Odd (Finset.univ.filter fun j => y j = 2 ^ (r - 1)).card ∧
      ∀ j, y j = 0 ∨ ∃ i < r, y j = 2 ^ i)
    (hxy : ∃ c : ZMod (2 ^ r), IsUnit c ∧ ∃ σ : Equiv.Perm (Fin (2 ^ r + r - 1)),
      ∃ b : Fin (2 ^ r + r - 1) → ZMod (2 ^ r), (∀ i, IsUnit (b i)) ∧
        ∀ i, c * y (σ i) = b i * x i) :
    ¬ HasUnitWeightedZeroSumOfCard (2 ^ r) (2 ^ r) x

/-- **Structure of extremal sequences for unit-weighted zero sums of length $2^r$.** Let $r \ge 1$,
let $n = 2^r$, let $U(n)$ be the set of units of $\mathbb{Z}_n = \mathbb{Z}/n\mathbb{Z}$, and let
$x = (x_1, \dots, x_{n+r-1})$ be a sequence in $\mathbb{Z}_n$ with no $U(n)$-weighted zero-sum
subsequence of length $n$: there is no set $I$ of exactly $n$ indices with units $a_i \in U(n)$
for $i \in I$ such that $\sum_{i \in I} a_i x_i = 0$. Then $x$ is $U(n)$-equivalent to a sequence
$(y_1, \dots, y_{n+r-1})$ in $\mathbb{Z}_n$ in which $2^i$ occurs exactly once for each
$i \in [0, r - 2]$, $2^{r-1}$ occurs an odd number of times and every other term is $0$: there
are a unit $c$, units $b_1, \dots, b_{n+r-1}$ and a permutation $\sigma$ of the indices with
$c \, y_{\sigma(i)} = b_i x_i$ for every $i$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 6.6 (`integers-2024-A38-thm-6-6`). -/
public theorem_wanted unitEquiv_profile_of_eExtremal {r : ℕ} (hr : 1 ≤ r)
    (x : Fin (2 ^ r + r - 1) → ZMod (2 ^ r))
    (hx : ¬ HasUnitWeightedZeroSumOfCard (2 ^ r) (2 ^ r) x) :
    ∃ y : Fin (2 ^ r + r - 1) → ZMod (2 ^ r),
      ((∀ i < r - 1, (Finset.univ.filter fun j => y j = 2 ^ i).card = 1) ∧
        Odd (Finset.univ.filter fun j => y j = 2 ^ (r - 1)).card ∧
        ∀ j, y j = 0 ∨ ∃ i < r, y j = 2 ^ i) ∧
      ∃ c : ZMod (2 ^ r), IsUnit c ∧ ∃ σ : Equiv.Perm (Fin (2 ^ r + r - 1)),
        ∃ b : Fin (2 ^ r + r - 1) → ZMod (2 ^ r), (∀ i, IsUnit (b i)) ∧
          ∀ i, c * y (σ i) = b i * x i

/-- **Luca's lemma on unit-weighted zero sums modulo $2^r$.** Let $r$ and $k$ be natural numbers
and let $x_1, \dots, x_k \in \mathbb{Z}/2^r\mathbb{Z}$. If the number of indices $j$ for which
$x_j$ is a unit is even and nonzero, then there are units $a_1, \dots, a_k$ of
$\mathbb{Z}/2^r\mathbb{Z}$ with $a_1 x_1 + \dots + a_k x_k = 0$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 6.5 (`integers-2024-A38-lem-6-5`). -/
public theorem_wanted unitWeightedZeroSum_of_even_units {r k : ℕ} (x : Fin k → ZMod (2 ^ r))
    (h0 : (Finset.univ.filter fun j => IsUnit (x j)).card ≠ 0)
    (he : Even (Finset.univ.filter fun j => IsUnit (x j)).card) :
    IsUnitWeightedZeroSum (2 ^ r) x

/-- **Unit-weighted zero sums of multiples of a prime.** Let $p$ be a prime, let $n'$ and $k$ be
natural numbers, put $n = p n'$, and let $z_1, \dots, z_k \in \mathbb{Z}/n\mathbb{Z}$. Write
$\bar z_i$ for the reduction of $z_i$ modulo $n'$. If there are units $a_1, \dots, a_k$ of
$\mathbb{Z}/n'\mathbb{Z}$ with $\sum_i a_i \bar z_i = 0$, then there are units $b_1, \dots, b_k$
of $\mathbb{Z}/n\mathbb{Z}$ with $\sum_i b_i \, p z_i = 0$.

In the source the sequence $(p z_1, \dots, p z_k)$ determines the $z_i$ only modulo $n'$, so the
hypothesis does not depend on the choice of the $z_i$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 6.7 (`integers-2024-A38-lem-6-7`). -/
public theorem_wanted unitWeightedZeroSum_of_div_prime {p n' k : ℕ} (hp : p.Prime)
    (z : Fin k → ZMod (p * n'))
    (h : IsUnitWeightedZeroSum n' (fun i => ZMod.castHom (dvd_mul_left n' p) (ZMod n') (z i))) :
    IsUnitWeightedZeroSum (p * n') (fun i => (p : ZMod (p * n')) * z i)

/-- **Halving consecutive unit-weighted zero-sum free sequences modulo a power of two.** Let
$s \ge 0$, $n = 2^{s+1}$ and $n' = 2^s$. Say that a sequence $y_1, \dots, y_L$ in $\mathbb{Z}_m$ has
no consecutive unit-weighted zero-sum if there are no indices $1 \le i \le j \le L$ and units
$a_i, \dots, a_j$ of $\mathbb{Z}_m$ with $a_i y_i + \dots + a_j y_j = 0$. For a sequence
$x_1, \dots, x_{n-1}$ in $\mathbb{Z}_n$, let $r_l \in \{0, \dots, n - 1\}$ be the representative of
$x_l$ and let $\bar x_l \in \mathbb{Z}_{n'}$ be the residue of $\lfloor r_l / 2 \rfloor$. Then
$x_1, \dots, x_{n-1}$ has no consecutive unit-weighted zero-sum if and only if $r_l$ is even for
every $l \ne n'$, $r_{n'}$ is odd, and neither of the sequences $\bar x_1, \dots, \bar x_{n'-1}$
and $\bar x_{n'+1}, \dots, \bar x_{n-1}$ in $\mathbb{Z}_{n'}$ has a consecutive unit-weighted
zero-sum.

Write $U(n)$ for the unit group of $\mathbb{Z}_n$ and $C_{U(n)}(n)$ for the least positive $k$ such
that every sequence of length $k$ in $\mathbb{Z}_n$ has a consecutive unit-weighted zero-sum. Since
$C_{U(n)}(n) = n$, the sequences on the left are the $C$-extremal sequences for $U(n)$: those of
length $C_{U(n)}(n) - 1$ with no consecutive unit-weighted zero-sum.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 6.8 (`integers-2024-A38-thm-6-8`). -/
public theorem_wanted cExtremal_iff_halves (s : ℕ) (x : ℕ → ZMod (2 ^ (s + 1))) :
    (NoConsecutiveUnitWeightedZeroSum (2 ^ (s + 1)) (2 ^ (s + 1) - 1) x) ↔
      (∀ j < 2 ^ (s + 1) - 1, j ≠ 2 ^ s - 1 → Even (x j).val) ∧ Odd (x (2 ^ s - 1)).val ∧
        (NoConsecutiveUnitWeightedZeroSum (2 ^ s) (2 ^ s - 1)
          (fun j => (((x j).val / 2 : ℕ) : ZMod (2 ^ s)))) ∧
        (NoConsecutiveUnitWeightedZeroSum (2 ^ s) (2 ^ s - 1)
          (fun j => (((x (2 ^ s + j)).val / 2 : ℕ) : ZMod (2 ^ s))))

/-- **Consecutive weighted zero-sum constant for interval weights.** Let $n \ge 2$ and
$1 \le r \le n - 1$, and let $A \subseteq \mathbb{Z}_n$ be the set of residues of
$1, 2, \dots, r$. Let $C_A(n)$ be the least positive integer $k$ such that every sequence
$x_1, \dots, x_k$ in $\mathbb{Z}_n$ has indices $s \le t$ and weights $a_s, \dots, a_t \in A$
with $a_s x_s + \dots + a_t x_t = 0$. Then $C_A(n) = \lceil n / r \rceil$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 7.1 (`integers-2024-A38-thm-7-1`). -/
public theorem_wanted consecutive_interval_weights {n r : ℕ} (hn : 2 ≤ n) (hr : 1 ≤ r)
    (hrn : r ≤ n - 1) :
    IsLeast (consecutiveSet (ZMod n) (ZMod n) ((fun j : ℕ => (j : ZMod n)) '' Set.Icc 1 r))
      ⌈(n : ℚ) / r⌉₊

/-- **Consecutive weighted zero-sum constant for odd weights.** Let $n$ be a positive even
integer, let $2^r$ be the largest power of $2$ dividing $n$ and let $m = n / 2^r$. Let
$A \subseteq \mathbb{Z}_n$ contain the residue of $m$ and consist of odd elements (residues whose
representative in $\{0, \dots, n - 1\}$ is odd). Let $C_A(n)$ be the least positive integer $k$
such that every sequence $x_1, \dots, x_k$ in $\mathbb{Z}_n$ has indices $s \le t$ and weights
$a_s, \dots, a_t \in A$ with $a_s x_s + \dots + a_t x_t = 0$. Then $C_A(n) = 2^r$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 7.2 (`integers-2024-A38-thm-7-2`). -/
public theorem_wanted consecutive_odd_weights {n : ℕ} (hn : 0 < n) (he : Even n)
    (A : Set (ZMod n)) (hmA : ((n / 2 ^ padicValNat 2 n : ℕ) : ZMod n) ∈ A)
    (hAB : A ⊆ {x : ZMod n | Odd x.val}) :
    IsLeast (consecutiveSet (ZMod n) (ZMod n) A) (2 ^ padicValNat 2 n)

/-- **Davenport constant of $\mathbb{Z}_p$ with $k$-th power unit weights is at most $k$.** Let
$k$ be an odd prime and $p$ a prime with $p \equiv 1 \pmod{k}$ and $p \not\equiv 1 \pmod{k^2}$.
Let $\mathbb{Z}_p = \mathbb{Z}/p\mathbb{Z}$ and let $U(p)^k$ be the set of $k$-th powers of units
of $\mathbb{Z}_p$. Then every sequence $x_1, \dots, x_k$ of $k$ elements of $\mathbb{Z}_p$ has a
$U(p)^k$-weighted zero-sum subsequence: there are a nonempty set $I \subseteq \{1, \dots, k\}$
and weights $a_i \in U(p)^k$ for $i \in I$ with $\sum_{i \in I} a_i x_i = 0$. In other words,
$D_{U(p)^k}(p) \le k$, where $D_A(p)$ is the least positive $\ell$ such that every sequence of
$\ell$ elements of $\mathbb{Z}_p$ has an $A$-weighted zero-sum subsequence.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Theorem 7.5 (`integers-2024-A38-thm-7-5`). -/
public theorem_wanted davenport_unit_pow_le {k p : ℕ} (hk : k.Prime) (hk2 : k ≠ 2)
    (hp : p.Prime) (hpk : p % k = 1) (hpk2 : p % k ^ 2 ≠ 1) :
    k ∈ davenportSet (ZMod p) (ZMod p) {x : ZMod p | ∃ u : ZMod p, IsUnit u ∧ x = u ^ k}

/-- **Weighted zero-sum free pairs in a field.** Let $F$ be a field, let $A$ be a subgroup of the
multiplicative group $F^*$, and let $x, y \in F$ be nonzero. Then the sequence
$(x_1, x_2) = (x, y)$ has no $A$-weighted zero-sum subsequence, that is, there is no nonempty
set $I \subseteq \{1, 2\}$ with elements $a_i \in A$ for $i \in I$ such that
$\sum_{i \in I} a_i x_i = 0$, if and only if $x$ and $-y$ lie in different cosets of $A$ in $F^*$.

A zero term is by itself a zero-sum subsequence, so the cosets are taken for nonzero $x$ and $y$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Lemma 7.6 (`integers-2024-A38-lem-7-6`). -/
public theorem_wanted pair_no_weightedZeroSum_iff {F : Type*} [Field F] (A : Subgroup Fˣ)
    {x y : F} (hx : x ≠ 0) (hy : y ≠ 0) :
    (¬ ∃ I : Finset (Fin 2), I.Nonempty ∧ ∃ a : Fin 2 → F,
      (∀ i ∈ I, a i ∈ ((↑) : Fˣ → F) '' A) ∧ ∑ i ∈ I, a i * ![x, y] i = 0) ↔
      (QuotientGroup.mk (Units.mk0 x hx) : Fˣ ⧸ A) ≠
        QuotientGroup.mk (Units.mk0 (-y) (neg_ne_zero.mpr hy))

/-- **Weighted zero-sum free pairs for a proper subgroup of $F^\times$.** Let $F$ be a field and
$A$ a proper subgroup of the multiplicative group $F^\times$. Then some sequence $x_1, x_2$ in
$F$ has no $A$-weighted zero-sum subsequence: there is no nonempty $I \subseteq \{1, 2\}$ with
weights $a_i \in A$ for $i \in I$ such that $\sum_{i \in I} a_i x_i = 0$.

Hence the weighted Davenport constant $D_A(F)$, the least positive $k$ such that every sequence
of length $k$ in $F$ has an $A$-weighted zero-sum subsequence, is at least $3$ when it exists.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Corollary 7.7 (`integers-2024-A38-cor-7-7`). -/
public theorem_wanted davenport_proper_subgroup_ge_three {F : Type*} [Field F]
    (A : Subgroup Fˣ) (hA : A ≠ ⊤) :
    2 ∉ davenportSet F F (((↑) : Fˣ → F) '' A)

/-- **Weighted zero-sum free pairs for $k$-th power weights modulo a prime.** Let $k \ge 2$, let
$p$ be a prime with $p \equiv 1 \pmod k$, and let $U(p)^k = \{u^k : u \in \mathbb{Z}_p^\times\}$.
Then some sequence $x_1, x_2$ in $\mathbb{Z}_p$ has no $U(p)^k$-weighted zero-sum subsequence:
there is no nonempty $I \subseteq \{1, 2\}$ with weights $a_i \in U(p)^k$ for $i \in I$ such that
$\sum_{i \in I} a_i x_i = 0$.

Hence the weighted Davenport constant $D_{U(p)^k}(p)$, the least positive $k'$ such that every
sequence of length $k'$ in $\mathbb{Z}_p$ has a $U(p)^k$-weighted zero-sum subsequence, is at
least $3$.

Source: Santanu Mondal, Krishnendu Paul and Shameek Paul, *On Unit-Weighted Zero-Sum Constants
of `ℤ_n`*, INTEGERS 24 (2024), Article A38, Corollary 7.8 (`integers-2024-A38-cor-7-8`). -/
public theorem_wanted davenport_unit_pow_ge_three {k p : ℕ} (hk : 2 ≤ k) (hp : p.Prime)
    (hpk : p % k = 1) :
    2 ∉ davenportSet (ZMod p) (ZMod p) {x : ZMod p | ∃ u : ZMod p, IsUnit u ∧ x = u ^ k}

end

end MetaMathlibExt
