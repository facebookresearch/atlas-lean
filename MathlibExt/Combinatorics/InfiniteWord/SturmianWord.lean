/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Number of ones in a factor.** For an infinite binary word $x = x_0 x_1 x_2 \cdots$ over
$\{0, 1\}$ and natural numbers $i$ and $n$, this is the number of indices $k < n$ with
$x_{i+k} = 1$, that is, the number of $1$s in the factor $x_i x_{i+1} \cdots x_{i+n-1}$ of length
$n$ starting at position $i$ (it is $0$ when $n = 0$).

Source: concept `jis_term_4c219044135404e2d10fb16f`, statement `jis_a07921e69f2b6f8112afb1b1`. -/
def factorOnes (x : ℕ → Bool) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | i, n + 1 => factorOnes x i n + if x (i + n) then 1 else 0

/-- **Balanced infinite words.** An infinite binary word $x = x_0 x_1 x_2 \cdots$ over $\{0, 1\}$
is balanced when for all natural numbers $i$, $j$ and $n$, the numbers of $1$s in the factors
$x_i x_{i+1} \cdots x_{i+n-1}$ and $x_j x_{j+1} \cdots x_{j+n-1}$ of length $n$ differ by at
most $1$.

Source: concept `jis_term_4c219044135404e2d10fb16f`, statement `jis_a07921e69f2b6f8112afb1b1`. -/
def IsBalanced (x : ℕ → Bool) : Prop :=
  ∀ i j n : ℕ, (((factorOnes x i n : ℤ) - (factorOnes x j n : ℤ)).natAbs ≤ 1)

/-- **Aperiodic infinite words.** An infinite binary word $x = x_0 x_1 x_2 \cdots$ over $\{0, 1\}$
is aperiodic when it is not ultimately periodic: there are no natural numbers $p > 0$ and $N$
such that $x_{n+p} = x_n$ for all $n \ge N$.

Source: concept `jis_term_4c219044135404e2d10fb16f`, statement `jis_a07921e69f2b6f8112afb1b1`. -/
def IsAperiodic (x : ℕ → Bool) : Prop :=
  ¬∃ p N : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n → x (n + p) = x n

/-- **Sturmian words.** An infinite binary word $x = x_0 x_1 x_2 \cdots$ over $\{0, 1\}$ is
Sturmian when it is both aperiodic and balanced.

Source: concept `jis_term_4c219044135404e2d10fb16f`, statement `jis_a07921e69f2b6f8112afb1b1`. -/
def IsSturmian (x : ℕ → Bool) : Prop :=
  IsAperiodic x ∧ IsBalanced x

end

end MetaMathlibExt
