/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.JosephusBaseThreeHalves

namespace MetaMathlibExt

/-- **Base-3/2 digits of the next Josephus fixed point, gap zero.** Let $J_3$ be the Josephus
function with elimination step $3$, let $n_\ell$ be the $\ell$-th positive fixed point of $J_3$
in increasing order (counting from $\ell = 0$), and let $m_\ell$ be the number of integers $n$
with $n_\ell < n < n_{\ell+1}$ and $J_3(n) + 1 = n$ (the pure high extremal points between
them). For every $\ell$, if $m_\ell = 0$, then the base-$3/2$ digit list of $n_{\ell+1}$, least
significant digit first, is the digit $1$ followed by the digit list of $n_\ell$.

This is part (i) of the cited Theorem 1.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem_wanted josephusThreeFixedPoint_digits_of_gap_zero (ℓ : ℕ) :
    let D := baseThreeHalvesDigits (josephusThreeFixedPoint ℓ)
    let E := baseThreeHalvesDigits (josephusThreeFixedPoint (ℓ + 1))
    let m := josephusThreeGap ℓ
    m = 0 → E = 1 :: D

/-- **Base-3/2 digits of the next Josephus fixed point, gap one.** Let $J_3$ be the Josephus
function with elimination step $3$, let $n_\ell$ be the $\ell$-th positive fixed point of $J_3$
in increasing order (counting from $\ell = 0$), and let $m_\ell$ be the number of integers $n$
with $n_\ell < n < n_{\ell+1}$ and $J_3(n) + 1 = n$ (the pure high extremal points between
them). For every $\ell$, if $m_\ell = 1$, then the base-$3/2$ digit list of $n_{\ell+1}$, least
significant digit first, is the digits $2, 0$ followed by the digit list of $n_\ell$.

This is part (ii) of the cited Theorem 1.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem_wanted josephusThreeFixedPoint_digits_of_gap_one (ℓ : ℕ) :
    let D := baseThreeHalvesDigits (josephusThreeFixedPoint ℓ)
    let E := baseThreeHalvesDigits (josephusThreeFixedPoint (ℓ + 1))
    let m := josephusThreeGap ℓ
    m = 1 → E = [2, 0] ++ D

/-- **Base-3/2 digits of the next Josephus fixed point, gap at least two.** Let $J_3$ be the
Josephus function with elimination step $3$, let $n_\ell$ be the $\ell$-th positive fixed point
of $J_3$ in increasing order (counting from $\ell = 0$), and let $m_\ell$ be the number of
integers $n$ with $n_\ell < n < n_{\ell+1}$ and $J_3(n) + 1 = n$ (the pure high extremal points
between them). For every $\ell$, if $m_\ell \ge 2$, then the base-$3/2$ digit list of
$n_{\ell+1}$, least significant digit first, is the digit $2$, then $m_\ell - 1$ digits equal to
$1$, then the digit $0$, followed by the digit list of $n_\ell$.

Written most significant digit first, this appends to the digits of $n_\ell$ a $0$, then
$m_\ell - 1$ ones, then a $2$. This is part (iii) of the cited Theorem 1.

Source: Yunier Bello-Cruz and Roy Quintero-Contreras, *Fixed Points of the Josephus Function via
Fractional Base Expansions*, INTEGERS 26 (2026), Article A54, Theorem 1. -/
public theorem_wanted josephusThreeFixedPoint_digits_of_gap_at_least_two (ℓ : ℕ) :
    let D := baseThreeHalvesDigits (josephusThreeFixedPoint ℓ)
    let E := baseThreeHalvesDigits (josephusThreeFixedPoint (ℓ + 1))
    let m := josephusThreeGap ℓ
    2 ≤ m → E = 2 :: List.replicate (m - 1) 1 ++ 0 :: D

end MetaMathlibExt
