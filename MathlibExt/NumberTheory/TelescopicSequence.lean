/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Algebra.Group.Submonoid.Basic

@[expose] public section

namespace MetaMathlibExt

/-- **Prefix gcds of a sequence.** For a finite sequence $G = (g_1, \dots, g_k)$ of natural numbers
and a natural number $j$, $d_j$ is the greatest common divisor of the first $j$ entries of $G$
(of all of $G$ when $j > k$), with $d_0 = 0$.

Source: JIS statements `jis_0047f665dcff445f0a87ef54`, `jis_e21a41021ffe77e39d11f0e2`,
`jis_480413725b64a0d49eabe98d`. -/
public def telescopicGcd (G : List ℕ) (j : ℕ) : ℕ :=
  (G.take j).foldl Nat.gcd 0

/-- **Successive gcd quotients.** For a finite sequence $G = (g_1, \dots, g_k)$ of natural numbers,
let $d_i$ be the greatest common divisor of the first $i$ entries of $G$ (of all of $G$ when
$i > k$), with $d_0 = 0$. For $j \ge 1$ the successive gcd quotient is $c_j = d_{j-1} / d_j$,
taken to be $0$ when $d_j = 0$, that is, when the first $j$ entries are all zero; and $c_0 = 0$.

The source always assumes $g_1 > 0$ or $\gcd(G) = 1$, which avoids the degenerate case
$d_j = 0$. For example, $(660, 550, 352, 50, 201)$ has $(c_2, \dots, c_5) = (6, 5, 11, 2)$ and
$(3, 4, 5)$ has $(c_2, c_3) = (3, 1)$.

Source: JIS statements `jis_0047f665dcff445f0a87ef54`, `jis_e21a41021ffe77e39d11f0e2`,
`jis_480413725b64a0d49eabe98d`, `jis_ce7ca3b188a2135cbe5b0077`. -/
public def telescopicC (G : List ℕ) (j : ℕ) : ℕ :=
  telescopicGcd G (j - 1) / telescopicGcd G j

/-- **Telescopic sequences.** Let $G = (g_1, \dots, g_k)$ be a finite sequence of natural numbers.
For $0 \le i \le k$ let $d_i$ be the greatest common divisor of $g_1, \dots, g_i$, with $d_0 = 0$,
and for $1 \le j \le k$ let $c_j = d_{j-1} / d_j$ be the successive gcd quotient, taken to be $0$
when $d_j = 0$. The sequence $G$ is telescopic when $k \ge 2$, $g_1 + g_2 > 0$, and for every $j$
with $2 \le j \le k$ the number $c_j g_j$ lies in the additive submonoid of $\mathbb{N}$ generated
by $g_1, \dots, g_{j-1}$.

Source: JIS statements `jis_480413725b64a0d49eabe98d`, `jis_5da42b058565b53729b9afa2`,
`jis_a68226f2d394da5aef17cdad`, `jis_ce7ca3b188a2135cbe5b0077`,
`jis_e21a41021ffe77e39d11f0e2`. -/
public def IsTelescopic (G : List ℕ) : Prop :=
  2 ≤ G.length ∧
    0 < G.getD 0 0 + G.getD 1 0 ∧
      ∀ j : ℕ, 2 ≤ j → j ≤ G.length →
        telescopicC G j * G.getD (j - 1) 0 ∈
          AddSubmonoid.closure {x | x ∈ G.take (j - 1)}

end MetaMathlibExt

end
