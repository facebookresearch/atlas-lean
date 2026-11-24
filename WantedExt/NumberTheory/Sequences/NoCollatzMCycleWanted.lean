/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MetaMathlibExt

open scoped BigOperators

/-- **No Collatz $m$-cycles with $m \le 91$ (Hercher).** Let $T$ be the shortcut Collatz map on
the natural numbers, $T(c) = c/2$ for even $c$ and $T(c) = (3c+1)/2$ for odd $c$, and let $m$ be
a natural number with $m \le 91$. There are no natural numbers $n$ and $p > 0$ such that
$T^i(n) > 2$ for all $i < p$, $T^p(n) = n$, $T^k(n) \ne n$ for all $k$ with $0 < k < p$, and
exactly $m$ indices $i < p$ satisfy both $T^i(n) < T^{(i+1) \bmod p}(n)$ and
$T^i(n) < T^{(i+p-1) \bmod p}(n)$.

In words: no cycle of $T$ all of whose entries exceed $2$ (which excludes the trivial cycle
$1, 2, 1, 2, \dots$), taken with its minimal period $p$, has exactly $m$ entries lying cyclically
strictly below both neighbours.

Source: Christian Hercher, "There are no Collatz m-Cycles with m ≤ 91,"
Journal of Integer Sequences 26 (2023), Article 23.3.5, Main Theorem
(label Theorem17), lines 541–543,
https://cs.uwaterloo.ca/journals/JIS/VOL26/Hercher/hercher5.tex
with the operator at lines 104–111 and the m-cycle definition at
lines 149–151. -/
public theorem_wanted no_collatz_m_cycle_le_ninety_one
    (m : ℕ) (hm : m ≤ 91) :
    ¬ ∃ n p : ℕ, 0 < p ∧
      (∀ i : ℕ, i < p →
        2 < (fun c : ℕ => if c % 2 = 0 then c / 2 else (3 * c + 1) / 2)^[i] n) ∧
      (fun c : ℕ => if c % 2 = 0 then c / 2 else (3 * c + 1) / 2)^[p] n = n ∧
      (∀ k : ℕ, 0 < k → k < p →
        (fun c : ℕ => if c % 2 = 0 then c / 2 else (3 * c + 1) / 2)^[k] n ≠ n) ∧
      (((Finset.range p).filter (fun i =>
        (fun c : ℕ => if c % 2 = 0 then c / 2 else (3 * c + 1) / 2)^[i] n <
          (fun c : ℕ => if c % 2 = 0 then c / 2 else (3 * c + 1) / 2)^[(i + 1) % p] n ∧
        (fun c : ℕ => if c % 2 = 0 then c / 2 else (3 * c + 1) / 2)^[i] n <
          (fun c : ℕ => if c % 2 = 0 then c / 2 else
            (3 * c + 1) / 2)^[(i + p - 1) % p] n)).card = m)

end MetaMathlibExt
