/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Int.Basic
public import Mathlib.Data.Nat.Factorial.Basic

@[expose] public section

namespace MetaMathlibExt

/-! # Tribonacci factorial-product classification
-/

/--
**Tribonacci numbers that are products of factorials.** Let $(T_n)_{n \in \mathbb{Z}}$ be the
integer sequence with $T_0 = 0$, $T_1 = T_2 = 1$ and $T_{j+3} = T_{j+2} + T_{j+1} + T_j$ for
every integer $j$. If $n$ is an integer such that $|T_n| = m_1! \, m_2! \cdots m_k!$ for some
$k \ge 1$ and some positive integers $m_1, \dots, m_k$, then
$n \in \{-9, -8, -7, -5, -3, -2, 1, 2, 3, 4, 7\}$.

Source: Adel Alahmadi and Florian Luca, "On Tribonacci Numbers that are Products of
Factorials", Journal of Integer Sequences 26 (2023), Article 23.2.2, Theorem 2
(label `thm:2`), lines 121-127,
<https://cs.uwaterloo.ca/journals/JIS/VOL26/Luca/luca52.tex>.
-/
public theorem_wanted tribonacci_factorialProduct_index_mem
    (T : ℤ → ℤ)
    (hT0 : T 0 = 0)
    (hT1 : T 1 = 1)
    (hT2 : T 2 = 1)
    (hTrec : ∀ j : ℤ, T (j + 3) = T (j + 2) + T (j + 1) + T j)
    (n : ℤ)
    (k : ℕ)
    (hk : 0 < k)
    (m : Fin k → ℕ)
    (hm : ∀ i, 0 < m i)
    (h : (T n).natAbs = ∏ i, (m i).factorial) :
    n ∈ ({-9, -8, -7, -5, -3, -2, 1, 2, 3, 4, 7} : Finset ℤ)

end MetaMathlibExt
