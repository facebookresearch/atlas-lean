/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Real zeros bounded by coefficient parity changes (AMR-021-0014)

For a polynomial with positive coefficients, the number of (distinct) real
zeros does not exceed the number of parity changes in the positive-`c̃`
index sequence.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Card

@[expose] public section

namespace MathlibExt.Algebra.RealZerosParityChangeBoundWanted

/-! Source record `AMR-021-0014`. -/

/-- **Newton-type coefficient differences.** For a real polynomial $f = \sum_k a_k x^k$ and a
natural number $k$, $\tilde c_k(f) = (k+1)\,a_k^2 - k\,a_{k-1}a_{k+1}$, where $a_j = 0$ for $j$
above the degree of $f$; for $k = 0$ the second term vanishes, so $\tilde c_0(f) = a_0^2$. -/
def cTilde (f : Polynomial ℝ) (k : ℕ) : ℝ :=
  ((k + 1 : ℕ) : ℝ) * (f.coeff k) ^ 2 -
    (k : ℝ) * f.coeff (k - 1) * f.coeff (k + 1)

/-- **Indices with positive Newton-type difference.** For a real polynomial
$f = a_0 + a_1 x + \dots + a_n x^n$ of degree $n$ (with $n = 0$ for $f = 0$), set $a_{n+1} = 0$,
$\tilde c_0(f) = a_0^2$ and $\tilde c_k(f) = (k+1)\,a_k^2 - k\,a_{k-1}a_{k+1}$ for $1 \le k \le n$.
This is the list of the indices $k \in \{0, \dots, n\}$ with $\tilde c_k(f) > 0$, in increasing
order. -/
noncomputable def posIndices (f : Polynomial ℝ) : List ℕ :=
  ((Finset.range (f.natDegree + 1)).filter (fun k => 0 < cTilde f k)).sort (· ≤ ·)

/-- **Parity changes of the positive-difference indices.** For a real polynomial
$f = a_0 + a_1 x + \dots + a_n x^n$ of degree $n$ (with $n = 0$ for $f = 0$), set $a_{n+1} = 0$,
$\tilde c_0(f) = a_0^2$ and $\tilde c_k(f) = (k+1)\,a_k^2 - k\,a_{k-1}a_{k+1}$ for $1 \le k \le n$.
Let $k_1 < k_2 < \dots < k_m$ be the indices $k \le n$ with $\tilde c_k(f) > 0$. Then $v(f)$ is the
number of $i < m$ such that $k_i$ and $k_{i+1}$ have different parities. -/
noncomputable def vVal (f : Polynomial ℝ) : ℕ :=
  ((posIndices f).zip ((posIndices f).drop 1)).countP
    (fun p => p.1 % 2 ≠ p.2 % 2)

/-- **Parity-change bound on real zeros (conjecture).** For a real polynomial
$f = a_0 + a_1 x + \dots + a_n x^n$ of degree $n$, set $a_{n+1} = 0$, $\tilde c_0(f) = a_0^2$ and
$\tilde c_k(f) = (k+1)\,a_k^2 - k\,a_{k-1}a_{k+1}$ for $1 \le k \le n$, and let $v(f)$ be the
number of parity changes between consecutive terms of the increasing list of indices $k \le n$
with $\tilde c_k(f) > 0$. The conjecture asserts that every such $f$ with $a_k > 0$ for all
$0 \le k \le n$ has at most $v(f)$ distinct real zeros.

Source: AMR-021-0014. -/
def conjecture : Prop :=
  ∀ f : Polynomial ℝ,
    (∀ k ∈ Finset.range (f.natDegree + 1), 0 < f.coeff k) →
    Set.ncard {x : ℝ | f.eval x = 0} ≤ vVal f

/--
**The parity-change bound on real zeros is false.** For a real polynomial
$f = a_0 + a_1 x + \dots + a_n x^n$ of degree $n$, set $a_{n+1} = 0$, $\tilde c_0(f) = a_0^2$ and
$\tilde c_k(f) = (k+1)\,a_k^2 - k\,a_{k-1}a_{k+1}$ for $1 \le k \le n$, and let $v(f)$ be the
number of parity changes between consecutive terms of the increasing list of indices $k \le n$
with $\tilde c_k(f) > 0$. There is such an $f$ with $a_k > 0$ for all $0 \le k \le n$ whose number
of distinct real zeros exceeds $v(f)$.

Katkova, Shapiro and Vishnyakova (Sec. 5) disprove Conjecture 9 via iterated primitives $Q_n$ of
an explicit $Q_{15}$. Splitting the repeated root also refutes the distinct-zero reading used
here: $\prod_{j<23}(x+1+j/10^4)\,(38x^2-199x+363)$ has positive coefficients, 23 distinct real
zeros and $v = 21$.

Source: Olga Katkova, Boris Shapiro and Anna Vishnyakova, In search of Newton-type
inequalities, arXiv:2403.12200 (2024), https://arxiv.org/abs/2403.12200. Moved from
`OpenConjectures/Algebra/RealZerosParityChangeBound`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.Algebra.RealZerosParityChangeBoundWanted
