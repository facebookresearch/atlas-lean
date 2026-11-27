/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
public import MathlibExt.Combinatorics.Enumerative.HypersequenceElementarySymmetric
public import MathlibExt.Combinatorics.Enumerative.HypersequenceMatrixB
public import MathlibExt.Combinatorics.Enumerative.MitrinovicNumbers
public import WantedExt.Combinatorics.Enumerative.HypersequenceWeightedSumsWanted

namespace MetaMathlibExt

@[expose] public section

/-! # Elementary symmetric coefficients from Parisse's hypersequence paper

Parisse writes `e_{j,k}(n)` for the elementary symmetric polynomial of degree `k` in
`x_1(n) = n + 1, …, x_j(n) = n + j` (Theorem 1, Equation (2.2)); here it is
`((Finset.Icc 1 j).val.map (n + ·)).esymm k` over `ℕ`. Unsigned Stirling numbers of the first
kind are `Nat.stirlingFirst`, and the rising factorial power `n^(j̄) = n (n + 1) ⋯ (n + j - 1)`
is `Nat.ascFactorial n j`.

The signed entries `b_{j,k}(n) = (-1)^k e_{j,j-k}(n)` of `B(n)` are `hyperseqB`; the entries
`c_{ℓ,m}(n)` of `C(n)` are `alternatingBinomialPowerSum ℓ m 1 (n + 1)` and the hypersequence
`a^{(r)}_n` is `hypersequence a r n`, both from the first paper's module; Mitrinović's numbers
`R^k_j(a, b)` (Section 4) are `mitrinovicR`.
-/

/-- **The inverse of Parisse's matrix $C(n)$.** Let $n \in \mathbb{N}$. Let $e_{j,i}(n)$ be the
elementary symmetric polynomial of degree $i$ in $n + 1, \dots, n + j$, let
$b_{j,k}(n) = (-1)^k e_{j,j-k}(n)$ for $k \le j$ and $b_{j,k}(n) = 0$ for $k > j$, let
$p_{\ell,m}(x, y) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (k x + y)^\ell$ for complex $x, y$, and let
$c_{\ell,m}(n) = p_{\ell,m}(1, n + 1) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (k + n + 1)^\ell$.
Then for all $j, m \in \mathbb{N}$, with $\delta_{j,m}$ the Kronecker delta,
$\sum_{k=0}^{j} \frac{b_{j,k}(n)}{j!} \, c_{k,m}(n) = \delta_{j,m}$ and
$\sum_{k=0}^{j} c_{j,k}(n) \, \frac{b_{k,m}(n)}{k!} = \delta_{j,m}$.

In matrix form, with $B(n) = (b_{j,k}(n))$, $C(n) = (c_{\ell,m}(n))$ and $D$ the diagonal matrix
of the factorials $j!$, this says $C(n)^{-1} = D^{-1} B(n)$; both matrices are lower triangular,
so each entry of the two products is the finite sum above.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Theorem 2 (`integers-2026-A36-thm-2`). -/
public theorem_wanted hyperseqC_inv_eq_hyperseqB_div_factorial (n j m : ℕ) :
    ∑ k ∈ Finset.range (j + 1), (hyperseqB n j k : ℂ) / j.factorial *
        alternatingBinomialPowerSum k m 1 (n + 1) = (if j = m then 1 else 0) ∧
      ∑ k ∈ Finset.range (j + 1), alternatingBinomialPowerSum j k 1 (n + 1) *
        ((hyperseqB n k m : ℂ) / k.factorial) = if j = m then 1 else 0

/-- **The inverse of Parisse's matrix $B(n)$.** Let $n \in \mathbb{N}$. Let $e_{j,i}(n)$ be the
elementary symmetric polynomial of degree $i$ in $n + 1, \dots, n + j$, let
$b_{j,k}(n) = (-1)^k e_{j,j-k}(n)$ for $k \le j$ and $b_{j,k}(n) = 0$ for $k > j$, let
$p_{\ell,m}(x, y) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (k x + y)^\ell$ for complex $x, y$, and let
$c_{\ell,m}(n) = p_{\ell,m}(1, n + 1) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (k + n + 1)^\ell$.
Then for all $j, m \in \mathbb{N}$, with $\delta_{j,m}$ the Kronecker delta,
$\sum_{k=0}^{j} b_{j,k}(n) \, \frac{c_{k,m}(n)}{m!} = \delta_{j,m}$ and
$\sum_{k=0}^{j} \frac{c_{j,k}(n)}{k!} \, b_{k,m}(n) = \delta_{j,m}$.

In matrix form, with $B(n) = (b_{j,k}(n))$, $C(n) = (c_{\ell,m}(n))$ and $D$ the diagonal matrix
of the factorials $j!$, this says $B(n)^{-1} = C(n) D^{-1}$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Corollary 1, Equation (2.9) (`integers-2026-A36-cor-1`). -/
public theorem_wanted hyperseqB_inv_eq_hyperseqC_div_factorial (n j m : ℕ) :
    ∑ k ∈ Finset.range (j + 1), (hyperseqB n j k : ℂ) *
        (alternatingBinomialPowerSum k m 1 (n + 1) / m.factorial) = (if j = m then 1 else 0) ∧
      ∑ k ∈ Finset.range (j + 1), alternatingBinomialPowerSum j k 1 (n + 1) / k.factorial *
        (hyperseqB n k m : ℂ) = if j = m then 1 else 0

/-- **The product of Parisse's matrices B(n) and C(n).** For $n, j, m \in \mathbb{N}$ let
$b_{j,i}(n) = (-1)^i e_{j-i}(n + 1, \dots, n + j)$ for $i \le j$ be the entries of Parisse's
matrix $B(n)$, where $e_d$ is the elementary symmetric polynomial of degree $d$, and let
$c_{i,m}(n) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (k + n + 1)^i$ be the entries
of $C(n)$. Then $\sum_{i=0}^{j} b_{j,i}(n)\, c_{i,m}(n)$ equals $j!$ if $j = m$ and $0$ otherwise.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Corollary 2 (`integers-2026-A36-cor-2`). -/
public theorem_wanted sum_hyperseqB_mul_hyperseqC (n j m : ℕ) :
    ∑ i ∈ Finset.range (j + 1), (hyperseqB n j i : ℂ) * alternatingBinomialPowerSum i m 1 (n + 1) =
      if j = m then (j.factorial : ℂ) else 0

/-- **Recurrence, closed form and row sums of Parisse's $b_{j,k}(n)$.** Let $n \in \mathbb{N}$ and
let $b_{j,k}(n)$ be the entries of Parisse's matrix $B(n)$. Write $[j, \ell]$ for the unsigned
Stirling numbers of the first kind and $x^{\overline{j}} = x (x + 1) \cdots (x + j - 1)$ for the
rising factorial. Then $b_{0,k}(n) = \delta_{0,k}$ for all $k$; for all $j, k \in \mathbb{N}$,
$b_{j+1,0}(n) = (n + j + 1) \, b_{j,0}(n)$ and
$b_{j+1,k+1}(n) = (n + j + 1) \, b_{j,k+1}(n) - b_{j,k}(n)$;
$b_{j,k}(n) = (-1)^k \sum_{\ell=k}^{j} \binom{\ell}{k} [j, \ell] \, (n + 1)^{\ell-k}$ for all
$j, k$ (an empty sum for $k > j$); and for all $j$,
$\sum_{k=0}^{j} b_{j,k}(n) = n^{\overline{j}}$ and
$\sum_{k=0}^{j} (-1)^k b_{j,k}(n) = (n + 2)^{\overline{j}}$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Proposition 2 (`integers-2026-A36-prop-2`). -/
public theorem_wanted hyperseqB_recurrence_closed_form_row_sums (n : ℕ) :
    (∀ k : ℕ, hyperseqB n 0 k = if k = 0 then 1 else 0) ∧
    (∀ j : ℕ, hyperseqB n (j + 1) 0 = (n + (j + 1)) * hyperseqB n j 0) ∧
    (∀ j k : ℕ, hyperseqB n (j + 1) (k + 1) =
      (n + (j + 1)) * hyperseqB n j (k + 1) - hyperseqB n j k) ∧
    (∀ j k : ℕ, hyperseqB n j k = (-1) ^ k * ∑ ℓ ∈ Finset.Icc k j,
      (ℓ.choose k * Nat.stirlingFirst j ℓ : ℤ) * ((n : ℤ) + 1) ^ (ℓ - k)) ∧
    (∀ j : ℕ, ∑ k ∈ Finset.range (j + 1), hyperseqB n j k = (n.ascFactorial j : ℤ)) ∧
    ∀ j : ℕ, ∑ k ∈ Finset.range (j + 1), (-1) ^ k * hyperseqB n j k =
      ((n + 2).ascFactorial j : ℤ)

/-- **Parisse's coefficients at $n$ from their values at $-1$.** Let $n \in \mathbb{Z}$. For
$j, k \in \mathbb{N}$ let $e_{j,k}(n)$ be the elementary symmetric polynomial of degree $k$ in
$n + 1, \dots, n + j$, let $b_{j,k}(n) = (-1)^k e_{j,j-k}(n)$ for $k \le j$ and $b_{j,k}(n) = 0$
for $k > j$, let
$p_{\ell,m}(x, y) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (k x + y)^\ell$ for complex $x, y$, with
$0^0 = 1$, and let
$c_{\ell,m}(n) = p_{\ell,m}(1, n + 1) = \sum_{k=0}^{m} (-1)^k \binom{m}{k} (k + n + 1)^\ell$. Then
$e_{j,k}(n) = \sum_{i=0}^{k} \binom{j - k + i}{i} (n + 1)^i e_{j,k-i}(-1)$ for all $k \le j$,
$b_{j,k}(n) = \sum_{i=k}^{j} (-1)^{i-k} \binom{i}{k} (n + 1)^{i-k} b_{j,i}(-1)$ for all $j, k$,
and $c_{\ell,m}(n) = \sum_{i=m}^{\ell} \binom{\ell}{i} (n + 1)^{\ell-i} c_{i,m}(-1)$ for all
$\ell, m \in \mathbb{N}$.

The first identity is stated only for $k \le j$; for $k > j$ the source's upper index
$j - k + i$ of the binomial coefficient can be negative.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Proposition 3 (`integers-2026-A36-prop-3`). -/
public theorem_wanted hyperseq_entries_eq_sum_at_neg_one (n : ℤ) :
    (∀ j k : ℕ, k ≤ j → ((Finset.Icc 1 j).val.map fun i : ℕ => n + i).esymm k =
      ∑ i ∈ Finset.range (k + 1), ((j - k + i).choose i : ℤ) * (n + 1) ^ i *
        ((Finset.Icc 1 j).val.map fun i : ℕ => (-1 : ℤ) + i).esymm (k - i)) ∧
    (∀ j k : ℕ, hyperseqB n j k =
      ∑ i ∈ Finset.Icc k j, (-1) ^ (i - k) * (i.choose k : ℤ) * (n + 1) ^ (i - k) *
        hyperseqB (-1) j i) ∧
    ∀ ℓ m : ℕ, alternatingBinomialPowerSum ℓ m 1 (n + 1) =
      ∑ i ∈ Finset.Icc m ℓ, (ℓ.choose i : ℂ) * ((n : ℂ) + 1) ^ (ℓ - i) *
        alternatingBinomialPowerSum i m 1 0

end

end MetaMathlibExt
