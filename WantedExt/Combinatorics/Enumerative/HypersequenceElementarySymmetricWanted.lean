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

/-- **Recurrence, closed form and row sums of $e_{j,k}(n)$.** Let $n \in \mathbb{N}$ and let
$e_{j,k}(n)$ be the elementary symmetric polynomial of degree $k$ in $n + 1, \dots, n + j$.
Write $[j, \ell]$ for the unsigned Stirling numbers of the first kind and
$x^{\overline{j}} = x (x + 1) \cdots (x + j - 1)$ for the rising factorial. Then
$e_{0,k}(n) = \delta_{0,k}$ for all $k$;
$e_{j+1,k+1}(n) = e_{j,k+1}(n) + (n + j + 1) \, e_{j,k}(n)$ for all $j, k \in \mathbb{N}$;
$e_{j,k}(n) = \sum_{\ell=0}^{k} \binom{j-k+\ell}{\ell} [j, j-k+\ell] \, (n + 1)^\ell$ for all
$k \le j$; and for all $j$, $\sum_{k=0}^{j} e_{j,k}(n) = (n + 2)^{\overline{j}}$ and
$\sum_{k=0}^{j} (-1)^k e_{j,k}(n) = (-1)^j n^{\overline{j}}$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36, Proposition 1 (`integers-2026-A36-prop-1`). -/
public theorem_wanted hyperseq_esymm_recurrence_closed_form_row_sums (n : ℕ) :
    (∀ k : ℕ, ((Finset.Icc 1 0).val.map (n + ·)).esymm k = if k = 0 then 1 else 0) ∧
    (∀ j k : ℕ, ((Finset.Icc 1 (j + 1)).val.map (n + ·)).esymm (k + 1) =
      ((Finset.Icc 1 j).val.map (n + ·)).esymm (k + 1) +
        (n + (j + 1)) * ((Finset.Icc 1 j).val.map (n + ·)).esymm k) ∧
    (∀ j k : ℕ, k ≤ j → ((Finset.Icc 1 j).val.map (n + ·)).esymm k =
      ∑ ℓ ∈ Finset.range (k + 1),
        (j - k + ℓ).choose ℓ * Nat.stirlingFirst j (j - k + ℓ) * (n + 1) ^ ℓ) ∧
    (∀ j : ℕ, ∑ k ∈ Finset.range (j + 1), ((Finset.Icc 1 j).val.map (n + ·)).esymm k =
      (n + 2).ascFactorial j) ∧
    ∀ j : ℕ, ∑ k ∈ Finset.range (j + 1),
        (-1 : ℤ) ^ k * (((Finset.Icc 1 j).val.map (n + ·)).esymm k : ℕ) =
      (-1 : ℤ) ^ j * (n.ascFactorial j : ℕ)

/-- **Elementary symmetric functions of the first integers via Stirling numbers.** For
$j, k \in \mathbb{N}$ let $e_{j,k}$ be the elementary symmetric polynomial of degree $k$ evaluated
at $1, 2, \dots, j$ (the source's $e_{j,k}(0)$), and let $c(j, i)$ be the unsigned Stirling number
of the first kind. Then $e_{0,k} = 1$ if $k = 0$ and $e_{0,k} = 0$ otherwise; for all $j, k$,
$e_{j+1,k+1} = e_{j,k+1} + (j + 1)\, e_{j,k}$; and for all $k \le j$,
$$e_{j,k} = \sum_{\ell=0}^{k} \binom{j-k+\ell}{\ell}\, c(j, j-k+\ell) = c(j + 1, j + 1 - k).$$

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36, Corollary 3 (`integers-2026-A36-cor-3`). -/
public theorem_wanted hyperseq_esymm_zero_recurrence_stirling :
    (∀ k : ℕ, ((Finset.Icc 1 0).val).esymm k = if k = 0 then 1 else 0) ∧
    (∀ j k : ℕ, ((Finset.Icc 1 (j + 1)).val).esymm (k + 1) =
      ((Finset.Icc 1 j).val).esymm (k + 1) +
        (j + 1) * ((Finset.Icc 1 j).val).esymm k) ∧
    ∀ j k : ℕ, k ≤ j →
      ((Finset.Icc 1 j).val).esymm k =
          ∑ ℓ ∈ Finset.range (k + 1), (j - k + ℓ).choose ℓ * Nat.stirlingFirst j (j - k + ℓ) ∧
        ((Finset.Icc 1 j).val).esymm k = Nat.stirlingFirst (j + 1) (j + 1 - k)


/-- **Parisse's matrix $B(n)$.** For an integer $n$ and $j, k \in \mathbb{N}$, let $e_{j,i}(n)$ be
the elementary symmetric polynomial of degree $i$ in $n + 1, \dots, n + j$. The entry
$b_{j,k}(n)$ of $B(n)$ is $(-1)^k e_{j,j-k}(n)$ for $k \le j$ and $0$ for $k > j$; it is an
integer.

The source also uses this for $n \in \mathbb{Z}$ (Proposition 3, after Remark 1), which is why
$n$ ranges over the integers.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Section 2, Equation (2.5). -/
public def hyperseqB (n : ℤ) (j k : ℕ) : ℤ :=
  if k ≤ j then (-1) ^ k * ((Finset.Icc 1 j).val.map fun i : ℕ => n + i).esymm (j - k) else 0

/-- **Row one of Parisse's matrix $B(n)$.** For every integer $n$, the entries $b_{j,k}(n)$ of
$B(n)$ satisfy $b_{1,0}(n) = n + 1$ and $b_{1,1}(n) = -1$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Section 2, display of `B(n)`. -/
public theorem hyperseqB_one (n : ℤ) : hyperseqB n 1 0 = n + 1 ∧ hyperseqB n 1 1 = -1 := by
  simp [hyperseqB, Multiset.esymm, Multiset.powersetCard_one]

/-- **Row three of Parisse's matrix $B(1)$.** The entries $b_{3,0}(1), b_{3,1}(1), b_{3,2}(1),
b_{3,3}(1)$ of $B(1)$ are $24, -26, 9, -1$.

This matches the source's display of row three of $B(n)$,
$(n + 1)(n + 2)(n + 3), -(3n^2 + 12n + 11), 3n + 6, -1$, at $n = 1$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Section 2, display of `B(n)`. -/
public theorem hyperseqB_row_three :
    (List.range 4).map (hyperseqB 1 3) = [24, -26, 9, -1] := by
  decide +kernel

/-- **Mitrinović's numbers.** For complex numbers $a$ and $b$, Mitrinović's numbers
$R^k_j(a, b)$, $j, k \in \mathbb{N}$ (lower index $j$, upper index $k$), are defined by
$R^k_0(a, b) = 1$ if $k = 0$ and $R^k_0(a, b) = 0$ otherwise, and, for all $j, k$, by
$R^0_{j+1}(a, b) = -(a + b j)\, R^0_j(a, b)$ and
$R^{k+1}_{j+1}(a, b) = R^k_j(a, b) - (a + b j)\, R^{k+1}_j(a, b)$.

With $R = 0$ at negative indices this is the recurrence (4.2),
$R^k_j(a, b) = R^{k-1}_{j-1}(a, b) - (a - b + b j)\, R^k_{j-1}(a, b)$ for $j \ge 1$. The start
value is the source's Corollary 5 at $a = 0$ and its solution (4.3) at $j = 0$ for every $a$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Section 4, Equation (4.2). -/
public def mitrinovicR (a b : ℂ) : ℕ → ℕ → ℂ
  | 0, k => if k = 0 then 1 else 0
  | j + 1, 0 => -(a + b * j) * mitrinovicR a b j 0
  | j + 1, k + 1 => mitrinovicR a b j k - (a + b * j) * mitrinovicR a b j (k + 1)

/-- **Mitrinović's numbers with lower index one.** For all complex numbers $a, b$, Mitrinović's
numbers satisfy $R^0_1(a, b) = -a$ and $R^1_1(a, b) = 1$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Section 4, Equation (4.2). -/
public theorem mitrinovicR_one (a b : ℂ) :
    mitrinovicR a b 1 0 = -a ∧ mitrinovicR a b 1 1 = 1 := by
  simp [mitrinovicR]

/-- **Hypersequences through elementary symmetric polynomials.** Let $a$ be a sequence of complex
numbers and let $j, n \in \mathbb{N}$. Write $a^{(r)}_n$ for the hypersequence of generation $r$
of $a$, write $e_{j,k}(n)$ for the elementary symmetric polynomial of degree $k$ in
$n + 1, \dots, n + j$, and put $t_i(n) = \sum_{k=0}^{n} k^i a_k$, with $0^0 = 1$. Then
$j! \, a^{(j+1)}_n = (-1)^j \sum_{k=0}^{j} (-1)^k e_{j,k}(n) \, t_{j-k}(n)$ and
$j! \, a^{(j+1)}_n = \sum_{k=0}^{j} (-1)^k e_{j,j-k}(n) \, t_k(n)$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Theorem 1, Equation (2.1) (`integers-2026-A36-thm-1`). -/
public theorem_wanted factorial_mul_hypersequence_eq_sum_esymm (a : ℕ → ℂ) (j n : ℕ) :
    (j.factorial : ℂ) * hypersequence a (j + 1) n =
        (-1) ^ j * ∑ k ∈ Finset.range (j + 1), (-1) ^ k *
          (((Finset.Icc 1 j).val.map (n + ·)).esymm k : ℕ) *
            ∑ i ∈ Finset.range (n + 1), (i : ℂ) ^ (j - k) * a i ∧
      (j.factorial : ℂ) * hypersequence a (j + 1) n =
        ∑ k ∈ Finset.range (j + 1), (-1) ^ k *
          (((Finset.Icc 1 j).val.map (n + ·)).esymm (j - k) : ℕ) *
            ∑ i ∈ Finset.range (n + 1), (i : ℂ) ^ k * a i

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

/-- **Parisse's $b_{j,k}(0)$ and Stirling numbers of the first kind.** Let $b_{j,k}(0)$ be the
entries of Parisse's matrix $B(0)$ and write $[j, \ell]$ for the unsigned Stirling numbers of the
first kind. Then $b_{0,k}(0) = \delta_{0,k}$ for all $k$; for all $j, k \in \mathbb{N}$,
$b_{j+1,0}(0) = (j + 1) \, b_{j,0}(0)$ and $b_{j+1,k+1}(0) = (j + 1) \, b_{j,k+1}(0) - b_{j,k}(0)$;
and for all $j, k \in \mathbb{N}$,
$b_{j,k}(0) = (-1)^k \sum_{\ell=k}^{j} \binom{\ell}{k} [j, \ell] = (-1)^k [j + 1, k + 1]$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Corollary 4 (`integers-2026-A36-cor-4`). -/
public theorem_wanted hyperseqB_zero_recurrence_stirling :
    (∀ k : ℕ, hyperseqB 0 0 k = if k = 0 then 1 else 0) ∧
    (∀ j : ℕ, hyperseqB 0 (j + 1) 0 = (j + 1) * hyperseqB 0 j 0) ∧
    (∀ j k : ℕ, hyperseqB 0 (j + 1) (k + 1) = (j + 1) * hyperseqB 0 j (k + 1) - hyperseqB 0 j k) ∧
    ∀ j k : ℕ,
      hyperseqB 0 j k = (-1) ^ k * ∑ ℓ ∈ Finset.Icc k j, (ℓ.choose k * Nat.stirlingFirst j ℓ : ℤ) ∧
        hyperseqB 0 j k = (-1) ^ k * Nat.stirlingFirst (j + 1) (k + 1)

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

/-- **Mitrinović's numbers at $a = 0$.** For every complex number $b$, Mitrinović's numbers
$R^k_j(0, b)$ satisfy the following. First, for every $k \in \mathbb{N}$, $R^k_0(0, b) = 1$ if
$k = 0$ and $R^k_0(0, b) = 0$ otherwise. Second, for all $j, k \in \mathbb{N}$,
$R^{k+1}_{j+1}(0, b) = R^k_j(0, b) + (b - b(j + 1))\, R^{k+1}_j(0, b)$. Third, for all
$j, k \in \mathbb{N}$, $R^k_j(0, b) = (-b)^{j-k} c(j, k)$, where $c(j, k)$ is the unsigned
Stirling number of the first kind, which is $0$ for $k > j$, and the exponent $j - k$ is read as
$0$ when $k > j$.

The source prints the last factor of the recurrence as $R^k_{j-1}(a, b)$; it is
$R^k_{j-1}(0, b)$, the case $a = 0$ of (4.2). The source's hypothesis $b \ne 0$ is dropped: at
$b = 0$ both sides of the closed form are $\delta_{j,k}$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Corollary 5 (`integers-2026-A36-cor-5`). -/
public theorem_wanted mitrinovicR_zero_eq (b : ℂ) :
    (∀ k : ℕ, mitrinovicR 0 b 0 k = if k = 0 then 1 else 0) ∧
    (∀ j k : ℕ, mitrinovicR 0 b (j + 1) (k + 1) =
      mitrinovicR 0 b j k + (b - b * (j + 1)) * mitrinovicR 0 b j (k + 1)) ∧
    ∀ j k : ℕ, mitrinovicR 0 b j k = (-b) ^ (j - k) * Nat.stirlingFirst j k

/-- **Binomial expansion of Mitrinović's numbers in the first parameter.** For all complex
numbers $a, b$ and all $j, k \in \mathbb{N}$, Mitrinović's numbers satisfy
$$R^k_j(a, b) = \sum_{\ell=0}^{j-k} (-1)^\ell \binom{k+\ell}{\ell} a^\ell R^{k+\ell}_j(0, b),$$
where the upper limit $j - k$ is read as $0$ when $k > j$ (both sides are then $0$).

The source's hypothesis $b \ne 0$ is not needed: the identity also holds at $b = 0$.

Source: Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted
Sums II*, INTEGERS 26 (2026), Article A36,
Proposition 4, Equation (4.6) (`integers-2026-A36-prop-4`). -/
public theorem_wanted mitrinovicR_eq_sum_mitrinovicR_zero (a b : ℂ) (j k : ℕ) :
    mitrinovicR a b j k =
      ∑ ℓ ∈ Finset.range (j - k + 1), (-1) ^ ℓ * ((k + ℓ).choose ℓ : ℂ) * a ^ ℓ *
        mitrinovicR 0 b j (k + ℓ)

end

end MetaMathlibExt
