/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.Algebra.Polynomial.AlgebraMap
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import Mathlib.Data.Fin.Tuple.NatAntidiagonal
public import Mathlib.Data.Fintype.Pi
public import Mathlib.GroupTheory.Perm.Cycle.Type
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.RingTheory.MvPowerSeries.Substitution
public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Exp
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.Substitution
public import MathlibExt.NumberTheory.MultipleZeta.CyclicSumFormula

/-!
# q-analogues of multiple zeta values: Schlesinger–Zudilin and OOZ models

Statements from Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24
(2024), Article A6 (arXiv:2111.00051), about Schlesinger–Zudilin (SZ) qMZVs,
their generating series and duality, the partition function, and the
Ohno–Okuda–Zudilin (OOZ) model, the general qMZVs of Bachmann–Kühn with the
spaces `𝒵_q` and `𝒵_{q,1}` they span, the Bradley–Zhao (BZ) model, and the
description of `𝒵_q` by polynomial functions on partitions in Stanley coordinates,
and the quasi-shuffle and shuffle products the evaluation maps respect.

All q-series are formal power series in `q = PowerSeries.X` over `ℚ`; the factor
`1/(1 - q^m)` is the inverse `(1 - X ^ m)⁻¹` in `ℚ⟦X⟧`. Indices are lists of
natural numbers.
-/

open PowerSeries

namespace MetaMathlibExt

@[expose] public section

/-- **Partial sums of Schlesinger–Zudilin qMZVs.** For an index $(k_1, \dots, k_r)$ of natural
numbers and a natural number $M$, the partial sum is the formal power series in $q$ over
$\mathbb{Q}$
$$\sum_{M > m_1 > \dots > m_r > 0} \prod_{j=1}^{r} \frac{q^{m_j k_j}}{(1 - q^{m_j})^{k_j}},$$
where the sum runs over integers $m_1, \dots, m_r$ and $1/(1 - q^m)$ is the inverse in
$\mathbb{Q}[[q]]$. For the empty index it equals $1$ for every $M$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Schlesinger–Zudilin qMZVs (defining sum truncated at
`m₁ < M`). -/
public noncomputable def szQMZVPartial : List ℕ → ℕ → ℚ⟦X⟧
  | [], _ => 1
  | k :: ks, M => ∑ m ∈ Finset.Ioo 0 M, (X ^ m * (1 - X ^ m)⁻¹) ^ k * szQMZVPartial ks m

/-- **Schlesinger–Zudilin qMZVs.** For an index $k = (k_1, \dots, k_r)$ of natural numbers, the
Schlesinger–Zudilin qMZV $\zeta_q^{SZ}(k)$ is the formal power series in $q$ over $\mathbb{Q}$
whose coefficient of $q^N$, for each $N \ge 0$, is the coefficient of $q^N$ in the partial sum
$$\sum_{N \ge m_1 > \dots > m_r > 0} \prod_{j=1}^{r} \frac{q^{m_j k_j}}{(1 - q^{m_j})^{k_j}}$$
over integers $m_1, \dots, m_r$. In particular $\zeta_q^{SZ}(\emptyset) = 1$.

When the index is empty or $k_1 \ge 1$, the summands with $m_1 > N$ have no term of degree at
most $N$, so $\zeta_q^{SZ}(k)$ is the full series
$\sum_{m_1 > \dots > m_r > 0} \prod_{j} q^{m_j k_j} / (1 - q^{m_j})^{k_j}$. The paper does not
define the value when $k_1 = 0$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Schlesinger–Zudilin qMZVs (extended version of
Ebrahimi-Fard, Manchon and Singer, allowing `kⱼ = 0` for `j ≥ 2`). -/
public noncomputable def szQMZV (k : List ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun N => coeff N (szQMZVPartial k (N + 1))

/-- **The empty Schlesinger–Zudilin qMZV.** The Schlesinger–Zudilin qMZV of the empty index is
$1$: $\zeta_q^{SZ}(\emptyset) = 1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Schlesinger–Zudilin qMZVs. -/
public theorem szQMZV_nil : szQMZV [] = 1 := by
  ext N
  simp [szQMZV, szQMZVPartial]

/-- **Recursion for partial sums of Schlesinger–Zudilin qMZVs.** For natural numbers $k_1$ and
$M$ and an index $\kappa = (k_2, \dots, k_r)$ (possibly empty), write $Z_M(k_1, \kappa)$ and
$Z_m(\kappa)$ for the partial sums of Schlesinger–Zudilin qMZVs with bounds $M$ and $m$. Then
$$Z_M(k_1, \kappa) = \sum_{0 < m < M} \left(\frac{q^m}{1 - q^m}\right)^{k_1} Z_m(\kappa).$$

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Schlesinger–Zudilin qMZVs. -/
public theorem szQMZVPartial_cons (k : ℕ) (ks : List ℕ) (M : ℕ) :
    szQMZVPartial (k :: ks) M =
      ∑ m ∈ Finset.Ioo 0 M, (X ^ m * (1 - X ^ m)⁻¹) ^ k * szQMZVPartial ks m :=
  rfl

/-- **Nonempty Schlesinger–Zudilin qMZVs have no constant term.** For every nonempty index
$(k_1, \dots, k_r)$ of natural numbers, the constant term of the Schlesinger–Zudilin qMZV
$\zeta_q^{\mathrm{SZ}}(k_1, \dots, k_r)$ is $0$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Schlesinger–Zudilin qMZVs. -/
public theorem coeff_zero_szQMZV_cons (k : ℕ) (ks : List ℕ) :
    coeff 0 (szQMZV (k :: ks)) = 0 := by
  have h : Finset.Ioo 0 1 = ∅ := by decide
  simp [szQMZV, szQMZVPartial, h]

/-- **The coefficient of $q$ in $\zeta_q^{\mathrm{SZ}}(1)$.** The coefficient of $q$ in the
Schlesinger–Zudilin qMZV $\zeta_q^{\mathrm{SZ}}(1) = \sum_{m > 0} q^m / (1 - q^m)$ is $1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Schlesinger–Zudilin qMZVs. -/
public theorem coeff_one_szQMZV_singleton_one : coeff 1 (szQMZV [1]) = 1 := by
  have h : Finset.Ioo 0 2 = {1} := by decide
  simp [szQMZV, szQMZVPartial, h, coeff_succ_X_mul, constantCoeff_inv]

/-- **Block indices for Schlesinger–Zudilin qMZVs.** For a list of pairs of natural numbers
$(k_1, d_1), \dots, (k_r, d_r)$, the block index is the index
$(k_1, \{0\}^{d_1 - 1}, \dots, k_r, \{0\}^{d_r - 1})$ obtained by concatenating, for
$j = 1, \dots, r$, the entry $k_j$ followed by $d_j - 1$ zeros (no zeros when $d_j = 0$).

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 4 and Theorem 5 (SZ duality), index notation. -/
public def szBlockIndex (kd : List (ℕ × ℕ)) : List ℕ :=
  (kd.map fun p => p.1 :: List.replicate (p.2 - 1) 0).flatten

/-- **Block index of the empty list.** The block index of the empty list of pairs is the empty
index.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 5, index notation. -/
public theorem szBlockIndex_nil : szBlockIndex [] = [] := rfl

/-- **Recursion for block indices.** For natural numbers $k$, $d$ and a list $L$ of pairs of
natural numbers, the block index of the list with first pair $(k, d)$ followed by $L$ is $k$,
followed by $d - 1$ zeros (none when $d = 0$), followed by the block index of $L$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 5, index notation. -/
public theorem szBlockIndex_cons (k d : ℕ) (kd : List (ℕ × ℕ)) :
    szBlockIndex ((k, d) :: kd) = k :: (List.replicate (d - 1) 0 ++ szBlockIndex kd) :=
  rfl

/-- **Partial Ohno–Okuda–Zudilin sums.** For an index $(k_1, \dots, k_r)$ of natural numbers and a
natural number $M$, the partial OOZ sum is the formal power series in $q$ over $\mathbb{Q}$
$$\sum_{M > m_1 > \dots > m_r > 0} \prod_{j=1}^{r} \frac{1}{(1 - q^{m_j})^{k_j}},$$
the defining sum of $\zeta_q^{\mathrm{OOZ}}(k_1, \dots, k_r)$ with the factor $q^{m_1}$ removed and
truncated to $m_1 < M$. For the empty index it is $1$, for every $M$ (including $M = 0$).

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of OOZ-qMZVs (inner sums of the defining series). -/
public noncomputable def oozQMZVPartial : List ℕ → ℕ → ℚ⟦X⟧
  | [], _ => 1
  | k :: ks, M => ∑ m ∈ Finset.Ioo 0 M, ((1 - X ^ m)⁻¹) ^ k * oozQMZVPartial ks m

/-- **Ohno–Okuda–Zudilin q-multiple zeta values.** For an index $(k_1, \dots, k_r)$ of natural
numbers with $r \ge 1$, the (extended) Ohno–Okuda–Zudilin qMZV is the formal power series in $q$
over $\mathbb{Q}$
$$\zeta_q^{\mathrm{OOZ}}(k_1, \dots, k_r) = \sum_{m_1 > \dots > m_r > 0}
\frac{q^{m_1}}{(1 - q^{m_1})^{k_1} \cdots (1 - q^{m_r})^{k_r}},$$
and $\zeta_q^{\mathrm{OOZ}}(\varnothing) = 1$ for the empty index. The summands with $m_1 > N$
have $q$-adic order greater than $N$, so the coefficient of $q^N$ is computed from the finitely
many summands with $m_1 \le N$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of OOZ-qMZVs (extended version, `k₁ ≥ 1`, `kᵢ ≥ 0`). -/
public noncomputable def oozQMZV : List ℕ → ℚ⟦X⟧
  | [] => 1
  | k :: ks => PowerSeries.mk fun N =>
      coeff N (∑ m ∈ Finset.Ioo 0 (N + 1), X ^ m * ((1 - X ^ m)⁻¹) ^ k * oozQMZVPartial ks m)

/-- **The OOZ-qMZV of the empty index.** The Ohno–Okuda–Zudilin qMZV of the empty index is $1$:
$\zeta_q^{\mathrm{OOZ}}(\varnothing) = 1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of OOZ-qMZVs. -/
public theorem oozQMZV_nil : oozQMZV [] = 1 := rfl

/-- **Nonempty Ohno–Okuda–Zudilin qMZVs have no constant term.** For every nonempty index
$(k_1, \dots, k_r)$ of natural numbers, the constant term of the Ohno–Okuda–Zudilin qMZV
$\zeta_q^{\mathrm{OOZ}}(k_1, \dots, k_r)$ is $0$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of OOZ-qMZVs. -/
public theorem coeff_zero_oozQMZV_cons (k : ℕ) (ks : List ℕ) :
    coeff 0 (oozQMZV (k :: ks)) = 0 := by
  have h : Finset.Ioo 0 1 = ∅ := by decide
  simp [oozQMZV, h]

/-- **Coefficients of Schlesinger–Zudilin qMZVs as sums of binomial products.** Let $r \ge 0$,
and let $k_1, \dots, k_r$ and $d_1, \dots, d_r$ be positive integers. For every natural number
$N$, the coefficient of $q^N$ in the Schlesinger–Zudilin qMZV
$\zeta_q^{\mathrm{SZ}}(k_1, \{0\}^{d_1 - 1}, \dots, k_r, \{0\}^{d_r - 1})$, whose index lists each
$k_j$ followed by $d_j - 1$ zeros, equals
$$\sum \prod_{j=1}^{r} \binom{n_j - 1}{k_j - 1} \binom{m_j - m_{j+1} - 1}{d_j - 1},$$
where the sum runs over all integers $m_1 > \dots > m_r > 0$ and $n_1, \dots, n_r \ge 1$ with
$m_1 n_1 + \dots + m_r n_r = N$, and where $m_{r+1} = 0$.

These are the coefficients of $X_1^{k_1 - 1} \cdots X_r^{k_r - 1} Y_1^{d_1 - 1} \cdots
Y_r^{d_r - 1} q^N$ on both sides of the paper's identity expressing the generating series
$s(X; Y)$ of these qMZVs as
$\sum \prod_j (1 + X_j)^{n_j - 1} (1 + Y_j)^{m_j - m_{j+1} - 1} q^{m_j n_j}$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 4 (`integers-2024-A6-thm-4`). -/
public theorem_wanted coeff_szQMZV_szBlockIndex_eq_sum_choose (r : ℕ) (k d : Fin r → ℕ)
    (hk : ∀ j, 1 ≤ k j) (hd : ∀ j, 1 ≤ d j) (N : ℕ) :
    coeff N (szQMZV (szBlockIndex (List.ofFn fun j => (k j, d j)))) =
      ∑ mn ∈ (Fintype.piFinset fun _ : Fin r => Finset.range (N + 1)) ×ˢ
          (Fintype.piFinset fun _ : Fin r => Finset.range (N + 1)) with
          StrictAnti mn.1 ∧ (∀ j, 0 < mn.1 j) ∧ (∀ j, 0 < mn.2 j) ∧
            ∑ j, mn.1 j * mn.2 j = N,
        ∏ j : Fin r, ((((mn.2 j - 1).choose (k j - 1)) *
          ((mn.1 j - (if h : j.val + 1 < r then mn.1 ⟨j.val + 1, h⟩ else 0) - 1).choose
            (d j - 1)) : ℕ) : ℚ)

/-- **Schlesinger–Zudilin duality.** Let $\zeta_q^{SZ}$ denote the Schlesinger–Zudilin qMZV, let
$(k_1, d_1), \dots, (k_r, d_r)$ be pairs of natural numbers with $k_j \ge 1$ and $d_j \ge 1$
for all $j$, and let $\{0\}^n$ denote $n$ zeros. Then
$$\zeta_q^{SZ}(k_1, \{0\}^{d_1 - 1}, \dots, k_r, \{0\}^{d_r - 1}) =
\zeta_q^{SZ}(d_r, \{0\}^{k_r - 1}, \dots, d_1, \{0\}^{k_1 - 1}).$$
That is, $\zeta_q^{SZ}$ takes the same value at the block index of the list of pairs and at
the block index of the reversed list with each pair swapped.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 5 (SZ duality, Zhao) (`integers-2024-A6-thm-5`). -/
public theorem_wanted szQMZV_szBlockIndex_dual (kd : List (ℕ × ℕ))
    (hkd : ∀ p ∈ kd, 1 ≤ p.1 ∧ 1 ≤ p.2) :
    szQMZV (szBlockIndex kd) = szQMZV (szBlockIndex (kd.reverse.map Prod.swap))

/-- **Partitions from Schlesinger–Zudilin qMZVs.** Let $\zeta_q^{SZ}$ denote the
Schlesinger–Zudilin qMZV, $\{1\}^r$ the index of $r$ ones and $p(N)$ the number of
partitions of $N$. For all natural numbers $N \ge 1$ and $R \ge N$, the coefficient of $q^N$ in
$\sum_{r=1}^{R} \zeta_q^{SZ}(\{1\}^r)$ equals $p(N)$.

Since the summands with $r > N$ have no $q^N$ term, this is the coefficientwise form of
$\sum_{r \ge 1} \zeta_q^{SZ}(\{1\}^r) = \sum_{N \ge 1} p(N) q^N$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Lemma 3 (`integers-2024-A6-lem-3`). -/
public theorem_wanted sum_coeff_szQMZV_replicate_one_eq_card_partition (N R : ℕ)
    (hN : 1 ≤ N) (hR : N ≤ R) :
    ∑ r ∈ Finset.Icc 1 R, coeff N (szQMZV (List.replicate r 1)) =
      Fintype.card N.Partition

/-- **Cycle type classifies conjugacy classes of permutations.** For every natural number $n$,
there is a bijection from the set of conjugacy classes of the symmetric group $S_n$ to the set
of partitions of $n$ that sends the class of each permutation $\sigma$ to the cycle type of
$\sigma$: the partition of $n$ formed by the lengths of the cycles of $\sigma$, fixed points
counting as cycles of length $1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Lemma 4 (`integers-2024-A6-lem-4`). -/
public theorem_wanted exists_conjClasses_perm_equiv_partition (n : ℕ) :
    ∃ e : ConjClasses (Equiv.Perm (Fin n)) ≃ (Fintype.card (Fin n)).Partition,
      ∀ σ : Equiv.Perm (Fin n), e (ConjClasses.mk σ) = σ.partition

/-- **Number of conjugacy classes of the symmetric group.** For every natural number $n$, the
number of conjugacy classes of the symmetric group $S_n$ equals the number $p(n)$ of partitions
of $n$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Lemma 4 (`integers-2024-A6-lem-4`). -/
public theorem_wanted card_conjClasses_perm_eq_card_partition (n : ℕ) :
    Nat.card (ConjClasses (Equiv.Perm (Fin n))) = Fintype.card n.Partition

/-- **Class numbers of finite general linear groups via OOZ-qMZVs.** Let $K$ be a finite field
with $c$ elements and, for $n \ge 0$, let $a_{n,K}$ be the number of conjugacy classes of
$\mathrm{GL}_n(K)$, so that $a_{0,K} = 1$ because $\mathrm{GL}_0(K)$ is the trivial group. Write
$\{1\}^r$ for the index consisting of $r$ ones and $\zeta_q^{\mathrm{OOZ}}$ for the
Ohno–Okuda–Zudilin qMZV. Then for all natural numbers $N \le R$, $a_{N,K}$ equals the coefficient
of $q^N$ in $\sum_{r=0}^{R} (c - 1)^r \zeta_q^{\mathrm{OOZ}}(\{1\}^r)$.

Since the summands with $r > N$ have no $q^N$ term, this is the identity of formal power series
$\sum_{n \ge 0} a_{n,K} q^n = \sum_{r \ge 0} (c - 1)^r \zeta_q^{\mathrm{OOZ}}(\{1\}^r)$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 20 (`integers-2024-A6-thm-20`). -/
public theorem_wanted card_conjClasses_GL_eq_coeff_sum_oozQMZV (K : Type*) [Field K]
    [Fintype K] (N R : ℕ) (hR : N ≤ R) :
    (Nat.card (ConjClasses (GL (Fin N) K)) : ℚ) =
      ∑ r ∈ Finset.range (R + 1),
        ((Fintype.card K : ℚ) - 1) ^ r * coeff N (oozQMZV (List.replicate r 1))

/-- **Partial sums of general qMZVs.** Let $(k_1, Q_1), \dots, (k_r, Q_r)$ be pairs of natural
numbers $k_j$ and polynomials $Q_j \in \mathbb{Q}[X]$, and let $M$ be a natural number. The
partial sum is the formal power series in $q$ over $\mathbb{Q}$
$$\sum_{M > m_1 > \dots > m_r > 0} \prod_{j=1}^{r} \frac{Q_j(q^{m_j})}{(1 - q^{m_j})^{k_j}},$$
where the sum runs over integers $m_1, \dots, m_r$ and $1/(1 - q^m)$ is the inverse in
$\mathbb{Q}[[q]]$. For $r = 0$ it equals $1$ for every $M$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of qMZVs (after Bachmann–Kühn), defining sum truncated at
`m₁ < M`. -/
public noncomputable def qMZVPartial : List (ℕ × Polynomial ℚ) → ℕ → ℚ⟦X⟧
  | [], _ => 1
  | (k, Q) :: kQ, M => ∑ m ∈ Finset.Ioo 0 M,
      Polynomial.aeval (X ^ m : ℚ⟦X⟧) Q * ((1 - X ^ m)⁻¹) ^ k * qMZVPartial kQ m

/-- **General q-multiple zeta values.** For natural numbers $k_1, \dots, k_r$ and polynomials
$Q_1, \dots, Q_r \in \mathbb{Q}[X]$, the general qMZV $\zeta_q(k_1, \dots, k_r; Q_1, \dots, Q_r)$
is the formal power series in $q$ over $\mathbb{Q}$ whose coefficient of $q^N$, for every $N$, is
the coefficient of $q^N$ in the finite sum
$\sum_{N \ge m_1 > m_2 > \dots > m_r > 0} \prod_{j=1}^{r} Q_j(q^{m_j}) / (1 - q^{m_j})^{k_j}$
over integers $m_1, \dots, m_r$, and $\zeta_q(\varnothing; \varnothing) = 1$.

When $Q_1(0) = 0$ (the paper's condition $Q_1 \in X \mathbb{Q}[X]$), the summands with
$m_1 > N$ have $q$-adic order greater than $N$, so this is the series
$\sum_{m_1 > \dots > m_r > 0} \prod_{j=1}^{r} Q_j(q^{m_j}) / (1 - q^{m_j})^{k_j}$; for other data
the value is a junk value.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of qMZVs (after Bachmann–Kühn). -/
public noncomputable def qMZV : List (ℕ × Polynomial ℚ) → ℚ⟦X⟧
  | [] => 1
  | (k, Q) :: kQ => PowerSeries.mk fun N => coeff N (∑ m ∈ Finset.Ioo 0 (N + 1),
      Polynomial.aeval (X ^ m : ℚ⟦X⟧) Q * ((1 - X ^ m)⁻¹) ^ k * qMZVPartial kQ m)

/-- **General qMZV of the empty index.** The general q-multiple zeta value of the empty data is
$\zeta_q(\varnothing; \varnothing) = 1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of qMZVs. -/
public theorem qMZV_nil : qMZV [] = 1 := rfl

/-- **Nonempty general qMZVs have no constant term.** For every nonempty list
$(k_1, Q_1), \dots, (k_r, Q_r)$ of natural numbers $k_j$ and polynomials $Q_j \in \mathbb{Q}[X]$,
the constant coefficient of the general q-multiple zeta value
$\zeta_q(k_1, \dots, k_r; Q_1, \dots, Q_r)$ is $0$. No condition on $Q_1(0)$ is assumed.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of qMZVs. -/
public theorem coeff_zero_qMZV_cons (k : ℕ) (Q : Polynomial ℚ) (kQ : List (ℕ × Polynomial ℚ)) :
    coeff 0 (qMZV ((k, Q) :: kQ)) = 0 := by
  have h : Finset.Ioo 0 1 = ∅ := by decide
  simp [qMZV, h]

/-- **Spaces of general qMZVs.** For a natural number $d$, $\mathcal{Z}_{q,d}$ is the
$\mathbb{Q}$-subspace of the formal power series $\mathbb{Q}[[q]]$ spanned by the general qMZVs
$\zeta_q(k_1, \dots, k_r; Q_1, \dots, Q_r)$ over all $r \ge 0$, natural numbers $k_1, \dots, k_r$
and polynomials $Q_1, \dots, Q_r \in \mathbb{Q}[X]$ with $\deg Q_j + d \le k_j$ for every $j$
(the zero polynomial counting as degree $0$) and $Q_1(0) = 0$ when $r \ge 1$.

The space $\mathcal{Z}_q := \mathcal{Z}_{q,0}$ is the space of qMZVs (with $k_j \ge 0$); for
$d = 1$ the degree condition forces $k_j \ge 1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of qMZVs (ii) and Definition of `𝒵_{q,d}` (after
Bachmann–Kühn). -/
public noncomputable def qMZVSpace (d : ℕ) : Submodule ℚ ℚ⟦X⟧ :=
  Submodule.span ℚ {f | ∃ kQ : List (ℕ × Polynomial ℚ),
    (∀ p ∈ kQ, p.2.natDegree + d ≤ p.1) ∧ (∀ p ∈ kQ.head?, p.2.coeff 0 = 0) ∧ f = qMZV kQ}

/-- **The constant series one lies in every space of qMZVs.** For every natural number $d$, the
constant power series $1$ lies in the $\mathbb{Q}$-span $\mathcal{Z}_{q,d}$ of the general
q-multiple zeta values $\zeta_q(k_1, \dots, k_r; Q_1, \dots, Q_r)$ with $Q_1(0) = 0$ and
$\deg Q_j + d \le k_j$ for all $j$, where the zero polynomial is given degree $0$; it is the
qMZV of the empty index.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of qMZVs (ii). -/
public theorem one_mem_qMZVSpace (d : ℕ) : (1 : ℚ⟦X⟧) ∈ qMZVSpace d :=
  Submodule.subset_span ⟨[], by simp, by simp, rfl⟩

/-- **Bradley–Zhao q-multiple zeta values.** For an index $k = (k_1, \dots, k_r)$ of natural
numbers, the Bradley–Zhao q-multiple zeta value is the general qMZV
$\zeta_q^{BZ}(k) = \zeta_q(k_1, \dots, k_r; X^{k_1 - 1}, \dots, X^{k_r - 1})$, a formal power
series in $q$ over $\mathbb{Q}$, where $k_j - 1$ is truncated at $0$. For an admissible index
($k_1 \ge 2$ and all $k_i \ge 1$) it equals

$$\zeta_q^{BZ}(k) = \sum_{m_1 > \dots > m_r > 0} \prod_{j=1}^{r}
\frac{q^{m_j (k_j - 1)}}{(1 - q^{m_j})^{k_j}};$$

for other indices the value has no intended meaning.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Bradley–Zhao qMZVs. -/
public noncomputable def bzQMZV (k : List ℕ) : ℚ⟦X⟧ :=
  qMZV (k.map fun k => (k, Polynomial.X ^ (k - 1)))

/-- **Bradley–Zhao qMZV of the empty index.** The Bradley–Zhao q-multiple zeta value of the
empty index is $\zeta_q^{BZ}(\varnothing) = 1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Bradley–Zhao qMZVs. -/
public theorem bzQMZV_nil : bzQMZV [] = 1 := rfl

/-- **Nonempty Bradley–Zhao qMZVs have no constant term.** For every nonempty index
$(k_1, \dots, k_r)$ of natural numbers, the constant coefficient of the Bradley–Zhao
q-multiple zeta value $\zeta_q^{BZ}(k_1, \dots, k_r)$ is $0$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Bradley–Zhao qMZVs. -/
public theorem coeff_zero_bzQMZV_cons (k : ℕ) (ks : List ℕ) :
    coeff 0 (bzQMZV (k :: ks)) = 0 :=
  coeff_zero_qMZV_cons _ _ _

/-- **Block index of a list of pairs.** The block index of a list
$[(a_1, b_1), \dots, (a_r, b_r)]$ of pairs of natural numbers is the index
$(a_1 + 1, \{1\}^{b_1 - 1}, \dots, a_r + 1, \{1\}^{b_r - 1})$, where $\{1\}^n$ stands for $n$
consecutive entries equal to $1$ and $b_j - 1$ is truncated at $0$.

When all $a_j, b_j \ge 1$ this is an admissible index; it corresponds to the word
$x^{a_1} y^{b_1} \cdots x^{a_r} y^{b_r}$ of the space $\mathfrak{h}^0$ of admissible words in
the letters $x, y$, and the duality $\tau$, the anti-automorphism of
$\mathbb{Q}\langle x, y \rangle$ exchanging $x$ and $y$, maps this word to the word of the block
index of $[(b_r, a_r), \dots, (b_1, a_1)]$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 6 and Theorem 7 (BZ duality), index notation. -/
public def bzBlockIndex (ab : List (ℕ × ℕ)) : List ℕ :=
  (ab.map fun p => (p.1 + 1) :: List.replicate (p.2 - 1) 1).flatten

/-- **Block index of a prepended pair.** For natural numbers $a, b$ and a list $L$ of pairs of
natural numbers, the block index of the list obtained by prepending $(a, b)$ to $L$ consists of
the entry $a + 1$, followed by $b - 1$ entries equal to $1$ (none when $b = 0$), followed by the
block index of $L$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 7, index notation. -/
public theorem bzBlockIndex_cons (a b : ℕ) (ab : List (ℕ × ℕ)) :
    bzBlockIndex ((a, b) :: ab) = (a + 1) :: (List.replicate (b - 1) 1 ++ bzBlockIndex ab) :=
  rfl

/-- **Spanning set of Schlesinger–Zudilin qMZVs.** Let $\mathcal{Z}_q$ be the space
$\mathcal{Z}_{q,d}$ of general qMZVs for $d = 0$. Then $\mathcal{Z}_q$ is the $\mathbb{Q}$-span of
the Schlesinger–Zudilin qMZVs $\zeta_q^{\mathrm{SZ}}(k_1, \dots, k_r)$ over all indices of natural
numbers with $k_1 \ge 1$ when $r \ge 1$ (including the empty index, with
$\zeta_q^{\mathrm{SZ}}(\varnothing) = 1$). Moreover, $\mathcal{Z}_q$ is closed under the operator
$q \frac{d}{dq}$: for every $f \in \mathcal{Z}_q$, the series $q f'$ lies in $\mathcal{Z}_q$, where
$f'$ is the formal derivative of $f$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Proposition 3 (`integers-2024-A6-prop-3`). -/
public theorem_wanted qMZVSpace_zero_eq_span_szQMZV :
    qMZVSpace 0 = Submodule.span ℚ {f | ∃ k : List ℕ,
        (∀ k₁ ∈ k.head?, 1 ≤ k₁) ∧ f = szQMZV k} ∧
      ∀ f ∈ qMZVSpace 0, X * derivative f ∈ qMZVSpace 0

/-- **Spanning set of Bradley–Zhao qMZVs.** Let $\mathcal{Z}_{q,1}$ be the space
$\mathcal{Z}_{q,d}$ of general qMZVs for $d = 1$. Then $\mathcal{Z}_{q,1}$ is the
$\mathbb{Q}$-span of the Bradley–Zhao qMZVs $\zeta_q^{\mathrm{BZ}}(k_1, \dots, k_r)$ over all
admissible indices, that is, all indices of natural numbers with $k_i \ge 1$ for every $i$ and
$k_1 \ge 2$ when $r \ge 1$ (including the empty index, with
$\zeta_q^{\mathrm{BZ}}(\varnothing) = 1$).

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Proposition 4 (`integers-2024-A6-prop-4`). -/
public theorem_wanted qMZVSpace_one_eq_span_bzQMZV :
    qMZVSpace 1 = Submodule.span ℚ {f | ∃ k : List ℕ,
        (∀ kᵢ ∈ k, 1 ≤ kᵢ) ∧ (∀ k₁ ∈ k.head?, 2 ≤ k₁) ∧ f = bzQMZV k}

/-- **Spanning sets of Ohno–Okuda–Zudilin qMZVs.** Let $\mathcal{Z}_{q,1}$ and $\mathcal{Z}_q$ be
the spaces $\mathcal{Z}_{q,d}$ of general qMZVs for $d = 1$ and $d = 0$. Then (i)
$\mathcal{Z}_{q,1}$ is the $\mathbb{Q}$-span of the Ohno–Okuda–Zudilin qMZVs
$\zeta_q^{\mathrm{OOZ}}(k_1, \dots, k_r)$ over all indices of natural numbers with $k_i \ge 1$ for
every $i$ and $k_1 \ge 2$ when $r \ge 1$; and (ii) $\mathcal{Z}_q$ is the $\mathbb{Q}$-span of the
$\zeta_q^{\mathrm{OOZ}}(k_1, \dots, k_r)$ over all indices of natural numbers with $k_1 \ge 1$
when $r \ge 1$. Both spanning sets contain the empty index, with
$\zeta_q^{\mathrm{OOZ}}(\varnothing) = 1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Proposition 10 (`integers-2024-A6-prop-10`). -/
public theorem_wanted qMZVSpace_eq_span_oozQMZV :
    qMZVSpace 1 = Submodule.span ℚ {f | ∃ k : List ℕ,
        (∀ kᵢ ∈ k, 1 ≤ kᵢ) ∧ (∀ k₁ ∈ k.head?, 2 ≤ k₁) ∧ f = oozQMZV k} ∧
      qMZVSpace 0 = Submodule.span ℚ {f | ∃ k : List ℕ,
        (∀ k₁ ∈ k.head?, 1 ≤ k₁) ∧ f = oozQMZV k}

/-- **Bradley–Zhao duality for q-multiple zeta values.** For every $r \ge 0$ and all natural
numbers $a_1, b_1, \dots, a_r, b_r \ge 1$, the Bradley–Zhao q-multiple zeta values satisfy

$$\zeta_q^{BZ}(a_1 + 1, \{1\}^{b_1 - 1}, \dots, a_r + 1, \{1\}^{b_r - 1}) =
\zeta_q^{BZ}(b_r + 1, \{1\}^{a_r - 1}, \dots, b_1 + 1, \{1\}^{a_1 - 1}),$$

where $\{1\}^n$ stands for $n$ consecutive entries equal to $1$.

In terms of words this is $\zeta_q^{BZ} \circ \tau = \zeta_q^{BZ}$ on the space $\mathfrak{h}^0$ of
admissible words, where $\tau$ is the anti-automorphism of $\mathbb{Q}\langle x, y \rangle$
exchanging $x$ and $y$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 7 (BZ duality, Bradley; Seki–Yamamoto)
(`integers-2024-A6-thm-7`). -/
public theorem_wanted bzQMZV_bzBlockIndex_dual (ab : List (ℕ × ℕ))
    (hab : ∀ p ∈ ab, 1 ≤ p.1 ∧ 1 ≤ p.2) :
    bzQMZV (bzBlockIndex ab) = bzQMZV (bzBlockIndex (ab.reverse.map Prod.swap))

/-- **q-Ohno relations for Bradley–Zhao qMZVs.** Let $(a_1, b_1), \dots, (a_r, b_r)$ be pairs of
positive integers, write $\{1\}^{n}$ for $n$ repetitions of $1$, let
$\mathbf{k} = (a_1 + 1, \{1\}^{b_1 - 1}, \dots, a_r + 1, \{1\}^{b_r - 1})$ be the admissible
index they determine, of depth $\ell$, and let
$\mathbf{k}^\vee = (b_r + 1, \{1\}^{a_r - 1}, \dots, b_1 + 1, \{1\}^{a_1 - 1})$ be its dual, of
depth $\ell^\vee$. Then for every natural number $c$,
$\sum_{\mathbf{c}} \zeta_q^{\mathrm{BZ}}(\mathbf{k} + \mathbf{c}) =
\sum_{\mathbf{c}'} \zeta_q^{\mathrm{BZ}}(\mathbf{k}^\vee + \mathbf{c}')$, where $\mathbf{c}$ runs
over the tuples in $\mathbb{N}^{\ell}$ and $\mathbf{c}'$ over the tuples in $\mathbb{N}^{\ell^\vee}$
whose entries sum to $c$, and indices are added componentwise.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 8 (q-Ohno relations, Okuda–Takeyama)
(`integers-2024-A6-thm-8`). -/
public theorem_wanted sum_bzQMZV_add_eq_sum_bzQMZV_dual_add (ab : List (ℕ × ℕ))
    (hab : ∀ p ∈ ab, 1 ≤ p.1 ∧ 1 ≤ p.2) (c : ℕ) :
    ∑ cs ∈ Finset.Nat.antidiagonalTuple (bzBlockIndex ab).length c,
        bzQMZV (List.zipWith (· + ·) (bzBlockIndex ab) (List.ofFn cs)) =
      ∑ cs ∈ Finset.Nat.antidiagonalTuple
          (bzBlockIndex (ab.reverse.map Prod.swap)).length c,
        bzQMZV (List.zipWith (· + ·) (bzBlockIndex (ab.reverse.map Prod.swap)) (List.ofFn cs))

/-- **Partitions in Stanley coordinates.** For natural numbers $r$ and $N$, $\mathcal{P}_r(N)$ is
the finite set of partitions of $N$ of length $r$ in Stanley coordinates: the pairs of tuples
$((m_1, \dots, m_r), (n_1, \dots, n_r))$ of positive integers with $m_1 > m_2 > \dots > m_r$ and
$m_1 n_1 + \dots + m_r n_r = N$.

All coordinates of such a pair are then at most $N$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Stanley coordinates and of `𝒫_r(N)` (Section 4). -/
public def stanleyPartitions (r N : ℕ) : Finset ((Fin r → ℕ) × (Fin r → ℕ)) :=
  ((Fintype.piFinset fun _ : Fin r => Finset.Icc 1 N) ×ˢ
      (Fintype.piFinset fun _ : Fin r => Finset.Icc 1 N)).filter
    fun p => (∀ i j : Fin r, i < j → p.1 j < p.1 i) ∧ ∑ j, p.1 j * p.2 j = N

/-- **Membership criterion for partitions in Stanley coordinates.** For natural numbers $r$ and
$N$, a pair $((m_1, \dots, m_r), (n_1, \dots, n_r))$ of $r$-tuples of natural numbers lies in the
set $\mathcal{P}_r(N)$ of partitions of $N$ of length $r$ in Stanley coordinates if and only if
$m_1 > m_2 > \dots > m_r$, every $m_j$ and every $n_j$ is positive, and
$m_1 n_1 + \dots + m_r n_r = N$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of `𝒫_r(N)` (Section 4). -/
public theorem mem_stanleyPartitions {r N : ℕ} {p : (Fin r → ℕ) × (Fin r → ℕ)} :
    p ∈ stanleyPartitions r N ↔
      (∀ i j : Fin r, i < j → p.1 j < p.1 i) ∧ (∀ j, 0 < p.1 j) ∧ (∀ j, 0 < p.2 j) ∧
        ∑ j, p.1 j * p.2 j = N := by
  constructor
  · intro h
    simp only [stanleyPartitions, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset,
      Finset.mem_Icc] at h
    exact ⟨h.2.1, fun j => (h.1.1 j).1, fun j => (h.1.2 j).1, h.2.2⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have hle : ∀ j, p.1 j * p.2 j ≤ N := fun j =>
      h4 ▸ Finset.single_le_sum (fun i _ => Nat.zero_le (p.1 i * p.2 i)) (Finset.mem_univ j)
    simp only [stanleyPartitions, Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset,
      Finset.mem_Icc]
    exact ⟨⟨fun j => ⟨h2 j, (Nat.le_mul_of_pos_right _ (h3 j)).trans (hle j)⟩,
      fun j => ⟨h3 j, (Nat.le_mul_of_pos_left _ (h2 j)).trans (hle j)⟩⟩, h1, h4⟩

/-- **Transposed partition in Stanley coordinates.** For tuples $\mathbf{m} = (m_1, \dots, m_r)$
and $\mathbf{n} = (n_1, \dots, n_r)$ of natural numbers, the transpose
$\rho(\mathbf{m}, \mathbf{n})$ is the pair of tuples
$((n_1 + \dots + n_r, \dots, n_1 + n_2, n_1), (m_r, m_{r-1} - m_r, \dots, m_1 - m_2))$: for
$1 \le j \le r$, the $j$-th entry of the first tuple is $n_1 + \dots + n_{r+1-j}$ and the $j$-th
entry of the second tuple is $m_{r+1-j} - m_{r+2-j}$, where $m_{r+1} := 0$ and subtraction of
natural numbers is truncated at $0$.

On a partition with $m_1 > \dots > m_r$ this reflects its Young diagram in the main diagonal.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Section 4, transposed partition in Stanley coordinates. -/
public def stanleyTranspose {r : ℕ} (p : (Fin r → ℕ) × (Fin r → ℕ)) :
    (Fin r → ℕ) × (Fin r → ℕ) :=
  (fun j => ∑ i : Fin r with i.val + j.val < r, p.2 i,
    fun j => p.1 (Fin.rev j) -
      (if h : (Fin.rev j).val + 1 < r then p.1 ⟨(Fin.rev j).val + 1, h⟩ else 0))

/-- **Transpose of a one-part partition.** For all natural numbers $m$ and $n$, the transpose
$\rho$ in Stanley coordinates sends the pair of one-entry tuples $((m), (n))$ to $((n), (m))$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Section 4, transposed partition in Stanley coordinates. -/
public theorem stanleyTranspose_fin_one (m n : Fin 1 → ℕ) :
    stanleyTranspose (m, n) = (n, m) := by
  ext j <;> fin_cases j <;> simp [stanleyTranspose]

/-- **Sums over partitions are invariant under transposition.** For all natural numbers $r$ and
$N$ and every function $a$ from pairs of $r$-tuples of natural numbers to $\mathbb{Q}$,
$\sum_{p \in \mathcal{P}_r(N)} a(p) = \sum_{p \in \mathcal{P}_r(N)} a(\rho(p))$, where
$\mathcal{P}_r(N)$ is the set of partitions of $N$ of length $r$ in Stanley coordinates and $\rho$
is the transpose map.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Lemma 1 (`integers-2024-A6-lem-1`). -/
public theorem_wanted sum_stanleyPartitions_comp_stanleyTranspose (r N : ℕ)
    (a : (Fin r → ℕ) × (Fin r → ℕ) → ℚ) :
    ∑ p ∈ stanleyPartitions r N, a p = ∑ p ∈ stanleyPartitions r N, a (stanleyTranspose p)

/-- **Coefficients of qMZVs as polynomial functions on partitions.** Let $r \ge 1$ and let
$(k_1, Q_1), \dots, (k_r, Q_r)$ be pairs of a natural number $k_j$ and a polynomial
$Q_j \in \mathbb{Q}[X]$ with $\deg Q_j \le k_j$ for every $j$ and $Q_1(0) = 0$. For $s, N \ge 0$
let $\mathcal{P}_s(N)$ be the set of pairs $(\mathbf{m}, \mathbf{n})$ of tuples
$\mathbf{m} = (m_1, \dots, m_s)$ and $\mathbf{n} = (n_1, \dots, n_s)$ of positive integers with
$m_1 > \cdots > m_s$ and $m_1 n_1 + \cdots + m_s n_s = N$ (the partitions of $N$ with $s$
distinct parts $m_i$, of multiplicities $n_i$). Then there are polynomials
$f_s \in \mathbb{Q}[X_1, \dots, X_s, Y_1, \dots, Y_s]$, one for each $s \ge 0$, such that for
every $N \ge 0$ the coefficient of $q^N$ in the general qMZV
$\zeta_q(k_1, \dots, k_r; Q_1, \dots, Q_r)$ equals

$$\sum_{s=1}^{r} \sum_{(\mathbf{m}, \mathbf{n}) \in \mathcal{P}_s(N)} f_s(\mathbf{m}, \mathbf{n}),$$

where $f_s(\mathbf{m}, \mathbf{n})$ is the value of $f_s$ at $X_i = m_i$, $Y_i = n_i$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 18 (`integers-2024-A6-thm-18`). -/
public theorem_wanted exists_mvPolynomial_coeff_qMZV_eq_sum_stanleyPartitions
    (kQ : List (ℕ × Polynomial ℚ)) (hr : kQ ≠ [])
    (hdeg : ∀ p ∈ kQ, p.2.natDegree ≤ p.1) (h0 : ∀ p ∈ kQ.head?, p.2.coeff 0 = 0) :
    ∃ f : (s : ℕ) → MvPolynomial (Fin s ⊕ Fin s) ℚ, ∀ N,
      coeff N (qMZV kQ) = ∑ s ∈ Finset.Icc 1 kQ.length, ∑ p ∈ stanleyPartitions s N,
        MvPolynomial.eval (Sum.elim (fun j => (p.1 j : ℚ)) fun j => (p.2 j : ℚ)) (f s)

/-- **Polynomial functions on partitions characterize $\mathcal{Z}_q$.** Let
$\mathcal{Z}_q = \mathcal{Z}_{q,0}$ be the space of general qMZVs, and for natural numbers $r$
and $N$ let $\mathcal{P}_r(N)$ be the set of partitions of $N$ of length $r$ in Stanley
coordinates. A power series $S = \sum_{N \ge 0} a_N q^N \in \mathbb{Q}[[q]]$ lies in
$\mathcal{Z}_q$ if and only if there are $f_0 \in \mathbb{Q}$, polynomials
$f_r \in \mathbb{Q}[X_1, \dots, X_r, Y_1, \dots, Y_r]$ for $r \ge 1$ and a natural number $R$
with $f_r = 0$ for every $r > R$, such that $a_0 = f_0$ and, for every $N \ge 1$,

$$a_N = \sum_{r=1}^{N} \sum_{(\mathbf{m}, \mathbf{n}) \in \mathcal{P}_r(N)}
f_r(\mathbf{m}, \mathbf{n}),$$

where $f_r(\mathbf{m}, \mathbf{n})$ is the value of $f_r$ at $X_i = m_i$, $Y_i = n_i$.

The sum over $r$ stops at $N$, which loses nothing because $\mathcal{P}_r(N)$ is empty for
$r > N$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 19 (`integers-2024-A6-thm-19`). -/
public theorem_wanted mem_qMZVSpace_zero_iff_exists_mvPolynomial (S : ℚ⟦X⟧) :
    S ∈ qMZVSpace 0 ↔ ∃ (f₀ : ℚ) (f : (r : ℕ) → MvPolynomial (Fin r ⊕ Fin r) ℚ) (R : ℕ),
      (∀ r, R < r → f r = 0) ∧
      ∀ N, coeff N S = if N = 0 then f₀ else
        ∑ r ∈ Finset.Icc 1 N, ∑ p ∈ stanleyPartitions r N,
          MvPolynomial.eval (Sum.elim (fun j => (p.1 j : ℚ)) fun j => (p.2 j : ℚ)) (f r)

/-- **Quasi-shuffle product.** Fix an alphabet and a product of letters $a \diamond b$, a formal
sum of letters given as a finite list (possibly empty, possibly with repetitions). The
quasi-shuffle product $u \ast v$ of two words $u$ and $v$ is the formal sum of words, recorded as
a list, defined recursively by $\mathbf{1} \ast w = w \ast \mathbf{1} = w$ for the empty word
$\mathbf{1}$ and by
$a u \ast b v = a (u \ast b v) + b (a u \ast v) + (a \diamond b)(u \ast v)$
for letters $a$, $b$ and words $u$, $v$. Here a letter, or a formal sum of letters, written in
front of a formal sum of words is prepended to each of its words, and the terms are listed in
the order of the formula.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, quasi-shuffle products of Section 2 (the induced quasi-shuffle
products on `M`, `𝔎`, `𝔥¹`). -/
public def quasiShuffle {α : Type*} (d : α → α → List α) : List α → List α → List (List α)
  | [], v => [v]
  | a :: u, [] => [a :: u]
  | a :: u, b :: v =>
      (quasiShuffle d u (b :: v)).map (a :: ·) ++ (quasiShuffle d (a :: u) v).map (b :: ·) ++
        (d a b).flatMap fun c => (quasiShuffle d u v).map (c :: ·)
termination_by u v => u.length + v.length

/-- **The empty word is a left unit for the quasi-shuffle product.** For every alphabet, every
product of letters and every word $w$, the quasi-shuffle product of the empty word $\mathbf{1}$
with $w$ is $\mathbf{1} \ast w = w$, the formal sum consisting of the single word $w$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, quasi-shuffle products of Section 2. -/
public theorem quasiShuffle_nil_left {α : Type*} (d : α → α → List α) (v : List α) :
    quasiShuffle d [] v = [v] := by
  simp [quasiShuffle]

/-- **The stuffle product of two letters.** For natural numbers $a$ and $b$, viewed as one-letter
words, the quasi-shuffle product with letter product $a \diamond b = a + b$ (the stuffle product)
is $a \ast b = ab + ba + (a + b)$: the two-letter words $ab$ and $ba$ and the one-letter word
$(a + b)$, listed in this order.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of the SZ-stuffle product. -/
public theorem quasiShuffle_singleton_singleton (a b : ℕ) :
    quasiShuffle (fun a b => [a + b]) [a] [b] = [[a, b], [b, a], [a + b]] := by
  simp [quasiShuffle]

/-- **SZ-qshuffle product.** The SZ-qshuffle product $\text{ш}$ of two words in the letters $p$
and $y$ is the formal sum of words, counted with multiplicity, defined recursively by
$\mathbf{1} \mathbin{\text{ш}} w = w \mathbin{\text{ш}} \mathbf{1} = w$ for the empty word
$\mathbf{1}$, and, for words $u, v$,
$y u \mathbin{\text{ш}} v = y (u \mathbin{\text{ш}} v)$,
$p u \mathbin{\text{ш}} y v = y (p u \mathbin{\text{ш}} v)$ and
$p u \mathbin{\text{ш}} p v = p (u \mathbin{\text{ш}} p v) + p (p u \mathbin{\text{ш}} v) +
p (u \mathbin{\text{ш}} v)$,
where a letter in front of a formal sum is prepended to each of its words.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of the SZ-qshuffle product. -/
public def szShuffle : List Bool → List Bool → List (List Bool)
  | [], v => [v]
  | false :: u, v => (szShuffle u v).map (false :: ·)
  | true :: u, [] => [true :: u]
  | true :: u, false :: v => (szShuffle (true :: u) v).map (false :: ·)
  | true :: u, true :: v =>
      (szShuffle u (true :: v)).map (true :: ·) ++ (szShuffle (true :: u) v).map (true :: ·) ++
        (szShuffle u v).map (true :: ·)
termination_by u v => u.length + v.length

/-- **SZ-qshuffle of $y$ with itself.** The SZ-qshuffle product of the one-letter word $y$ with
itself is the single word $yy$: $y \mathbin{\text{ш}} y = yy$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of the SZ-qshuffle product. -/
public theorem szShuffle_y_y : szShuffle [false] [false] = [[false, false]] := by
  simp [szShuffle]

/-- **Word of an index.** The word of an index $(k_1, \dots, k_r)$ of natural numbers is the word
$p^{k_1} y \cdots p^{k_r} y$ in the letters $p$ and $y$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, identification of SZ-admissible indices with words of `𝔎¹`. -/
public def szWord (k : List ℕ) : List Bool :=
  (k.map fun n => List.replicate n true ++ [false]).flatten

/-- **Word of the empty index.** The word of the empty index is the empty word.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, identification of SZ-admissible indices with words of `𝔎¹`. -/
public theorem szWord_nil : szWord [] = [] := rfl

/-- **Reading an index off a word in $p$ and $y$.** For $c \in \mathbb{N}$ and a word $w$ in the
letters $p$ and $y$, the index $R_c(w)$, a finite sequence of natural numbers, is defined
recursively by $R_c(\mathbf{1}) = ()$ for the empty word $\mathbf{1}$, $R_c(p w) = R_{c+1}(w)$,
and $R_c(y w) = (c, R_0(w))$, the index with first entry $c$ followed by the entries of
$R_0(w)$. Thus $R_c(p^{k_1} y\, p^{k_2} y \cdots p^{k_r} y\, p^j) = (c + k_1, k_2, \dots, k_r)$
for $r \ge 1$ and $R_c(p^j) = ()$: the entries are the lengths of the blocks of $p$s before
each $y$, with $c$ added to the first, and trailing $p$s are dropped.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, identification of SZ-admissible indices with words of `𝔎¹`. -/
public def szIndexOfWordAux : ℕ → List Bool → List ℕ
  | _, [] => []
  | c, true :: w => szIndexOfWordAux (c + 1) w
  | c, false :: w => c :: szIndexOfWordAux 0 w

/-- **Reading off a leading block of $p$s.** Write $R_c(w)$ for the index read off a word $w$ in
the letters $p$ and $y$ when $c$ letters $p$ have already been read. For all $c, n \in \mathbb{N}$
and every word $w$, $R_c(p^n y w)$ is the index whose first entry is $c + n$ and whose remaining
entries are those of $R_0(w)$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, identification of SZ-admissible indices with words of `𝔎¹`. -/
public theorem szIndexOfWordAux_replicate_append (c n : ℕ) (w : List Bool) :
    szIndexOfWordAux c (List.replicate n true ++ false :: w) = (c + n) :: szIndexOfWordAux 0 w := by
  induction n generalizing c with
  | zero => simp [szIndexOfWordAux]
  | succ n ih =>
    rw [List.replicate_succ, List.cons_append, szIndexOfWordAux, ih]
    congr 1
    omega

/-- **Schlesinger–Zudilin qMZVs of words.** Write $\zeta_q^{SZ}$ for the Schlesinger–Zudilin qMZV
of an index of natural numbers. For a word $w$ in the letters $p$ and $y$ with $r$ letters $y$,
let $k_j$ be the number of letters $p$ between the $(j-1)$-st and the $j$-th letter $y$ of $w$
(for $j = 1$, before the first $y$); letters $p$ after the last $y$ are ignored. The value of
$\zeta_q^{SZ}$ on $w$ is $\zeta_q^{SZ}(k_1, \dots, k_r)$. In particular the word
$p^{k_1} y \cdots p^{k_r} y$ is sent to $\zeta_q^{SZ}(k_1, \dots, k_r)$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of the SZ-qshuffle product (ii). -/
public noncomputable def szQMZVWord (w : List Bool) : ℚ⟦X⟧ :=
  szQMZV (szIndexOfWordAux 0 w)

/-- **SZ-qMZV of the word of a one-entry index.** Write $\zeta_q^{SZ}$ for the Schlesinger–Zudilin
qMZV, extended to words in the letters $p$ and $y$ by sending a word to $\zeta_q^{SZ}$ of the
index read off it: the number of letters $p$ before each letter $y$ since the previous $y$, with
letters $p$ after the last $y$ dropped. For every natural number $k$, the value of
$\zeta_q^{SZ}$ on the word $p^k y$ of the one-entry index $(k)$ is $\zeta_q^{SZ}(k)$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of the SZ-qshuffle product (ii). -/
public theorem szQMZVWord_szWord_singleton (k : ℕ) :
    szQMZVWord (szWord [k]) = szQMZV [k] := by
  simp only [szQMZVWord, szWord, List.map_cons, List.map_nil, List.flatten_cons,
    List.flatten_nil, List.append_nil]
  rw [szIndexOfWordAux_replicate_append]
  simp [szIndexOfWordAux]

/-- **Quasi-shuffle relations for general qMZVs.** Consider words in letters $(k, Q)$ with
$k \in \mathbb{N}$ and $Q \in \mathbb{Q}[X]$, and let $u$ and $v$ be words in which every letter
satisfies $\deg Q \le k$ and the first letter, if any, satisfies $Q(0) = 0$. Let $u \ast v$ be
the quasi-shuffle product of $u$ and $v$ with letter product
$(k_1, Q_1) \diamond (k_2, Q_2) = (k_1 + k_2, Q_1 Q_2)$, a formal sum of words. Then
$\zeta_q(u)\,\zeta_q(v) = \zeta_q(u \ast v)$, where $\zeta_q$ sends a word
$(k_1, Q_1) \cdots (k_r, Q_r)$ to the general qMZV $\zeta_q(k_1, \dots, k_r; Q_1, \dots, Q_r)$
and is extended linearly to formal sums of words.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Proposition 2 (`integers-2024-A6-prop-2`). -/
public theorem_wanted qMZV_mul_eq_sum_quasiShuffle (u v : List (ℕ × Polynomial ℚ))
    (hu : ∀ p ∈ u, p.2.natDegree ≤ p.1) (hu0 : ∀ p ∈ u.head?, p.2.coeff 0 = 0)
    (hv : ∀ p ∈ v, p.2.natDegree ≤ p.1) (hv0 : ∀ p ∈ v.head?, p.2.coeff 0 = 0) :
    qMZV u * qMZV v =
      ((quasiShuffle (fun a b => [(a.1 + b.1, a.2 * b.2)]) u v).map qMZV).sum

/-- **Stuffle product formula for Schlesinger–Zudilin qMZVs.** Write $\zeta_q^{SZ}$ for the
Schlesinger–Zudilin qMZV. Let $v$ and $w$ be finite lists of natural numbers that are
SZ-admissible, that is, each is empty or has first entry at least $1$. Then
$$\zeta_q^{SZ}(v)\,\zeta_q^{SZ}(w) = \sum_{u} \zeta_q^{SZ}(u),$$
where $u$ runs, counted with multiplicity, over the terms of the stuffle product $v \ast w$: the
quasi-shuffle product of $v$ and $w$ as words in the alphabet $\mathbb{N}$ with the product of
letters $a \diamond b = a + b$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 2 (`integers-2024-A6-thm-2`). -/
public theorem_wanted szQMZV_mul_eq_sum_stuffle (v w : List ℕ)
    (hv : ∀ k₁ ∈ v.head?, 1 ≤ k₁) (hw : ∀ k₁ ∈ w.head?, 1 ≤ k₁) :
    szQMZV v * szQMZV w = ((quasiShuffle (fun a b => [a + b]) v w).map szQMZV).sum

/-- **Shuffle product formula for Schlesinger–Zudilin qMZVs (Singer).** Write $\zeta_q^{SZ}$ for
the Schlesinger–Zudilin qMZV. Let $u$ and $v$ be finite lists of natural numbers that are
SZ-admissible, that is, each is empty or has first entry at least $1$, and let $w_u$ and $w_v$
be their words in the letters $p$ and $y$ (the index $(k_1, \dots, k_r)$ has word
$p^{k_1} y \cdots p^{k_r} y$). Then
$$\zeta_q^{SZ}(u)\,\zeta_q^{SZ}(v) = \sum_{w} \zeta_q^{SZ}(w),$$
where $w$ runs, counted with multiplicity, over the terms of the SZ-qshuffle product
$w_u \mathbin{\text{ш}} w_v$, and $\zeta_q^{SZ}$ of a word is $\zeta_q^{SZ}$ of the index read
off it: the number of letters $p$ before each letter $y$ since the previous $y$, with letters $p$
after the last $y$ dropped.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Theorem 3 (Singer) (`integers-2024-A6-thm-3`). -/
public theorem_wanted szQMZV_mul_eq_sum_szShuffle (u v : List ℕ)
    (hu : ∀ k₁ ∈ u.head?, 1 ≤ k₁) (hv : ∀ k₁ ∈ v.head?, 1 ≤ k₁) :
    szQMZV u * szQMZV v = ((szShuffle (szWord u) (szWord v)).map szQMZVWord).sum

/-- **Quasi-shuffle relations for Bradley–Zhao qMZVs.** Identify an index $(k_1, \dots, k_r)$
with the word $z_{k_1} \cdots z_{k_r}$, and let $u$ and $v$ be admissible indices: finite,
possibly empty, sequences of positive integers whose first entry, if any, is at least $2$. Let
$u \ast_{BZ} v$ be the quasi-shuffle product of $u$ and $v$ with letter product
$z_a \diamond z_b = z_{a+b} + z_{a+b-1}$, a formal sum of indices. Then
$\zeta_q^{BZ}(u)\,\zeta_q^{BZ}(v) = \zeta_q^{BZ}(u \ast_{BZ} v)$, where the Bradley–Zhao qMZV
$\zeta_q^{BZ}$ is extended linearly to formal sums of indices.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Proposition 5 (`integers-2024-A6-prop-5`). -/
public theorem_wanted bzQMZV_mul_eq_sum_quasiShuffle (u v : List ℕ)
    (hu : ∀ k ∈ u, 1 ≤ k) (hu₁ : ∀ k₁ ∈ u.head?, 2 ≤ k₁)
    (hv : ∀ k ∈ v, 1 ≤ k) (hv₁ : ∀ k₁ ∈ v.head?, 2 ≤ k₁) :
    bzQMZV u * bzQMZV v =
      ((quasiShuffle (fun a b => [a + b, a + b - 1]) u v).map bzQMZV).sum


/-- **Analytic properties of general qMZVs.** Let $(k_1, Q_1), \dots, (k_r, Q_r)$ be pairs of an
integer $k_j \ge 1$ and a polynomial $Q_j \in \mathbb{Q}[X]$ with $\deg Q_j \le k_j$ for every
$j$ and $Q_1(0) = 0$, and write the general qMZV as
$\zeta_q(k_1, \dots, k_r; Q_1, \dots, Q_r) = \sum_{n \ge 0} c_n q^n$. Then (i) for every complex
$q$ with $|q| < 1$ the series $\sum_{n \ge 0} c_n q^n$ converges absolutely; (ii) the function
$\tau \mapsto \sum_{n \ge 0} c_n e^{2 \pi i n \tau}$ is holomorphic on the upper half-plane
$\{\tau \in \mathbb{C} : \operatorname{Im} \tau > 0\}$; (iii) if $r \ge 1$ and $k_1 \ge 2$, then
$(1 - q)^{k_1 + \cdots + k_r} \sum_{n \ge 0} c_n q^n$ tends to
$\zeta(k_1, \dots, k_r) \prod_{j=1}^{r} Q_j(1)$ as the real number $q$ tends to $1$ from below,
where $\zeta(k_1, \dots, k_r) = \sum_{n_1 > \cdots > n_r > 0} n_1^{-k_1} \cdots n_r^{-k_r}$ is the
multiple zeta value.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 1 (`integers-2024-A6-prop-1`). -/
public theorem_wanted qMZV_summable_differentiableOn_tendsto (kQ : List (ℕ × Polynomial ℚ))
    (hk : ∀ p ∈ kQ, 1 ≤ p.1) (hQ : ∀ p ∈ kQ, p.2.natDegree ≤ p.1)
    (hQ₁ : ∀ p ∈ kQ.head?, p.2.eval 0 = 0) :
    (∀ q : ℂ, ‖q‖ < 1 → Summable fun n : ℕ => ((coeff n (qMZV kQ) : ℚ) : ℂ) * q ^ n) ∧
    DifferentiableOn ℂ
      (fun τ : ℂ => ∑' n : ℕ, ((coeff n (qMZV kQ) : ℚ) : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * τ) ^ n) {τ : ℂ | 0 < τ.im} ∧
    (∀ p ∈ kQ.head?, 2 ≤ p.1 →
      Filter.Tendsto (fun q : ℝ => (1 - q) ^ (kQ.map Prod.fst).sum *
          ∑' n : ℕ, ((coeff n (qMZV kQ) : ℚ) : ℝ) * q ^ n)
        (nhdsWithin 1 (Set.Iio 1))
        (nhds (multipleZetaValue (kQ.map Prod.fst) *
          ((kQ.map fun p => ((p.2.eval 1 : ℚ) : ℝ)).prod))))


/-- **Letters of the Takeyama–Bradley–Zhao model as qMZV data.** The letters of the TBZ model
are the symbol $\bar 1$ and the natural numbers $k \ge 1$. The letter $\bar 1$, with summand
$f(\bar 1, m) = q^m / (1 - q^m)$, is sent to the pair $(1, X)$, and the letter $k$, with
summand $f(k, m) = q^{(k-1)m} / (1 - q^m)^k$, is sent to the pair $(k, X^{k-1})$. Here a pair
$(k, Q)$ of a natural number and a rational polynomial stands for the summand
$Q(q^m) / (1 - q^m)^k$ of a general qMZV. The number $0$, which is not a letter of the
model, is sent to $(0, 1)$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of the Takeyama–Bradley–Zhao model (`f(1̄, m)`, `f(k, m)`). -/
public noncomputable def tbzLetter : Option ℕ → ℕ × Polynomial ℚ
  | none => (1, Polynomial.X)
  | some k => (k, Polynomial.X ^ (k - 1))

/-- **Takeyama–Bradley–Zhao qMZVs.** For an index $(k_1, \dots, k_r)$ whose entries are the symbol
$\bar 1$ or natural numbers, the TBZ-qMZV is the general qMZV of the data obtained by replacing
each entry by its pair in the Takeyama–Bradley–Zhao letter encoding. When every natural-number
entry is at least $1$ and $k_1 \ne 1$, this is
$$\zeta_q^{TBZ}(k_1, \dots, k_r) = \sum_{m_1 > \cdots > m_r > 0} f(k_1, m_1) \cdots f(k_r, m_r),$$
with $f(\bar 1, m) = q^m / (1 - q^m)$ and $f(k, m) = q^{(k-1)m} / (1 - q^m)^k$; the empty index
gives $1$. For $k_1 = 1$, or when some entry is $0$, the value is a junk value.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of the Takeyama–Bradley–Zhao model. -/
public noncomputable def tbzQMZV (k : List (Option ℕ)) : ℚ⟦X⟧ :=
  qMZV (k.map tbzLetter)

/-- **TBZ-qMZV of the empty index.** The Takeyama–Bradley–Zhao qMZV of the empty index is $1$:
$\zeta_q^{\mathrm{TBZ}}(\varnothing) = 1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of the Takeyama–Bradley–Zhao model. -/
public theorem tbzQMZV_nil : tbzQMZV [] = 1 := rfl

/-- **The TBZ model extends the BZ model.** For every index $(k_1, \dots, k_r)$ of natural
numbers, read as a TBZ index without the symbol $\bar 1$, the TBZ-qMZV equals the Bradley–Zhao
qMZV: $\zeta_q^{\mathrm{TBZ}}(k_1, \dots, k_r) = \zeta_q^{\mathrm{BZ}}(k_1, \dots, k_r)$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of the Takeyama–Bradley–Zhao model. -/
public theorem tbzQMZV_map_some (k : List ℕ) : tbzQMZV (k.map some) = bzQMZV k := by
  simp only [tbzQMZV, bzQMZV, List.map_map]
  rfl

/-- **The Takeyama–Bradley–Zhao model spans $\mathcal{Z}_q$.** Let $\overline{\mathbb{N}}$
consist of the positive integers and one further symbol $\bar 1$. The space
$\mathcal{Z}_q = \mathcal{Z}_{q,0}$ equals the $\mathbb{Q}$-linear span of the TBZ-qMZVs
$\zeta_q^{\mathrm{TBZ}}(k_1, \dots, k_r)$ over all $r \ge 0$ and all
$k_1, \dots, k_r \in \overline{\mathbb{N}}$ with $k_1 \ne 1$ when $r \ge 1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Proposition 6 (`integers-2024-A6-prop-6`). -/
public theorem_wanted qMZVSpace_zero_eq_span_tbzQMZV :
    qMZVSpace 0 = Submodule.span ℚ {f | ∃ k : List (Option ℕ),
        (∀ j ∈ k, ∀ kⱼ ∈ j, 1 ≤ kⱼ) ∧ k.head? ≠ some (some 1) ∧ f = tbzQMZV k}

/-- **The spaces $\mathcal{Z}^\circ_{q,d}$.** For a natural number $d$, the space
$\mathcal{Z}^\circ_{q,d}$ is the $\mathbb{Q}$-linear span, in the formal power series ring
$\mathbb{Q}[[q]]$, of the general qMZVs $\zeta_q(k_1, \dots, k_r; Q_1, \dots, Q_r)$ over all
$r \ge 0$, natural numbers $k_1, \dots, k_r$ and polynomials $Q_1, \dots, Q_r \in \mathbb{Q}[X]$
such that for every $j$ we have $k_j \ge 1$, $\deg Q_j + d \le k_j$ and $Q_j(0) = 0$. Here the
zero polynomial has degree $0$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of `𝒵_{q,d}` and `𝒵°_{q,d}` (after Bachmann–Kühn). -/
public noncomputable def qMZVSpaceCirc (d : ℕ) : Submodule ℚ ℚ⟦X⟧ :=
  Submodule.span ℚ {f | ∃ kQ : List (ℕ × Polynomial ℚ),
    (∀ p ∈ kQ, 1 ≤ p.1 ∧ p.2.natDegree + d ≤ p.1 ∧ p.2.coeff 0 = 0) ∧ f = qMZV kQ}

/-- **The constant $1$ lies in $\mathcal{Z}^\circ_{q,d}$.** For every natural number $d$, the
constant power series $1$ (the qMZV of the empty index) lies in
the space $\mathcal{Z}^\circ_{q,d}$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of `𝒵°_{q,d}`. -/
public theorem one_mem_qMZVSpaceCirc (d : ℕ) : (1 : ℚ⟦X⟧) ∈ qMZVSpaceCirc d :=
  Submodule.subset_span ⟨[], by simp, rfl⟩

/-- **$\mathcal{Z}^\circ_{q,d}$ is contained in $\mathcal{Z}_{q,d}$.** For every natural number
$d$, the space $\mathcal{Z}^\circ_{q,d}$ is a subspace of $\mathcal{Z}_{q,d}$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of `𝒵°_{q,d}` (a subspace of `𝒵_{q,d}`). -/
public theorem qMZVSpaceCirc_le_qMZVSpace (d : ℕ) : qMZVSpaceCirc d ≤ qMZVSpace d := by
  refine Submodule.span_mono ?_
  rintro f ⟨kQ, h, rfl⟩
  exact ⟨kQ, fun p hp => (h p hp).2.1,
    fun p hp => (h p (List.mem_of_mem_head? hp)).2.2, rfl⟩

/-- **Okounkov polynomials.** For $k \in \mathbb{N}$, the Okounkov polynomial
$p_k \in \mathbb{Q}[X]$ is $p_k(X) = X^{k/2}$ if $k$ is even and $p_k(X) = X^{(k-1)/2}(1 + X)$ if
$k$ is odd.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Okounkov qMZVs. -/
public noncomputable def okounkovPoly (k : ℕ) : Polynomial ℚ :=
  if k % 2 = 0 then Polynomial.X ^ (k / 2) else Polynomial.X ^ ((k - 1) / 2) * (1 + Polynomial.X)

/-- **The Okounkov polynomials $p_2$ and $p_3$.** The Okounkov polynomials of index $2$ and $3$
are $p_2(X) = X$ and $p_3(X) = X(1 + X)$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Okounkov qMZVs. -/
public theorem okounkovPoly_two_three :
    okounkovPoly 2 = Polynomial.X ∧ okounkovPoly 3 = Polynomial.X * (1 + Polynomial.X) := by
  simp [okounkovPoly]

/-- **Okounkov $q$-multiple zeta values.** For a natural number $k$ let $p_k$ be Okounkov's
polynomial: $p_k(X) = X^{k/2}$ if $k$ is even and $p_k(X) = X^{(k-1)/2}(1 + X)$ if $k$ is odd.
For an index $(k_1, \dots, k_r)$ of natural numbers, the Okounkov qMZV is the general qMZV
$\zeta_q^{\mathrm{Oko}}(k_1, \dots, k_r) = \zeta_q(k_1, \dots, k_r; p_{k_1}, \dots, p_{k_r})$,
a formal power series in $q$ over $\mathbb{Q}$.

The paper uses it only for indices with every $k_i \ge 2$; for other indices the value is a
placeholder.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Okounkov qMZVs. -/
public noncomputable def okounkovQMZV (k : List ℕ) : ℚ⟦X⟧ :=
  qMZV (k.map fun k => (k, okounkovPoly k))

/-- **Okounkov qMZV of the empty index.** The Okounkov $q$-multiple zeta value of the empty
index is $1$: $\zeta_q^{\mathrm{Oko}}(\varnothing) = 1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Definition of Okounkov qMZVs. -/
public theorem okounkovQMZV_nil : okounkovQMZV [] = 1 := rfl

/-- **Okounkov qMZVs span $\mathcal{Z}^\circ_{q,1}$.** The space $\mathcal{Z}^\circ_{q,1}$ equals
the $\mathbb{Q}$-linear span of the Okounkov qMZVs $\zeta_q^{\mathrm{Oko}}(k_1, \dots, k_r)$ over
all indices of length $r \ge 0$ with every $k_i \ge 2$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024),
Article A6, Proposition 13 (after Bachmann–Kühn) (`integers-2024-A6-prop-13`). -/
public theorem_wanted qMZVSpaceCirc_one_eq_span_okounkovQMZV :
    qMZVSpaceCirc 1 = Submodule.span ℚ {f | ∃ k : List ℕ,
        (∀ kᵢ ∈ k, 2 ≤ kᵢ) ∧ f = okounkovQMZV k}

/-- **Eulerian q-series.** For natural numbers $k$ and $m \ge 1$, the Eulerian $q$-series is
$$
\sum_{n \ge 1} \frac{n^{k-1}}{(k-1)!} \, q^{mn},
$$
the inner sum of a bi-bracket; here $k - 1$ is read as $0$ when $k = 0$. For $m = 0$ the series
is defined to be $0$.

For $k, m \ge 1$ it equals $P_k(q^m)/(1 - q^m)^k$, where $P_k$ is the $k$-th Eulerian polynomial.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition-Proposition of bi-brackets (Eulerian polynomials). -/
public noncomputable def eulerianQSeries (k m : ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun e =>
    if 0 < e ∧ m ∣ e then ((e / m : ℕ) : ℚ) ^ (k - 1) / (k - 1).factorial else 0

/-- **Coefficients of the Eulerian q-series.** For natural numbers $k$, $m$ and $n$ with $m > 0$
and $n > 0$, the coefficient of $q^{mn}$ in the Eulerian $q$-series
$\sum_{\ell \ge 1} \frac{\ell^{k-1}}{(k-1)!} q^{m\ell}$ is $\frac{n^{k-1}}{(k-1)!}$, where $k - 1$
is read as $0$ when $k = 0$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition-Proposition of bi-brackets. -/
public theorem coeff_mul_eulerianQSeries (k m n : ℕ) (hm : 0 < m) (hn : 0 < n) :
    coeff (m * n) (eulerianQSeries k m) = (n : ℚ) ^ (k - 1) / (k - 1).factorial := by
  simp [eulerianQSeries, Nat.mul_pos hm hn, Nat.mul_div_cancel_left n hm]

/-- **Partial sums of bi-brackets.** For pairs $(k_1, d_1), \dots, (k_r, d_r)$ of natural numbers
and a bound $M \in \mathbb{N}$, the partial bi-bracket is the $q$-series
$$
\sum_{M > m_1 > \dots > m_r > 0} \, \prod_{j=1}^{r} \frac{m_j^{d_j}}{d_j!} E_{k_j}(m_j),
$$
where $E_k(m) = \sum_{n \ge 1} \frac{n^{k-1}}{(k-1)!} q^{mn}$ is the Eulerian $q$-series (with
$k - 1$ read as $0$ when $k = 0$). For $r = 0$ it is $1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition-Proposition of bi-brackets (defining sum truncated at `m₁ < M`). -/
public noncomputable def biBracketPartial : List (ℕ × ℕ) → ℕ → ℚ⟦X⟧
  | [], _ => 1
  | (k, d) :: kd, M => ∑ m ∈ Finset.Ioo 0 M,
      ((m : ℚ) ^ d / d.factorial) • (eulerianQSeries k m * biBracketPartial kd m)

/-- **Bi-brackets.** For integers $k_1, \dots, k_r \ge 1$ and $d_1, \dots, d_r \ge 0$, the
bi-bracket is the $q$-series
$$
g(k_1, \dots, k_r; d_1, \dots, d_r) =
\sum_{m_1 > \dots > m_r > 0} \, \sum_{n_1, \dots, n_r > 0} \, \prod_{j=1}^{r}
\frac{m_j^{d_j}}{d_j!} \frac{n_j^{k_j - 1}}{(k_j - 1)!} \, q^{m_1 n_1 + \dots + m_r n_r},
$$
and $g(\varnothing; \varnothing) = 1$. The summands with $m_1 > N$ have $q$-adic order greater
than $N$, so the coefficient of $q^N$ is that of the finite partial sum over $m_1 \le N$; this
is how the series is defined.

The same formula, with $k_j - 1$ read as $0$, defines a value when some $k_j = 0$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition-Proposition of bi-brackets (after Bachmann). -/
public noncomputable def biBracket (kd : List (ℕ × ℕ)) : ℚ⟦X⟧ :=
  PowerSeries.mk fun N => coeff N (biBracketPartial kd (N + 1))

/-- **Empty bi-bracket.** The bi-bracket of the empty index is $1$:
$g(\varnothing; \varnothing) = 1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition-Proposition of bi-brackets. -/
public theorem biBracket_nil : biBracket [] = 1 := by
  ext N
  simp [biBracket, biBracketPartial]

/-- **Generating series of bi-brackets.** For $r \in \mathbb{N}$, the generating series of the
bi-brackets of depth $r$ is the formal power series in the variables $X_1, \dots, X_r$,
$Y_1, \dots, Y_r$ with coefficients in $\mathbb{Q}[[q]]$
$$
g(X_1, \dots, X_r; Y_1, \dots, Y_r) =
\sum_{k_1, \dots, k_r \ge 1} \, \sum_{d_1, \dots, d_r \ge 1}
g(k_1, \dots, k_r; d_1 - 1, \dots, d_r - 1) \prod_{j=1}^{r} X_j^{k_j - 1} Y_j^{d_j - 1},
$$
where $g(k_1, \dots, k_r; d_1, \dots, d_r)$ is the bi-bracket. Equivalently, the coefficient of
$\prod_{j=1}^{r} X_j^{a_j} Y_j^{b_j}$ is $g(a_1 + 1, \dots, a_r + 1; b_1, \dots, b_r)$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 11 (definition of the generating series). -/
public noncomputable def biBracketGen (r : ℕ) : MvPowerSeries (Fin r ⊕ Fin r) ℚ⟦X⟧ :=
  fun e => biBracket (List.ofFn fun j => (e (Sum.inl j) + 1, e (Sum.inr j)))

/-- **Coefficients of the bi-bracket generating series.** For $r \in \mathbb{N}$ and exponents
$a_1, \dots, a_r, b_1, \dots, b_r \ge 0$, the coefficient of $\prod_{j=1}^{r} X_j^{a_j} Y_j^{b_j}$
in the generating series $g(X_1, \dots, X_r; Y_1, \dots, Y_r)$ of bi-brackets of depth $r$ is
the bi-bracket $g(a_1 + 1, \dots, a_r + 1; b_1, \dots, b_r)$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 11. -/
public theorem coeff_biBracketGen (r : ℕ) (e : Fin r ⊕ Fin r →₀ ℕ) :
    MvPowerSeries.coeff e (biBracketGen r) =
      biBracket (List.ofFn fun j => (e (Sum.inl j) + 1, e (Sum.inr j))) :=
  rfl

/-- **Generating series of Schlesinger–Zudilin qMZVs.** For a natural number $r$, the
generating series of SZ-qMZVs of depth $r$ is the formal power series in the $2r$ variables
$X_1, \dots, X_r, Y_1, \dots, Y_r$ with coefficients in $\mathbb{Q}[[q]]$
$$
s(X_1, \dots, X_r; Y_1, \dots, Y_r) = \sum_{k_1, \dots, k_r \ge 1} \sum_{d_1, \dots, d_r \ge 0}
\zeta_q^{\mathrm{SZ}}(k_1, \{0\}^{d_1}, \dots, k_r, \{0\}^{d_r})
\prod_{j=1}^{r} X_j^{k_j - 1} Y_j^{d_j},
$$
where $\{0\}^{d}$ stands for $d$ consecutive zeros.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 4 (definition of the generating series). -/
public noncomputable def szGen (r : ℕ) : MvPowerSeries (Fin r ⊕ Fin r) ℚ⟦X⟧ :=
  fun e => szQMZV (szBlockIndex (List.ofFn fun j => (e (Sum.inl j) + 1, e (Sum.inr j) + 1)))

/-- **Coefficients of the SZ generating series.** For $r \in \mathbb{N}$ and exponents
$a_1, \dots, a_r, b_1, \dots, b_r \ge 0$, the coefficient of $\prod_{j=1}^{r} X_j^{a_j} Y_j^{b_j}$
in the generating series $s(X_1, \dots, X_r; Y_1, \dots, Y_r)$ of Schlesinger–Zudilin
$q$-multiple zeta values of depth $r$ is
$\zeta_q^{\mathrm{SZ}}(a_1 + 1, \{0\}^{b_1}, \dots, a_r + 1, \{0\}^{b_r})$, where $\{0\}^b$
stands for $b$ consecutive zeros.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 4. -/
public theorem coeff_szGen (r : ℕ) (e : Fin r ⊕ Fin r →₀ ℕ) :
    MvPowerSeries.coeff e (szGen r) =
      szQMZV (szBlockIndex (List.ofFn fun j => (e (Sum.inl j) + 1, e (Sum.inr j) + 1))) :=
  rfl

/-- **The logarithm series $\ln(1 + T)$.** The formal power series $\ln(1 + T)$ over
$\mathbb{Q}$ is $\sum_{n \ge 1} (-1)^{n+1} T^n / n$; its constant term is $0$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 13 (ii) (the substitution `Xⱼ ↦ ln(Xⱼ + 1)`). -/
public noncomputable def logOneAddSeries : ℚ⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 0 else (-1) ^ (n + 1) / n

/-- **Low-order coefficients of the logarithm series.** The power series
$\ln(1 + T) = \sum_{n \ge 1} (-1)^{n+1} T^n / n$ over $\mathbb{Q}$ has constant coefficient $0$
and coefficient $1$ at $T$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 13 (ii). -/
public theorem coeff_logOneAddSeries_zero_one :
    coeff 0 logOneAddSeries = 0 ∧ coeff 1 logOneAddSeries = 1 := by
  simp [logOneAddSeries]

/-- **Bi-bracket generating series as a sum of exponentials.** Let $r$ and $N$ be natural numbers
and let $g(X_1, \dots, X_r; Y_1, \dots, Y_r)$ be the generating series of bi-brackets of depth $r$,
a power series in the $2r$ variables over $\mathbb{Q}[[q]]$. The power series over $\mathbb{Q}$
obtained by taking the coefficient of $q^N$ in every coefficient of $g$ equals the finite sum
$$\sum \prod_{j=1}^r e^{m_j Y_j} e^{n_j X_j}$$
over all integers $m_1 > m_2 > \dots > m_r > 0$ and $n_1, \dots, n_r \ge 1$ with
$m_1 n_1 + \dots + m_r n_r = N$, where $e^Z$ is the exponential series evaluated at $Z$.

This is the $q^N$-part of the identity
$g(X; Y) = \sum \prod_j e^{m_j Y_j} e^{n_j X_j} q^{m_j n_j}$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 11 (after Bachmann) (`integers-2024-A6-thm-11`). -/
public theorem_wanted coeff_biBracketGen_eq_sum_exp (r N : ℕ) :
    (fun e => coeff N (MvPowerSeries.coeff e (biBracketGen r)) :
        MvPowerSeries (Fin r ⊕ Fin r) ℚ) =
      ∑ mn ∈ (Fintype.piFinset fun _ : Fin r => Finset.range (N + 1)) ×ˢ
          (Fintype.piFinset fun _ : Fin r => Finset.range (N + 1)) with
          StrictAnti mn.1 ∧ (∀ j, 0 < mn.1 j) ∧ (∀ j, 0 < mn.2 j) ∧
            ∑ j, mn.1 j * mn.2 j = N,
        ∏ j : Fin r,
          PowerSeries.subst ((mn.1 j : ℚ) • MvPowerSeries.X (Sum.inr j)) (exp ℚ) *
            PowerSeries.subst ((mn.2 j : ℚ) • MvPowerSeries.X (Sum.inl j)) (exp ℚ)

/-- **Partition relation for bi-brackets.** For every natural number $r$, the generating series
$g(X_1, \dots, X_r; Y_1, \dots, Y_r)$ of bi-brackets of depth $r$ satisfies
$$g(X_1, \dots, X_r; Y_1, \dots, Y_r) = g(Y_1 + \dots + Y_r, \dots, Y_1 + Y_2, Y_1;
X_r, X_{r-1} - X_r, \dots, X_1 - X_2),$$
where the right side substitutes linear forms into $g$ simultaneously: for $1 \le i \le r$, the
variable $X_i$ is replaced by $Y_1 + \dots + Y_{r+1-i}$ and the variable $Y_i$ by
$X_{r+1-i} - X_{r+2-i}$, with $X_{r+1} := 0$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 12 (partition relation, after Bachmann) (`integers-2024-A6-thm-12`). -/
public theorem_wanted biBracketGen_partition_relation (r : ℕ) :
    biBracketGen r = MvPowerSeries.subst
      (Sum.elim
        (fun i : Fin r => ∑ j ∈ Finset.univ.filter (fun j : Fin r => j.val < r - i.val),
          MvPowerSeries.X (Sum.inr j))
        (fun i : Fin r => MvPowerSeries.X (Sum.inl i.rev) -
          ∑ j ∈ Finset.univ.filter (fun j : Fin r => j.val = r - i.val),
            MvPowerSeries.X (Sum.inl j)))
      (biBracketGen r)

/-- **Translation between bi-brackets and the Schlesinger–Zudilin model.** Let $r$ be a natural
number, let $g(X_1, \dots, X_r; Y_1, \dots, Y_r)$ be the generating series of bi-brackets of depth
$r$ and $s(X_1, \dots, X_r; Y_1, \dots, Y_r)$ the generating series of Schlesinger–Zudilin qMZVs of
depth $r$, both power series in the $2r$ variables over $\mathbb{Q}[[q]]$. For a power series $Z$
without constant term, write $e^Z$ and $\ln(1 + Z)$ for the substitution of $Z$ into the
exponential series and into $\ln(1 + T) = \sum_{n \ge 1} (-1)^{n+1} T^n / n$, and put
$S_j = Y_1 + \dots + Y_j$. Then:

(i) $\prod_{j=1}^r e^{X_j} e^{S_j} \cdot s(e^{X_1} - 1, \dots, e^{X_r} - 1; e^{S_1} - 1, \dots,
e^{S_r} - 1) = g(X_1, \dots, X_r; Y_1, \dots, Y_r)$;

(ii) $\prod_{j=1}^r (1 + X_j)(1 + Y_j) \cdot s(X_1, \dots, X_r; Y_1, \dots, Y_r)$ equals
$g(\ln(1 + X_1), \dots, \ln(1 + X_r); \ln(1 + Y_1), \ln(1 + Y_2) - \ln(1 + Y_1), \dots,
\ln(1 + Y_r) - \ln(1 + Y_{r-1}))$.

Part (ii) is stated with the unit $\prod_j (1 + X_j)(1 + Y_j)$ multiplied out instead of inverted.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 13 (translation bi-brackets/SZ model) (`integers-2024-A6-thm-13`). -/
public theorem_wanted biBracketGen_eq_szGen_subst (r : ℕ) :
    (∏ j : Fin r,
        PowerSeries.subst (MvPowerSeries.X (Sum.inl j) :
            MvPowerSeries (Fin r ⊕ Fin r) ℚ⟦X⟧) (exp ℚ) *
          PowerSeries.subst (∑ i ∈ Finset.Iic j,
            (MvPowerSeries.X (Sum.inr i) : MvPowerSeries (Fin r ⊕ Fin r) ℚ⟦X⟧)) (exp ℚ)) *
        MvPowerSeries.subst
          (Sum.elim
            (fun j : Fin r => PowerSeries.subst (MvPowerSeries.X (Sum.inl j) :
              MvPowerSeries (Fin r ⊕ Fin r) ℚ⟦X⟧) (exp ℚ) - 1)
            (fun j : Fin r => PowerSeries.subst (∑ i ∈ Finset.Iic j,
              (MvPowerSeries.X (Sum.inr i) : MvPowerSeries (Fin r ⊕ Fin r) ℚ⟦X⟧)) (exp ℚ) - 1))
          (szGen r) = biBracketGen r ∧
    (∏ j : Fin r, (1 + MvPowerSeries.X (Sum.inl j)) * (1 + MvPowerSeries.X (Sum.inr j))) *
        szGen r =
      MvPowerSeries.subst
        (Sum.elim
          (fun j : Fin r => PowerSeries.subst (MvPowerSeries.X (Sum.inl j) :
            MvPowerSeries (Fin r ⊕ Fin r) ℚ⟦X⟧) logOneAddSeries)
          (fun j : Fin r => PowerSeries.subst (MvPowerSeries.X (Sum.inr j) :
              MvPowerSeries (Fin r ⊕ Fin r) ℚ⟦X⟧) logOneAddSeries -
            ∑ i ∈ Finset.univ.filter (fun i : Fin r => i.val + 1 = j.val),
              PowerSeries.subst (MvPowerSeries.X (Sum.inr i) :
                MvPowerSeries (Fin r ⊕ Fin r) ℚ⟦X⟧) logOneAddSeries))
        (biBracketGen r)

/-- **Generating series of OOZ-qMZVs, coefficientwise.** Let $r$ and $N$ be natural numbers and
let $k_1, \dots, k_r \ge 1$ and $d_1, \dots, d_r \ge 0$ be integers. Writing $\{0\}^d$ for $d$
consecutive zeros, the coefficient of $q^N$ in the Ohno–Okuda–Zudilin qMZV
$\zeta_q^{\mathrm{OOZ}}(k_1, \{0\}^{d_1}, \dots, k_r, \{0\}^{d_r})$ equals the coefficient of
$q^N$ in
$$\sum q^{m_1} \prod_{j=1}^r \binom{m_j - m_{j+1} - 1}{d_j} \frac{1}{(1 - q^{m_j})^{k_j}},$$
the sum running over integers $N \ge m_1 > m_2 > \dots > m_r > 0$, where $m_{r+1} := 0$ and the
factor $q^{m_1}$ is read as $1$ when $r = 0$.

In the untruncated sum, the summands with $m_1 > N$ have $q$-adic order greater than $N$. Let
$\mathfrak{oz}(X; Y)$ be the paper's generating series of OOZ-qMZVs of depth $r$ in the variables
$X_1, \dots, X_r$ and $Y_1, \dots, Y_r$ over $\mathbb{Q}[[q]]$. The statement compares the
coefficients of $\prod_j X_j^{k_j}/k_j! \, Y_j^{d_j}$ on both sides of the paper's identity
$\mathfrak{oz}(X; Y) = \sum q^{m_1} \prod_j (1 + Y_j)^{m_j - m_{j+1} - 1}
(e^{X_j/(1 - q^{m_j})} - 1)$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 11 (`integers-2024-A6-prop-11`). -/
public theorem_wanted coeff_oozQMZV_szBlockIndex_eq_sum_choose (r : ℕ) (k d : Fin r → ℕ)
    (hk : ∀ j, 1 ≤ k j) (N : ℕ) :
    coeff N (oozQMZV (szBlockIndex (List.ofFn fun j => (k j, d j + 1)))) =
      coeff N (∑ m ∈ (Fintype.piFinset fun _ : Fin r => Finset.range (N + 1)) with
          StrictAnti m ∧ ∀ j, 0 < m j,
        X ^ (if h : 0 < r then m ⟨0, h⟩ else 0) *
          ∏ j : Fin r, ((((m j - (if h : j.val + 1 < r then m ⟨j.val + 1, h⟩ else 0) - 1).choose
            (d j) : ℕ) : ℚ⟦X⟧) * ((1 - X ^ m j)⁻¹) ^ k j))

/-- **Brackets, Okounkov qMZVs and Bradley–Zhao qMZVs span $\mathcal{Z}^\circ_{q,1}$.** For an
index $k = (k_1, \dots, k_r)$ of natural numbers let $g(k) = g(k_1, \dots, k_r; 0, \dots, 0)$ be
the bracket, that is, the bi-bracket with all $d_j = 0$, and let $\zeta_q^{\mathrm{Oko}}(k)$ and
$\zeta_q^{BZ}(k)$ be the Okounkov and Bradley–Zhao qMZVs. Then the space
$\mathcal{Z}^\circ_{q,1}$ equals the $\mathbb{Q}$-linear span of the brackets $g(k)$, equals the
$\mathbb{Q}$-linear span of the Okounkov qMZVs $\zeta_q^{\mathrm{Oko}}(k)$, and equals the
$\mathbb{Q}$-linear span of the Bradley–Zhao qMZVs $\zeta_q^{BZ}(k)$, where in each case $k$ runs
over all indices of length $r \ge 0$ with every $k_i \ge 2$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 16 (`integers-2024-A6-prop-16`). -/
public theorem_wanted qMZVSpaceCirc_one_eq_span_bracket_okounkov_bz :
    qMZVSpaceCirc 1 = Submodule.span ℚ {f | ∃ k : List ℕ,
        (∀ kᵢ ∈ k, 2 ≤ kᵢ) ∧ f = biBracket (k.map fun kᵢ => (kᵢ, 0))} ∧
      qMZVSpaceCirc 1 = Submodule.span ℚ {f | ∃ k : List ℕ,
        (∀ kᵢ ∈ k, 2 ≤ kᵢ) ∧ f = okounkovQMZV k} ∧
      qMZVSpaceCirc 1 = Submodule.span ℚ {f | ∃ k : List ℕ,
        (∀ kᵢ ∈ k, 2 ≤ kᵢ) ∧ f = bzQMZV k}

/-- **Weighted quasi-shuffle product.** Let $A$ be an alphabet and let $d$ assign to any two
letters $a, b \in A$ a finite formal $\mathbb{Q}$-linear combination
$d(a, b) = \sum_c d(a, b)_c \, c$ of letters. The weighted quasi-shuffle product $u \ast v$ of
two words over $A$ is the finite formal $\mathbb{Q}$-linear combination of words defined by
recursion on total length: $\mathbf{1} \ast w = w \ast \mathbf{1} = w$ for the empty word
$\mathbf{1}$, and for letters $a, b$ and words $u, v$,
$a u \ast b v = a (u \ast b v) + b (a u \ast v) + \sum_c d(a, b)_c \, c (u \ast v)$, where
prefixing a letter is extended linearly to combinations of words.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
quasi-shuffle products of Section 2 (with `ℚ`-valued letter product, as for bi-brackets). -/
public noncomputable def weightedQuasiShuffle {α : Type*} (d : α → α → (α →₀ ℚ)) :
    List α → List α → (List α →₀ ℚ)
  | [], v => Finsupp.single v 1
  | a :: u, [] => Finsupp.single (a :: u) 1
  | a :: u, b :: v =>
      (weightedQuasiShuffle d u (b :: v)).mapDomain (a :: ·) +
        (weightedQuasiShuffle d (a :: u) v).mapDomain (b :: ·) +
        (d a b).sum fun c x => x • (weightedQuasiShuffle d u v).mapDomain (c :: ·)
termination_by u v => u.length + v.length

/-- **The empty word is a left unit for the weighted quasi-shuffle.** For every alphabet $A$,
every weighted letter product $d$ on $A$ (assigning to two letters a finite formal
$\mathbb{Q}$-linear combination of letters) and every word $v$ over $A$, the weighted
quasi-shuffle product of the empty word $\mathbf{1}$ with $v$ is $v$: $\mathbf{1} \ast v = v$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
quasi-shuffle products of Section 2. -/
public theorem weightedQuasiShuffle_nil_left {α : Type*} (d : α → α → (α →₀ ℚ)) (v : List α) :
    weightedQuasiShuffle d [] v = Finsupp.single v 1 := by
  simp [weightedQuasiShuffle]

/-- **Bachmann's coefficients.** For natural numbers $a$, $b$ and $j$,
$$\lambda_{a,b}^j = (-1)^{b-1} \binom{a + b - j - 1}{a - j} \frac{B_{a+b-j}}{(a + b - j)!},$$
where $B_n$ is the $n$-th Bernoulli number with $B_1 = -1/2$ and every subtraction of natural
numbers is truncated at $0$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition of the bi-bracket product `⊠` (after Bachmann). -/
public noncomputable def biBracketLambda (a b j : ℕ) : ℚ :=
  (-1) ^ (b - 1) * ((a + b - j - 1).choose (a - j) : ℚ) * bernoulli (a + b - j) /
    (a + b - j).factorial

/-- **Bachmann's coefficient $\lambda_{1,1}^1$.** Bachmann's coefficient $\lambda_{1,1}^1$ equals
$-1/2$, the Bernoulli number $B_1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition of the bi-bracket product `⊠`. -/
public theorem biBracketLambda_one_one_one : biBracketLambda 1 1 1 = -1 / 2 := by
  simp [biBracketLambda, bernoulli_one]

/-- **Bachmann's product of bi-bracket letters.** Write $z_{k,d}$ for the letter indexed by a pair
$(k, d)$ of natural numbers, and let $\lambda_{a,b}^j$ be Bachmann's coefficients. The product of
the letters $z_{k_1,d_1}$ and $z_{k_2,d_2}$ is the formal $\mathbb{Q}$-linear combination of letters
$$z_{k_1,d_1} \boxtimes z_{k_2,d_2} = \binom{d_1 + d_2}{d_1} \Big( \sum_{j=1}^{k_1}
\lambda_{k_1,k_2}^j z_{j,d_1+d_2} + \sum_{j=1}^{k_2} \lambda_{k_2,k_1}^j z_{j,d_1+d_2} +
z_{k_1+k_2,d_1+d_2} \Big).$$

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition of the bi-bracket product `⊠` (after Bachmann). -/
public noncomputable def biBracketDiamond (x y : ℕ × ℕ) : (ℕ × ℕ) →₀ ℚ :=
  ((x.2 + y.2).choose x.2 : ℚ) •
    ((∑ j ∈ Finset.Icc 1 x.1, biBracketLambda x.1 y.1 j • Finsupp.single (j, x.2 + y.2) 1) +
      (∑ j ∈ Finset.Icc 1 y.1, biBracketLambda y.1 x.1 j • Finsupp.single (j, x.2 + y.2) 1) +
      Finsupp.single (x.1 + y.1, x.2 + y.2) 1)

/-- **Bi-brackets form a quasi-shuffle algebra.** Let $u$ and $v$ be words in the letters $z_{k,d}$,
indexed by pairs $(k, d)$ of natural numbers, with $k \ge 1$ in every letter. Write
$\sum_w c_w w$ for the quasi-shuffle product of $u$ and $v$ induced by Bachmann's letter product
$\boxtimes$, a formal $\mathbb{Q}$-linear combination of words, and $g(w)$ for the bi-bracket of a
word $w$. Then $g(u) g(v) = \sum_w c_w g(w)$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 10 (i) (`integers-2024-A6-thm-10`). -/
public theorem_wanted biBracket_mul_eq_sum_weightedQuasiShuffle (u v : List (ℕ × ℕ))
    (hu : ∀ p ∈ u, 1 ≤ p.1) (hv : ∀ p ∈ v, 1 ≤ p.1) :
    biBracket u * biBracket v =
      (weightedQuasiShuffle biBracketDiamond u v).sum fun w c => c • biBracket w

/-- **The map $T$ of the OOZ quasi-shuffle product.** Words are finite sequences of letters
$z_k$ with $k$ a natural number. The map $T$ sends each word to a finite formal
$\mathbb{Q}$-linear combination of words: it sends the empty word $\mathbf{1}$ to $\mathbf{1}$,
and a word $z_n v$ with first letter $z_n$ to $z_n v - z_{n-1} v$, where $n - 1$ is truncated
at $0$ (so $T(z_0 v) = 0$).

In the paper $T$ is defined only on a subspace of the combinations of words; here it is defined
on all words.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition of the OOZ quasi-shuffle product. -/
public noncomputable def oozT : List ℕ → (List ℕ →₀ ℚ)
  | [] => Finsupp.single [] 1
  | n :: v => Finsupp.single (n :: v) 1 - Finsupp.single ((n - 1) :: v) 1

/-- **The OOZ map fixes the empty word.** Let $T$ be the map of the OOZ quasi-shuffle product,
which sends words in letters $z_k$ ($k$ a natural number) to finite formal $\mathbb{Q}$-linear
combinations of words. Then $T$ sends the empty word $\mathbf{1}$ to itself:
$T(\mathbf{1}) = \mathbf{1}$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition of the OOZ quasi-shuffle product. -/
public theorem oozT_nil : oozT [] = Finsupp.single [] 1 := rfl

/-- **The OOZ map on a one-letter word.** Let $T$ be the map of the OOZ quasi-shuffle product,
which sends words in letters $z_k$ ($k$ a natural number) to finite formal $\mathbb{Q}$-linear
combinations of words. Then $T$ sends the one-letter word $z_2$ to $z_2 - z_1$:
$T(z_2) = z_2 - z_1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition of the OOZ quasi-shuffle product. -/
public theorem oozT_singleton_two : oozT [2] = Finsupp.single [2] 1 - Finsupp.single [1] 1 := rfl

/-- **Stuffle product of formal linear combinations of words.** On words in letters $z_k$
($k$ a natural number), the stuffle product $\ast$ is the quasi-shuffle product with letter
product $z_m \diamond z_n = z_{m+n}$: $\mathbf{1} \ast w = w \ast \mathbf{1} = w$ for the empty
word $\mathbf{1}$, and $z_m u \ast z_n v = z_m (u \ast z_n v) + z_n (z_m u \ast v) +
z_{m+n} (u \ast v)$, counted with multiplicity. It is extended $\mathbb{Q}$-bilinearly to finite
formal $\mathbb{Q}$-linear combinations of words: $A \ast B = \sum_{a, b} A_a B_b \, (a \ast b)$,
where $A_a$ is the coefficient of the word $a$ in $A$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition of the stuffle product `∗` on `𝔥¹`. -/
public noncomputable def stuffleComb (A B : List ℕ →₀ ℚ) : List ℕ →₀ ℚ :=
  A.sum fun a x => B.sum fun b y =>
    (x * y) • ((quasiShuffle (fun m n => [m + n]) a b).map fun w => Finsupp.single w (1 : ℚ)).sum

/-- **The empty word is a left unit for the stuffle product.** For every word $b$ in letters
$z_k$ ($k$ a natural number), the stuffle product of the empty word $\mathbf{1}$ with $b$ is
$b$: $\mathbf{1} \ast b = b$, as formal $\mathbb{Q}$-linear combinations of words.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Definition of the stuffle product `∗` on `𝔥¹`. -/
public theorem stuffleComb_single_nil (b : List ℕ) :
    stuffleComb (Finsupp.single [] 1) (Finsupp.single b 1) = Finsupp.single b 1 := by
  simp [stuffleComb, quasiShuffle_nil_left]

/-- **OOZ qMZVs respect the OOZ quasi-shuffle product.** Identify words in letters $z_k$ with
lists $(k_1, \dots, k_r)$ of natural numbers, and call such a word admissible if every
$k_i \ge 1$ and, when $r \ge 1$, $k_1 \ge 2$. Let $T$ send the empty word $\mathbf{1}$ to
$\mathbf{1}$ and a word $z_n v$ with first letter $z_n$ to the formal $\mathbb{Q}$-linear
combination $z_n v - z_{n-1} v$ (with $n - 1$ truncated at $0$). Extend $T$ and the
Ohno–Okuda–Zudilin qMZV $\zeta_q^{\mathrm{OOZ}}$ $\mathbb{Q}$-linearly to finite formal
$\mathbb{Q}$-linear combinations of words, and let $\ast$ be the stuffle product (the
quasi-shuffle product with letter product $z_m \diamond z_n = z_{m+n}$) of such combinations.
For all admissible words $u$ and $v$, there is exactly one finite formal $\mathbb{Q}$-linear
combination $w$ of admissible words with $T(w) = T(u) \ast T(v)$, and every finite formal
$\mathbb{Q}$-linear combination $w$ of admissible words with $T(w) = T(u) \ast T(v)$ satisfies
$\zeta_q^{\mathrm{OOZ}}(w) = \zeta_q^{\mathrm{OOZ}}(u) \, \zeta_q^{\mathrm{OOZ}}(v)$.

Thus the OOZ quasi-shuffle product, defined by $T(u \ast_{\mathrm{OOZ}} v) = T(u) \ast T(v)$,
is well defined, and $\zeta_q^{\mathrm{OOZ}}$ is multiplicative for it.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 16 (after Castillo Medina, Ebrahimi-Fard and Manchon) (`integers-2024-A6-thm-16`). -/
public theorem_wanted oozQMZV_mul_eq_of_oozT_eq_stuffleComb (u v : List ℕ)
    (hu : ∀ k ∈ u, 1 ≤ k) (hu₁ : ∀ k₁ ∈ u.head?, 2 ≤ k₁)
    (hv : ∀ k ∈ v, 1 ≤ k) (hv₁ : ∀ k₁ ∈ v.head?, 2 ≤ k₁) :
    (∃! w : List ℕ →₀ ℚ, (∀ x ∈ w.support, (∀ k ∈ x, 1 ≤ k) ∧ ∀ k₁ ∈ x.head?, 2 ≤ k₁) ∧
        (w.sum fun x c => c • oozT x) = stuffleComb (oozT u) (oozT v)) ∧
      ∀ w : List ℕ →₀ ℚ, (∀ x ∈ w.support, (∀ k ∈ x, 1 ≤ k) ∧ ∀ k₁ ∈ x.head?, 2 ≤ k₁) →
        (w.sum fun x c => c • oozT x) = stuffleComb (oozT u) (oozT v) →
        (w.sum fun x c => c • oozQMZV x) = oozQMZV u * oozQMZV v

/-- **Weighted chain sums.** Let $o_1, \dots, o_\ell$ be a word of markers, each either a natural
number (a weighted position) or a blank (an unweighted position); let $W$ be the set of weighted
positions and $k_t$ the number at position $t \in W$. For natural numbers $M$ and $R$, the
weighted chain sum of the word at bound $M$ and target $R$ is the natural number
$$\sum \prod_{t \in W} \binom{j_t}{k_t},$$
the sum running over strictly decreasing chains $M > a_1 > a_2 > \dots > a_\ell > 0$ of natural
numbers and multiplicities $j_1, \dots, j_\ell \ge 0$ with $a_1 j_1 + \dots + a_\ell j_\ell = R$.
For the empty word ($\ell = 0$) the sum has a single empty term, so the value is $1$ if $R = 0$
and $0$ otherwise, whatever $M$ is.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 1 (the sums over `m₁ > n₁ > ⋯ > m_r > ⋯ > 0` with multiplicities `j, i ≥ 0`). -/
public def bzChainSum : List (Option ℕ) → ℕ → ℕ → ℕ
  | [], _, R => if R = 0 then 1 else 0
  | o :: os, M, R => ∑ m ∈ Finset.Ioo 0 M, ∑ j ∈ Finset.range (R / m + 1),
      (match o with
        | some k => j.choose k
        | none => 1) * bzChainSum os m (R - m * j)

/-- **Marker word of a list of blocks.** A marker is either a weight $k \in \mathbb{N}$ (a weighted
position) or a blank (an unweighted position). The marker word of a list of blocks
$(s_1, k_1), \dots, (s_r, k_r)$ of natural numbers is the concatenation, in order, of the words
consisting of the weight $k_t$ followed by $s_t - 1$ blanks (no blanks when $s_t \le 1$).

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 1 (block `t` of the chain is `m_t > n > ⋯ > n` with `d_t - 1` entries `n`). -/
public def bzChainWord (b : List (ℕ × ℕ)) : List (Option ℕ) :=
  b.flatMap fun sk => some sk.2 :: List.replicate (sk.1 - 1) none

/-- **Chain sum of the single block $(1, 1)$.** The marker word of the single block $(1, 1)$ is
one position weighted by $1$, and its chain sum with bound $M = 3$ and target $R = 2$ equals $3$:
it is the sum of $\binom{j}{1} = j$ over $0 < m < 3$ and $j \ge 0$ with $m j = 2$, which is
$2 + 1 = 3$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 1 (case `r = 1`, `k₁ = d₁ = 1`, `N = 2`). -/
public theorem bzChainSum_bzChainWord_one_one :
    bzChainSum (bzChainWord [(1, 1)]) 3 2 = 3 := by
  decide

/-- **Combinatorial form of Bradley–Zhao duality.** For a list of blocks
$(s_1, w_1), \dots, (s_r, w_r)$ of positive integers and an integer $N \ge 1$, let
$S_N((s_1, w_1), \dots, (s_r, w_r))$ be the sum of $\binom{j_1}{w_1} \cdots \binom{j_r}{w_r}$
over all strictly decreasing chains $N + 1 > a_1 > \dots > a_n > 0$ of length
$n = s_1 + \dots + s_r$ and all multiplicities $c_1, \dots, c_n \ge 0$ with
$a_1 c_1 + \dots + a_n c_n = N$, where the chain is cut into consecutive blocks of lengths
$s_1, \dots, s_r$ and $j_t$ is the multiplicity of the first entry of block $t$. Let $r \ge 1$
and $k_1, \dots, k_r, d_1, \dots, d_r \ge 1$. Then

$$S_N((d_1, k_1), \dots, (d_r, k_r)) = S_N((k_r, d_r), \dots, (k_1, d_1)).$$

The bound $N + 1$ loses nothing: since $w_1 \ge 1$, a nonzero term has $j_1 \ge 1$ and hence
$a_1 \le N$.

Source: arXiv:2111.00051, Theorem 4.18; the record's formula is garbled and is read from there,
and the paper's closing remark (equivalence with BZ duality) is not part of this statement.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 1 (`integers-2024-A6-thm-1`). -/
public theorem_wanted bzChainSum_dual (k d : List ℕ) (hlen : k.length = d.length)
    (hr : k ≠ []) (hk : ∀ x ∈ k, 1 ≤ x) (hd : ∀ x ∈ d, 1 ≤ x) (N : ℕ) (hN : 1 ≤ N) :
    bzChainSum (bzChainWord (d.zip k)) (N + 1) N =
      bzChainSum (bzChainWord (k.zip d).reverse) (N + 1) N

/-- **The SZ dual index.** Identify an index $k = (k_1, \dots, k_r)$ of natural numbers with the
word $p^{k_1} y \cdots p^{k_r} y$ in the letters $p$ and $y$, and let $\tilde\tau$ be the
anti-automorphism of words with $\tilde\tau(p) = y$ and $\tilde\tau(y) = p$ (reverse the word and
swap the letters). Write $\tilde\tau(p^{k_1} y \cdots p^{k_r} y)$ as $p^{a_1} y \cdots p^{a_s} y$
followed by a possibly empty run of letters $p$ (nonempty only when $k_1 = 0$); that run is
dropped, and the SZ dual index is $k^\dagger = (a_1, \dots, a_s)$.

For $k = (k_1, \{0\}^{d_1 - 1}, \dots, k_r, \{0\}^{d_r - 1})$ with all $k_i, d_i \ge 1$, where
$\{0\}^m$ stands for $m$ zeros, this gives
$k^\dagger = (d_r, \{0\}^{k_r - 1}, \dots, d_1, \{0\}^{k_1 - 1})$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 5 (SZ duality, the map `τ̃` and the SZ dual index). -/
public def szDualIndex (k : List ℕ) : List ℕ :=
  szIndexOfWordAux 0 ((szWord k).reverse.map not)

/-- **The SZ dual of $(2)$.** The SZ dual index of the one-entry index $(2)$ is $(1, 0)$, that
is, $(2)^\dagger = (1, 0)$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 5 (SZ dual index). -/
public theorem szDualIndex_two : szDualIndex [2] = [1, 0] := by decide

/-- **Bradley–Zhao dual index.** For an index $k = (k_1, \dots, k_r)$ of natural numbers, form the
word $x^{k_1 - 1} y \cdots x^{k_r - 1} y$ in two letters $x$ and $y$ (each $k_i - 1$ truncated at
$0$); when all $k_i \ge 1$ this is $z_{k_1} \cdots z_{k_r}$ with $z_k = x^{k-1} y$. Apply the
anti-automorphism $\tau$ of words with $\tau(x) = y$ and $\tau(y) = x$, which reverses a word and
swaps its letters, and write the result as $x^{n_1} y \cdots x^{n_s} y \, x^e$. The BZ dual index
of $k$ is $(n_1 + 1, \dots, n_s + 1)$; the trailing $x^e$ is dropped. For an admissible index
($k_1 \ge 2$ and all $k_i \ge 1$, or empty) $e = 0$, so the dual index is the index of
$\tau(z_{k_1} \cdots z_{k_r})$.

Equivalently, it is the SZ dual index of $(k_1 - 1, \dots, k_r - 1)$ with every entry increased
by one.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 7 (BZ duality, the map `τ`). -/
public def bzDualIndex (k : List ℕ) : List ℕ :=
  (szDualIndex (k.map (· - 1))).map (· + 1)

/-- **Bradley–Zhao dual of $(3)$.** The Bradley–Zhao dual index of $(3)$ is $(2, 1)$. In terms of
words in the letters $x$ and $y$, with $z_k = x^{k-1} y$ and $\tau$ the anti-automorphism of words
that reverses a word and swaps $x$ and $y$, this says $\tau(z_3) = \tau(x x y) = x y y = z_2 z_1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 7 (BZ duality). -/
public theorem bzDualIndex_three : bzDualIndex [3] = [2, 1] := by decide

/-- **The tail part of the map $U$.** A word is a finite sequence $z_{k_1} \cdots z_{k_s}$ of
letters $z_k$, $k \in \mathbb{N}$. This map sends the empty word to itself and, for $s \ge 1$,
sends $z_{k_1} \cdots z_{k_s}$ to the formal $\mathbb{Q}$-linear combination of words
$$\sum \binom{k_1 - 1}{n_1 - 1} \cdots \binom{k_s - 1}{n_s - 1} \, z_{n_1} \cdots z_{n_s}$$
over $1 \le n_j \le k_j$ for $1 \le j \le s$ (an empty sum is $0$). The map $U$ from OOZ to BZ
words applies it to the letters after the first.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 12 (i) (after Ebrahimi-Fard, Manchon and Singer, the map `U`). -/
public noncomputable def oozToBZTail : List ℕ → (List ℕ →₀ ℚ)
  | [] => Finsupp.single [] 1
  | b :: k => ∑ n ∈ Finset.Icc 1 b,
      (((b - 1).choose (n - 1) : ℕ) : ℚ) • (oozToBZTail k).mapDomain (List.cons n)

/-- **The map $U$ from OOZ to BZ words.** A word is a finite sequence $z_{k_1} \cdots z_{k_r}$ of
letters $z_k$, $k \in \mathbb{N}$. The map $U$ sends each word to a formal $\mathbb{Q}$-linear
combination of words: $U(\mathbf{1}) = \mathbf{1}$ for the empty word $\mathbf{1}$, and for
$r \ge 1$
$$U(z_{k_1} \cdots z_{k_r}) = \sum \binom{k_1 - 2}{n_1 - 2} \binom{k_2 - 1}{n_2 - 1} \cdots
\binom{k_r - 1}{n_r - 1} \, z_{n_1} \cdots z_{n_r}$$
where the sum runs over $2 \le n_1 \le k_1$ and $1 \le n_j \le k_j$ for $2 \le j \le r$ (an empty
sum is $0$).

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 12 (i) (after Ebrahimi-Fard, Manchon and Singer, the map `U`). -/
public noncomputable def oozToBZ : List ℕ → (List ℕ →₀ ℚ)
  | [] => Finsupp.single [] 1
  | a :: k => ∑ n ∈ Finset.Icc 2 a,
      (((a - 2).choose (n - 2) : ℕ) : ℚ) • (oozToBZTail k).mapDomain (List.cons n)

/-- **$U$ fixes the empty index.** Write $\mathbf{1}$ for the empty index. The map $U$ from OOZ to
BZ indices sends $\mathbf{1}$ to the $\mathbb{Q}$-linear combination of indices consisting of
$\mathbf{1}$ with coefficient $1$; that is, $U(\mathbf{1}) = \mathbf{1}$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 12 (i). -/
public theorem oozToBZ_nil : oozToBZ [] = Finsupp.single [] 1 := rfl

/-- **The map $U$ fixes $z_2$.** The map $U$ from OOZ to BZ words sends the one-letter word $z_2$
to itself with coefficient $1$: $U(z_2) = z_2$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 12 (i). -/
public theorem oozToBZ_two : oozToBZ [2] = Finsupp.single [2] 1 := by
  simp [oozToBZ, oozToBZTail]

/-- **The tail part of the map $V$.** Identify an index $(k_1, \dots, k_s)$ of natural numbers
with the word $p^{k_1} y \cdots p^{k_s} y$ in the letters $p$ and $y$. This map sends the empty
word to itself and, for $s \ge 1$, sends $p^{k_1} y \cdots p^{k_s} y$ to the formal
$\mathbb{Q}$-linear combination of words
$$\sum \binom{k_1}{n_1} \cdots \binom{k_s}{n_s} \, p^{n_1} y \cdots p^{n_s} y$$
over $0 \le n_j \le k_j$ for $1 \le j \le s$. The map $V$ from OOZ to SZ words applies it to the
blocks $p^{k_j} y$ after the first.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 12 (ii) (after Ebrahimi-Fard, Manchon and Singer, the map `V`). -/
public noncomputable def oozToSZTail : List ℕ → (List ℕ →₀ ℚ)
  | [] => Finsupp.single [] 1
  | b :: k => ∑ n ∈ Finset.range (b + 1),
      ((b.choose n : ℕ) : ℚ) • (oozToSZTail k).mapDomain (List.cons n)

/-- **The map $V$ from OOZ to SZ words.** Identify an index $(k_1, \dots, k_r)$ of natural
numbers with the word $p^{k_1} y \cdots p^{k_r} y$ in the letters $p$ and $y$. The map $V$ sends
each such word to a formal $\mathbb{Q}$-linear combination of words: $V(\mathbf{1}) = \mathbf{1}$
for the empty word $\mathbf{1}$, and for $r \ge 1$
$$V(p^{k_1} y \cdots p^{k_r} y) = \sum \binom{k_1 - 1}{n_1 - 1} \binom{k_2}{n_2} \cdots
\binom{k_r}{n_r} \, p^{n_1} y \cdots p^{n_r} y$$
where the sum runs over $1 \le n_1 \le k_1$ and $0 \le n_j \le k_j$ for $2 \le j \le r$ (an empty
sum is $0$).

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 12 (ii) (after Ebrahimi-Fard, Manchon and Singer, the map `V`). -/
public noncomputable def oozToSZ : List ℕ → (List ℕ →₀ ℚ)
  | [] => Finsupp.single [] 1
  | a :: k => ∑ n ∈ Finset.Icc 1 a,
      (((a - 1).choose (n - 1) : ℕ) : ℚ) • (oozToSZTail k).mapDomain (List.cons n)

/-- **The map $V$ fixes $py$.** The map $V$ from OOZ to SZ words sends the word $py$ (the index
$(1)$) to itself with coefficient $1$: $V(py) = py$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 12 (ii). -/
public theorem oozToSZ_one : oozToSZ [1] = Finsupp.single [1] 1 := by
  simp [oozToSZ, oozToSZTail]

/-- **OOZ-qMZVs of admissible indices via BZ-qMZVs.** Write $\zeta_q^{\mathrm{OOZ}}$ and
$\zeta_q^{\mathrm{BZ}}$ for the Ohno–Okuda–Zudilin and Bradley–Zhao qMZVs. Let
$k = (k_1, \dots, k_r)$ be an index of natural numbers with all $k_i \ge 1$ and, when $r \ge 1$,
$k_1 \ge 2$ (the empty index is allowed). Write the image of $k$ under the map $U$ from OOZ to BZ
indices as a $\mathbb{Q}$-linear combination $U(k) = \sum_w c_w \, w$ of indices. Then
$\zeta_q^{\mathrm{OOZ}}(k) = \sum_w c_w \, \zeta_q^{\mathrm{BZ}}(w)$.

On admissible indices $\zeta_q^{\mathrm{OOZ}}$ is the restricted OOZ-qMZV
$\zeta_q^{\mathrm{OBZ}}$ of the source.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 12 (i) (`integers-2024-A6-prop-12`). -/
public theorem_wanted oozQMZV_eq_sum_bzQMZV_oozToBZ (k : List ℕ) (hk : ∀ a ∈ k, 1 ≤ a)
    (hk₁ : ∀ a ∈ k.head?, 2 ≤ a) :
    oozQMZV k = (oozToBZ k).sum fun w c => c • bzQMZV w

/-- **The map $U$ is a bijection on combinations of admissible indices.** Call an index
$(k_1, \dots, k_r)$ of natural numbers admissible if all $k_i \ge 1$ and, when $r \ge 1$,
$k_1 \ge 2$; the empty index is admissible. Extend the map $U$ from OOZ to BZ indices
$\mathbb{Q}$-linearly to finite $\mathbb{Q}$-linear combinations of indices. This extension maps
the set of $\mathbb{Q}$-linear combinations of admissible indices bijectively onto itself.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 12 (i) (`integers-2024-A6-prop-12`). -/
public theorem_wanted bijOn_linearCombination_oozToBZ :
    Set.BijOn (Finsupp.linearCombination ℚ oozToBZ)
      (Finsupp.supported ℚ ℚ {w : List ℕ | (∀ a ∈ w, 1 ≤ a) ∧ ∀ a ∈ w.head?, 2 ≤ a})
      (Finsupp.supported ℚ ℚ {w : List ℕ | (∀ a ∈ w, 1 ≤ a) ∧ ∀ a ∈ w.head?, 2 ≤ a})

/-- **OOZ-qMZVs via SZ-qMZVs.** Write $\zeta_q^{\mathrm{OOZ}}$ and $\zeta_q^{\mathrm{SZ}}$ for the
Ohno–Okuda–Zudilin and Schlesinger–Zudilin qMZVs. Let $k = (k_1, \dots, k_r)$ be an index of
natural numbers that is empty or has $k_1 \ge 1$ (the entries $k_2, \dots, k_r$ may be $0$).
Write the image of $k$ under the map $V$ from OOZ to SZ indices as a $\mathbb{Q}$-linear
combination $V(k) = \sum_w c_w \, w$ of indices. Then
$\zeta_q^{\mathrm{OOZ}}(k) = \sum_w c_w \, \zeta_q^{\mathrm{SZ}}(w)$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 12 (ii) (`integers-2024-A6-prop-12`). -/
public theorem_wanted oozQMZV_eq_sum_szQMZV_oozToSZ (k : List ℕ) (hk₁ : ∀ a ∈ k.head?, 1 ≤ a) :
    oozQMZV k = (oozToSZ k).sum fun w c => c • szQMZV w

/-- **The map $V$ is a bijection on combinations of SZ-admissible indices.** Call an index
$(k_1, \dots, k_r)$ of natural numbers SZ-admissible if it is empty or $k_1 \ge 1$ (the entries
$k_2, \dots, k_r$ may be $0$). Extend the map $V$ from OOZ to SZ indices $\mathbb{Q}$-linearly to
finite $\mathbb{Q}$-linear combinations of indices. This extension maps the set of
$\mathbb{Q}$-linear combinations of SZ-admissible indices bijectively onto itself.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 12 (ii) (`integers-2024-A6-prop-12`). -/
public theorem_wanted bijOn_linearCombination_oozToSZ :
    Set.BijOn (Finsupp.linearCombination ℚ oozToSZ)
      (Finsupp.supported ℚ ℚ {w : List ℕ | ∀ a ∈ w.head?, 1 ≤ a})
      (Finsupp.supported ℚ ℚ {w : List ℕ | ∀ a ∈ w.head?, 1 ≤ a})

/-- **Duality for restricted OOZ-qMZVs.** Call an index $(k_1, \dots, k_r)$ of natural numbers
admissible if $k_j \ge 1$ for all $j$ and, when $r \ge 1$, $k_1 \ge 2$. Extend
$\zeta_q^{\mathrm{OOZ}}$ and the map $U$ linearly to formal $\mathbb{Q}$-linear combinations of
indices, and let $\tau$ act on such a combination by replacing each index with its BZ dual index.
Let $w$ be an admissible index and let $x$ be a $\mathbb{Q}$-linear combination of admissible
indices with $U(x) = \tau(U(w))$. Then $\zeta_q^{\mathrm{OOZ}}(x) = \zeta_q^{\mathrm{OOZ}}(w)$.

Since $U$ is a bijection on combinations of admissible indices (Proposition 12 (i) of the source),
this is the identity
$\zeta_q^{\mathrm{OOZ}} = \zeta_q^{\mathrm{OOZ}} \circ U^{-1} \circ \tau \circ U$ on
admissible indices.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 17 (i) (after Ebrahimi-Fard, Manchon and Singer) (`integers-2024-A6-thm-17`). -/
public theorem_wanted sum_oozQMZV_eq_of_oozToBZ_eq_bzDual (w : List ℕ) (hw : ∀ a ∈ w, 1 ≤ a)
    (hw₁ : ∀ a ∈ w.head?, 2 ≤ a) (x : List ℕ →₀ ℚ)
    (hx : x ∈ Finsupp.supported ℚ ℚ {v : List ℕ | (∀ a ∈ v, 1 ≤ a) ∧ ∀ a ∈ v.head?, 2 ≤ a})
    (hUx : Finsupp.linearCombination ℚ oozToBZ x = (oozToBZ w).mapDomain bzDualIndex) :
    (x.sum fun v c => c • oozQMZV v) = oozQMZV w

/-- **Duality for OOZ-qMZVs.** Call an index $(k_1, \dots, k_r)$ of natural numbers SZ-admissible
if it is empty or $k_1 \ge 1$. Extend $\zeta_q^{\mathrm{OOZ}}$ and the map $V$ linearly to formal
$\mathbb{Q}$-linear combinations of indices, and let $\tilde\tau$ act on such a combination by
replacing each index with its SZ dual index. Let $w$ be an SZ-admissible index and let $x$ be a
$\mathbb{Q}$-linear combination of SZ-admissible indices with $V(x) = \tilde\tau(V(w))$. Then
$\zeta_q^{\mathrm{OOZ}}(x) = \zeta_q^{\mathrm{OOZ}}(w)$.

Since $V$ is a bijection on combinations of SZ-admissible indices (Proposition 12 (ii) of the
source), this is the identity
$\zeta_q^{\mathrm{OOZ}} = \zeta_q^{\mathrm{OOZ}} \circ V^{-1} \circ \tilde\tau \circ V$ on
SZ-admissible indices.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 17 (ii) (after Ebrahimi-Fard, Manchon and Singer) (`integers-2024-A6-thm-17`). -/
public theorem_wanted sum_oozQMZV_eq_of_oozToSZ_eq_szDual (w : List ℕ)
    (hw₁ : ∀ a ∈ w.head?, 1 ≤ a) (x : List ℕ →₀ ℚ)
    (hx : x ∈ Finsupp.supported ℚ ℚ {v : List ℕ | ∀ a ∈ v.head?, 1 ≤ a})
    (hVx : Finsupp.linearCombination ℚ oozToSZ x = (oozToSZ w).mapDomain szDualIndex) :
    (x.sum fun v c => c • oozQMZV v) = oozQMZV w

/-- **Partial sums of SZ-star qMZVs.** For an index $k = (k_1, \dots, k_r)$ of natural numbers and
a bound $M \in \mathbb{N}$, the partial sum is the formal power series in $q$ over $\mathbb{Q}$
$$
\sum_{M \ge m_1 \ge \dots \ge m_r > 0} \prod_{j=1}^{r} \frac{q^{m_j k_j}}{(1 - q^{m_j})^{k_j}};
$$
for the empty index it is $1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 17 (iii) (SZ-star qMZVs, defining sum truncated at `m₁ ≤ M`). -/
public noncomputable def szStarQMZVPartial : List ℕ → ℕ → ℚ⟦X⟧
  | [], _ => 1
  | k :: ks, M => ∑ m ∈ Finset.Icc 1 M, (X ^ m * (1 - X ^ m)⁻¹) ^ k * szStarQMZVPartial ks m

/-- **SZ-star qMZVs.** For an index $k = (k_1, \dots, k_r)$ of natural numbers, the SZ-star qMZV
$\zeta_q^{SZ,\star}(k)$ is the formal power series in $q$ over $\mathbb{Q}$
$$
\zeta_q^{SZ,\star}(k_1, \dots, k_r) =
\sum_{m_1 \ge \dots \ge m_r > 0} \prod_{j=1}^{r} \frac{q^{m_j k_j}}{(1 - q^{m_j})^{k_j}},
$$
with $\zeta_q^{SZ,\star}(\varnothing) = 1$. Precisely, its coefficient of $q^N$ is defined as the
coefficient of $q^N$ in the partial sum over $N \ge m_1 \ge \dots \ge m_r > 0$. For $k_1 \ge 1$ the
summands with $m_1 > N$ have $q$-adic order $> N$, so this is the coefficient of $q^N$ in the full
sum; for $k_1 = 0$ the full sum is not a formal power series and the value is a junk value.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 17 (iii) (the map `ζ_q^{SZ,⋆}` of SZ-star qMZVs). -/
public noncomputable def szStarQMZV (k : List ℕ) : ℚ⟦X⟧ :=
  PowerSeries.mk fun N => coeff N (szStarQMZVPartial k N)

/-- **The empty SZ-star qMZV.** The SZ-star qMZV of the empty index is $1$:
$\zeta_q^{SZ,\star}(\varnothing) = 1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 17 (iii). -/
public theorem szStarQMZV_nil : szStarQMZV [] = 1 := by
  ext N
  simp [szStarQMZV, szStarQMZVPartial]

/-- **The coefficient of $q$ in $\zeta_q^{SZ,\star}(1)$.** The coefficient of $q$ in the SZ-star
qMZV $\zeta_q^{SZ,\star}(1) = \sum_{m > 0} q^m / (1 - q^m)$ is $1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 17 (iii). -/
public theorem coeff_one_szStarQMZV_singleton_one : coeff 1 (szStarQMZV [1]) = 1 := by
  simp [szStarQMZV, szStarQMZVPartial, coeff_succ_X_mul, constantCoeff_inv]

/-- **OOZ-qMZVs are SZ-star qMZVs of the dual index.** For every index $k = (k_1, \dots, k_r)$ of
natural numbers that is empty or has $k_1 \ge 1$, the Ohno–Okuda–Zudilin qMZV of $k$ equals the
SZ-star qMZV of the SZ dual index $k^\dagger$: $\zeta_q^{OOZ}(k) = \zeta_q^{SZ,\star}(k^\dagger)$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Theorem 17 (iii) (after Ebrahimi-Fard, Manchon and Singer) (`integers-2024-A6-thm-17`). -/
public theorem_wanted oozQMZV_eq_szStarQMZV_szDualIndex (k : List ℕ)
    (hk₁ : ∀ a ∈ k.head?, 1 ≤ a) :
    oozQMZV k = szStarQMZV (szDualIndex k)

/-- **The map from TBZ words to SZ indices.** Words in the letters $\bar{1}$ and $k \in \mathbb{N}$
are sent to formal $\mathbb{Q}$-linear combinations of finite sequences of natural numbers (SZ
indices) letter by letter: the empty word goes to the empty index with coefficient $1$, and a
word $x w$ with first letter $x$ goes to the image of $w$ with a new first entry prepended to each
index, where $\bar{1}$ contributes the entry $1$ and a letter $k$ contributes the sum of the two
terms obtained with the entries $k$ and $k - 1$ (subtraction truncated at $0$, so the letter $0$
gives the entry $0$ with coefficient doubled). This is the map $U_{\mathrm{TBZ}}$ on words.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 9 (i) (the map `U_TBZ`). -/
public noncomputable def tbzToSZ : List (Option ℕ) → (List ℕ →₀ ℚ)
  | [] => Finsupp.single [] 1
  | none :: w => (tbzToSZ w).mapDomain (List.cons 1)
  | some k :: w => (tbzToSZ w).mapDomain (List.cons k) + (tbzToSZ w).mapDomain (List.cons (k - 1))

/-- **The TBZ-to-SZ map on the letter $\bar{1}$.** The map $U_{\mathrm{TBZ}}$ sends the one-letter
word $\bar{1}$ to the index $(1)$ with coefficient $1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 9 (i). -/
public theorem tbzToSZ_bar : tbzToSZ [none] = Finsupp.single [1] 1 := by
  simp [tbzToSZ]

/-- **The map $V_{TBZ}$ from SZ indices to TBZ words.** For an index $k = (k_1, \dots, k_r)$ of
natural numbers, $V_{TBZ}(k)$ is the formal $\mathbb{Q}$-linear combination of TBZ words (words in
the letters $\bar 1$ and $j \ge 1$; write $z_a$ for the one-letter word $a$) obtained by replacing
each letter $k_i = 0$ by $z_1 - z_{\bar 1}$ and each letter $k_i \ge 1$ by
$\sum_{j=1}^{k_i} (-1)^{k_i - j} z_{j'}$, where $j' = \bar 1$ for $j = 1$ and $j' = j$ otherwise,
and multiplying out by concatenation of words. The empty index goes to the empty word with
coefficient $1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 9 (ii) (the map `V_TBZ`). -/
public noncomputable def szToTBZ : List ℕ → (List (Option ℕ) →₀ ℚ)
  | [] => Finsupp.single [] 1
  | 0 :: k => (szToTBZ k).mapDomain (List.cons (some 1)) - (szToTBZ k).mapDomain (List.cons none)
  | (a + 1) :: k => ∑ j ∈ Finset.Icc 1 (a + 1),
      ((-1 : ℚ) ^ (a + 1 - j)) •
        (szToTBZ k).mapDomain (List.cons (if j = 1 then none else some j))

/-- **The map $V_{TBZ}$ on the index $(1)$.** The map $V_{TBZ}$ sends the SZ index $(1)$ to the
one-letter TBZ word $\bar 1$ with coefficient $1$.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 9 (ii). -/
public theorem szToTBZ_one : szToTBZ [1] = Finsupp.single [none] 1 := by
  simp [szToTBZ]

/-- **TBZ-qMZVs in the SZ model.** Let $w = (w_1, \dots, w_r)$ be a TBZ word: each letter is
either $\bar 1$ or a natural number $k \ge 1$, and $w_1$ is not the number $1$. Let
$U_{TBZ}(w) = \sum_v c_v\, v$ be the formal $\mathbb{Q}$-linear combination of SZ indices obtained
by replacing each letter $\bar 1$ by $1$ and each letter $k$ by $k$ or by $k - 1$, summed over all
choices. Then the Takeyama–Bradley–Zhao qMZV of $w$ is the corresponding combination of
Schlesinger–Zudilin qMZVs: $\zeta_q^{TBZ}(w) = \sum_v c_v\, \zeta_q^{SZ}(v)$.

In block form, writing $\{a\}^d$ for $d$ copies of the letter $a$: for $d_1, \dots, d_s \ge 0$ and
$k_1, \dots, k_{s-1} \ge 1$ with $k_1 \ge 2$ if $d_1 = 0$,
$$
\zeta_q^{TBZ}(\{\bar 1\}^{d_1}, k_1, \{\bar 1\}^{d_2}, \dots, k_{s-1}, \{\bar 1\}^{d_s}) =
\sum_{\delta \in \{0,1\}^{s-1}} \zeta_q^{SZ}(\{1\}^{d_1}, k_1 - \delta_1, \{1\}^{d_2}, \dots,
k_{s-1} - \delta_{s-1}, \{1\}^{d_s}).
$$

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 9 (i) (`integers-2024-A6-prop-9`). -/
public theorem_wanted tbzQMZV_eq_sum_szQMZV_tbzToSZ (w : List (Option ℕ))
    (hw : ∀ j ∈ w, ∀ k ∈ j, 1 ≤ k) (hw₁ : w.head? ≠ some (some 1)) :
    tbzQMZV w = (tbzToSZ w).sum fun v c => c • szQMZV v

/-- **SZ-qMZVs in the TBZ model.** Let $k = (k_1, \dots, k_r)$ be an index of natural numbers
that is empty or has $k_1 \ge 1$. Let $V_{TBZ}(k) = \sum_w c_w\, w$ be the formal
$\mathbb{Q}$-linear combination of TBZ words (words in the letters $\bar 1$ and $j \ge 1$; write
$z_a$ for the one-letter word $a$) obtained by replacing each letter $k_i = 0$ by
$z_1 - z_{\bar 1}$ and each letter $k_i \ge 1$ by $\sum_{j=1}^{k_i} (-1)^{k_i - j} z_{j'}$, where
$j' = \bar 1$ for $j = 1$ and $j' = j$ otherwise, and multiplying out by concatenation of words.
Then the Schlesinger–Zudilin qMZV of $k$ is the corresponding combination of
Takeyama–Bradley–Zhao qMZVs: $\zeta_q^{SZ}(k) = \sum_w c_w\, \zeta_q^{TBZ}(w)$, that is,
$\zeta_q^{SZ}(k) = \zeta_q^{TBZ}(V_{TBZ}(k))$ with $\zeta_q^{TBZ}$ extended
$\mathbb{Q}$-linearly.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 9 (ii) (`integers-2024-A6-prop-9`). -/
public theorem_wanted szQMZV_eq_sum_tbzQMZV_szToTBZ (k : List ℕ) (hk₁ : ∀ a ∈ k.head?, 1 ≤ a) :
    szQMZV k = (szToTBZ k).sum fun w c => c • tbzQMZV w

/-- **Duality for TBZ-qMZVs.** Let $w$ be a TBZ word: each letter is either $\bar 1$ or a natural
number $k \ge 1$, and the first letter is not the number $1$. Let $U_{TBZ}(w) = \sum_v c_v\, v$ be
the formal $\mathbb{Q}$-linear combination of SZ indices obtained by replacing each letter $\bar 1$
by $1$ and each letter $k$ by $k$ or by $k - 1$, summed over all choices. For an SZ index
$u = (u_1, \dots, u_s)$ of natural numbers, let $V_{TBZ}(u) = \sum_x d_{u,x}\, x$ be the formal
$\mathbb{Q}$-linear combination of TBZ words obtained by replacing each letter $u_i = 0$ by
$z_1 - z_{\bar 1}$ and each letter $u_i \ge 1$ by $\sum_{j=1}^{u_i} (-1)^{u_i - j} z_{j'}$, where
$z_a$ is the one-letter word $a$, $j' = \bar 1$ for $j = 1$ and $j' = j$ otherwise, and
multiplying out by concatenation of words. Then the Takeyama–Bradley–Zhao qMZVs satisfy
$$
\zeta_q^{TBZ}(w) = \sum_v c_v \sum_x d_{v^\dagger, x}\, \zeta_q^{TBZ}(x),
$$
where $v^\dagger$ is the SZ dual index of $v$; that is,
$\zeta_q^{TBZ} = \zeta_q^{TBZ} \circ V_{TBZ} \circ \tilde\tau \circ U_{TBZ}$ on such words, where
$\tilde\tau$ is the dual-index map and $V_{TBZ}$, $\tilde\tau$ and $\zeta_q^{TBZ}$ are extended
$\mathbb{Q}$-linearly.

Source: Benjamin Brindle, *A Unified Approach to qMZVs*, INTEGERS 24 (2024), Article A6,
Proposition 8 (after Takeyama) (`integers-2024-A6-prop-8`). -/
public theorem_wanted tbzQMZV_eq_sum_tbzQMZV_szToTBZ_szDual (w : List (Option ℕ))
    (hw : ∀ j ∈ w, ∀ k ∈ j, 1 ≤ k) (hw₁ : w.head? ≠ some (some 1)) :
    tbzQMZV w = ((tbzToSZ w).mapDomain szDualIndex).sum fun v c =>
      c • (szToTBZ v).sum fun u d => d • tbzQMZV u

end

end MetaMathlibExt
