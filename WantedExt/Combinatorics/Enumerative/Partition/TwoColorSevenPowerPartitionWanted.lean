/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import Mathlib.RingTheory.PowerSeries.Inverse
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Instances.Rat
public import MathlibExt.Combinatorics.Enumerative.Partition.TwoColorSevenPowerPartition
public import MathlibExt.Combinatorics.Enumerative.Partition.TwoColorSevenPowerPartitionSevenPowDvdGarvanYEven

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

/-- **Congruences for two-color partitions modulo powers of 7.** For all natural numbers $n$,
$\beta$ and $k \ge 1$, the two-color partition count $p_{1,\ell}$ satisfies
$$
p_{1,7^{2k-1}}(7^{2k+\beta-1} n + (16 \cdot 7^{2k+\beta-1} + 7^{2k-1} + 1)/24)
\equiv 0 \pmod{7^k},
$$
$$
p_{1,7^{2k}}(7^{2k+2\beta-1} n + (10 \cdot 7^{2k+2\beta-1} + 7^{2k} + 1)/24)
\equiv 0 \pmod{7^{k+\beta}},
$$
$$
p_{1,7^{2k}}(7^{2k+2\beta} n + (22 \cdot 7^{2k+2\beta} + 7^{2k} + 1)/24)
\equiv 0 \pmod{7^{k+\beta+1}},
$$
and, for each $r \in \{3, 4, 6\}$,
$$
p_{1,7^{2k}}(7^{2k+2\beta+1} n + ((24r + 22) \cdot 7^{2k+2\beta} + 7^{2k} + 1)/24)
\equiv 0 \pmod{7^{k+\beta+2}}.
$$
Each numerator is divisible by $24$, so every division above is exact.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Theorem 1 (`integers-2026-A94-thm-1`), congruences (6)-(9). -/
public theorem_wanted twoColorMultiplePartitionCount_seven_pow_congr (k β n : ℕ) (hk : 1 ≤ k) :
    7 ^ k ∣ twoColorMultiplePartitionCount (7 ^ (2 * k - 1))
        (7 ^ (2 * k + β - 1) * n + (16 * 7 ^ (2 * k + β - 1) + 7 ^ (2 * k - 1) + 1) / 24) ∧
    7 ^ (k + β) ∣ twoColorMultiplePartitionCount (7 ^ (2 * k))
        (7 ^ (2 * k + 2 * β - 1) * n + (10 * 7 ^ (2 * k + 2 * β - 1) + 7 ^ (2 * k) + 1) / 24) ∧
    7 ^ (k + β + 1) ∣ twoColorMultiplePartitionCount (7 ^ (2 * k))
        (7 ^ (2 * k + 2 * β) * n + (22 * 7 ^ (2 * k + 2 * β) + 7 ^ (2 * k) + 1) / 24) ∧
    ∀ r ∈ ({3, 4, 6} : Finset ℕ), 7 ^ (k + β + 2) ∣ twoColorMultiplePartitionCount (7 ^ (2 * k))
        (7 ^ (2 * k + 2 * β + 1) * n +
          ((24 * r + 22) * 7 ^ (2 * k + 2 * β) + 7 ^ (2 * k) + 1) / 24)

/-- **Garvan's huffing identities for powers of $\xi$.** Let
$f_k = \prod_{n \ge 1} (1 - q^{kn})$ in $\mathbb{Q}[[q]]$, let $H$ be the huffing operator
$H\bigl(\sum_n p_n q^n\bigr) = \sum_n p_{7n} q^{7n}$, and let $m_{i,j}$ be Garvan's matrix. Write
$\xi^{-a} = q^{2a} f_{49}^a / f_1^a$ and $T^{-b} = q^{7b} f_{49}^{4b} / f_7^{4b}$ for the
negative powers of $\xi = f_1 / (q^2 f_{49})$ and $T = f_7^4 / (q^7 f_{49}^4)$, which are formal
power series. For every $i \ge 1$,
$$H(\xi^{-i}) = \sum_{j=1}^{2i} m_{i,j}\, T^{-j}$$
and
$$H(\xi^{-4i}) = \sum_{j=1}^{7i} m_{4i,i+j}\, T^{-i-j}.$$
These are identities of formal power series over $\mathbb{Q}$. The sums stop at $j = 2i$,
resp. $j = 7i$, beyond which the coefficients $m$ vanish.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Lemma 1 (`integers-2026-A94-lem-1`). -/
public theorem_wanted huffing_xi_inv_pow_eq_sum_garvanM (i : ℕ) (hi : 1 ≤ i) :
    let f : ℕ → ℚ⟦X⟧ := fun k => ∏' n : ℕ, (1 - X ^ (k * (n + 1)))
    let H : ℚ⟦X⟧ → ℚ⟦X⟧ := fun F => PowerSeries.mk fun n => if 7 ∣ n then coeff n F else 0
    let ξinv : ℕ → ℚ⟦X⟧ := fun a => X ^ (2 * a) * f 49 ^ a * (f 1 ^ a)⁻¹
    let Tinv : ℕ → ℚ⟦X⟧ := fun b => X ^ (7 * b) * f 49 ^ (4 * b) * (f 7 ^ (4 * b))⁻¹
    H (ξinv i) = ∑ j ∈ Finset.Icc 1 (2 * i), (garvanM i j : ℚ⟦X⟧) * Tinv j ∧
      H (ξinv (4 * i)) = ∑ j ∈ Finset.Icc 1 (7 * i), (garvanM (4 * i) (i + j) : ℚ⟦X⟧) * Tinv (i + j)

/-- **Huffing identities for three eta quotients.** Let
$f_k = \prod_{n \ge 1} (1 - q^{kn})$ in $\mathbb{Q}[[q]]$, let $H$ be the huffing operator
$H\bigl(\sum_n p_n q^n\bigr) = \sum_n p_{7n} q^{7n}$, and let $m_{i,j}$ be Garvan's matrix. For
every $i \ge 1$,
$$H\Bigl(\frac{q^{i+2} f_7^{4i}}{f_1^{4i+1}}\Bigr)
= \sum_{j=1}^{7i+4} m_{4i+1,i+j}\, \frac{q^{7j} f_{49}^{4j-1}}{f_7^{4j}},$$
$$H\Bigl(\frac{q^{i+4} f_7^{4i}}{f_1^{4i+2}}\Bigr)
= \sum_{j=1}^{7i+4} m_{4i+2,i+j}\, \frac{q^{7j} f_{49}^{4j-2}}{f_7^{4j}},$$
$$H\Bigl(\frac{q^{i} f_7^{4i}}{f_1^{4i}}\Bigr)
= \sum_{j=1}^{7i+4} m_{4i,i+j}\, \frac{q^{7j} f_{49}^{4j}}{f_7^{4j}}.$$
These are identities of formal power series over $\mathbb{Q}$. The sums stop at $j = 7i + 4$,
beyond which the coefficients $m$ vanish.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Lemma 2 (`integers-2026-A94-lem-2`). -/
public theorem_wanted huffing_eta_quotients_eq_sum_garvanM (i : ℕ) (hi : 1 ≤ i) :
    let f : ℕ → ℚ⟦X⟧ := fun k => ∏' n : ℕ, (1 - X ^ (k * (n + 1)))
    let H : ℚ⟦X⟧ → ℚ⟦X⟧ := fun F => PowerSeries.mk fun n => if 7 ∣ n then coeff n F else 0
    H (X ^ (i + 2) * f 7 ^ (4 * i) * (f 1 ^ (4 * i + 1))⁻¹) =
        ∑ j ∈ Finset.Icc 1 (7 * i + 4), (garvanM (4 * i + 1) (i + j) : ℚ⟦X⟧) *
          (X ^ (7 * j) * f 49 ^ (4 * j - 1) * (f 7 ^ (4 * j))⁻¹) ∧
      H (X ^ (i + 4) * f 7 ^ (4 * i) * (f 1 ^ (4 * i + 2))⁻¹) =
        ∑ j ∈ Finset.Icc 1 (7 * i + 4), (garvanM (4 * i + 2) (i + j) : ℚ⟦X⟧) *
          (X ^ (7 * j) * f 49 ^ (4 * j - 2) * (f 7 ^ (4 * j))⁻¹) ∧
      H (X ^ i * f 7 ^ (4 * i) * (f 1 ^ (4 * i))⁻¹) =
        ∑ j ∈ Finset.Icc 1 (7 * i + 4), (garvanM (4 * i) (i + j) : ℚ⟦X⟧) *
          (X ^ (7 * j) * f 49 ^ (4 * j) * (f 7 ^ (4 * j))⁻¹)

/-- **7-adic bounds for the vectors $y^{(2k-1)}_\beta$.** Let $y^{(2k-1)}_\beta$ be the
coefficient vectors for odd powers of $7$, built from Garvan's vectors and matrix. For all
$k, j \ge 1$ and $\beta \ge 0$, $7^{k + \lfloor (7j-7)/4 \rfloor}$ divides $y^{(2k-1)}_{\beta+1,j}$.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Lemma 6 (`integers-2026-A94-lem-6`). -/
public theorem_wanted seven_pow_dvd_garvanYOdd (k β j : ℕ) (hk : 1 ≤ k) (hj : 1 ≤ j) :
    7 ^ (k + (7 * j - 7) / 4) ∣ garvanYOdd k (β + 1) j

/-- **Generating functions for $p_{1,7^{2k-1}}$ on progressions.** Let $p_{1,\ell}(n)$ be the
number of 2-color partitions of $n$ in which the parts of the second color are multiples of
$\ell$, let $f_k = \prod_{n \ge 1} (1 - q^{kn})$ in $\mathbb{Q}[[q]]$, and let $y^{(2k-1)}_\beta$
be the coefficient vectors for odd powers of $7$. For all $k \ge 1$ and $\beta \ge 0$, with
$N = 7^{2k+\beta-1}$,
$$\sum_{n \ge 0} p_{1,7^{2k-1}}\Bigl(N n + \frac{16 N + 7^{2k-1} + 1}{24}\Bigr) q^n
= \sum_{i=1}^{N} y^{(2k-1)}_{\beta+1,i}\, q^{i-1} \frac{f_7^{4i-1}}{f_1^{4i+1}}$$
as formal power series over $\mathbb{Q}$.

The numerator $16 N + 7^{2k-1} + 1$ is divisible by $24$. The sum over $i$ stops at $N$, above
the support of $y^{(2k-1)}_{\beta+1}$.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Theorem 2 (`integers-2026-A94-thm-2`). -/
public theorem_wanted twoColorMultiplePartitionCount_seven_pow_odd_generatingFunction
    (k β : ℕ) (hk : 1 ≤ k) :
    let f : ℕ → ℚ⟦X⟧ := fun k => ∏' n : ℕ, (1 - X ^ (k * (n + 1)))
    PowerSeries.mk (fun n => (twoColorMultiplePartitionCount (7 ^ (2 * k - 1))
        (7 ^ (2 * k + β - 1) * n + (16 * 7 ^ (2 * k + β - 1) + 7 ^ (2 * k - 1) + 1) / 24) : ℚ)) =
      ∑ i ∈ Finset.Icc 1 (7 ^ (2 * k + β - 1)), (garvanYOdd k (β + 1) i : ℚ⟦X⟧) *
        (X ^ (i - 1) * f 7 ^ (4 * i - 1) * (f 1 ^ (4 * i + 1))⁻¹)

/-- **Generating functions for $p_{1,7^{2k}}$ on progressions.** Let $p_{1,\ell}(n)$ be the
number of 2-color partitions of $n$ in which the parts of the second color are multiples of
$\ell$, let $f_k = \prod_{n \ge 1} (1 - q^{kn})$ in $\mathbb{Q}[[q]]$, and let $y^{(2k)}_\beta$ be
the coefficient vectors for even powers of $7$. For all $k \ge 1$ and $\beta \ge 0$, with
$N = 7^{2k+2\beta-1}$,
$$\sum_{n \ge 0} p_{1,7^{2k}}\Bigl(N n + \frac{10 N + 7^{2k} + 1}{24}\Bigr) q^n
= \sum_{i=1}^{7N} y^{(2k)}_{2\beta+1,i}\, q^{i-1} \frac{f_7^{4i-2}}{f_1^{4i}}$$
and
$$\sum_{n \ge 0} p_{1,7^{2k}}\Bigl(7N n + \frac{22 \cdot 7N + 7^{2k} + 1}{24}\Bigr) q^n
= \sum_{j=1}^{49N} y^{(2k)}_{2\beta+2,j}\, q^{j-1} \frac{f_7^{4j}}{f_1^{4j+2}}$$
as formal power series over $\mathbb{Q}$.

Both numerators are divisible by $24$. The sums stop at $7N$, resp. $49N$, above the supports of
the vectors.

Source: D. S. Gireesh, C. Shivashankar, and B. Hemanthkumar, *On 2-Color Partitions in Which
the Parts of One Color Are Restricted to Multiples of 7^k*, INTEGERS 26 (2026), Article A94,
Theorem 3 (`integers-2026-A94-thm-3`). -/
public theorem_wanted twoColorMultiplePartitionCount_seven_pow_even_generatingFunction
    (k β : ℕ) (hk : 1 ≤ k) :
    let f : ℕ → ℚ⟦X⟧ := fun k => ∏' n : ℕ, (1 - X ^ (k * (n + 1)))
    PowerSeries.mk (fun n => (twoColorMultiplePartitionCount (7 ^ (2 * k))
        (7 ^ (2 * k + 2 * β - 1) * n + (10 * 7 ^ (2 * k + 2 * β - 1) + 7 ^ (2 * k) + 1) / 24) :
          ℚ)) =
        ∑ i ∈ Finset.Icc 1 (7 ^ (2 * k + 2 * β)), (garvanYEven k (2 * β + 1) i : ℚ⟦X⟧) *
          (X ^ (i - 1) * f 7 ^ (4 * i - 2) * (f 1 ^ (4 * i))⁻¹) ∧
      PowerSeries.mk (fun n => (twoColorMultiplePartitionCount (7 ^ (2 * k))
        (7 ^ (2 * k + 2 * β) * n + (22 * 7 ^ (2 * k + 2 * β) + 7 ^ (2 * k) + 1) / 24) : ℚ)) =
        ∑ j ∈ Finset.Icc 1 (7 ^ (2 * k + 2 * β + 1)), (garvanYEven k (2 * β + 2) j : ℚ⟦X⟧) *
          (X ^ (j - 1) * f 7 ^ (4 * j) * (f 1 ^ (4 * j + 2))⁻¹)

end

end MetaMathlibExt
