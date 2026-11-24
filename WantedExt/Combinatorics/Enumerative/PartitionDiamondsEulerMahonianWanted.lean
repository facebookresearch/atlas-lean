/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Data.Set.Card
public import MathlibExt.Combinatorics.Enumerative.PartitionDiamondsEulerMahonian
public import Mathlib.RingTheory.PowerSeries.Basic

namespace MetaMathlibExt

@[expose] public section

/-- **Product formula for equal-fold partition diamonds.** Let $d$ and $M$ be positive integers.
Let $\sigma_{d,M}(a, b)$ be the generating function of multifold partition diamonds of shape
$(d, \dots, d)$ ($M$ copies), where $a$ marks the fold sum and $b$ marks the link sum, and let
$E_d(x, y) = \sum_{\tau} x^{\mathrm{des}(\tau)} y^{\mathrm{maj}(\tau)}$ be the Euler–Mahonian
polynomial, summed over the permutations $\tau$ of $\{1, \dots, d\}$. Then the following
identity holds in $\mathbb{Z}[[a, b]]$:

$$\left(1 - a^{Md} b^{M+1}\right) \prod_{n=1}^{M} \prod_{j=0}^{d} \left(1 - a^{nd-j} b^{n}\right)
\cdot \sigma_{d,M}(a, b) = \prod_{n=1}^{M} E_d\left(a^{(n-1)d} b^{n}, a\right).$$

Equivalently, $\sigma_{d,M}(a, b)$ is the product of the $E_d(a^{(n-1)d} b^n, a)$ divided by
$(1 - a^{Md} b^{M+1}) \prod_{n=1}^{M} \prod_{j=0}^{d} (1 - a^{nd-j} b^n)$.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Theorem 2 (`integers-2026-A13-thm-2`). -/
public theorem_wanted partitionDiamond_genFun (d M : ℕ) (hd : 1 ≤ d) (hM : 1 ≤ M) :
    (1 - MvPowerSeries.X 0 ^ (M * d) * MvPowerSeries.X 1 ^ (M + 1)) *
        (∏ n ∈ Finset.Icc 1 M, ∏ j ∈ Finset.range (d + 1),
          (1 - MvPowerSeries.X 0 ^ (n * d - j) * MvPowerSeries.X 1 ^ n)) *
        multifoldDiamondSeries (List.replicate M d) =
      ∏ n ∈ Finset.Icc 1 M, eulerMahonian (MvPowerSeries (Fin 2) ℤ) d
        (MvPowerSeries.X 0 ^ ((n - 1) * d) * MvPowerSeries.X 1 ^ n) (MvPowerSeries.X 0)

/-- **Product formula for multifold partition diamonds.** Let $d_1, \dots, d_M$ be positive
integers with $M \ge 1$, and let $\omega_k = \sum_{m=k+1}^{M} d_m$ for $0 \le k \le M$. Let
$\sigma_{d_1, \dots, d_M}(a, b)$ be the generating function of multifold partition diamonds of
shape $(d_1, \dots, d_M)$, where $a$ marks the fold sum and $b$ marks the link sum, and let
$E_d(x, y) = \sum_{\tau} x^{\mathrm{des}(\tau)} y^{\mathrm{maj}(\tau)}$ be the Euler–Mahonian
polynomial, summed over the permutations $\tau$ of $\{1, \dots, d\}$. Then the following
identity holds in $\mathbb{Z}[[a, b]]$:

$$\left(1 - a^{\omega_0} b^{M+1}\right) \prod_{k=1}^{M} \prod_{j=0}^{d_k}
\left(1 - a^{\omega_k + d_k - j} b^{M-k+1}\right) \cdot \sigma_{d_1, \dots, d_M}(a, b) =
\prod_{k=1}^{M} E_{d_k}\left(a^{\omega_k} b^{M-k+1}, a\right).$$

The $k$th diamond (with $d_k$ folds) is the $k$th from the smallest part, as in the paper's poset
$\{1\} \oplus Q_{d_1} \oplus \dots \oplus Q_{d_M}$. If the parts are read in the opposite order,
the formula holds only for the reversed sequence: for $(d_1, d_2) = (1, 2)$ the coefficient of
$ab$ would be $1$, not $2$.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Theorem 3 (`integers-2026-A13-thm-3`). -/
public theorem_wanted multifoldPartitionDiamond_genFun (ds : List ℕ) (hds : ds ≠ [])
    (hpos : ∀ d ∈ ds, 1 ≤ d) :
    (1 - MvPowerSeries.X 0 ^ ds.sum * MvPowerSeries.X 1 ^ (ds.length + 1)) *
        (∏ k ∈ Finset.Icc 1 ds.length, ∏ j ∈ Finset.range (ds.getD (k - 1) 0 + 1),
          (1 - MvPowerSeries.X 0 ^ ((ds.drop k).sum + ds.getD (k - 1) 0 - j) *
            MvPowerSeries.X 1 ^ (ds.length - k + 1))) *
        multifoldDiamondSeries ds =
      ∏ k ∈ Finset.Icc 1 ds.length, eulerMahonian (MvPowerSeries (Fin 2) ℤ) (ds.getD (k - 1) 0)
        (MvPowerSeries.X 0 ^ (ds.drop k).sum * MvPowerSeries.X 1 ^ (ds.length - k + 1))
        (MvPowerSeries.X 0)

/-- **Generating function of Schmidt type $d$-fold partition diamonds.** Let $d \ge 1$. A Schmidt
type $d$-fold partition diamond is a finitely supported sequence $(a_p)_{p \ge 0}$ of natural
numbers such that $a_{k(d+1)} \ge a_{k(d+1)+f} \ge a_{(k+1)(d+1)}$ for all $k \ge 0$ and all
$f$ with $1 \le f \le d$; its weight is the sum of its links $a_{k(d+1)}$, $k \ge 0$. Let
$s_d(w)$ be the number of such diamonds of weight $w$, and let
$S_d(q) = \sum_{w \ge 0} s_d(w) q^w \in \mathbb{Z}[[q]]$. Then for all natural numbers $n \le N$,
the coefficient of $q^n$ in $S_d(q) \prod_{m=1}^{N} (1 - q^m)^{d+1}$ equals the coefficient of
$q^n$ in $\prod_{m=1}^{N} E_d(q^m, 1)$, where $E_d$ is the Euler–Mahonian polynomial.

Since every factor $E_d(q^m, 1)/(1 - q^m)^{d+1}$ with $m > N$ is $1$ modulo $q^{N+1}$, the
statement for all $N$ is equivalent to $S_d(q) = \prod_{m \ge 1} E_d(q^m, 1)/(1 - q^m)^{d+1}$.

Source: Matthias Beck and Kobe Wijesekera, *MacMahon's Double Vision: Partition Diamonds
Revisited*, INTEGERS 26 (2026), Article A13, Corollary 1 (`integers-2026-A13-cor-1`), quoting
Dockery-Jameson-Sellers-Wilson. -/
public theorem_wanted schmidtPartitionDiamond_genFun (d : ℕ) (hd : 1 ≤ d) (N n : ℕ)
    (hn : n ≤ N) :
    PowerSeries.coeff n
        ((∏ m ∈ Finset.Icc 1 N, (1 - PowerSeries.X ^ m) ^ (d + 1)) *
          PowerSeries.mk fun w => ((Set.ncard {a : ℕ →₀ ℕ |
            (∀ k f : ℕ, 1 ≤ f → f ≤ d →
              a (k * (d + 1) + f) ≤ a (k * (d + 1)) ∧
                a ((k + 1) * (d + 1)) ≤ a (k * (d + 1) + f)) ∧
            (a.support.filter fun p => p % (d + 1) = 0).sum a = w} : ℕ) : ℤ)) =
      PowerSeries.coeff n
        (∏ m ∈ Finset.Icc 1 N, eulerMahonian (PowerSeries ℤ) d (PowerSeries.X ^ m) 1)

end

end MetaMathlibExt
