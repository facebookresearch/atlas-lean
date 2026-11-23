/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
public import MathlibExt.Algebra.DeepPowerSumCongruences.DividedPowerIdeal
import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Products over partitions with divisible multiplicities

When every multiplicity is divisible by `p ^ v`, the multiset of parts is `p ^ v` copies
of a smaller multiset. Taking products turns this repetition into a power.
-/

namespace MetaMathlibExt

/-- **Congruence of products over a partition with multiplicities divisible by $p^v$.** Let $p$
be a prime, $A$ a commutative ring and $\mathfrak{a}$ a divided-power ideal of $A$. Let
$f, g : \mathbb{N} \to A$ satisfy $f_n - g_n \in \mathfrak{a}$ for every $n \ge 1$. For a
partition $\lambda = (\lambda_1, \dots, \lambda_k)$ of a natural number $m$, write
$f_\lambda = f_{\lambda_1} \cdots f_{\lambda_k}$ and
$g_\lambda = g_{\lambda_1} \cdots g_{\lambda_k}$. If $v$ is a natural number such that every part
of $\lambda$ occurs a multiple of $p^v$ times, then $f_\lambda - g_\lambda = p^v c$ for some
$c \in \mathfrak{a}$, that is, $f_\lambda \equiv g_\lambda \bmod p^v \mathfrak{a}$.

The paper takes $v = v_p(\lambda) = \min_i v_p(\lambda_i)$, which is false: for $p = 2$,
$\lambda = (2)$, $A = \mathbb{Z}_{(2)}$, $\mathfrak{a} = (2)$, $f_n = e_n(X^2 + 2)$ and
$g_n = e_n(X^2)$, where $e_n(P)$ is the $n$-th elementary symmetric function of the roots of $P$,
$f_n \equiv g_n \bmod 2$ for all $n$ but $f_2 - g_2 = 2 \notin 4\mathbb{Z}_{(2)}$. The paper's
proof writes $\lambda = \mu^{p^v}$ in the partition monoid, which uses the multiplicity condition
stated here. The paper's symmetric functions are abstracted to arbitrary sequences $f, g$, as the
statement only uses their values.

Source: S. Anni, A. Ghitza and A. Medvedovsky, *Elementary Symmetric Functions and Deep Power-Sum
Congruences*, INTEGERS 24 (2024), Article A46, Corollary 26 (`integers-2024-A46-cor-26`). -/
public theorem multiset_prod_sub_prod_mem_of_count_dvd {p : ℕ} [Fact p.Prime]
    {A : Type*} [CommRing A] {I : Ideal A} (hI : IsDividedPowerIdeal I) (f g : ℕ → A)
    (hfg : ∀ n, 1 ≤ n → f n - g n ∈ I) {n : ℕ} (l : n.Partition) {v : ℕ}
    (hv : ∀ a ∈ l.parts, p ^ v ∣ l.parts.count a) :
    ∃ c ∈ I, (l.parts.map f).prod - (l.parts.map g).prod = (p : A) ^ v * c := by
  obtain ⟨s, hs⟩ := l.parts.exists_smul_of_dvd_count hv
  have hprod : (s.map f).prod - (s.map g).prod ∈ I := by
    apply Ideal.Quotient.eq.mp
    simp only [map_multiset_prod, Multiset.map_map]
    refine congrArg Multiset.prod (Multiset.map_congr rfl ?_)
    intro a ha
    refine Ideal.Quotient.eq.mpr (hfg a (l.parts_pos ?_))
    rw [hs]
    exact Multiset.mem_nsmul.mpr ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero, ha⟩
  simpa only [hs, Multiset.map_nsmul, Multiset.prod_nsmul, Nat.cast_pow] using
    hI.exists_pow_sub_pow_eq_mul hprod (p ^ v)

end MetaMathlibExt
