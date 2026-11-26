/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.LaurentCartierCongruence

/-!
# Kohen's linear representation step modulo a prime

`MetaMathlibExt.coeff_pow_modEq_sum_gamma_mul_V` expresses the coefficients of $P^{pn+k}$
on a bounded exponent box in terms of those of $P^n$ on the same box, modulo $p$.
-/

namespace MetaMathlibExt

open AddMonoidAlgebra

/-- **Kohen's linear representation step modulo $p$.** Let $p$ be a prime, let $P$ be a Laurent
polynomial in $r$ variables with integer coefficients, and write $\deg P$ for the largest absolute
value of an exponent of a single variable in a monomial occurring in $P$ ($0$ if $P = 0$). Let $m$
be a natural number with $\deg P \le m + 1$. Write $T = [-m, m]^r \subseteq \mathbb{Z}^r$ and
$[x^e]F$ for the coefficient of $x^e$ in a Laurent polynomial $F$. Then for every natural number
$k < p$, every natural number $n$ and every $i \in T$,
$$[x^{-i}]P^{pn+k} \equiv \sum_{j \in T} [x^{pj - i}]P^k \cdot [x^{-j}]P^n \pmod{p}.$$

With Kohen's $a^n_i = [x^{-i}]P^n$, $\gamma(k) = (a^k_{i-pj})_{i,j \in T}$ and
$V(n) = (a^n_i)_{i \in T}$, this is the entrywise form of $\gamma(k) V(n) = V(pn + k)$ over
$\mathbb{F}_p$.

Source: Nadav Kohen, *A Linear Representation for Constant Term Sequences mod p^a with
Applications to Uniform Recurrence*, Journal of Integer Sequences 29 (2026), Article 26.4.2,
Lemma 9 (`jis-2026-26.4.2-lem-9`). -/
public theorem coeff_pow_modEq_sum_gamma_mul_V {r p : ℕ} (hp : p.Prime)
    (P : AddMonoidAlgebra ℤ (Fin r → ℤ)) (m : ℕ) (hm : laurentDeg P ≤ m + 1) (k : ℕ)
    (hk : k < p) (n : ℕ) (i : Fin r → ℤ)
    (hi : i ∈ Fintype.piFinset fun _ : Fin r => Finset.Icc (-(m : ℤ)) m) :
    (P ^ (p * n + k)).coeff (-i) ≡
      ∑ j ∈ Fintype.piFinset (fun _ : Fin r => Finset.Icc (-(m : ℤ)) m),
        (P ^ k).coeff (p • j - i) * (P ^ n).coeff (-j) [ZMOD p] := by
  have h := constantTerm_pow_mul_modEq_laurentCartier hp P (single i 1) n k
  rw [laurentCartier_pow_mul_single_eq_sum hp P m hm k hk i hi, Finset.mul_sum,
    coeff_sum, Finsupp.finsetSum_apply] at h
  simpa only [coeff_mul_single_apply, zero_add, mul_one, Int.mul_comm] using h

end MetaMathlibExt
