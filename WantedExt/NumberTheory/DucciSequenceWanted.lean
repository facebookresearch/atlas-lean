/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The maximum length for Ducci sequences on `ℤ_m^n` when `n` is even

Statements from Mark L. Lewis and Shannon M. Tefft, "The
Maximum Length for Ducci Sequences on `ℤ_m^n` when `n`
is Even", *INTEGERS* 26 (2026), Article A17
(<https://math.colgate.edu/~integers/aa17/aa17.pdf>).

The Ducci map on `ℤ_m^n` is `D(x)_i = x_i + x_{i+1}`
(indices cyclically); `ducciCoeff n r s` is the paper's
coefficient `a_{r,s}` of `x_s` in the first entry of
`D^r(x)`, i.e. `∑_{j ≡ s-1 (mod n)} C(r, j)` (equal to
`C(r, s-1)` for `r < n`, as the paper notes). Lemma 2 is
stated with upper index `p^k - p^{k-1}`: the extracted
`p^k - p^{k-1} - 1` gives binomial coefficients that are
never `0 mod p` on the checked grid, while with
`p^k - p^{k-1}` the stated case values hold for all
checked `p, k` and `j ≤ p^k - p^{k-1}` (it is the
Lucas-theorem computation); the range hypothesis is
necessary, since for `j` above the upper index the
binomial coefficient vanishes while the case value does
not (e.g. `p = 3`, `k = 2`, `j = 9`).
All statements were verified numerically (binomial
congruences for `p ≤ 7`; the predecessor criterion by
brute force for `m ∈ {2, 3, 4, 6}`, `n ∈ {2, 4}`).
Theorem 1, on the maximum length `L_m(n)`, is not
stated: the definition of `L_m(n)` is not recoverable
from the extracted statements (see the source audit table).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

@[expose] public section

namespace MathlibExt.NumberTheory.DucciWanted

/-- **Ducci coefficients.** For natural numbers $n$, $r$ and $s$, the Ducci coefficient is
$a_{r,s} = \sum_{0 \le j \le r,\ j \equiv s - 1 \ (\mathrm{mod}\ n)} \binom{r}{j}$, where $s - 1$
is read as $0$ when $s = 0$ and congruence modulo $0$ is equality.

For $1 \le s \le n$, $a_{r,s}$ is the coefficient of $x_s$ in the first entry of $D^r(x)$, where
the Ducci map $D$ on $\mathbb{Z}_m^n$ sends $(x_1, \dots, x_n)$ to
$(x_1 + x_2, x_2 + x_3, \dots, x_n + x_1)$. -/
def ducciCoeff (n r s : ℕ) : ℕ :=
  ∑ j ∈ (Finset.range (r + 1)).filter
    (fun j => j % n = (s - 1) % n), Nat.choose r j

/-- **Binomial coefficients $\binom{p^k - 1}{j}$ modulo $p$.** Let $p$ be a prime, let $k \ge 1$,
and let $j$ be an integer with $0 \le j \le p^k - 1$. Then
$\binom{p^k - 1}{j} \equiv (-1)^j \pmod{p}$.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
Lemma 1. -/
theorem_wanted choose_prime_pow_sub_one_mod (p k j : ℕ)
    (hp : p.Prime) (hk : 1 ≤ k) (hj : j ≤ p ^ k - 1) :
    ((Nat.choose (p ^ k - 1) j : ℤ) : ZMod p) = (-1) ^ j

/-- **Binomial coefficients $\binom{p^k - p^{k-1}}{j}$ modulo $p$.** Let $p$ be an odd prime,
let $k \ge 2$, and let $j$ be an integer with $0 \le j \le p^k - p^{k-1}$. If $j = c\,p^{k-1}$
for an integer $c$, then $\binom{p^k - p^{k-1}}{j} \equiv (-1)^c \pmod{p}$; otherwise
$\binom{p^k - p^{k-1}}{j} \equiv 0 \pmod{p}$.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
Lemma 2. -/
theorem_wanted choose_prime_pow_sub_mod (p k j : ℕ)
    (hp : p.Prime) (hpo : p ≠ 2) (hk : 2 ≤ k)
    (hj : j ≤ p ^ k - p ^ (k - 1)) :
    ((Nat.choose (p ^ k - p ^ (k - 1)) j : ℤ) : ZMod p) =
      if j % p ^ (k - 1) = 0 then (-1) ^ (j / p ^ (k - 1))
      else 0

/-- **Vanishing of Ducci coefficients modulo $p$.** For integers $N \ge 1$, $r \ge 0$ and $s \ge 1$
write $a^{(N)}_{r,s} = \sum_{0 \le j \le r,\ j \equiv s - 1 \ (\mathrm{mod}\ N)} \binom{r}{j}$ for
the Ducci coefficients of length $N$. Let $p$ be a prime, let $k \ge 0$ and $n_1 \ge 2$ be
integers, and let $n = p^k n_1$. Let $c \ge 1$, and let $s$ be an integer with $1 \le s \le n$
that is not of the form $b\,p^k + 1$ with $0 \le b < n_1$. Then
$a^{(n)}_{c p^k, s} \equiv 0 \pmod{p}$.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
Lemma 3. -/
theorem_wanted ducciCoeff_vanish_mod (p k n1 c s : ℕ)
    (hp : p.Prime) (hn1 : 2 ≤ n1) (hc : 1 ≤ c)
    (hs1 : 1 ≤ s) (hs2 : s ≤ p ^ k * n1)
    (hs : ¬ ∃ b : ℕ, b < n1 ∧ s = b * p ^ k + 1) :
    ((ducciCoeff (p ^ k * n1) (c * p ^ k) s : ℤ) : ZMod p) = 0

/-- **Reduction of Ducci coefficients modulo $p$.** For integers $N \ge 1$, $r \ge 0$ and $s \ge 1$
write $a^{(N)}_{r,s} = \sum_{0 \le j \le r,\ j \equiv s - 1 \ (\mathrm{mod}\ N)} \binom{r}{j}$ for
the Ducci coefficients of length $N$. Let $p$ be a prime, let $k \ge 0$ and $n_1 \ge 2$ be
integers, and let $n = p^k n_1$. Then for every integer $c \ge 1$ and every integer $b$ with
$0 \le b < n_1$,
$a^{(n)}_{c p^k,\, b p^k + 1} \equiv a^{(n_1)}_{c,\, b + 1} \pmod{p}$.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
Lemma 4. -/
theorem_wanted ducciCoeff_reduce_mod (p k n1 c b : ℕ)
    (hp : p.Prime) (hn1 : 2 ≤ n1) (hc : 1 ≤ c) (hb : b < n1) :
    ((ducciCoeff (p ^ k * n1) (c * p ^ k) (b * p ^ k + 1) : ℤ) :
      ZMod p) =
      ((ducciCoeff n1 c (b + 1) : ℤ) : ZMod p)

/-- **Ducci predecessor criterion for even length.** Let $m \ge 0$ be an integer, let $n \ge 2$ be
even, and write $\mathbb{Z}_m = \mathbb{Z}/m\mathbb{Z}$ (so $\mathbb{Z}_0 = \mathbb{Z}$). A tuple
$x = (x_1, \dots, x_n) \in \mathbb{Z}_m^n$ has a Ducci predecessor, that is, a tuple
$y \in \mathbb{Z}_m^n$ with $y_i + y_{i+1} = x_i$ for all $i$ (indices taken cyclically, so
$y_{n+1} = y_1$), if and only if $x_1 - x_2 + x_3 - \cdots + x_{n-1} - x_n = 0$ in $\mathbb{Z}_m$.

Source: Mark L. Lewis and Shannon M. Tefft, "The Maximum
Length for Ducci Sequences on `ℤ_m^n` when `n` is Even",
Theorem 2. -/
theorem_wanted ducci_pred_iff (m n : ℕ) [NeZero n]
    (hn : Even n) (x : Fin n → ZMod m) :
    (∃ y : Fin n → ZMod m, ∀ i : Fin n, y i + y (i + 1) = x i) ↔
      ∑ i : Fin n, (-1 : ZMod m) ^ i.val * x i = 0

end MathlibExt.NumberTheory.DucciWanted
