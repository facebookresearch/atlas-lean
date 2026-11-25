/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Polynomial.Basic

/-!
# Morgan-Voyce polynomials

Formalizes the Morgan-Voyce polynomial family (OEIS A085478) whose coefficient
array is the Riordan array `(1 / (1 - x), x / (1 - x) ^ 2)`.

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL27/Brietzke/bri3.tex>.
-/

@[expose] public section

namespace MetaMathlibExt

/-- **Morgan–Voyce coefficients.** For natural numbers $n$ and $k$, the Morgan–Voyce coefficient
$d(n, k)$ is the binomial coefficient $\binom{n + k}{n - k}$ if $k \le n$, and $0$ if $k > n$.

These numbers form the lower-triangular Riordan array
$\left(\frac{1}{1 - x}, \frac{x}{(1 - x)^2}\right)$, OEIS A085478.

Source: statement `jis_9df126595a4035315bd915ac`,
concept `jis_sem_455f7ec0e8ec92a0f271843b`. -/
def morganVoyceCoeff (n k : ℕ) : ℕ :=
  if k ≤ n then (n + k).choose (n - k) else 0

/-- **Morgan–Voyce polynomials.** For a semiring $R$ and a natural number $n$, the Morgan–Voyce
polynomial of index $n$ over $R$ is
$$b_n(x) = \sum_{k=0}^{n} d(n, k)\, x^k \in R[x],$$
where $d(n, k) = \binom{n + k}{n - k}$ is the Morgan–Voyce coefficient, read in $R$ through the
map from the natural numbers.

The coefficients of $b_n$ form row $n$ of the Riordan array
$\left(\frac{1}{1 - x}, \frac{x}{(1 - x)^2}\right)$, OEIS A085478.

Source: statement `jis_9df126595a4035315bd915ac`,
concept `jis_sem_455f7ec0e8ec92a0f271843b` (OEIS A085478). -/
noncomputable def morganVoycePolynomial (R : Type*) [Semiring R] (n : ℕ) :
    Polynomial R :=
  Finset.sum (Finset.range (n + 1)) fun k =>
    Polynomial.C ((morganVoyceCoeff n k : ℕ) : R) * Polynomial.X ^ k

end MetaMathlibExt

end
