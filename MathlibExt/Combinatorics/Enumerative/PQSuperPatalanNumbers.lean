/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.PQPatalanNumbers

/-!
# (p,q)-super Patalan numbers

This file formalizes a definition from Thomas M. Richardson, *The Super
Patalan Numbers*, Journal of Integer Sequences 18 (2015), Article 15.3.3.
-/

namespace MetaMathlibExt

@[expose]
public section

/-- **The (p,q)-super Patalan numbers.** For natural numbers $p$ and $q$ with $p > 1$ and
$0 < q < p$, and natural numbers $i$ and $j$, the $(p,q)$-super Patalan number is the rational
number $Q(i,j) = (-1)^j p^{2(i+j)} \binom{i - q/p}{i+j}$, where
$\binom{r}{k} = r(r-1)\cdots(r-k+1)/k!$ is the binomial coefficient with rational upper
argument $r$.

Source: Thomas M. Richardson, "The Super Patalan Numbers," Journal of Integer Sequences 18
(2015), Article 15.3.3; concept `jis_sem_6d22b6520f5edbfe81e62b58`, statement
`jis_a9d7ecad34cde5accbc27d08`.
-/
def pqSuperPatalanNumber (P : PQPatalanParams) (i j : ℕ) : ℚ :=
  (-1) ^ j * (P.p : ℚ) ^ (2 * (i + j)) *
    patalanGeneralizedBinomial ((i : ℚ) - (P.q : ℚ) / P.p) (i + j)

/-- **Super Patalan numbers of order p.** For a natural number $p > 1$ and natural numbers $i$ and
$j$, the super Patalan number of order $p$ is the $(p,q)$-super Patalan number with $q = 1$, that
is, the rational number $(-1)^j p^{2(i+j)} \binom{i - 1/p}{i+j}$, where
$\binom{r}{k} = r(r-1)\cdots(r-k+1)/k!$ is the binomial coefficient with rational upper
argument $r$. -/
def superPatalanNumber (p i j : ℕ) (hp : 1 < p) : ℚ :=
  pqSuperPatalanNumber
    { p := p, q := 1, hp := hp, hq_pos := by omega, hq := hp } i j

end

end MetaMathlibExt
