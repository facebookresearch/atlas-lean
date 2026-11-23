/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Rat.Cast.Order

/-!
# (p,q)-Patalan numbers

Formalization of the `(p,q)-Patalan numbers` concept.

Source: <https://cs.uwaterloo.ca/journals/JIS/VOL18/Richardson/rich2.tex>.
-/

namespace MetaMathlibExt

@[expose]
public section

/-- **Binomial coefficient with rational upper argument.** For a rational number $r$ and a natural
number $k$, the generalized binomial coefficient is the rational number
$\binom{r}{k} = r(r-1)\cdots(r-k+1)/k!$, which is $1$ for $k = 0$.

It is the binomial coefficient with fractional upper argument used in the $(p,q)$-Patalan
numbers.

Source: Thomas M. Richardson, "The Super Patalan Numbers," Journal of Integer Sequences 18
(2015), Article 15.3.3, <https://cs.uwaterloo.ca/journals/JIS/VOL18/Richardson/rich2.tex>;
concept `jis_sem_46b7b4c899beee2d386fd944`, statement `jis_64b108040f7dd4c159a901dc`,
source `jis_source_dcf0849efa23d51892aa79c7`. -/
def patalanGeneralizedBinomial (r : ℚ) (k : ℕ) : ℚ :=
  Finset.prod (Finset.range k) (fun i => r - (i : ℚ)) / (Nat.factorial k : ℚ)

/-- **Admissible parameters for the (p,q)-Patalan numbers.** An admissible parameter pair for the
$(p,q)$-Patalan numbers is a pair of natural numbers $p$ and $q$ with $p > 1$ and $0 < q < p$.

Source: Thomas M. Richardson, "The Super Patalan Numbers," Journal of Integer Sequences 18
(2015), Article 15.3.3, <https://cs.uwaterloo.ca/journals/JIS/VOL18/Richardson/rich2.tex>;
concept `jis_sem_46b7b4c899beee2d386fd944`, statement `jis_64b108040f7dd4c159a901dc`,
source `jis_source_dcf0849efa23d51892aa79c7`. -/
structure PQPatalanParams where
  p : ℕ
  q : ℕ
  hp : 1 < p
  hq_pos : 0 < q
  hq : q < p

/-- **The (p,q)-Patalan numbers.** For natural numbers $p$ and $q$ with $p > 1$ and $0 < q < p$,
the $(p,q)$-Patalan number with index $n \in \mathbb{N}$ is the rational number
$b(n) = -p^{2n+1} \binom{n - q/p}{n+1}$, where $\binom{r}{k} = r(r-1)\cdots(r-k+1)/k!$ is the
binomial coefficient with rational upper argument $r$.

Source: Thomas M. Richardson, "The Super Patalan Numbers," Journal of Integer Sequences 18
(2015), Article 15.3.3, <https://cs.uwaterloo.ca/journals/JIS/VOL18/Richardson/rich2.tex>;
concept `jis_sem_46b7b4c899beee2d386fd944`, statement `jis_64b108040f7dd4c159a901dc`,
source `jis_source_dcf0849efa23d51892aa79c7`. -/
def pqPatalanNumber (P : PQPatalanParams) (n : ℕ) : ℚ :=
  -((P.p : ℚ) ^ (2 * n + 1)) *
    patalanGeneralizedBinomial ((n : ℚ) - (P.q : ℚ) / (P.p : ℚ)) (n + 1)

end

end MetaMathlibExt
