/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.Enumerative.PartitionGenus
public import Mathlib.RingTheory.PowerSeries.Binomial

namespace MetaMathlibExt

@[expose] public section

open Equiv Finset

/-- **Genus generating function of pairings.** Let $g \ge 1$, and for $k \ge 0$ let
$C_{2k,[2^k]}^{(g)}$ be the number of genus-$g$ set partitions of $\{0, \dots, 2k-1\}$ into $k$
blocks of size $2$. There is a polynomial $Q^{(g)}$ with rational coefficients, of degree
$g - 1$, with $Q^{(g)}(0) = \frac{(4g)!}{2^{2g}\,(2g+1)!}$, such that, as formal power series
in $u$ over $\mathbb{Q}$,
$$\sum_{k \ge 0} C_{2k,[2^k]}^{(g)}\, u^k = u^{2g}\, Q^{(g)}(u)\, (1 - 4u)^{-(6g-1)/2}.$$

Here $(1 - 4u)^{-(6g-1)/2}$ is the binomial series $(1 + X)^r = \sum_{m \ge 0} \binom{r}{m} X^m$
with $r = -(6g-1)/2$, evaluated at $X = -4u$.

Source: Coquereaux and Zuber, *Counting Partitions by Genus: a Compendium of Results*,
Journal of Integer Sequences 27 (2024), Article 24.2.6, Proposition 11
(`jis-2024-24.2.6-prop-11`). -/
public theorem_wanted pairing_genus_generatingFunction (g : ℕ) (hg : 0 < g) :
    ∃ Q : Polynomial ℚ, Q.natDegree = g - 1 ∧
      Q.eval 0 = ((4 * g).factorial : ℚ) / (2 ^ (2 * g) * ((2 * g + 1).factorial : ℚ)) ∧
      PowerSeries.mk (fun k => (partitionGenusCount (2 * k) (Multiset.replicate k 2) g : ℚ)) =
        PowerSeries.X ^ (2 * g) * (Q : PowerSeries ℚ) *
          PowerSeries.rescale (-4 : ℚ)
            (PowerSeries.binomialSeries ℚ (-((6 * (g : ℚ) - 1) / 2)))

end

end MetaMathlibExt
