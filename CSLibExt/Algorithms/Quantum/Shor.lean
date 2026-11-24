/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Quantum.Shor.ContinuedFractions
public import CSLibExt.Algorithms.Quantum.Shor.OrderToFactor
public import CSLibExt.Algorithms.Quantum.Shor.OrderToFactorProbability

/-!
# Shor's factoring algorithm

This is the public entry point for the formalization of Shor's factoring
algorithm. So far it contains the proved classical post-processing step:
from a multiplicative order `r` of `a` modulo `N` with `r` even and
`a ^ (r / 2) ≢ ±1 (mod N)`, `gcd (a ^ (r / 2) - 1) N` is a nontrivial factor
of `N` (`gcd_factor_of_order`, with the existential form
`exists_factor_of_order`). For odd `N` with `k` distinct prime factors,
`card_units_good_for_factoring_ge` gives a lower bound of `1 - 1 / 2 ^ (k - 1)`
on the fraction of units for which this step yields a factor.

In the continued-fraction step of order finding, a fraction `d / r` with
`0 < r < n` within `1 / (2 q)` of the observed
`c / q`, where `n ^ 2 ≤ q`, is unique (`eq_of_abs_sub_le_of_lt`) and is a
convergent of the continued fraction of `c / q`
(`exists_convergent_eq_of_abs_sub_le`). The quantum order-finding subroutine
itself and the full factoring theorem are not formalized in this module.
-/
