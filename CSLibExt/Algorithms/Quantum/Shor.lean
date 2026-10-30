/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Quantum.Shor.OrderToFactor

/-!
# Shor's factoring algorithm

This is the public entry point for the formalization of Shor's factoring
algorithm. So far it contains the proved classical post-processing step:
from a multiplicative order `r` of `a` modulo `N` with `r` even and
`a ^ (r / 2) ≢ ±1 (mod N)`, `gcd (a ^ (r / 2) - 1) N` is a nontrivial factor
of `N` (`gcd_factor_of_order`, with the existential form
`exists_factor_of_order`). The quantum order-finding subroutine and the full
factoring theorem are not formalized in this module.
-/
