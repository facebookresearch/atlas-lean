/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Quantum.ShorGoodUnits

/-!
# Success probability of Shor's order-to-factor reduction

For an odd modulus with `k` distinct prime factors, `Cslib.Shor.card_units_good_for_factoring_ge`
gives the lower bound `1 - 1 / 2 ^ (k - 1)` on the fraction of units with even order `r` and
half-order power different from `-1`.
-/
