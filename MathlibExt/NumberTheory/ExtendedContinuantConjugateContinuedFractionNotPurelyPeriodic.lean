/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ContinuedFractions.LagrangePeriodic

/-!
# The conjugate continued fraction is not purely periodic

For integers `P`, `Q` and `D` with `0 < D` not a perfect square and `0 < Q`, the simple
continued fraction of the conjugate `(P - √D) / Q` is not purely periodic
(`MetaMathlibExt.conjugate_continuedFraction_not_purelyPeriodic`): there is no period `s ≥ 1`
with `a_{n+s} = a_n` for every `n ≥ 0`, where the partial quotients `a_n` include
`a_0 = ⌊(P - √D) / Q⌋`.

The theorem is proved in `MathlibExt.NumberTheory.ContinuedFractions.LagrangePeriodic`, beside the
complete quotients `cfXi`, the convergents `cfP` and `cfQ` and the Möbius identity `cfMobius` of
the proof of Lagrange's theorem on periodic continued fractions, which it reuses. This module
re-exports it under its original import path.

Statements from Dixon J. Jones, *Extended Continuants and Bi-infinite Periodic Continued
Fractions*, INTEGERS 26 (2026), Article A73.
-/
