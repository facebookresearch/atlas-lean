/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.EisensteinRamanujanCongruence
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.NumberTheory.ArithmeticFunction.Misc
public import Mathlib.NumberTheory.Bernoulli
public import Mathlib.RingTheory.PowerSeries.PiTopology
public import Mathlib.Topology.Instances.Rat

/-!
# Explicit Ramanujan-type congruences between Eisenstein series and cusp forms (Lu)

Statements from Qing Lu, *Explicit Congruences for Modular Forms of Higher Weights*, Journal of
Integer Sequences 29 (2026), Article 26.5.1.

All modular forms are handled through their `q`-expansion coefficients, following Section 2 of
the paper: `σ_{w-1}(n)` is the divisor sum for `n ≥ 1`, `σ_{w-1}(0) = -B_w/(2w)` for even
`w ≥ 4`, and weight `0` gives `σ_{-1}(n) = [n = 0]`, so `G_w = ∑_n σ_{w-1}(n) q^n` and
`E_w = G_w / σ_{w-1}(0)`. `Δ = q ∏_{n ≥ 1} (1 - q^n)^{24}` (in `ℚ⟦X⟧`, `∏'` in the
coefficientwise topology), so `τ^{*i} * σ_{w-1}` (additive convolution) is the coefficient
sequence of `Δ^i G_w`. `N_w` is the numerator of `|σ_{w-1}(0)|` (`N_0 = N_2 = 1`), and
`N'_k` is the largest divisor of `N_k` coprime to every `N_{k-12i}`, `1 ≤ i ≤ ⌊k/12⌋`.
A congruence `a ≡ b (mod N)` between rationals means that `(a - b)/N` has denominator coprime
to `N`; a congruence of `q`-series is coefficientwise.
-/

open PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

@[expose] public section

end

end MetaMathlibExt
