/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
public import Mathlib.NumberTheory.LSeries.RiemannZeta
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-! # Constancy of an infinite cyclotomic product

Statement-only request for Bal's theorem that `∏_{n ≥ 1} Φ̂ₙ(z)^{-1/n} ≡ 1` on the open unit
disk, where `Φ̂ₙ(z) = ∏_{ζ primitive n-th root of unity} (1 - z ζ)`.
-/

open Filter Topology

namespace MetaMathlibExt

@[expose] public section

/-- For every complex `z` with `‖z‖ < 1`, the partial products
`∏_{n=1}^{N} Φ̂ₙ(z)^{-1/n}` tend to `1` as `N → ∞`, where
`Φ̂ₙ(z) = ∏_{ζ primitive n-th root of unity} (1 - z ζ)` (so `Φ̂₁(z) = 1 - z` and
`Φ̂ₙ = Φₙ` for `n ≥ 2`). The `n`-th root is taken on the branch
`Φ̂ₙ(z)^{-1/n} = exp(-(1/n) ∑_ζ log(1 - z ζ))` with principal logarithms of the linear factors
(each `1 - z ζ` has positive real part), which is the branch equal to `1` at `z = 0` used in the
paper's logarithmic-derivative proof. The paper writes the product as
`P(z) = -∏_{n ≥ 1} Φₙ(z)^{-1/n}`; the sign absorbs `Φ₁(z) = -(1 - z)`, and the claim is
`P(z) ≡ 1`. Convergence is stated for the natural ordering by `n`.

Source: Hartosh Singh Bal, *Constancy of an Infinite Cyclotomic Product via Ramanujan Sums*,
INTEGERS 25 (2025), Article A96, Theorem 1 (`integers-2025-A96-thm-1`). -/
public theorem_wanted tendsto_prod_cyclotomicHat_inv_root_one {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun N : ℕ => ∏ n ∈ Finset.Icc 1 N,
        Complex.exp (-(n : ℂ)⁻¹ * ∑ ζ ∈ primitiveRoots n ℂ, Complex.log (1 - z * ζ)))
      atTop (𝓝 1)

/-- Zeta-twisted companion of Theorem 1: for real `s > 1` and `‖z‖ < 1`,
`∏_{i ≥ 1} (1 - z^i)^{-1/i^s} = ∏_{i ≥ 1} Φ̂ᵢ(z)^{-ζ(s)/i^s}`, written as: the partial products of
both sides (ordered by `i`) converge to one common limit. Powers use the branches of Theorem 1:
the principal logarithm for `(1 - zⁱ)` and `∑_ζ log(1 - z ζ)` for `Φ̂ᵢ(z)`, each `0` at `z = 0`.

The exponent `-ζ(s)/i^s` follows the arXiv version (arXiv:2511.16975, Theorem 2.2). The garbled
record shows `-ζ(s)/i` with a stray `s`, which is the misplaced exponent of `i^s`. Read literally,
the right side would be `1` by Theorem 1 while the left side is not.

Source: Hartosh Singh Bal, *Constancy of an Infinite Cyclotomic Product via Ramanujan Sums*,
INTEGERS 25 (2025), Article A96, Theorem 2 (`integers-2025-A96-thm-2`). -/
public theorem_wanted exists_tendsto_prod_one_sub_pow_and_cyclotomicHat_zeta {z : ℂ}
    (hz : ‖z‖ < 1) {s : ℝ} (hs : 1 < s) :
    ∃ L : ℂ,
      Tendsto (fun N : ℕ => ∏ i ∈ Finset.Icc 1 N,
          Complex.exp (-(((i : ℝ) ^ s : ℝ) : ℂ)⁻¹ * Complex.log (1 - z ^ i))) atTop (𝓝 L) ∧
      Tendsto (fun N : ℕ => ∏ i ∈ Finset.Icc 1 N,
          Complex.exp (-(riemannZeta (s : ℂ) / (((i : ℝ) ^ s : ℝ) : ℂ)) *
            ∑ ζ ∈ primitiveRoots i ℂ, Complex.log (1 - z * ζ))) atTop (𝓝 L)

end

end MetaMathlibExt
