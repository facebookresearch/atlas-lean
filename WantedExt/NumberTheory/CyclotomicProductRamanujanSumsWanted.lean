/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.CyclotomicProductRamanujanSums
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

/-- **Constancy of an infinite cyclotomic product.** For $n \ge 1$ and complex $z$, let
$\hat\Phi_n(z) = \prod_\omega (1 - z\omega)$, the product over the primitive $n$-th roots of
unity $\omega$; thus $\hat\Phi_1(z) = 1 - z$ and $\hat\Phi_n = \Phi_n$ for $n \ge 2$, where
$\Phi_n$ is the $n$-th cyclotomic polynomial. For every complex $z$ with $|z| < 1$, the partial
products $\prod_{n=1}^{N} \hat\Phi_n(z)^{-1/n}$ tend to $1$ as $N \to \infty$, where
$\hat\Phi_n(z)^{-1/n} = \exp\bigl(-\tfrac{1}{n} \sum_\omega \log(1 - z\omega)\bigr)$ and $\log$
is the principal branch of the logarithm.

Each factor $1 - z\omega$ has positive real part, and this branch equals $1$ at $z = 0$, as in
the paper's logarithmic-derivative proof. The paper writes the product as
$P(z) = -\prod_{n \ge 1} \Phi_n(z)^{-1/n}$; the sign absorbs $\Phi_1(z) = -(1 - z)$, and the
claim is $P(z) \equiv 1$.

Source: Hartosh Singh Bal, *Constancy of an Infinite Cyclotomic Product via Ramanujan Sums*,
INTEGERS 25 (2025), Article A96, Theorem 1 (`integers-2025-A96-thm-1`). -/
public theorem_wanted tendsto_prod_cyclotomicHat_inv_root_one {z : ℂ} (hz : ‖z‖ < 1) :
    Tendsto (fun N : ℕ => ∏ n ∈ Finset.Icc 1 N,
        Complex.exp (-(n : ℂ)⁻¹ * ∑ ζ ∈ primitiveRoots n ℂ, Complex.log (1 - z * ζ)))
      atTop (𝓝 1)

end

end MetaMathlibExt
