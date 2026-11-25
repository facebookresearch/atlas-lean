/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.DeBruijnNewman
public import MathlibExt.NumberTheory.LSeries.RiemannXi

@[expose] public section

namespace MathlibExt.NumberTheory.DeBruijnNewmanXiWanted

open Complex MathlibExt.NumberTheory.DeBruijnNewman RiemannXi

/-!
# The de Bruijn–Newman deformation at time zero and the Riemann ξ function

At time `0` the de Bruijn–Newman deformation `H 0` is the Riemann ξ function on the critical line,
rescaled: `8 H 0 z = ξ(1/2 + i z / 2)`. A real `z` corresponds to a point of the line `Re s = 1/2`.
-/

/-- **Fourier integral for the Riemann ξ function.** For every complex number `z`,
`8 H₀(z) = ξ(1/2 + i z / 2)`, where `H₀(z) = ∫₀^∞ Φ(u) cos(z u) du` is the de Bruijn–Newman
deformation at time `0`, `Φ` is Newman's kernel, and `ξ` is the Riemann ξ function:
`ξ(s) = s (s - 1) / 2 · Λ(s)` for `s ≠ 0, 1` and `ξ(0) = ξ(1) = 1/2`, where `Λ` is the completed
zeta function, the meromorphic function `π^(-s/2) Γ(s/2) ζ(s)` continued across its removable
singularities at `-2, -4, …`, whose only poles are simple poles at `0` and `1`.

Source: B. Rodgers and T. Tao, *The de Bruijn–Newman constant is non-negative*, Forum Math. Pi 8
(2020), e6, arXiv:1801.05914v3, §1: equation (1) defines `H₀(z) = ξ(1/2 + i z / 2) / 8` with `ξ`
as in (2), and the next sentence gives the Fourier representation `H₀(z) = ∫₀^∞ Φ(u) cos(z u) du`
with `Φ` as in (3), as a classical fact (citing E. C. Titchmarsh, *The theory of the Riemann
zeta-function*, 2nd ed., p. 255). -/
theorem_wanted eight_mul_H_zero_eq_riemannXi (z : ℂ) :
    8 * H 0 z = riemannXi (1 / 2 + I * z / 2)

end MathlibExt.NumberTheory.DeBruijnNewmanXiWanted
