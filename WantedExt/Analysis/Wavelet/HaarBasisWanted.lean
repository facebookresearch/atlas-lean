/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.Wavelet.HaarBasisUnitInterval

/-!
# The Haar wavelet basis of the real line (wanted)

The Haar functions at all integer scales and translations form an orthonormal basis of
real `L²(ℝ)`. The corresponding unit-interval basis, which includes the constant function,
is proved in `MathlibExt.Analysis.Wavelet.HaarBasisUnitInterval`.
-/

@[expose] public section

open MeasureTheory Set

namespace MathlibExt.Analysis.Wavelet.HaarBasisWanted

open MathlibExt.Analysis.Wavelet.Haar

/-- **The Haar wavelet basis of `L²(ℝ)`** (S. Mallat, *Multiresolution approximations and
wavelet orthonormal bases of `L²(ℝ)`*, Trans. Amer. Math. Soc. 315 (1989), Section 4, after (70):
the Haar basis is the wavelet orthonormal basis `√(2^j) ψ(2^j x - k)`, `(k, j) ∈ ℤ²`, of the
multiresolution approximation with scaling function `1_{[0,1]}`). The functions
`H_{j,k}(x) = 2^{j/2} H(2^j x - k)`, `j, k ∈ ℤ`, form an orthonormal basis of `L²(ℝ)`: there is
a Hilbert basis of `L²(ℝ)` indexed by `ℤ × ℤ` whose elements are a.e. equal to them. -/
theorem_wanted exists_hilbertBasis_haarSystem :
    ∃ b : HilbertBasis (ℤ × ℤ) ℝ (Lp ℝ 2 (volume : Measure ℝ)),
      ∀ jk : ℤ × ℤ, ⇑(b jk : Lp ℝ 2 (volume : Measure ℝ)) =ᵐ[volume] haarSystem jk.1 jk.2

end MathlibExt.Analysis.Wavelet.HaarBasisWanted
