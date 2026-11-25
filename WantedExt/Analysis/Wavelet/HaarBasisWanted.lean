/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.MeasureTheory.Function.L2Space
public import MathlibExt.Analysis.Wavelet.Haar

/-!
# The Haar system is an orthonormal basis (wanted)

The Haar system `H_{j,k}(x) = 2^{j/2} H(2^j x - k)` of `MathlibExt.Analysis.Wavelet.Haar` is the
first wavelet orthonormal basis: of `L²[0,1)` together with the constant `1` (R. A. DeVore,
*Nonlinear approximation*, Acta Numerica 7 (1998), Section 3.5, (3.44)–(3.47)), and of `L²(ℝ)`
over all `j, k ∈ ℤ` (S. Mallat, *Multiresolution approximations and wavelet orthonormal bases of
`L²(ℝ)`*, Trans. Amer. Math. Soc. 315 (1989), Section 4, after (70), as the multiresolution
approximation with scaling function `1_{[0,1)}`). The statements are recorded as Hilbert bases of
the real `L²` spaces whose elements are almost everywhere equal to the Haar functions.
Orthonormality is proved (`MathlibExt.Analysis.Wavelet.Haar.integral_haarSystem_mul_haarSystem`, in
integral form); completeness, through the density of dyadic step functions, is deferred.
-/

@[expose] public section

open MeasureTheory Set

namespace MathlibExt.Analysis.Wavelet.HaarBasisWanted

open MathlibExt.Analysis.Wavelet.Haar

/-- **The Haar basis of `L²[0,1)`** (R. A. DeVore, *Nonlinear approximation*, Acta Numerica 7
(1998), Section 3.5, (3.47)). The constant function `1` together with the Haar functions
`H_{k,j}(x) = 2^{k/2} H(2^k x - j)`, `k ≥ 0`, `0 ≤ j < 2^k`, fitted to the dyadic intervals
`2^{-k}[j, j+1)`, form an orthonormal basis of `L²[0,1)`: there is a Hilbert basis of
`L²([0,1))` indexed by `Option (Σ k, Fin (2^k))` whose elements are a.e. equal to these
functions. -/
theorem_wanted exists_hilbertBasis_haar_unitInterval :
    ∃ b : HilbertBasis (Option (Σ k : ℕ, Fin (2 ^ k))) ℝ
        (Lp ℝ 2 (volume.restrict (Ico (0 : ℝ) 1))),
      (⇑(b none : Lp ℝ 2 (volume.restrict (Ico (0 : ℝ) 1))) =ᵐ[volume.restrict (Ico (0 : ℝ) 1)]
          fun _ => (1 : ℝ)) ∧
      ∀ (k : ℕ) (j : Fin (2 ^ k)),
        ⇑(b (some ⟨k, j⟩) : Lp ℝ 2 (volume.restrict (Ico (0 : ℝ) 1)))
          =ᵐ[volume.restrict (Ico (0 : ℝ) 1)] haarSystem k (j : ℕ)

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
