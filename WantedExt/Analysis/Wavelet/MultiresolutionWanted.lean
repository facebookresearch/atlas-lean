/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.InnerProductSpace.l2Space
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import MathlibExt.Analysis.Wavelet.Multiresolution

/-!
# Scaling functions and wavelet bases of multiresolution approximations (wanted)

The two main constructions of S. Mallat, *Multiresolution approximations and wavelet orthonormal
bases of `L²(ℝ)`*, Trans. Amer. Math. Soc. 315 (1989), 69–87, for a multiresolution
approximation `(V_j)` in the sense of
`MathlibExt.Analysis.Wavelet.Multiresolution.IsMultiresolutionApproximation`:

* Section 2: there is a scaling function `φ` whose integer translates form an orthonormal basis
  of `V_0` (and then, by property (3), `√(2^j) φ(2^j x - k)` is an orthonormal basis of `V_j`);
* Section 4: there is a wavelet `ψ` such that `√(2^j) ψ(2^j x - k)`, `(j, k) ∈ ℤ²`, is an
  orthonormal basis of `L²(ℝ)`.

The proofs (orthonormalization of the Riesz basis given by property (5) in the Fourier domain,
the filter `H` and the conjugate filter `G(ω) = e^{-iω} conj(H(ω + π))`) are deferred. Statements
are existence statements; the paper's normalization of `φ` and its uniqueness claim are not
recorded.
-/

@[expose] public section

open MeasureTheory

namespace MathlibExt.Analysis.Wavelet.MultiresolutionWanted

open MathlibExt.Analysis.Wavelet.Multiresolution

/-- **Scaling function of a multiresolution approximation** (S. Mallat, *Multiresolution
approximations and wavelet orthonormal bases of `L²(ℝ)`*, Trans. Amer. Math. Soc. 315 (1989),
Section 2). If `(V_j)` is a multiresolution approximation of `L²(ℝ)`, there is `φ ∈ L²(ℝ)` whose
integer translates `x ↦ φ(x - k)`, `k ∈ ℤ`, form an orthonormal basis of `V_0`: a Hilbert basis
of `V_0` indexed by `ℤ` whose elements are a.e. equal to these translates. -/
theorem_wanted exists_scaling_function {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) :
    ∃ φ : Lp ℂ 2 (volume : Measure ℝ), ∃ b : HilbertBasis ℤ ℂ (V 0),
      ∀ k : ℤ, ⇑((b k : V 0) : Lp ℂ 2 (volume : Measure ℝ)) =ᵐ[volume] fun x => φ (x - k)

/-- **Wavelet orthonormal basis of a multiresolution approximation** (S. Mallat,
*Multiresolution approximations and wavelet orthonormal bases of `L²(ℝ)`*, Trans. Amer. Math.
Soc. 315 (1989), Section 4, the conclusion after (70)). If `(V_j)` is a multiresolution
approximation of `L²(ℝ)`, there is a wavelet `ψ ∈ L²(ℝ)` such that the functions
`x ↦ √(2^j) ψ(2^j x - k)`, `(j, k) ∈ ℤ²`, form an orthonormal basis of `L²(ℝ)`, and those of
scale `j` lie in the orthogonal complement `O_j` of `V_j` in `V_{j+1}` (so that, the `O_j` being
mutually orthogonal, they form an orthonormal basis of `O_j`). -/
theorem_wanted exists_wavelet_hilbertBasis {V : ℤ → Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))}
    (hV : IsMultiresolutionApproximation V) :
    ∃ ψ : Lp ℂ 2 (volume : Measure ℝ), ∃ b : HilbertBasis (ℤ × ℤ) ℂ (Lp ℂ 2 (volume : Measure ℝ)),
      (∀ jk : ℤ × ℤ, ⇑(b jk : Lp ℂ 2 (volume : Measure ℝ)) =ᵐ[volume]
        fun x => ((Real.sqrt ((2 : ℝ) ^ jk.1) : ℝ) : ℂ) * ψ ((2 : ℝ) ^ jk.1 * x - jk.2)) ∧
      ∀ (j k : ℤ), (b (j, k) : Lp ℂ 2 (volume : Measure ℝ)) ∈ V (j + 1) ∧
        (b (j, k) : Lp ℂ 2 (volume : Measure ℝ)) ∈ (V j)ᗮ

end MathlibExt.Analysis.Wavelet.MultiresolutionWanted
