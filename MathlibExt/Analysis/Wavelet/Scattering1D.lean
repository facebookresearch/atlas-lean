/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Convolution
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.Fourier.FourierTransform
public import MathlibExt.Analysis.Wavelet.ScatteringCascade

/-!
# The one-dimensional wavelet scattering transform: definitions

Definitions for S. Mallat's windowed scattering transform (*Group invariant scattering*, Comm.
Pure Appl. Math. 65 (2012), arXiv:1101.2286, Section 2) in dimension `d = 1`, where the finite
rotation group is `G = {1, -1}` and, for real-valued signals, paths only use the positive
rotation (`G⁺ = {1}`); a frequency index `λ = 2^j` is then determined by `j ∈ ℤ`.

* `angularFourier f ω = ∫ f(x) e^{-ixω} dx`, the Fourier transform in the convention of the
  paper (Notations, p. 4), written through Mathlib's `𝓕` as `𝓕 f (ω / (2π))`.
* `dilate ψ j x = 2^j ψ(2^j x)`, the dilated wavelet `ψ_{2^j}` (equation (4) with `d = 1`).
* `lowPass φ J x = 2^{-J} φ(2^{-J} x)`, the averaging window `φ_{2^J}` (equation (7)).
* `modulusLayer ψ j h = |h ⋆ ψ_{2^j}|`, the operator `U[λ]` of Definition 2.2.
* `windowedScattering ψ φ J p f = U[p] f ⋆ φ_{2^J}` for a path `p` of indices `j > -J`
  (Definition 2.4, equation (22)); `U[p]` is the abstract `propagator`, applying the first index
  of the path first.

Convolution is Mathlib's `convolution f g (lsmul ℂ ℂ) volume`,
`(f ⋆ g)(x) = ∫ f(u) g(x - u) du`, as in the paper's equation (6). The standing assumptions
on the wavelet (`IsScatteringWavelet`) and the admissibility condition (29)–(30)
(`IsAdmissible`) are also defined here. The theorems of the paper about these objects (energy
conservation, Theorem 2.6, and Lipschitz continuity to deformations, Theorem 2.12) are recorded
in `WantedExt.Analysis.Wavelet.ScatteringWanted`.
-/

@[expose] public section

open MeasureTheory
open scoped FourierTransform

noncomputable section

namespace MathlibExt.Analysis.Wavelet.Scattering1D

/-- **Fourier transform in angular frequency.** `angularFourier f ω = ∫ f(x) e^{-ixω} dx`, the
convention of S. Mallat, *Group invariant scattering*, Comm. Pure Appl. Math. 65 (2012),
Notations (p. 4); in terms of Mathlib's `𝓕 f ξ = ∫ f(x) e^{-2πixξ} dx` it is
`𝓕 f (ω / (2π))`. -/
def angularFourier (f : ℝ → ℂ) (ω : ℝ) : ℂ := 𝓕 f (ω / (2 * Real.pi))

/-- **Dilated wavelet.** `dilate ψ j x = 2^j ψ(2^j x)`: the wavelet `ψ_{2^j}` of S. Mallat,
*Group invariant scattering*, Comm. Pure Appl. Math. 65 (2012), equation (4) in dimension
`d = 1` with the rotation `r = 1`. Its Fourier transform is `ψ̂(2^{-j} ω)`. -/
def dilate (ψ : ℝ → ℂ) (j : ℤ) (x : ℝ) : ℂ := (2 : ℂ) ^ j * ψ ((2 : ℝ) ^ j * x)

/-- **Low-pass window at scale `2^J`.** `lowPass φ J x = 2^{-J} φ(2^{-J} x)`, the window
`φ_{2^J}` of S. Mallat, *Group invariant scattering*, Comm. Pure Appl. Math. 65 (2012),
equation (7) in dimension `d = 1`; `A_J f = f ⋆ φ_{2^J}`. -/
def lowPass (φ : ℝ → ℂ) (J : ℤ) (x : ℝ) : ℂ := (2 : ℂ) ^ (-J) * φ ((2 : ℝ) ^ (-J) * x)

/-- **Wavelet modulus operator.** `modulusLayer ψ j h = |h ⋆ ψ_{2^j}|`, the operator
`U[λ] h = |h ⋆ ψ_λ|` for `λ = 2^j` of S. Mallat, *Group invariant scattering*, Comm. Pure Appl.
Math. 65 (2012), Definition 2.2 (in dimension `d = 1`), with values viewed in `ℂ`. -/
def modulusLayer (ψ : ℝ → ℂ) (j : ℤ) (h : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((‖convolution h (dilate ψ j) (ContinuousLinearMap.lsmul ℂ ℂ) volume x‖ : ℝ) : ℂ)

/-- **Windowed scattering transform.** For `J ∈ ℤ` and a path `p` of frequency indices
`j₁, …, j_m` with `j_k > -J` (that is `2^{j_k} > 2^{-J}`, the path set `P_J`),
`windowedScattering ψ φ J p f = U[p] f ⋆ φ_{2^J} = | |f ⋆ ψ_{2^{j₁}}| ⋆ ⋯ | ⋆ φ_{2^J}`
(S. Mallat, *Group invariant scattering*, Comm. Pure Appl. Math. 65 (2012), Definition 2.4,
equation (22), in dimension `d = 1` for real-valued signals). -/
def windowedScattering (ψ φ : ℝ → ℂ) (J : ℤ) {m : ℕ} (p : Fin m → {j : ℤ // -J < j})
    (f : ℝ → ℂ) : ℝ → ℂ :=
  convolution
    (ScatteringCascade.propagator (fun j : {j : ℤ // -J < j} => modulusLayer ψ j) p f)
    (lowPass φ J) (ContinuousLinearMap.lsmul ℂ ℂ) volume

/-- **Scattering wavelet in dimension one** (S. Mallat, *Group invariant scattering*, Comm. Pure
Appl. Math. 65 (2012), the standing assumptions of Section 2.1, p. 7, with `d = 1`,
`G = {1, -1}` and real-valued signals, so `β = 1/2` in (9)):
* `ψ̂` is real, and `φ̂` is real and symmetric (`ψ̂ = angularFourier ψ`);
* `ψ` and `φ` are twice differentiable, and they and their derivatives of order `1` and `2`
  are `O((1 + |x|)^{-d-2}) = O((1 + |x|)^{-3})`;
* the Littlewood–Paley condition (9) holds for almost every `ω`:
  `(1/2) ∑_{j ∈ ℤ} ∑_{r = ±1} |ψ̂(2^{-j} r ω)|² = 1` and
  `|φ̂(ω)|² = (1/2) ∑_{j ≤ 0} ∑_{r = ±1} |ψ̂(2^{-j} r ω)|²` (the second sum is written with
  `n = -j ∈ ℕ`). By Proposition 2.1 this makes the wavelet transform `W_J` unitary on
  real-valued functions of `L²(ℝ)`. -/
def IsScatteringWavelet (ψ φ : ℝ → ℂ) : Prop :=
  (∀ ω, (angularFourier ψ ω).im = 0) ∧
  (∀ ω, (angularFourier φ ω).im = 0 ∧ angularFourier φ (-ω) = angularFourier φ ω) ∧
  ContDiff ℝ 2 ψ ∧ ContDiff ℝ 2 φ ∧
  (∃ C : ℝ, ∀ n ≤ 2, ∀ x : ℝ,
    ‖iteratedDeriv n ψ x‖ ≤ C / (1 + |x|) ^ 3 ∧ ‖iteratedDeriv n φ x‖ ≤ C / (1 + |x|) ^ 3) ∧
  ∀ᵐ ω : ℝ,
    (1 / 2 : ℝ) * ∑' j : ℤ, (‖angularFourier ψ ((2 : ℝ) ^ (-j) * ω)‖ ^ 2 +
      ‖angularFourier ψ (-((2 : ℝ) ^ (-j) * ω))‖ ^ 2) = 1 ∧
    ‖angularFourier φ ω‖ ^ 2 = (1 / 2 : ℝ) * ∑' n : ℕ, (‖angularFourier ψ ((2 : ℝ) ^ n * ω)‖ ^ 2 +
      ‖angularFourier ψ (-((2 : ℝ) ^ n * ω))‖ ^ 2)

/-- **The function `Ψ̂` of the admissibility condition** (S. Mallat, *Group invariant
scattering*, Comm. Pure Appl. Math. 65 (2012), Theorem 2.6, equation (29)):
`Ψ̂(ω) = |ρ̂(ω - η)|² - ∑_{k ≥ 1} k (1 - |ρ̂(2^{-k} (ω - η))|²)`, written with `k + 1` for
`k ∈ ℕ`. -/
def admissibilityFunction (ρ : ℝ → ℝ) (η ω : ℝ) : ℝ :=
  ‖angularFourier (fun x => (ρ x : ℂ)) (ω - η)‖ ^ 2 -
    ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) *
      (1 - ‖angularFourier (fun x => (ρ x : ℂ)) ((2 : ℝ) ^ (-((k : ℤ) + 1)) * (ω - η))‖ ^ 2)

/-- **Admissible scattering wavelet in dimension one** (S. Mallat, *Group invariant
scattering*, Comm. Pure Appl. Math. 65 (2012), Theorem 2.6, conditions (29)–(30), with `d = 1`
and `G = {1, -1}`). `ψ, φ` satisfy the standing assumptions (`IsScatteringWavelet`), and there
are `η ∈ ℝ` and an integrable `ρ ≥ 0` with `|ρ̂(ω)| ≤ |φ̂(2ω)|`, `ρ̂(0) = 1`, such that
`α = inf_{1 ≤ |ω| ≤ 2} ∑_{j ∈ ℤ} ∑_{r = ±1} Ψ̂(2^{-j} r ω) |ψ̂(2^{-j} r ω)|² > 0`, where `Ψ̂` is
`admissibilityFunction ρ η`. Two side conditions make the series of (29)–(30) meaningful: the
series defining `Ψ̂` converges at every `ω` (its terms are nonnegative), and the positive lower
bound `α` is required of the `ℤ`-indexed sums, which Lean sums unconditionally.

Satisfiability is supported numerically, not formally: Mallat (Section 2.3, the remark after the
proof of Theorem 2.6) reports that the analytic cubic-spline Battle–Lemarié wavelet is admissible
in dimension one with `η = 3π/2`, taking for `ρ` a positive cubic box spline, by a numerical
evaluation of (30) giving `α = 0.2766`. Explicitly, `ψ̂ = √2 |ψ̂_BL| 1_{ω > 0}`,
`φ̂(ω) = φ̂_BL(ω / 2)` and `ρ` the centred cubic B-spline, `ρ̂(ω) = sinc⁴(ω / 2)`. No instance is
formalized. -/
def IsAdmissible (ψ φ : ℝ → ℂ) : Prop :=
  IsScatteringWavelet ψ φ ∧
  ∃ η : ℝ, ∃ ρ : ℝ → ℝ, (∀ x, 0 ≤ ρ x) ∧ Integrable ρ ∧
    (∀ ω, ‖angularFourier (fun x => (ρ x : ℂ)) ω‖ ≤ ‖angularFourier φ (2 * ω)‖) ∧
    angularFourier (fun x => (ρ x : ℂ)) 0 = 1 ∧
    (∀ ω, Summable fun k : ℕ => ((k + 1 : ℕ) : ℝ) *
      (1 - ‖angularFourier (fun x => (ρ x : ℂ)) ((2 : ℝ) ^ (-((k : ℤ) + 1)) * (ω - η))‖ ^ 2)) ∧
    ∃ α > 0, ∀ ω : ℝ, 1 ≤ |ω| → |ω| ≤ 2 →
      α ≤ ∑' j : ℤ,
        (admissibilityFunction ρ η ((2 : ℝ) ^ (-j) * ω) *
            ‖angularFourier ψ ((2 : ℝ) ^ (-j) * ω)‖ ^ 2 +
          admissibilityFunction ρ η (-((2 : ℝ) ^ (-j) * ω)) *
            ‖angularFourier ψ (-((2 : ℝ) ^ (-j) * ω))‖ ^ 2)

end MathlibExt.Analysis.Wavelet.Scattering1D
