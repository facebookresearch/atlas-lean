/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Shifted moments of the Riemann zeta function without the ε loss (Moments problem list, Problem 7)

Moments of L-functions Problem List, Problem 7 (N. Ng): improve Chandee's Theorem 1.2, which states
that under the Riemann hypothesis `∫_0^T ∏ᵢ |ζ(1/2 + i (t + αᵢ))|^{2kᵢ} dt ≪_{k,ε} T (log T)^{k₁² +
⋯ + kₘ² + ε} ∏_{i<j} min{1/|αᵢ - αⱼ|, log T}^{2kᵢkⱼ}` for shifts `αᵢ = αᵢ(T) = o(T)` with bounded
distinct differences: use Harper's method to remove the `ε`.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.NumberTheory.LSeries.RiemannZeta

@[expose] public section

namespace MathlibExt.NumberTheory.ShiftedZetaMomentsAMR117Problem0006Wanted

/-!
Source: A. Hamieh, H. Kadiri, G. Martin, N. Ng (eds.), Moments of L-functions Problem List,
arXiv:2405.17800 (2024), Moments of the Riemann zeta function, Problem 7 (N. Ng). UnsolvedMath
record UM-00800158 (`AMR-117-0006`), dataset ulamai/UnsolvedMath v1.8.0.

The list records that Michael Curran solved the problem. The target is Curran's theorem in the form
he proves it: under the Riemann hypothesis, for `βₖ ≥ 0` and all shifts with `|αₖ| ≤ T/2`, the
moment over `[T, 2T]` is `≪_β T (log T)^{Σ βₖ²} ∏_{j<k} |ζ(1 + i (αⱼ - αₖ) + 1/log T)|^{2βⱼβₖ}`,
uniformly in the shifts, for `T` large in terms of `β`. For bounded differences `|ζ(1 + i y + 1/log
T)| ≍ min{1/|y|, log T}`, which is Chandee's factor; that reduction and the passage from `[T, 2T]`
to `[0, T]` are not formalized. The record's integrand drops the factor `i` (as the list's display
does); Chandee's moments are on the critical line.
-/

open Complex

/-- Curran's bound for shifted moments of the Riemann zeta function, conditional on the Riemann
hypothesis: for exponents `β₁, …, βₘ ≥ 0` there are `C, T₀` such that for `T ≥ T₀` and all shifts
with `|αₖ| ≤ T/2`,
`∫_T^{2T} ∏ₖ |ζ(1/2 + i (t + αₖ))|^{2βₖ} dt ≤ C T (log T)^{β₁² + ⋯ + βₘ²}
  ∏_{j < k} |ζ(1 + i (αⱼ - αₖ) + 1/log T)|^{2βⱼβₖ}`. -/
def shiftedMomentBound : Prop :=
  RiemannHypothesis → ∀ (m : ℕ) (β : Fin m → ℝ), (∀ k, 0 ≤ β k) →
    ∃ C T₀ : ℝ, ∀ T ≥ T₀, ∀ α : Fin m → ℝ, (∀ k, |α k| ≤ T / 2) →
      ∫ t in T..2 * T, ∏ k, ‖riemannZeta (1 / 2 + ((t + α k : ℝ) : ℂ) * I)‖ ^ (2 * β k) ≤
        C * T * Real.log T ^ (∑ k, β k ^ 2) *
          ∏ j, ∏ k, if j < k then
            ‖riemannZeta (1 + ((α j - α k : ℝ) : ℂ) * I + ((1 / Real.log T : ℝ) : ℂ))‖ ^
              (2 * β j * β k) else 1

/--
Resolved true (conditionally on RH, as posed): Curran proves the ε-free bound for shifted moments in
the form stated here, and the problem list records that he solved the problem. Source: A. Hamieh, H.
Kadiri, G. Martin, N. Ng (eds.), Moments of L-functions Problem List, arXiv:2405.17800 (2024),
Moments of the Riemann zeta function, Problem 7 (N. Ng); resolution: M. J. Curran, Correlations of
the Riemann zeta function, Mathematika 70 (2024), no. 4, e12268, arXiv:2303.10123, Theorem 1.1
(assuming RH, for βₖ ≥ 0 and |αₖ| ≤ T/2, ∫_T^{2T} ∏ₖ |ζ(1/2 + i(t + αₖ))|^{2βₖ} dt ≪_β T (log
T)^{β₁² + ⋯ + βₘ²} ∏_{j<k} |ζ(1 + i(αⱼ - αₖ) + 1/log T)|^{2βⱼβₖ}, T large in terms of β), which §1
presents as removing the ε loss of Chandee's bound in general (Chandee's bounds are 'sharp up to a
(log T)^ε loss', Ng, Shen and Wong 'removed the (log T)^ε loss in the special case β = (β, β)', and
the paper extends their work 'to arbitrary α and β'); the problem list (arXiv:2405.17800, Problem 7)
records 'Michael Curran [Cu] has solved this problem', https://doi.org/10.1112/mtk.12268.
-/
public theorem_wanted shiftedMomentBound_holds : shiftedMomentBound

end MathlibExt.NumberTheory.ShiftedZetaMomentsAMR117Problem0006Wanted
