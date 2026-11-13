/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Milin's conjecture on logarithmic coefficients (Hayman–Lingham Problem 6.42)

W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Problem 6.42 (P. L. Duren):
for `f ∈ S` write `log(f(z)/z) = 2 ∑ γₖ zᵏ`. Milin conjectured `∑_{n=1}^{N} ∑_{k=1}^{n} k |γₖ|² ≤
∑_{n=1}^{N} ∑_{k=1}^{n} 1/k`; is it true in general if `f` has real coefficients, or if `f` is
close-to-convex?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Complex.Exponential
public import WantedExt.Analysis.UnivalentClassSShared

@[expose] public section

namespace MathlibExt.Analysis.MilinLogarithmicCoefficientsAMR22Problem6042Wanted

/-!
Source: W. K. Hayman and E. F. Lingham, Research Problems in Function Theory, Fiftieth Anniversary
Edition (2019), arXiv:1809.07200, Problem 6.42 (P. L. Duren). UnsolvedMath record UM-02306042
(`AMR-022-6042`), dataset ulamai/UnsolvedMath v1.8.0.

The class `S` is `IsNormalizedUnivalent` (`WantedExt.Analysis.UnivalentClassSShared`, shared with
Problem 6.78): `f` holomorphic and injective on the open unit disc with `f 0 = 0` and `f' 0 = 1`.
The logarithmic coefficients are given by a holomorphic branch `L` of `log(f(z)/z)` on the disc with
`L 0 = 0` and `L z = 2 ∑ γ (k+1) z^(k+1)`; such `L` and `γ` exist and are unique for `f ∈ S`, so
quantifying over them states the inequality for the actual coefficients. The target is Milin's
inequality (6.4) for every `f ∈ S`, which answers both sub-questions (real coefficients,
close-to-convex) since those classes lie in `S`.
-/

open MathlibExt.Analysis.UnivalentClassSShared

/-- `γ` are the logarithmic coefficients of `f`: `log (f z / z) = 2 ∑_{k ≥ 1} γ k z ^ k` on the unit
disc, for the holomorphic branch `L` of `log (f z / z)` with `L 0 = 0`. -/
def IsLogCoeffs (f : ℂ → ℂ) (γ : ℕ → ℂ) : Prop :=
  ∃ L : ℂ → ℂ, DifferentiableOn ℂ L (Metric.ball 0 1) ∧ L 0 = 0 ∧
    (∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → Complex.exp (L z) = f z / z) ∧
    ∀ z ∈ Metric.ball (0 : ℂ) 1, HasSum (fun k : ℕ => 2 * γ (k + 1) * z ^ (k + 1)) (L z)

/-- Milin's conjecture (Hayman–Lingham Problem 6.42, inequality (6.4)): for every `f ∈ S` with
logarithmic coefficients `γ` and every `N ≥ 1`,
`∑_{n=1}^{N} ∑_{k=1}^{n} k |γ k|² ≤ ∑_{n=1}^{N} ∑_{k=1}^{n} 1 / k`. -/
def milinConjecture : Prop :=
  ∀ (f : ℂ → ℂ) (γ : ℕ → ℂ), IsNormalizedUnivalent f → IsLogCoeffs f γ → ∀ N : ℕ, 1 ≤ N →
    ∑ n ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 n, (k : ℝ) * ‖γ k‖ ^ 2 ≤
      ∑ n ∈ Finset.Icc 1 N, ∑ k ∈ Finset.Icc 1 n, (1 : ℝ) / k

/--
Resolved true: de Branges proved Milin's conjecture for the whole class `S` (Hayman–Lingham Update
6.1, referenced from Update 6.42), so the inequality holds in general and in particular for `f` with
real coefficients and for close-to-convex `f`. Source: W. K. Hayman and E. F. Lingham, Research
Problems in Function Theory, Fiftieth Anniversary Edition (2019), arXiv:1809.07200, Problem 6.42 (P.
L. Duren); resolution: L. de Branges, A proof of the Bieberbach conjecture, Acta Math. 154 (1985),
137-152; recorded in Hayman–Lingham, Update 6.42 and Update 6.1, Hayman–Lingham Update 6.1: "de
Branges proved Milin's conjecture ... ∑_{n=1}^{N} ∑_{k=1}^{n} k|γ_k|² ≤ ∑_{n=1}^{N} ∑_{k=1}^{n} 1/k
(Problem 6.42)" for the class S; Update 6.42: "See Update 6.1", https://doi.org/10.1007/BF02392821.
-/
public theorem_wanted milinConjecture_holds : milinConjecture

end MathlibExt.Analysis.MilinLogarithmicCoefficientsAMR22Problem6042Wanted
