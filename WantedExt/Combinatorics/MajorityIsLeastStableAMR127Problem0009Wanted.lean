/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Majority Is Least Stable conjecture (O'Donnell's open problems on Boolean functions)

Majority Is Least Stable Conjecture (Benjamini–Kalai–Schramm), as stated in O'Donnell's list: if `n`
is odd and `f` is a linear threshold function on `{-1, 1}ⁿ`, then `Stab_ρ[f] ≥ Stab_ρ[Maj_n]` for
all `ρ ∈ [0, 1]`.
-/

module

public import Batteries.Util.ProofWanted
public import MathlibExt.Analysis.Fourier.BooleanCube

@[expose] public section

namespace MathlibExt.Combinatorics.MajorityIsLeastStableAMR127Problem0009Wanted

/-!
Source: R. O'Donnell, Open problems in analysis of Boolean functions, arXiv:1204.6447 (2012),
'Majority Is Least Stable Conjecture' (Benjamini, Kalai, Schramm). UnsolvedMath record UM-00800440
(`AMR-127-0009`), dataset ulamai/UnsolvedMath v1.8.0.

The cube `{-1, 1}ⁿ` and Fourier coefficients are MathlibExt's `BooleanCube` (`true` is `1`,
`boolFourierCoeff n f S = E_x[f(x) χ_S(x)]`). A linear threshold function is `x ↦ sgn(w₀ + Σᵢ wᵢ
xᵢ)` with `sgn z = 1` for `z ≥ 0` and `-1` for `z < 0`, the convention of Biswas and Sarkar (raising
`w₀` slightly gives the same class with nonzero arguments). The noise stability is given by its
Fourier formula `Stab_ρ[f] = Σ_S ρ^{|S|} f̂(S)²` (O'Donnell, Analysis of Boolean Functions, Theorem
2.49; Biswas–Sarkar, §2). Biswas and Sarkar prove the conjecture for `n = 1, 3` and refute it for
every odd `n ≥ 5`, so the target is stated for some odd `n ≥ 5` and refuted, which is stronger than
refuting the conjecture as posed; the cases `n = 1, 3` are not formalized. The list's remarks after
the conjecture (a weaker noise-sensitivity version, the `ρ → 0` consequence) are related questions,
not part of the conjecture.
-/

open BooleanCube

/-- `f : {-1, 1}ⁿ → ℝ` is a linear threshold function: for some reals `w₀, w₁, …, wₙ`,
`f(x) = sgn(w₀ + w₁ x₁ + ⋯ + wₙ xₙ)`, where `sgn z = 1` for `z ≥ 0` and `sgn z = -1` for `z < 0`
(the coordinate `xᵢ ∈ {-1, 1}` of a point `x : BoolCube n` is `cubeVal (x i)`). -/
def IsLinearThresholdFunction {n : ℕ} (f : BoolCube n → ℝ) : Prop :=
  ∃ (w₀ : ℝ) (w : Fin n → ℝ), ∀ x : BoolCube n,
    f x = if 0 ≤ w₀ + ∑ i, w i * cubeVal (x i) then 1 else -1

/-- The majority function `Maj_n(x) = sgn(x₁ + ⋯ + xₙ)`. -/
noncomputable def majority (n : ℕ) (x : BoolCube n) : ℝ :=
  if 0 ≤ ∑ i, cubeVal (x i) then 1 else -1

/-- The noise stability `Stab_ρ[f] = ∑_{S ⊆ [n]} ρ^{|S|} f̂(S)²`, the Fourier expansion of
`E[f(x) f(y)]` for uniform `x` and a `ρ`-correlated copy `y` of `x`. -/
noncomputable def noiseStability {n : ℕ} (ρ : ℝ) (f : BoolCube n → ℝ) : ℝ :=
  ∑ S : Finset (Fin n), ρ ^ S.card * boolFourierCoeff n f S ^ 2

/-- The Majority Is Least Stable conjecture in `n` variables: every linear threshold function
`f : {-1, 1}ⁿ → {-1, 1}` satisfies `Stab_ρ[f] ≥ Stab_ρ[Maj_n]` for all `ρ ∈ [0, 1]`. -/
def MajorityIsLeastStableFor (n : ℕ) : Prop :=
  ∀ f : BoolCube n → ℝ, IsLinearThresholdFunction f → ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
    noiseStability ρ (majority n) ≤ noiseStability ρ f

/-- The Majority Is Least Stable conjecture holds in some odd number `n ≥ 5` of variables. -/
def majorityIsLeastStableForSomeOddAtLeastFive : Prop :=
  ∃ n : ℕ, Odd n ∧ 5 ≤ n ∧ MajorityIsLeastStableFor n

/--
Resolved false: for every odd n ≥ 5 Biswas and Sarkar exhibit a linear threshold function g_n with
Stab_ρ[g_n] < Stab_ρ[Maj_n] for all small ρ > 0, so the conjecture fails in every odd dimension n ≥
5 (it holds for n = 1 and n = 3). Source: R. O'Donnell, Open problems in analysis of Boolean
functions, arXiv:1204.6447 (2012), 'Majority Is Least Stable Conjecture' (Benjamini, Kalai,
Schramm); resolution: A. Biswas, P. Sarkar, On the "majority is least stable" conjecture, Inform.
Process. Lett. 179 (2023), 106295, arXiv:2202.09024, Theorem 2 of arXiv:2202.09024v2: the conjecture
is true for n = 1 and n = 3 and false for every odd n ≥ 5; for odd n ≥ 5 the linear threshold
function g_n(x) = sgn(2(x₁ + ⋯ + x_{n-3}) + x_{n-2} + x_{n-1} + x_n) has W⁰[g_n] = 0 and W¹[g_n] <
W¹[Maj_n] (Lemmas 3 and 4), hence Stab_ρ[g_n] < Stab_ρ[Maj_n] for all small ρ > 0 (Lemma 1); the
case n = 5 is V. Jain, arXiv:1703.07657, https://doi.org/10.1016/j.ipl.2022.106295.
-/
public theorem_wanted majorityIsLeastStableForSomeOddAtLeastFive_refuted :
    ¬ majorityIsLeastStableForSomeOddAtLeastFive

end MathlibExt.Combinatorics.MajorityIsLeastStableAMR127Problem0009Wanted
