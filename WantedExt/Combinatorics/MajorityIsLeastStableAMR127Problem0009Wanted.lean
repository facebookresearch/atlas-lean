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

/-- **Linear threshold function.** A function $f : \{-1, 1\}^n \to \mathbb{R}$ is a linear
threshold function if there are reals $w_0, w_1, \dots, w_n$ such that for every
$x \in \{-1, 1\}^n$ we have $f(x) = \operatorname{sgn}(w_0 + w_1 x_1 + \dots + w_n x_n)$, where
$x_i \in \{-1, 1\}$ is the $i$-th coordinate of $x$, $\operatorname{sgn} z = 1$ for $z \ge 0$ and
$\operatorname{sgn} z = -1$ for $z < 0$. -/
def IsLinearThresholdFunction {n : ℕ} (f : BoolCube n → ℝ) : Prop :=
  ∃ (w₀ : ℝ) (w : Fin n → ℝ), ∀ x : BoolCube n,
    f x = if 0 ≤ w₀ + ∑ i, w i * cubeVal (x i) then 1 else -1

/-- **Majority function.** For $n \in \mathbb{N}$, the majority function
$\mathrm{Maj}_n : \{-1, 1\}^n \to \mathbb{R}$ is given by $\mathrm{Maj}_n(x) = 1$ if
$x_1 + \dots + x_n \ge 0$ and $\mathrm{Maj}_n(x) = -1$ otherwise, where $x_i \in \{-1, 1\}$ is the
$i$-th coordinate of $x$. -/
noncomputable def majority (n : ℕ) (x : BoolCube n) : ℝ :=
  if 0 ≤ ∑ i, cubeVal (x i) then 1 else -1

/-- **Noise stability.** For a real number $\rho$ and a function $f : \{-1, 1\}^n \to \mathbb{R}$,
the noise stability of $f$ at $\rho$ is
$\mathrm{Stab}_\rho[f] = \sum_{S \subseteq \{1, \dots, n\}} \rho^{|S|} \hat f(S)^2$, where
$\hat f(S)$ is the Fourier coefficient of $f$ at $S$.

For $-1 \le \rho \le 1$ this is the Fourier expansion of $\mathbb{E}[f(x) f(y)]$ for uniform $x$
and a $\rho$-correlated copy $y$ of $x$. -/
noncomputable def noiseStability {n : ℕ} (ρ : ℝ) (f : BoolCube n → ℝ) : ℝ :=
  ∑ S : Finset (Fin n), ρ ^ S.card * boolFourierCoeff n f S ^ 2

/-- **Majority Is Least Stable conjecture in $n$ variables.** For $n \in \mathbb{N}$, this is the
statement that every linear threshold function $f : \{-1, 1\}^n \to \mathbb{R}$ satisfies
$\mathrm{Stab}_\rho[f] \ge \mathrm{Stab}_\rho[\mathrm{Maj}_n]$ for every real $\rho$ with
$0 \le \rho \le 1$, where $\mathrm{Stab}_\rho$ is the noise stability and $\mathrm{Maj}_n$ is the
majority function. -/
def MajorityIsLeastStableFor (n : ℕ) : Prop :=
  ∀ f : BoolCube n → ℝ, IsLinearThresholdFunction f → ∀ ρ : ℝ, 0 ≤ ρ → ρ ≤ 1 →
    noiseStability ρ (majority n) ≤ noiseStability ρ f

/-- **Majority Is Least Stable in some odd dimension at least five.** There is an odd natural
number $n \ge 5$ for which the Majority Is Least Stable conjecture in $n$ variables holds: every
linear threshold function $f : \{-1, 1\}^n \to \mathbb{R}$ satisfies
$\mathrm{Stab}_\rho[f] \ge \mathrm{Stab}_\rho[\mathrm{Maj}_n]$ for every real $\rho$ with
$0 \le \rho \le 1$, where $\mathrm{Stab}_\rho$ is the noise stability and $\mathrm{Maj}_n$ is the
majority function. -/
def majorityIsLeastStableForSomeOddAtLeastFive : Prop :=
  ∃ n : ℕ, Odd n ∧ 5 ≤ n ∧ MajorityIsLeastStableFor n

/--
**Majority Is Least Stable fails in every odd dimension at least five.** For every odd natural
number $n \ge 5$, the Majority Is Least Stable conjecture in $n$ variables fails: there are a
linear threshold function $f : \{-1, 1\}^n \to \mathbb{R}$ and a real number $\rho$ with
$0 \le \rho \le 1$ such that $\mathrm{Stab}_\rho[f] < \mathrm{Stab}_\rho[\mathrm{Maj}_n]$, where
$\mathrm{Stab}_\rho$ is the noise stability and $\mathrm{Maj}_n$ is the majority function.

Biswas and Sarkar exhibit, for every odd $n \ge 5$, a linear threshold function $g_n$ with
$\mathrm{Stab}_\rho[g_n] < \mathrm{Stab}_\rho[\mathrm{Maj}_n]$ for all small $\rho > 0$. The
conjecture holds for $n = 1$ and $n = 3$; those cases are not formalized here.

Source: R. O'Donnell, Open problems in analysis of Boolean
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
