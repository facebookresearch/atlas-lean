/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Pointwise ergodic theorems for non-conventional bilinear polynomial averages

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.

Attribution and modification notice (Apache License 2.0, Section 4):
taken from leanprover/lean-eval at commit
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Dynamics.PointwiseErgodicTheorems` — annals_pointwise_ergodic_theorems (manifest `manifests/problems/annals_pointwise_ergodic_theorems.toml`, rev 1, submitter David Ledvinka, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Dynamics.PointwiseErgodicTheoremsWanted` namespace. Mathematical
statements are unchanged. Source: B. Krause, M. Mirek, and T. Tao, `Pointwise ergodic theorems for non-conventional bilinear polynomial averages`, Annals of Math, 195 (3) 2022. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2022-195-3-PointwiseErgodicTheorems.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Normed.Lp.PiLp
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

@[expose] public section

namespace MathlibExt.Dynamics.PointwiseErgodicTheoremsWanted
/-!
# Main Statements from Pointwise ergodic theorems for non-conventional bilinear polynomial averages

We formalise the statements of the main results from B. Krause, M. Mirek, and T. Tao,
`Pointwise ergodic theorems for non-conventional bilinear polynomial averages`,
Annals of Math, 195 (3) 2022.
-/

set_option autoImplicit false

namespace PointwiseErgodicTheorems

open MeasureTheory Polynomial Finset Filter Topology

open scoped ENNReal NNReal PNat

/-- We say a sequence `a : ℕ → ℝ≥0` is `Λ-lacunary` if for each `n ∈ ℕ`, `a (n + 1) / a n > Λ`. -/
def Lacunary (Λ : ℝ≥0) (a : ℕ → ℝ≥0) : Prop := ∀ n, a (n + 1) / a n > Λ

/-- We define the `r`-variational norm of a sequence `a : ℕ → ℂ` by
`‖a‖_𝕍ʳ :=`
  `sup_{n ∈ ℕ} |a_n| + sup_{J ∈ ℕ} sup_{N_0 ≤ … ≤ N_J} (∑_j^{J-1} |a_{N_{j+1}} - a_{N_j}|^r)^{1/r}`.
-/
noncomputable def variationalNorm (r : ℝ≥0) (a : ℕ → ℂ) : ℝ≥0∞ :=
  (⨆ n, ‖a n‖ₑ) + ⨆ (J : ℕ) (N : ℕ → ℕ) (_ : Monotone N),
    ENNReal.ofReal ‖(WithLp.toLp r (fun (i : Fin J) ↦ a (N (i + 1)) - a (N i)))‖

/- We assume that `(X, μ, T)` is a Measure-preserving system. That is `(X, μ)` is a
`σ`-finite measure space, and `T : X → X` is an invertible bimeasurable map that is
measure preserving in the sense that `μ(T(E)) = μ(E)` for all measurable `E`.-/
variable {𝓧 : Type*} [σX : MeasurableSpace 𝓧] {μ : Measure 𝓧} [SigmaFinite μ]
  {T : 𝓧 ≃ᵐ 𝓧} (hT : MeasurePreserving T μ μ)

include hT

/-- Given a real number `N ≥ 0`, `P₁, P₂ ∈ ℤ[X]`, `f,g : X → ℂ`, we define the bilinear
averages by the formula
`A T N P₁ P₂ f g x := ⌊N⌋⁻¹ ∑_{n=1}^{⌊N⌋} f(T^{P₁(n)} x) g(T^{P₂(n)} x)`. -/
noncomputable def A (T : 𝓧 ≃ᵐ 𝓧) (N : ℝ≥0) (P₁ : ℤ[X]) (P₂ : ℤ[X]) (f g : 𝓧 → ℂ) (x : 𝓧) : ℂ :=
  (Nat.floor N : ℝ)⁻¹ * ∑ n ∈ Icc 1 (Nat.floor N),
    f ((T ^ (P₁.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x) * g ((T ^ (P₂.eval (n : ℤ)) : 𝓧 ≃ 𝓧) x)

/- Let `P : ℤ[X]` be a polynomial with degree at least `2`. -/
variable {P : ℤ[X]} (hP : P.degree ≥ 2)

include hP

/- Let `p₁, p₂, p` be real numbers such that `1 < p₁, p₂ < ∞` and `p₁⁻¹ + p₂⁻¹ = p⁻¹ ≤ 1`. -/
variable {p₁ p₂ p : ℝ≥0∞} (h₁p₁ : 1 < p₁) (h₁p₂ : 1 < p₂) (h₂p₁ : p₁ < ∞) (h₂p₂ : p₂ < ∞)
  (hp₁p₂p : p₁⁻¹ + p₂⁻¹ = p⁻¹) (hp : p⁻¹ ≤ 1)

include h₁p₁ h₁p₂ h₂p₁ h₁p₂ h₂p₂ hp₁p₂p hp

/--
Statement of Theorem 1.17(i) (Mean ergodic theorem):

The averages `A T N X P f g` converge as `N → ∞` in `Lᵖ(X)` norm.
Source: B. Krause, M. Mirek, and T. Tao, `Pointwise ergodic theorems for non-conventional bilinear polynomial averages`, Annals of Math, 195 (3) 2022. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2022-195-3-PointwiseErgodicTheorems.lean Via leanprover/lean-eval@38361be, problem `annals_pointwise_ergodic_theorems`.
-/
public theorem_wanted theorem_1_17_i {f g : 𝓧 → ℂ} (hf : MemLp f p₁ μ) (hg : MemLp g p₂ μ) :
    ∃ h : 𝓧 → ℂ, MemLp h p μ ∧
    Tendsto (fun N ↦ eLpNorm (A T N (X : ℤ[X]) P f g - h) p μ) atTop (𝓝 0)

/--
Statement of Theorem 1.17(ii) (Pointwise ergodic theorem):

The averages `A T N X P f g` converge as `N → ∞` pointwise almost everywhere.
Source: B. Krause, M. Mirek, and T. Tao, `Pointwise ergodic theorems for non-conventional bilinear polynomial averages`, Annals of Math, 195 (3) 2022. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2022-195-3-PointwiseErgodicTheorems.lean Via leanprover/lean-eval@38361be, problem `annals_pointwise_ergodic_theorems`.
-/
public theorem_wanted theorem_1_17_ii {f g : 𝓧 → ℂ} (hf : MemLp f p₁ μ) (hg : MemLp g p₂ μ) :
    ∃ h : 𝓧 → ℂ, MemLp h p μ ∧
    ∀ᵐ x ∂μ, Tendsto (fun N ↦ A T N (X : ℤ[X]) P f g x) atTop (𝓝 (h x))

/--
Statement of Theorem 1.17(iii) (Maximal ergodic theorem):

There exists a constant `C ≥ 0` such that for any `f ∈ Lᵖ₁(X)` and `g ∈ Lᵖ₂(X)`,
`‖A T (N : ℕ+) X P f g‖_{Lᵖ(X;ℓ∞)} ≤ C ‖f‖_{Lᵖ₁(X)} ‖g‖_{Lᵖ₂(X)}`.
Source: B. Krause, M. Mirek, and T. Tao, `Pointwise ergodic theorems for non-conventional bilinear polynomial averages`, Annals of Math, 195 (3) 2022. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2022-195-3-PointwiseErgodicTheorems.lean Via leanprover/lean-eval@38361be, problem `annals_pointwise_ergodic_theorems`.
-/
public theorem_wanted theorem_1_17_iii : ∃ C : ℝ≥0, ∀ {f g : 𝓧 → ℂ} (hf : MemLp f p₁ μ) (hg : MemLp g p₂ μ),
    eLpNorm (fun x ↦ ⨆ (N : ℕ+), ‖A T N (X : ℤ[X]) P f g x‖ₑ) p μ ≤
      C * ‖hf.toLp‖ₑ * ‖hg.toLp‖ₑ

/--
Statement of Theorem 1.17(iv) (Long variational ergodic theorem):

For any `r > 2` and `Λ > 1`, there exists a constant `C ≥ 0` such that for any `f ∈ Lᵖ₁(X)`,
`g ∈ Lᵖ₂(X)` and `Λ`-lacunary sequence `a` such that `1 ≤ a n` for all `n ∈ ℕ`,
`‖A T (a n) X P f g‖_{Lᵖ(X;Vʳ)} ≤ C ‖f‖_{Lᵖ₁(X)} ‖g‖_{Lᵖ₂(X)}`.
Source: B. Krause, M. Mirek, and T. Tao, `Pointwise ergodic theorems for non-conventional bilinear polynomial averages`, Annals of Math, 195 (3) 2022. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2022-195-3-PointwiseErgodicTheorems.lean Via leanprover/lean-eval@38361be, problem `annals_pointwise_ergodic_theorems`.
-/
public theorem_wanted theorem_1_17_iv (r Λ : ℝ≥0) (hr : r > 2) (hΛ : Λ > 1) :
    ∃ C : ℝ≥0, ∀ {f g : 𝓧 → ℂ} (hf : MemLp f p₁ μ) (hg : MemLp g p₂ μ) (a : ℕ → ℝ≥0),
    Lacunary Λ a → (∀ n, 1 ≤ a n) →
    eLpNorm (fun x ↦ variationalNorm r fun n ↦ A T (a n) X P f g x) p μ ≤
      C * ‖hf.toLp‖ₑ * ‖hg.toLp‖ₑ

end PointwiseErgodicTheorems

end MathlibExt.Dynamics.PointwiseErgodicTheoremsWanted
