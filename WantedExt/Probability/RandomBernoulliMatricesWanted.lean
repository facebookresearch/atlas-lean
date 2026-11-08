/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Singularity of random Bernoulli matrices

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.LinearAlgebra.RandomBernoulliMatrices` — annals_random_bernoulli_matrices (manifest `manifests/problems/annals_random_bernoulli_matrices.toml`, rev 1, submitter David Ledvinka, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Probability.RandomBernoulliMatricesWanted` namespace. Mathematical
statements are unchanged. Source: K. Tikhomirov, `Singularity of random Bernoulli matrices`, Annals of Math, 191 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-191-2-RandomBernoulliMatrices.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Distributions.Bernoulli

@[expose] public section

namespace MathlibExt.Probability.RandomBernoulliMatricesWanted
/-!
# Main Statements from Singularity of random Bernoulli matrices

We formalise the statements of the main results from K. Tikhomirov,
`Singularity of random Bernoulli matrices`, Annals of Math, 191 (2) 2020.
-/

set_option autoImplicit false

namespace RandomBernoulliMatrices

open Matrix MeasureTheory ProbabilityTheory Measure Filter unitInterval

open scoped ENNReal

/-- We define the smallest singular value `σ_min` of a `n × m` matrix `M` by the formula

`σ_min(M) := inf_{‖x‖₂ = 1} ‖M x‖₂`. -/
noncomputable def σ_min {𝕜 n m : Type*} [Fintype n] [Fintype m] [DecidableEq m]
    [RCLike 𝕜] (M : Matrix n m 𝕜) :=
  ⨅ x : {x : EuclideanSpace 𝕜 m // ‖x‖ = 1}, ‖M.toEuclideanLin x‖

/-- We define the Rademacher measure as the probability measure on `ℝ`, which assigns
`1/2` mass to `1` and `1/2` mass to `-1`. -/
noncomputable def rademacherMeasure : Measure ℝ :=
  bernoulliMeasure 1 (-1) ⟨1 / 2, by norm_num⟩

/--
Statement of Theorem A:

For every `p ∈ (0, 1/2]` and `ε > 0` there exists `N, C > 0` such that for any `n ≥ N` and any
`n × n` random matrix `B` with mutually independent `Bernoulli(p)` entries,

`P(σ_min (B + sIIᵀ) ≤ t/√n) ≤ (1 - p + ε)ⁿ + Ct` for all `s ∈ [-1,0]` and `t > 0`.
Source: K. Tikhomirov, `Singularity of random Bernoulli matrices`, Annals of Math, 191 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-191-2-RandomBernoulliMatrices.lean Via leanprover/lean-eval@38361be, problem `annals_random_bernoulli_matrices`.
-/
public theorem_wanted theorem_A {p : I} {ε : ℝ} (hp₀ : 0 < p) (hp₁ : (p : ℝ) ≤ 1 / 2) (hε : 0 < ε) :
    ∃ N > 0, ∃ C > 0, ∀ n ≥ N,
      ∀ (Ω : Type*) (_mΩ : MeasurableSpace Ω) (P : Measure Ω) (B : Ω → Matrix (Fin n) (Fin n) ℝ)
        (_B_indep : iIndepFun (fun x : Fin n × Fin n ↦ (B · x.1 x.2)) P)
        (_B_bernoulli : ∀ i j, HasLaw (B · i j) (bernoulliMeasure 1 0 p) P),
        ∀ s : ℝ, -1 ≤ s ∧ s ≤ 0 → ∀ t : ℝ, 0 < t →
          P.real {ω : Ω | σ_min (B ω + of (fun _ _ ↦ s)) ≤ t / √n} ≤ (1 - p + ε) ^ n + C * t

/--
This (unnamed) corollary appears directly below Theorem A in the paper:

For every `p ∈ (0, 1/2]` and any sequence `Bₙ` of `n × n` random matrices with mutually
independent `Bernoulli(p)` entries we have that

`P(Bₙ is singular) = (1 - p + oₙ(1))ⁿ`.
Source: K. Tikhomirov, `Singularity of random Bernoulli matrices`, Annals of Math, 191 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-191-2-RandomBernoulliMatrices.lean Via leanprover/lean-eval@38361be, problem `annals_random_bernoulli_matrices`.
-/
public theorem_wanted corollary_1 {p : I} (hp₀ : 0 < p) (hp₁ : (p : ℝ) ≤ 1 / 2)
    {Ω : ℕ → Type*} [mΩ : ∀ n, MeasurableSpace (Ω n)] {P : (n : ℕ) → Measure (Ω n)}
    {B : (n : ℕ) → Ω n → Matrix (Fin n) (Fin n) ℝ}
    (B_indep : ∀ n, iIndepFun (fun x : Fin n × Fin n ↦ (B n · x.1 x.2)) (P n))
    (B_bernoulli : ∀ n i j, HasLaw (B n · i j) (bernoulliMeasure 1 0 p) (P n)) :
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ n > 0, (P n).real {ω | (B n ω).det = 0} = (1 - p + o n) ^ n

/--
This is the result stated in the paper's abstract:

For any sequence `Mₙ` of `n × n` random matrices with mutually independent `Rademacher` entries
we have that

`P(Mₙ is singular) = (1/2 + oₙ(1))ⁿ`.
Source: K. Tikhomirov, `Singularity of random Bernoulli matrices`, Annals of Math, 191 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-191-2-RandomBernoulliMatrices.lean Via leanprover/lean-eval@38361be, problem `annals_random_bernoulli_matrices`.
-/
public theorem_wanted corollary_2 {Ω : ℕ → Type*} (mΩ : ∀ n, MeasurableSpace (Ω n)) {P : (n : ℕ) → Measure (Ω n)}
    {M : (n : ℕ) → Ω n → Matrix (Fin n) (Fin n) ℝ}
    (M_indep : ∀ n, iIndepFun (fun x : Fin n × Fin n ↦ (M n · x.1 x.2)) (P n))
    (M_rademacher : ∀ n i j, HasLaw (M n · i j) rademacherMeasure (P n)) :
    ∃ o : ℕ → ℝ, o =o[atTop] (1 : ℕ → ℝ) ∧
      ∀ n > 0, (P n).real {ω | (M n ω).det = 0} = (1 / 2 + o n) ^ n

end RandomBernoulliMatrices

end MathlibExt.Probability.RandomBernoulliMatricesWanted
