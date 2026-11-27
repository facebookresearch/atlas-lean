/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Rademacher type and Enflo type coincide

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.RademacherEnfloType` — annals_rademacher_enflo_type (manifest `manifests/problems/annals_rademacher_enflo_type.toml`, rev 1, submitter David Ledvinka, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.RademacherEnfloTypeWanted` namespace. Mathematical
statements are unchanged. Source: P. Ivanisvili, R. van Handel, and A. Volberg, `Rademacher type and Enflo type coincide`, Annals of Math, 192 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-2-RademacherEnfloType.lean
-/
module


public import Batteries.Util.ProofWanted
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Distributions.Bernoulli
open ProbabilityTheory

@[expose] public section

namespace MathlibExt.Analysis.RademacherEnfloTypeWanted
/-!
# Notation for AnnalsChallenge

This file defines notation (mostly probability-theoretic) for the AnnalsChallenge project.

Ported verbatim from `AnnalsChallenge/Notation.lean` in
<https://github.com/ImperialCollegeLondon/AnnalsChallenge> (v1.0.0, `e32eb14`). It is a
trusted support module, not a benchmark problem: it contains no `sorry` and no
`@[eval_problem]` declarations. It is imported by `LeanEval.Analysis.RademacherEnfloType`
and `LeanEval.Analysis.SupremumOfSelectorProcesses`.
-/

set_option autoImplicit false

namespace ProbabilityTheory

open MeasureTheory Lean

/-- Suppose `P : Measure Ω`, `X : Ω → E`:

`𝔼[X; P] = ∫ ω, ↑(X ω) ∂P`

is notation for the integral (expectation) of a function `X` with respect to the measure `P`. -/
macro "𝔼[" X:term "; " P:term "]" : term => `(∫ ω, ↑($X ω) ∂$P)

/-- Suppose `μ : Measure E`

`𝔼[t; X ∼ μ] = ∫ X; t ∂μ`

where `X` is a variable and `t` is a term (possibly) depending on `X`. In probability theory
this represents the expectation of a function of `X` when `X` has law `μ`. For example we
could write `𝔼[X ^ 2; X ∼ μ]` for the second moment of `μ`.
-/
notation "𝔼[" t "; " X " ∼ " μ "]" => MeasureTheory.integral μ (fun X ↦ ↑t)

/-- Suppose `P : Measure Ω`, `X : Ω → ℝ≥0∞`:

`𝔼⁻[X; P] = ∫⁻ ω, ↑(X ω) ∂P`

is notation for the lintegral (expectation) of a function `X` with respect to the measure `P`. -/
macro "𝔼⁻[" X:term "; " P:term "]" : term => `(∫⁻ ω, ↑($X ω) ∂$P)

/-- Suppose `μ : Measure ℝ≥0∞`

`𝔼[t; X ∼ μ] = ∫ X; t ∂μ`

where `X` is a variable and `t` is a term (possibly) depending on `X`. In probability theory
this represents the expectation of a function of `X` when `X` has law `μ`. For example we
could write `𝔼⁻[X ^ 2; X ∼ μ]` for the second moment of `μ`.
-/
notation "𝔼⁻[" t "; " X " ∼ " μ "]" => MeasureTheory.lintegral μ (fun X ↦ ↑t)

end ProbabilityTheory

/-!
# Main Statement from Rademacher type and Enflo type coincide

We formalise the statement of the main result from P. Ivanisvili, R. van Handel, and A. Volberg,
`Rademacher type and Enflo type coincide`, Annals of Math, 192 (2) 2020.
-/

set_option autoImplicit false

namespace RademacherEnfloType

open Function MeasureTheory ProbabilityTheory Measure NNReal

open scoped ENNReal

instance : Neg ({-1, 1} : Set ℤ) where
  neg x := ⟨Neg.neg (α := ℤ) (x : ℤ), by grind⟩

/-- **Rademacher distribution.** The Rademacher distribution is the measure on $\{-1, 1\}$,
viewed as a subset of $\mathbb{Z}$, that gives mass $1/2$ to each of $1$ and $-1$. -/
noncomputable def rademacherDistribution : Measure ({-1, 1} : Set ℤ) :=
  bernoulliMeasure ⟨1, by decide⟩ ⟨-1, by decide⟩ ⟨1 / 2, by norm_num⟩

/-- **Product Rademacher distribution.** For an index type $\iota$, this is the product over
$\iota$ of copies of the Rademacher distribution: the joint law of a family
$(\varepsilon_i)_{i \in \iota}$ of independent Rademacher random variables, as a measure on the
functions $\iota \to \{-1, 1\}$. -/
noncomputable def rademacherProductDistribution (ι : Type*) :
    Measure (ι → ({-1, 1} : Set ℤ)) :=
  infinitePi (fun _ : ι ↦ rademacherDistribution)

/- Let `X` be a Banach space. -/
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- **Discrete partial derivative on the Rademacher cube.** Let $X$ be a real Banach space, $n$ a
natural number and $f : \{-1, 1\}^n \to X$. For $j \in \{1, \dots, n\}$ and
$\varepsilon = (\varepsilon_1, \dots, \varepsilon_n) \in \{-1, 1\}^n$, the discrete partial
derivative of $f$ in direction $j$ at $\varepsilon$ is
$$
D_j f(\varepsilon) = \frac{1}{2}\bigl(f(\varepsilon) -
f(\varepsilon_1, \dots, -\varepsilon_j, \dots, \varepsilon_n)\bigr),
$$
where only the $j$-th coordinate of $\varepsilon$ is negated in the second term.
-/
noncomputable def D {n : ℕ} (j : Fin n) (f : (Fin n → ({-1, 1} : Set ℤ)) → X)
      (ε : Fin n → ({-1, 1} : Set ℤ)) : X :=
  (1 / (2 : ℝ)) • (f ε - f (update ε j (- ε j)))

/- Let `X` be a Banach space. -/
variable (X : Type*) [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

/-- **Rademacher type.** Let $X$ be a real Banach space, $C \in [0, \infty]$ and $p$ a real
number. We say that $X$ has Rademacher type $p$ with constant $C$ if for every $n \ge 1$ and all
$x_1, \dots, x_n \in X$,
$$
\mathbb{E}\Bigl\|\sum_{j=1}^n \varepsilon_j x_j\Bigr\|^p \le C^p \sum_{j=1}^n \|x_j\|^p,
$$
where $\varepsilon_1, \dots, \varepsilon_n$ are independent Rademacher random variables. Both
sides are computed in $[0, \infty]$.
-/
def IsRademacherType (C : ℝ≥0∞) (p : ℝ) : Prop :=
  ∀ n ≥ 1, ∀ (x : Fin n → X),
    𝔼⁻[‖ ∑ j : Fin n, ((ε j) : ℝ) • (x j) ‖ₑ ^ p; ε ∼ rademacherProductDistribution (Fin n)]
    ≤ C ^ p * ∑ j : Fin n, ‖ x j ‖ₑ ^ p

/-- **Rademacher type constant.** For a real Banach space $X$ and a real number $p$,
$T^R_p(X)$ is the infimum in $[0, \infty]$ of all $C \in [0, \infty]$ such that $X$ has
Rademacher type $p$ with constant $C$. -/
noncomputable def TR (p : ℝ) : ℝ≥0∞ := sInf {C : ℝ≥0∞ | IsRademacherType X C p}

/-- **Enflo type.** Let $X$ be a real Banach space, $C \in [0, \infty]$ and $p$ a real number. We
say that $X$ has Enflo type $p$ with constant $C$ if for every $n \ge 1$ and every function
$f : \{-1, 1\}^n \to X$,
$$
\mathbb{E}\Bigl\|\frac{f(\varepsilon) - f(-\varepsilon)}{2}\Bigr\|^p \le
C^p \sum_{j=1}^n \mathbb{E}\,\|D_j f(\varepsilon)\|^p,
$$
where $\varepsilon = (\varepsilon_1, \dots, \varepsilon_n)$ is a sequence of independent
Rademacher random variables, $-\varepsilon = (-\varepsilon_1, \dots, -\varepsilon_n)$, and
$D_j f$ is the discrete partial derivative of $f$ in direction $j$. Both sides are computed in
$[0, \infty]$.
-/
def IsEnfloType (C : ℝ≥0∞) (p : ℝ) : Prop :=
    ∀ n ≥ 1, ∀ (f : (Fin n → ({-1, 1} : Set ℤ)) → X),
  𝔼⁻[‖ (1 / (2 : ℝ)) • (f ε - f (- ε)) ‖ₑ ^ p; ε ∼ rademacherProductDistribution (Fin n)]
  ≤ C ^ p * ∑ j : Fin n, 𝔼⁻[‖ D j f ε ‖ₑ ^ p; ε ∼ rademacherProductDistribution (Fin n)]

/-- **Enflo type constant.** For a real Banach space $X$ and a real number $p$, $T^E_p(X)$ is
the infimum in $[0, \infty]$ of all $C \in [0, \infty]$ such that $X$ has Enflo type $p$ with
constant $C$. -/
noncomputable def TE (p : ℝ) : ℝ≥0∞ := sInf {C : ℝ≥0∞ | IsEnfloType X C p}

/--
**Comparison of Rademacher and Enflo type constants.** For every real Banach space $X$ and every
real number $p$ with $1 \le p \le 2$, the Rademacher type constant and the Enflo type constant
of $X$ satisfy $T^R_p(X) \le T^E_p(X) \le \frac{\pi}{\sqrt{2}}\, T^R_p(X)$.

Source: P. Ivanisvili, R. van Handel, and A. Volberg, `Rademacher type and Enflo type coincide`, Annals of Math, 192 (2) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-2-RademacherEnfloType.lean Via leanprover/lean-eval@38361be, problem `annals_rademacher_enflo_type`.
-/
public theorem_wanted theorem_1_1 (p : ℝ) (h1p : 1 ≤ p) (hp2 : p ≤ 2) :
    TR X p ≤ TE X p ∧ TE X p ≤ (pi / sqrt 2) * TR X p

end RademacherEnfloType

end MathlibExt.Analysis.RademacherEnfloTypeWanted
