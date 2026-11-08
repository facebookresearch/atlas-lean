/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Sobolev embedding theorem (Morrey regime)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.SobolevMorrey` — sobolev_embedding_morrey (manifest `manifests/problems/sobolev_embedding_morrey.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.SobolevMorreyWanted` namespace. Mathematical
statements are unchanged. Source: C.B. Morrey, 'Functions of several variables and absolute continuity, II', Duke Math. J. 6 (1940) 187–215; full Sobolev-embedding development in *Multiple Integrals in the Calculus of Variations*, Springer 1966. Listed as §111 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Analysis.SobolevMorreyWanted
namespace Analysis
namespace SobolevMorreyProblem

/-!
# Sobolev embedding theorem (Morrey regime)

When `n < p` and `r + α < k − n/p`, every `W^{k,p}(ℝⁿ)` function has a
`C^{r,α}` representative — the Sobolev embedding into Hölder spaces.
Charles Morrey, *Functions of several variables and absolute
continuity, II*, Duke Math. J. **6** (1940). The theorem is listed as
§111 in Knill's *Some Fundamental Theorems in Mathematics*.

The `LocallyIntegrable f` conjunct in `MemSobolevWk` is essential to
faithfulness: without it, a non-a.e.-measurable `f` would make every
distributional pairing `∫ f · D^m φ` collapse to the default value
that Lean's Bochner integral assigns outside integrability hypotheses,
so `IsWeakDeriv f 0 m` would hold vacuously and `f` would spuriously
satisfy `W^{k,p}` membership while having no a.e.-equal continuous
representative.

Mathlib has the subcritical Gagliardo–Nirenberg–Sobolev inequality
(`eLpNorm_le_eLpNorm_fderiv_*`) and the Bessel-potential / `H^{s,p}`
spaces (`TemperedDistribution.MemSobolev`), but no
weak-derivative Sobolev space `W^{k,p}` and no Morrey-regime embedding.
-/

open MeasureTheory
open scoped ENNReal NNReal

/-- The model space `ℝⁿ`. -/
abbrev E (n : ℕ) := EuclideanSpace ℝ (Fin n)

/-- Classical partial derivative `∂_i φ` (directional derivative along
the `i`-th coordinate axis). -/
noncomputable def partialDeriv {n : ℕ} (i : Fin n) (φ : E n → ℝ) : E n → ℝ :=
  fun x => fderiv ℝ φ x (EuclideanSpace.single i (1 : ℝ))

/-- Classical mixed partial derivative `D^m φ` for a multi-index `m`. -/
noncomputable def mixedDeriv {n : ℕ} (m : Fin n → ℕ) (φ : E n → ℝ) : E n → ℝ :=
  (List.finRange n).foldr (fun i ψ => (partialDeriv i)^[m i] ψ) φ

/-- `g` is the **weak partial derivative** `D^m f` (multi-index `m`):
`∫ f · D^m φ = (−1)^{|m|} ∫ g · φ` for every smooth compactly supported
test function `φ`. -/
def IsWeakDeriv {n : ℕ} (f g : E n → ℝ) (m : Fin n → ℕ) : Prop :=
  ∀ φ : E n → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    ∫ x, f x * mixedDeriv m φ x = (-1) ^ (∑ i, m i) * ∫ x, g x * φ x

/-- Membership in `W^{k,p}(ℝⁿ)`: locally integrable, and every weak
derivative `D^m f` of order `|m| ≤ k` exists and lies in `L^p`. -/
def MemSobolevWk {n : ℕ} (k : ℕ) (p : ℝ≥0∞) (f : E n → ℝ) : Prop :=
  LocallyIntegrable f volume ∧
  ∀ m : Fin n → ℕ, (∑ i, m i) ≤ k →
    ∃ g : E n → ℝ, IsWeakDeriv f g m ∧ MemLp g p volume

/-- Membership in `C^{r,α}(ℝⁿ)`: `r`-times continuously differentiable,
derivatives up to order `r` bounded, `r`-th derivative `α`-Hölder. -/
def MemHolder {n : ℕ} (r : ℕ) (α : ℝ) (g : E n → ℝ) : Prop :=
  ContDiff ℝ (r : ℕ∞) g ∧
  (∃ C : NNReal, HolderWith C α.toNNReal (iteratedFDeriv ℝ r g)) ∧
  (∀ j ≤ r, ∃ M : ℝ, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ M)

/- **Sobolev embedding theorem (Morrey regime).** If `n < p`,
`0 < α ≤ 1` and `r + α < k − n/p`, then every `W^{k,p}(ℝⁿ)` function
has a `C^{r,α}` representative. -/
/-- Source: C.B. Morrey, 'Functions of several variables and absolute continuity, II', Duke Math. J. 6 (1940) 187–215; full Sobolev-embedding development in *Multiple Integrals in the Calculus of Variations*, Springer 1966. Listed as §111 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `sobolev_embedding_morrey`. -/
public theorem_wanted sobolev_embedding {n k r : ℕ} {α p : ℝ}
    (_hp : (n : ℝ) < p) (_hα : 0 < α) (_hα1 : α ≤ 1)
    (_hgap : (r : ℝ) + α < (k : ℝ) - n / p)
    (f : E n → ℝ) (_hf : MemSobolevWk k (ENNReal.ofReal p) f) :
    ∃ g : E n → ℝ, f =ᵐ[volume] g ∧ MemHolder r α g

end SobolevMorreyProblem
end Analysis

end MathlibExt.Analysis.SobolevMorreyWanted
