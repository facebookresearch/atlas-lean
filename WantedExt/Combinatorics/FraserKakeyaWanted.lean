/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fraser: Fourier decay for finite-field Kakeya sets is q^{-1} and sharp

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.FraserKakeya` — fraser_kakeya_fourier_decay (manifest `manifests/problems/fraser_kakeya_fourier_decay.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.FraserKakeyaWanted` namespace. Mathematical
statements are unchanged. Source: J.M. Fraser, 'Fourier analytic properties of Kakeya sets in finite fields', Bull. London Math. Soc. 58(5) (2026); DOI 10.1112/blms.70367; arXiv:2505.09464.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Combinatorics.FraserKakeyaWanted
namespace Combinatorics
namespace FraserKakeyaProblem

/-!
# Fraser: Fourier decay for finite-field Kakeya sets

For every dimension `d ≥ 2`, every finite-field Kakeya set
`K ⊆ F_q^d` supports a probability measure whose finite-field Fourier
transform is bounded by `q^{-1}` at every nonzero frequency, **and**
this exponent is sharp in every dimension (for sufficiently large
`q`). Jonathan M. Fraser, *Fourier analytic properties of Kakeya sets
in finite fields*, Bull. London Math. Soc. **58**(5) (2026); DOI
`10.1112/blms.70367`; arXiv:2505.09464.

A *finite-field Kakeya set* is a subset of `F_q^d` containing a line
in every direction. The theorem combines the upper Fourier-decay
bound with a matching sharpness construction valid in arbitrary
ambient dimension.
-/

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The ambient finite vector space `F_q^d`. -/
abbrev Space (F : Type*) (d : ℕ) := Fin d → F

/-- Standard dot product on `F_q^d`. -/
def dot {d : ℕ} (x y : Space F d) : F :=
  ∑ i, x i * y i

/-- The affine line with base point `y` and direction `x`. -/
def affineLine {d : ℕ} (y x : Space F d) : Set (Space F d) :=
  {z | ∃ a : F, z = y + a • x}

/-- A **Kakeya set**: it contains a line in every direction. -/
def IsKakeya {d : ℕ} (K : Set (Space F d)) : Prop :=
  ∀ x : Space F d, ∃ y : Space F d, affineLine y x ⊆ K

/-- A real-valued probability measure on the finite vector space
whose support is contained in `K`. -/
def IsProbabilityMeasureOn {d : ℕ} (K : Set (Space F d))
    (μ : Space F d → ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ (∑ x, μ x = 1) ∧ ∀ x, μ x ≠ 0 → x ∈ K

/-- The finite-field Fourier transform with respect to a nontrivial
additive character. -/
noncomputable def fourier {d : ℕ} (χ : AddChar F ℂ) (μ : Space F d → ℝ)
    (ξ : Space F d) : ℂ :=
  ∑ x, χ (-(dot ξ x)) * (μ x : ℂ)

/- **Fraser, Theorem 2.4.** Every finite-field Kakeya set in
dimension `d ≥ 2` supports a probability measure with finite-field
Fourier transform bounded by `q^{-1}` at every nonzero frequency, and
this exponent is sharp in every dimension `d ≥ 2`: for every
`κ ∈ (0, 1)` there is a threshold `Q` such that every finite field
`F'` with `|F'| ≥ Q` admits a Kakeya set `K' ⊆ F'^d` on which every
probability measure has some nonzero frequency at which the Fourier
transform satisfies `‖μ̂(ξ)‖ ≥ κ · q'^{-1}`. -/
/-- Source: J.M. Fraser, 'Fourier analytic properties of Kakeya sets in finite fields', Bull. London Math. Soc. 58(5) (2026); DOI 10.1112/blms.70367; arXiv:2505.09464. Via leanprover/lean-eval@38361be, problem `fraser_kakeya_fourier_decay`. -/
public theorem_wanted fraser_kakeya_fourier_decay_and_sharp
    {d : ℕ} (_hd : 2 ≤ d) {K : Set (Space F d)} (_hK : IsKakeya K)
    (χ : AddChar F ℂ) (_hχ : χ ≠ 1) :
    (∃ μ : Space F d → ℝ, IsProbabilityMeasureOn K μ ∧
      ∀ ξ : Space F d, ξ ≠ 0 →
        ‖fourier χ μ ξ‖ ≤ (Fintype.card F : ℝ)⁻¹) ∧
    (∀ κ : ℝ, 0 < κ → κ < 1 →
      ∃ Q : ℕ, ∀ (F' : Type*) [Field F'] [Fintype F'] [DecidableEq F'],
        Q ≤ Fintype.card F' →
          ∃ K' : Set (Space F' d), IsKakeya K' ∧
            ∀ μ : Space F' d → ℝ, IsProbabilityMeasureOn K' μ →
              ∃ ξ : Space F' d, ξ ≠ 0 ∧
                κ * (Fintype.card F' : ℝ)⁻¹ ≤
                  ‖fourier (AddChar.FiniteField.primitiveChar_to_Complex F') μ ξ‖)

end FraserKakeyaProblem
end Combinatorics

end MathlibExt.Combinatorics.FraserKakeyaWanted
