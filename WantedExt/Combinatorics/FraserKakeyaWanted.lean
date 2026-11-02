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

/-- **Coordinate space.** For a type $F$ and a natural number $d$, $F^d$ denotes the set of
$d$-tuples $(x_1, \dots, x_d)$ of elements of $F$, that is, functions from a $d$-element index set
to $F$.

In this module $F$ is a finite field, so $F^d$ is the $d$-dimensional vector space over $F$. -/
abbrev Space (F : Type*) (d : ℕ) := Fin d → F

/-- **Dot product.** Let $F$ be a finite field and $d$ a natural number. For $x, y \in F^d$, the
dot product is $x \cdot y = \sum_{i} x_i y_i \in F$, the sum running over the $d$ coordinates. -/
def dot {d : ℕ} (x y : Space F d) : F :=
  ∑ i, x i * y i

/-- **Affine line.** Let $F$ be a finite field and $d$ a natural number. For $y, x \in F^d$, the
affine line with base point $y$ and direction $x$ is the set $\{y + a x : a \in F\} \subseteq F^d$.
When $x = 0$ this set is the single point $\{y\}$. -/
def affineLine {d : ℕ} (y x : Space F d) : Set (Space F d) :=
  {z | ∃ a : F, z = y + a • x}

/-- **Kakeya set.** Let $F$ be a finite field and $d$ a natural number. A set $K \subseteq F^d$ is a
Kakeya set if for every $x \in F^d$ there is $y \in F^d$ such that the affine line
$\{y + a x : a \in F\}$ is contained in $K$; that is, $K$ contains a line in every direction. -/
def IsKakeya {d : ℕ} (K : Set (Space F d)) : Prop :=
  ∀ x : Space F d, ∃ y : Space F d, affineLine y x ⊆ K

/-- **Probability measure supported on a set.** Let $F$ be a finite field, $d$ a natural number
and $K \subseteq F^d$. A function $\mu : F^d \to \mathbb{R}$ is a probability measure on $K$ if
$\mu(x) \ge 0$ for every $x \in F^d$, $\sum_{x \in F^d} \mu(x) = 1$, and $\mu(x) \ne 0$ implies
$x \in K$. -/
def IsProbabilityMeasureOn {d : ℕ} (K : Set (Space F d))
    (μ : Space F d → ℝ) : Prop :=
  (∀ x, 0 ≤ μ x) ∧ (∑ x, μ x = 1) ∧ ∀ x, μ x ≠ 0 → x ∈ K

/-- **Finite-field Fourier transform.** Let $F$ be a finite field, $d$ a natural number and $\chi$
an additive character of $F$ with values in $\mathbb{C}$. For $\mu : F^d \to \mathbb{R}$ and
$\xi \in F^d$, the Fourier transform of $\mu$ at $\xi$ is
$\hat{\mu}(\xi) = \sum_{x \in F^d} \chi(-\xi \cdot x)\, \mu(x) \in \mathbb{C}$, where
$\xi \cdot x$ is the dot product.

The definition allows any character; it is used with a nontrivial one. -/
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
/-- **Fraser's Fourier decay theorem for finite-field Kakeya sets.** Let $F$ be a finite field
with $q$ elements, let $d \ge 2$ be a natural number, let $K \subseteq F^d$ be a Kakeya set and let
$\chi$ be a nontrivial additive character of $F$ with values in $\mathbb{C}$. Then, first, there is
a probability measure $\mu$ on $K$ whose Fourier transform $\hat{\mu}$ with respect to $\chi$
satisfies $|\hat{\mu}(\xi)| \le q^{-1}$ for every nonzero $\xi \in F^d$. Second, this bound is
sharp: for every real $\kappa$ with $0 < \kappa < 1$ there is a natural number $Q$ such that for
every finite field $F'$ with $q' \ge Q$ elements there is a Kakeya set $K' \subseteq (F')^d$ such
that every probability measure $\mu$ on $K'$ has a nonzero $\xi \in (F')^d$ at which its Fourier
transform $\hat{\mu}$ with respect to a fixed primitive additive character of $F'$ satisfies
$|\hat{\mu}(\xi)| \ge \kappa \, q'^{-1}$.

Source: J.M. Fraser, 'Fourier analytic properties of Kakeya sets in finite fields', Bull. London Math. Soc. 58(5) (2026); DOI 10.1112/blms.70367; arXiv:2505.09464. Via leanprover/lean-eval@38361be, problem `fraser_kakeya_fourier_decay`. -/
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
