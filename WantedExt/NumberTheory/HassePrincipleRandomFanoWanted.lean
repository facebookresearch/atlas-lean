/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The Hasse principle for random Fano hypersurfaces

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.HassePrincipleRandomFano` — annals_hasse_principle_random_fano (manifest `manifests/problems/annals_hasse_principle_random_fano.toml`, rev 1, submitter Justus Springer, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.HassePrincipleRandomFanoWanted` namespace. Mathematical
statements are unchanged. Source: T. Browning, P. L. Boudec, and W. Sawin, `The Hasse principle for random Fano hypersurfaces`, Annals of Math, 197 (3) 2023. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2023-197-3-HassePrincipleRandomFano.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.LinearAlgebra.Projectivization.Basic
public import Mathlib.NumberTheory.NumberField.AdeleRing
public import Mathlib.RingTheory.MvPolynomial.Homogeneous

@[expose] public section

namespace MathlibExt.NumberTheory.HassePrincipleRandomFanoWanted
/-!
# Main Statement from The Hasse principle for random Fano hypersurfaces

We formalise the statement of the main result from T. Browning, P. L. Boudec, and W. Sawin,
`The Hasse principle for random Fano hypersurfaces`, Annals of Math, 197 (3) 2023.
-/

set_option autoImplicit false

namespace HassePrincipleRandomFano

open MvPolynomial Filter NumberField Real

open scoped LinearAlgebra.Projectivization

/-- The adele ring `𝔸 = 𝔸_ℚ` of the rationals. -/
abbrev 𝔸 := AdeleRing ℤ ℚ

/-- The height of a rational homogeneous polynomial `f`, defined as the Euclidean norm
of the primitive integer coefficient vector of `f`. -/
noncomputable def height {σ : Type*} (f : MvPolynomial σ ℚ) : ℝ :=
  let D : ℕ := f.support.lcm fun m ↦ (f.coeff m).den
  let intCoeff m := (D * f.coeff m).num
  let a m := intCoeff m / f.support.gcd intCoeff
  √ (f.support.sum fun m ↦ (a m) ^ 2)

/-- A polynomial `f : MvPolynomial σ R` has a solution in `S` if there exists a
unimodular vector `x : σ → S`, such that `f` evaluated at `x` is zero. Here, a vector
is unimodular if its components generate the ring. -/
def HasSolutionsIn {σ : Type*} {R : Type*} [CommSemiring R] (f : MvPolynomial σ R) (S : Type*)
    [CommSemiring S] [Algebra R S] : Prop :=
  ∃ x : σ → S, Ideal.span (Set.range x) = ⊤ ∧ aeval x f = 0

variable (d n : ℕ)

/-- The parameter space `𝕍 d n = ℙ^{N_{d,n}-1}(ℚ)` of degree-`d` hypersurfaces in `ℙⁿ`
defined over `ℚ`, where `N_{d,n} = C(n+d, d)` is the number of degree-`d` monomials in
`n+1` variables.
In Lean, we use the projectivization of the sub-vector space of homogeneous
degree-`d` polynomials directly, and don't bother with lexicographic ordering. -/
abbrev 𝕍 : Type := ℙ ℚ (homogeneousSubmodule (Fin (n + 1)) ℚ d)

/-- The set `𝕍_{d,n}(A)` of degree-`d` hypersurfaces in `ℙⁿ` with height at most `A`. -/
def heightLE (A : ℝ) : Set (𝕍 d n) := { V | height V.rep.1 ≤ A }

/-- The set `𝕍ˡᵒᶜ_{d,n}` of everywhere locally soluble degree-`d` hypersurfaces in `ℙⁿ`:
those `V` for which `V(𝔸_ℚ) ≠ ∅`, i.e., which have a solution in the adele ring. -/
def 𝕍Loc : Set (𝕍 d n) := { V | HasSolutionsIn V.rep.1 𝔸 }

/-- The local density `ϱˡᵒᶜ_{d,n}`: the limiting proportion of degree-`d` hypersurfaces
in `ℙⁿ` that are everywhere locally soluble, as the height bound tends to infinity.
By a theorem of Poonen–Voloch [17, Th. 3.6], this limit exists (and is positive) for
`(d, n) ≠ (2, 2)`, and equals a product of local densities over all places of `ℚ`. -/
noncomputable def ρLoc : ℝ :=
  atTop.limUnder fun A ↦ (𝕍Loc d n ∩ heightLE d n A).ncard / (heightLE d n A).ncard

/-- `ρ_{d,n}(A)` is the proportion of degree-`d` hypersurfaces in `ℙⁿ` of height at most `A`
that have a rational point:
`ρ_{d,n}(A) = #{V ∈ 𝕍_{d,n}(A) | V(ℚ) ≠ ∅} / #𝕍_{d,n}(A)`. -/
noncomputable def ρ (A : ℝ) : ℝ :=
  { V ∈ heightLE d n A | HasSolutionsIn V.rep.1 ℚ }.ncard / (heightLE d n A).ncard

/--
Statement of Theorem 1.1:

Let `d ≥ 2` and `n ≥ d` with `(d, n) ≠ (3, 3)`. Then we have `lim_{A → ∞} ρ_{d,n}(A) = ρˡᵒᶜ_{d,n}`.
Source: T. Browning, P. L. Boudec, and W. Sawin, `The Hasse principle for random Fano hypersurfaces`, Annals of Math, 197 (3) 2023. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2023-197-3-HassePrincipleRandomFano.lean Via leanprover/lean-eval@38361be, problem `annals_hasse_principle_random_fano`.
-/
public theorem_wanted theorem_1_1 (hd : 2 ≤ d) (h₁ : d ≤ n) (h₂ : (d, n) ≠ (3, 3)) :
    Tendsto (ρ d n) atTop (nhds (ρLoc d n))

end HassePrincipleRandomFano

end MathlibExt.NumberTheory.HassePrincipleRandomFanoWanted
