/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lorentzian polynomials

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.LorentzianPolynomials` — annals_lorentzian_polynomials (manifest `manifests/problems/annals_lorentzian_polynomials.toml`, rev 1, submitter Justus Springer, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.LorentzianPolynomialsWanted` namespace. Mathematical
statements are unchanged. Source: P. Brändén and J. Huh, `Lorentzian polynomials`, Annals of Math, 192 (3) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-3-LorentzianPolynomials.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.RingTheory.MvPolynomial.EulerIdentity
public import Mathlib.Topology.Algebra.Module.ModuleTopology

@[expose] public section

namespace MathlibExt.Combinatorics.LorentzianPolynomialsWanted
/-!
# Main Statement from Lorentzian polynomials

We formalise the statement of the main result from P. Brändén and J. Huh,
`Lorentzian polynomials`, Annals of Math, 192 (3) 2020.
-/

set_option autoImplicit false

namespace LorentzianPolynomials

open Finsupp Matrix MvPolynomial UpperHalfPlane

/-- We write `H n d` for the set of degree `d` homogeneous polynomials in `ℝ[w₁,...,wₙ]`. -/
def H (n d : ℕ) : Type := homogeneousSubmodule (Fin n) ℝ d

/-- See start of Section 2: We define a topology on `H n d` using the Euclidean norm
for the coefficients. Since `homogeneousSubmodule (Fin n) ℝ d` is a finite-dimensional
`ℝ`-vector space, this coincides with its module topology over `ℝ`. -/
noncomputable instance {n d : ℕ} : TopologicalSpace (H n d) :=
  moduleTopology ℝ (homogeneousSubmodule (Fin n) ℝ d)

/-- The set of degree `d` homogeneous polynomials in `ℝ[w₁,...,wₙ]` whose coefficients
are positive. -/
abbrev P (n d : ℕ) : Set (H n d) :=
  { f | ∀ m : Fin n →₀ ℕ, weight 1 m = d → 0 < f.1.coeff m }

/-- The Hessian matrix of a degree 2 homogeneous polynomial `f` in `n` variables. -/
noncomputable def H.hessian {n : ℕ} (f : H n 2) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j ↦
    if i = j then
      2 * f.1.coeff (single i 2)
    else
      f.1.coeff (single i 1 + single j 1)

/-- The set of degree `d` strictly Lorentzian polynomials in `ℝ[w₁,...,wₙ]`. -/
def Ŀ (n d : ℕ) : Set (H n d) := match d with
  | 0 => P n 0
  | 1 => P n 1
  | 2 => { f ∈ P n 2 | IsUnit f.hessian ∧ (f.hessian.charpoly.roots.filter (0 < ·)).card = 1 }
  | d + 3 => { f ∈ P n (d + 3) | ∀ i, ⟨f.1.pderiv i, f.2.pderiv⟩ ∈ Ŀ n (d + 2) }

/-- A subset `J ⊆ ℕⁿ` is said to be M-convex, if for any `α, β ∈ J` and any index `i`
satisfying `αᵢ > βᵢ`, there is an index `j` satisfying `αⱼ < βⱼ` and `α - eᵢ + eⱼ ∈ J`. -/
def IsMConvex {n : ℕ} (J : Set (Fin n →₀ ℕ)) : Prop :=
  ∀ α ∈ J, ∀ β ∈ J, ∀ i, α i > β i → ∃ j, α j < β j ∧ α - single i 1 + single j 1 ∈ J

/-- We write `M n d` for the set of all degree `d` homogeneous polynomials with non-negative
coefficients in `ℝ[w₁,...,wₙ]` whose supports are M-convex. -/
abbrev M (n d : ℕ) : Set (H n d) :=
  { f | IsMConvex (f.1.support : Set (Fin n →₀ ℕ)) ∧ ∀ m, 0 ≤ f.1.coeff m }

/-- A polynomial `f` in `ℝ[w₁,...,wₙ]` is stable if it is nonvanishing on
`ℍⁿ` or identically zero, where `ℍ` is the open upper half plane in `ℂ`. -/
def IsStable {n : ℕ} (f : MvPolynomial (Fin n) ℝ) : Prop :=
  f = 0 ∨ ∀ z : Fin n → ℍ, aeval (((↑) : ℍ → ℂ) ∘ z) f ≠ 0

/-- Let `S n d` be the set of degree `d` homogeneous stable polynomials in `n` variables
with nonnegative coefficients. -/
abbrev S (n d : ℕ) : Set (H n d) := { f | IsStable f.1 ∧ ∀ m, 0 ≤ f.1.coeff m }

/-- We set `L n 0 := S n 0`, `L n 1 := S n 1`, and `L n 2 := S n 2`.
For `d` larger than 2, we define `L n d := { f ∈ M n d | ∂ᵢf ∈ L n (d−1) for all i ∈ [n] }`. -/
def L (n d : ℕ) : Set (H n d) := match d with
  | 0 => S n 0
  | 1 => S n 1
  | 2 => S n 2
  | d + 3 => { f ∈ M n (d + 3) | ∀ i, ⟨f.1.pderiv i, f.2.pderiv⟩ ∈ L n (d + 2) }

/--
Statement of Theorem 2.25:

The closure of `Ŀ n d` in `H n d` is `L n d`.

The paper allows `n` and `d` to be nonnegative, but the theorem is false for `n = 0` and `d = 2`
where `Ŀ 0 2 = {f ∈ P 0 2 | ℋ_f is nonsingular and has exactly one positive eigenvalue } = ∅`
since the `0×0` Hessian matrix of `f` cannot have a positive eigenvalue, but `L 0 2 = S 0 2`
contains the zero polynomial since the zero polynomial is homogeneous of degree `2`.
Source: P. Brändén and J. Huh, `Lorentzian polynomials`, Annals of Math, 192 (3) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-3-LorentzianPolynomials.lean Via leanprover/lean-eval@38361be, problem `annals_lorentzian_polynomials`.
-/
public theorem_wanted theorem_2_25 (n d : ℕ) (hn : 0 < n) : closure (Ŀ n d) = L n d

end LorentzianPolynomials

end MathlibExt.Combinatorics.LorentzianPolynomialsWanted
