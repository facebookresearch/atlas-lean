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

/-- **Adele ring of the rationals.** $\mathbb{A}_\mathbb{Q}$, also written $\mathbb{A}$, is the
adele ring of $\mathbb{Q}$. -/
abbrev 𝔸 := AdeleRing ℤ ℚ

/-- **Height of a rational polynomial.** Let $f$ be a multivariate polynomial with rational
coefficients. Multiply the coefficients of $f$ by the least common multiple of their denominators
and divide the resulting integers by their greatest common divisor; this gives the primitive
integer coefficient vector $(a_m)_m$ of $f$, indexed by the monomials $m$ in the support of $f$.
The height of $f$ is the Euclidean norm $\sqrt{\sum_m a_m^2}$ of this vector. The zero polynomial
has height $0$. -/
noncomputable def height {σ : Type*} (f : MvPolynomial σ ℚ) : ℝ :=
  let D : ℕ := f.support.lcm fun m ↦ (f.coeff m).den
  let intCoeff m := (D * f.coeff m).num
  let a m := intCoeff m / f.support.gcd intCoeff
  √ (f.support.sum fun m ↦ (a m) ^ 2)

/-- **Unimodular solutions of a polynomial.** Let $R$ and $S$ be commutative semirings with $S$ an
$R$-algebra, and let $f$ be a multivariate polynomial over $R$ in variables indexed by a type
$\sigma$. Then $f$ has a solution in $S$ if there is a vector $x \in S^\sigma$ whose components
generate the unit ideal of $S$ and such that $f(x) = 0$, where $f$ is evaluated at $x$ through
the algebra map $R \to S$. -/
def HasSolutionsIn {σ : Type*} {R : Type*} [CommSemiring R] (f : MvPolynomial σ R) (S : Type*)
    [CommSemiring S] [Algebra R S] : Prop :=
  ∃ x : σ → S, Ideal.span (Set.range x) = ⊤ ∧ aeval x f = 0

variable (d n : ℕ)

/-- **Parameter space of hypersurfaces.** $\mathbb{V}_{d,n}$ is the projectivization of the
$\mathbb{Q}$-vector space of homogeneous polynomials of degree $d$ in $n + 1$ variables with
rational coefficients; its points are the degree-$d$ hypersurfaces in $\mathbb{P}^n$ defined over
$\mathbb{Q}$. Since this space has dimension $N_{d,n} = \binom{n+d}{d}$, the number of degree-$d$
monomials in $n + 1$ variables, $\mathbb{V}_{d,n}$ is a copy of
$\mathbb{P}^{N_{d,n} - 1}(\mathbb{Q})$. -/
abbrev 𝕍 : Type := ℙ ℚ (homogeneousSubmodule (Fin (n + 1)) ℚ d)

/-- **Hypersurfaces of bounded height.** For a real number $A$, $\mathbb{V}_{d,n}(A)$ is the set of
degree-$d$ hypersurfaces $V \in \mathbb{V}_{d,n}$ in $\mathbb{P}^n$ whose height is at most $A$,
where the height of $V$ is the height of the chosen nonzero homogeneous polynomial of degree $d$
that represents $V$. -/
def heightLE (A : ℝ) : Set (𝕍 d n) := { V | height V.rep.1 ≤ A }

/-- **Everywhere locally soluble hypersurfaces.** $\mathbb{V}^{\mathrm{loc}}_{d,n}$ is the set of
degree-$d$ hypersurfaces $V \in \mathbb{V}_{d,n}$ in $\mathbb{P}^n$ that are everywhere locally
soluble, that is, with $V(\mathbb{A}_\mathbb{Q}) \ne \emptyset$: the chosen homogeneous polynomial
representing $V$ has a solution in the adele ring $\mathbb{A}_\mathbb{Q}$, namely a zero given by
$n + 1$ adeles that generate the unit ideal of $\mathbb{A}_\mathbb{Q}$. -/
def 𝕍Loc : Set (𝕍 d n) := { V | HasSolutionsIn V.rep.1 𝔸 }

/-- **Local density of everywhere locally soluble hypersurfaces.** For natural numbers $d$ and
$n$ and a real number $A$, let $\mathbb{V}_{d,n}(A)$ be the set of degree-$d$ hypersurfaces in
$\mathbb{P}^n$ of height at most $A$, and let $\mathbb{V}^{\mathrm{loc}}_{d,n}$ be the set of
everywhere locally soluble ones. The local density $\rho^{\mathrm{loc}}_{d,n}$ is the limit, as
$A \to \infty$, of the number of elements of
$\mathbb{V}^{\mathrm{loc}}_{d,n} \cap \mathbb{V}_{d,n}(A)$ divided by the number of elements of
$\mathbb{V}_{d,n}(A)$, a quotient taken to be $0$ when $\mathbb{V}_{d,n}(A)$ is empty; when this
limit does not exist, $\rho^{\mathrm{loc}}_{d,n}$ is an unspecified real number.

By a theorem of Poonen–Voloch [17, Th. 3.6], this limit exists (and is positive) when
$d \ge 2$, $n \ge 2$ and $(d, n) \ne (2, 2)$, and equals a product of local densities over all
places of $\mathbb{Q}$. -/
noncomputable def ρLoc : ℝ :=
  atTop.limUnder fun A ↦ (𝕍Loc d n ∩ heightLE d n A).ncard / (heightLE d n A).ncard

/-- **Proportion of soluble hypersurfaces of bounded height.** For a real number $A$,
$\rho_{d,n}(A)$ is the proportion of hypersurfaces in $\mathbb{V}_{d,n}(A)$, the degree-$d$
hypersurfaces in $\mathbb{P}^n$ of height at most $A$, that have a rational point: it is the
number of $V \in \mathbb{V}_{d,n}(A)$ with $V(\mathbb{Q}) \ne \emptyset$ divided by the number of
elements of $\mathbb{V}_{d,n}(A)$, taken to be $0$ when $\mathbb{V}_{d,n}(A)$ is empty. Here
$V(\mathbb{Q}) \ne \emptyset$ means that the chosen homogeneous polynomial representing $V$ has a
nonzero rational zero. -/
noncomputable def ρ (A : ℝ) : ℝ :=
  { V ∈ heightLE d n A | HasSolutionsIn V.rep.1 ℚ }.ncard / (heightLE d n A).ncard

/-- **Density of soluble Fano hypersurfaces.** Let $d$ and $n$ be natural numbers with $d \ge 2$,
$n \ge d$ and $(d, n) \ne (3, 3)$. Then the proportion $\rho_{d,n}(A)$ of degree-$d$
hypersurfaces in $\mathbb{P}^n$ of height at most $A$ that have a rational point tends to the
local density $\rho^{\mathrm{loc}}_{d,n}$ as the real number $A$ tends to $\infty$.

Source: T. Browning, P. L. Boudec, and W. Sawin, `The Hasse principle for random Fano hypersurfaces`, Annals of Math, 197 (3) 2023. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2023-197-3-HassePrincipleRandomFano.lean Via leanprover/lean-eval@38361be, problem `annals_hasse_principle_random_fano`.
-/
public theorem_wanted theorem_1_1 (hd : 2 ≤ d) (h₁ : d ≤ n) (h₂ : (d, n) ≠ (3, 3)) :
    Tendsto (ρ d n) atTop (nhds (ρLoc d n))

end HassePrincipleRandomFano

end MathlibExt.NumberTheory.HassePrincipleRandomFanoWanted
