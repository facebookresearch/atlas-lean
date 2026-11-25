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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.LorentzianPolynomials`,
problem `annals_lorentzian_polynomials` (manifest
`manifests/problems/annals_lorentzian_polynomials.toml`, rev 1, submitter Justus Springer),
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.LorentzianPolynomialsWanted` namespace.
Later ATLAS change: the body of `IsMConvex` now refers to the identical general
predicate `MathlibExt.Combinatorics.Matroid.MConvex.IsMConvex` (definitionally the same
condition), so that M-convexity has a single definition. Mathematical
statements are unchanged. Source: P. Brändén and J. Huh, `Lorentzian polynomials`, Annals of Math, 192 (3) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-3-LorentzianPolynomials.lean
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.Combinatorics.LorentzianPolynomials

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

/--
**Lorentzian polynomials as the closure of strictly Lorentzian polynomials.** For all natural
numbers $n \ge 1$ and $d$, the closure of the set $\mathring{L}^d_n$ of strictly Lorentzian
polynomials of degree $d$ in $n$ variables, taken in the space $H^d_n$ of homogeneous polynomials
of degree $d$ in $\mathbb{R}[w_1, \dots, w_n]$ with the Euclidean topology on coefficients, is the
set $L^d_n$ of Lorentzian polynomials of degree $d$ in $n$ variables.

The paper (Theorem 2.25) allows $n = 0$, but the statement fails for $n = 0$ and $d = 2$: the
$0 \times 0$ Hessian of a polynomial cannot have a positive eigenvalue, so $\mathring{L}^2_0$ is
empty, while $L^2_0 = S^2_0$ contains the zero polynomial, which is homogeneous of degree $2$.

Source: P. Brändén and J. Huh, `Lorentzian polynomials`, Annals of Math, 192 (3) 2020. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2020-192-3-LorentzianPolynomials.lean Via leanprover/lean-eval@38361be, problem `annals_lorentzian_polynomials`.
-/
public theorem_wanted theorem_2_25 (n d : ℕ) (hn : 0 < n) : closure (Ŀ n d) = L n d

end LorentzianPolynomials

end MathlibExt.Combinatorics.LorentzianPolynomialsWanted
