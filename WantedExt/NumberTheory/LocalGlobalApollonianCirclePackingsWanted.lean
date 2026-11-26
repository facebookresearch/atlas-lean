/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The local-global conjecture for Apollonian circle packings is false

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
38361be884302c7edce1908c4aef8296eb2cb27e, module
`LeanEval.NumberTheory.LocalGlobalApollonianCirclePackings` —
annals_local_global_apollonian_circle_packings (manifest
`manifests/problems/annals_local_global_apollonian_circle_packings.toml`, rev 1, submitter
Thomas Browning, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the
`MathlibExt.NumberTheory.LocalGlobalApollonianCirclePackingsWanted` namespace. Mathematical
statements are unchanged. Source: S. Haag, C. Kertzer, J. Rickards, and K. E. Stange, `The local-global conjecture for Apollonian circle packings is false`, Annals of Math, 200 (2) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-200-2-LocalGlobalApollonianCirclePackings.lean
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.NumberTheory.LocalGlobalApollonianCirclePackings

@[expose] public section

namespace MathlibExt.NumberTheory.LocalGlobalApollonianCirclePackingsWanted
/-!
# Main Statements from The local-global conjecture for Apollonian circle packings is false

We formalise the statements of the main results from S. Haag, C. Kertzer, J. Rickards, and
K. E. Stange, `The local-global conjecture for Apollonian circle packings is false`,
Annals of Math, 200 (2) 2024.
-/

set_option autoImplicit false

namespace LocalGlobalApollonianCirclePackings

/-- **Missing curvature set.** Let $A$ be a primitive Apollonian circle packing. The missing
curvature set of $A$ is the set of positive integers $n$ that do not lie in the curvature set
of $A$ but are congruent modulo $24$ to some element of the curvature set of $A$.

Source: S. Haag, C. Kertzer, J. Rickards, and K. E. Stange, `The local-global conjecture for
Apollonian circle packings is false`, Annals of Math, 200 (2) 2024, start of Section 1.2. -/
def missingCurvatureSet (A : PrimitiveApollonianCirclePacking) : Set ℤ :=
  {n | n > 0 ∧ n ∉ curvatureSet A ∧ ∃ k ∈ curvatureSet A, k ≡ n [ZMOD 24]}

/-- **Number of missing curvatures.** For a primitive Apollonian circle packing $A$ and a real
number $N$, the number of missing curvatures of $A$ up to $N$ is the number of elements $n$ of
the missing curvature set of $A$ with $n \le N$, regarded as a real number. -/
noncomputable def missingCurvatures (A : PrimitiveApollonianCirclePacking) (N : ℝ) : ℝ :=
  (missingCurvatureSet A ∩ {x | x ≤ N}).ncard

/--
**Infinitely many packings with many missing curvatures.** For a primitive Apollonian circle
packing $\mathcal{A}$ and a real number $N$, let $M_{\mathcal{A}}(N)$ be the number of missing
curvatures of $\mathcal{A}$ up to $N$. There are infinitely many primitive Apollonian circle
packings $\mathcal{A}$ such that $\sqrt{N} = O(M_{\mathcal{A}}(N))$ as $N$ tends to infinity.
In other words, for these packings the number of missing curvatures up to $N$ is
$\Omega(\sqrt{N})$.

Source: S. Haag, C. Kertzer, J. Rickards, and K. E. Stange, `The local-global conjecture for Apollonian circle packings is false`, Annals of Math, 200 (2) 2024. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2024-200-2-LocalGlobalApollonianCirclePackings.lean Via leanprover/lean-eval@38361be, problem `annals_local_global_apollonian_circle_packings`.
-/
public theorem_wanted theorem_1_3 : {A : PrimitiveApollonianCirclePacking |
    Real.sqrt =O[Filter.atTop] missingCurvatures A}.Infinite

end LocalGlobalApollonianCirclePackings

end MathlibExt.NumberTheory.LocalGlobalApollonianCirclePackingsWanted
