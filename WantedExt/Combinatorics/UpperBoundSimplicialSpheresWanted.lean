/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Upper bound theorem for geometric simplicial spheres (Stanley 1975)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.UpperBoundSimplicialSpheres` — upper_bound_simplicial_spheres (manifest `manifests/problems/upper_bound_simplicial_spheres.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.UpperBoundSimplicialSpheresWanted` namespace. Mathematical
statements are unchanged. Source: R.P. Stanley, 'The upper bound conjecture and Cohen–Macaulay rings', Studies in Appl. Math. 54 (1975) 135–142. Conjecture: T.S. Motzkin (1957); polytope case: P. McMullen, 'The maximum numbers of faces of a convex polytope', Mathematika 17 (1970) 179–184. §142 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Combinatorics.SimplicialSphereShared
public import Mathlib

@[expose] public section

open MathlibExt.Combinatorics.SimplicialSphereShared

namespace MathlibExt.Combinatorics.UpperBoundSimplicialSpheresWanted
namespace Combinatorics
namespace UpperBoundSimplicialSpheresProblem

/-!
# Upper bound theorem for simplicial spheres (Stanley 1975),
geometrically-embedded variant

Among finite `(d − 1)`-dimensional simplicial spheres with `n`
vertices, the cyclic polytope `C(n, d)` maximises every face number
`f_k`. Conjectured by Motzkin (1957); McMullen 1970 for the polytope
case; Stanley 1975 extended to all finite simplicial spheres via the
Stanley–Reisner face-ring proof. §142 in Knill's *Some Fundamental
Theorems in Mathematics*.

The Lean encoding `FiniteSimplicialSphere d` uses mathlib's
`Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin d))` — finite
geometric complexes linearly embedded in `ℝᵈ` whose underlying space
is homeomorphic to the unit sphere in `ℝᵈ`. Stanley's full theorem
applies to *all* finite abstract simplicial spheres, and our
geometric class is a subset (not every abstract finite simplicial
sphere embeds linearly in `ℝᵈ`), so Stanley 1975 *implies* the
statement here.

Mathlib has the finite-simplicial-complex substrate
(`AbstractSimplicialComplex`, `Geometry.SimplicialComplex` with
`faces` / `vertices` / `facets` / `space`) but no cyclic polytopes,
h-vectors, g-vectors, Dehn–Sommerville, face rings, or upper bound
theorem.
-/

noncomputable section

open BigOperators

/-- The ambient Euclidean space for a `(d − 1)`-sphere. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)





/-- h-vector of the cyclic polytope `C(n, d)`: first half
`choose (n − d − 1 + j) j`, second half symmetric. -/
def cyclicH (n d j : ℕ) : ℕ :=
  Nat.choose (n - d - 1 + min j (d - j)) (min j (d - j))

/-- Face number `f_k(C(n, d))`, via the inverse h-to-f transform. -/
def cyclicPolytopeFaceCount (n d k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range (k + 2),
    Nat.choose (d - j) (k + 1 - j) * cyclicH n d j

/- **Upper bound theorem for simplicial spheres** (Stanley 1975).
Every `k`-face count of a finite simplicial `(d − 1)`-sphere with `n`
vertices is bounded above by the corresponding face count of the
cyclic polytope `C(n, d)`. -/
/-- Source: R.P. Stanley, 'The upper bound conjecture and Cohen–Macaulay rings', Studies in Appl. Math. 54 (1975) 135–142. Conjecture: T.S. Motzkin (1957); polytope case: P. McMullen, 'The maximum numbers of faces of a convex polytope', Mathematika 17 (1970) 179–184. §142 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `upper_bound_simplicial_spheres`. -/
public theorem_wanted upper_bound_theorem_simplicial_spheres
    {d n k : ℕ} (X : FiniteSimplicialSphere d)
    (_hn : faceCount X 0 = n) (_hk : k < d) :
    faceCount X k ≤ cyclicPolytopeFaceCount n d k

end

end UpperBoundSimplicialSpheresProblem
end Combinatorics

end MathlibExt.Combinatorics.UpperBoundSimplicialSpheresWanted
