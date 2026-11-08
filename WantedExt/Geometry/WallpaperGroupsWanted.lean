/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Seventeen wallpaper groups (Pólya–Niggli 1924)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.WallpaperGroups` — wallpaper_groups_17 (manifest `manifests/problems/wallpaper_groups_17.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.WallpaperGroupsWanted` namespace. Mathematical
statements are unchanged. Source: G. Pólya, 'Über die Analogie der Kristallsymmetrie in der Ebene', Z. Kristallogr. 60 (1924) 278–282; P. Niggli, 'Die Flächensymmetrien homogener Diskontinuen', Z. Kristallogr. 60 (1924) 283–298. Listed as §94 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Geometry.CrystallographicShared
public import Mathlib

@[expose] public section

open MathlibExt.Geometry.CrystallographicShared

namespace MathlibExt.Geometry.WallpaperGroupsWanted
namespace Geometry
namespace WallpaperGroupsProblem

/-!
# Seventeen wallpaper groups (Pólya–Niggli 1924)

There are exactly 17 wallpaper groups, the discrete cocompact subgroups
of the Euclidean motion group `E_2` (planar affine isometries), counted
up to affine equivalence. Pólya–Niggli 1924; §94 in Knill's *Some
Fundamental Theorems in Mathematics*.

The discreteness definition uses a properly discontinuous action
(local finiteness of the return set at each point: for every `x` and
every `ε > 0`, only finitely many group elements move `x` by at most
`ε`) rather than a topological formulation on the Euclidean motion
group, since mathlib does not equip the affine-isometry equivalence
type with a default topology. The two formulations agree for subgroups
of `E_d` once `E_d` is given the standard Lie-group topology.
-/

/-- The Euclidean model space `ℝᵈ`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/- The Euclidean motion group `E_d`: affine isometries of `ℝᵈ`. -/
/- The affine group `Aff(ℝᵈ)`: invertible affine self-maps of `ℝᵈ`. -/
/- `g ∈ E_d` is **translation by `v`** if it acts as `x ↦ x + v`. -/
/- A subgroup `G ≤ E_d` is **discrete** (proper discontinuity): for
every `x ∈ ℝᵈ` and every `ε > 0`, only finitely many `g ∈ G` satisfy
`dist (g x) x ≤ ε`. -/
/- A subgroup `G ≤ E_d` is **crystallographic** if it is discrete and
contains `d` linearly independent translations (equivalently, acts
cocompactly on `ℝᵈ`). -/
/- Two subgroups `G₁, G₂ ≤ E_d` are **affinely equivalent** if some
`φ ∈ Aff(ℝᵈ)` conjugates one into the other (inside `Aff(ℝᵈ)` via
`AffineIsometryEquiv.toAffineEquiv`). -/
/- The set of crystallographic groups in dimension `d`. -/
/- Count of crystallographic groups in dimension `d`, modulo affine
equivalence, as `ℕ∞`. -/
/- **There are exactly 17 wallpaper groups** (Pólya–Niggli 1924). -/
/-- Source: G. Pólya, 'Über die Analogie der Kristallsymmetrie in der Ebene', Z. Kristallogr. 60 (1924) 278–282; P. Niggli, 'Die Flächensymmetrien homogener Diskontinuen', Z. Kristallogr. 60 (1924) 283–298. Listed as §94 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `wallpaper_groups_17`. -/
public theorem_wanted there_are_17_wallpaper_groups :
    crystallographicCount 2 = 17

end WallpaperGroupsProblem
end Geometry

end MathlibExt.Geometry.WallpaperGroupsWanted
