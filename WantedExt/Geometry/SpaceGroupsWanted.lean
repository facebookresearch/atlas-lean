/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# 230 space groups (Fedorov 1891 / Schoenflies 1891)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.SpaceGroups` — space_groups_230 (manifest `manifests/problems/space_groups_230.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.SpaceGroupsWanted` namespace. Mathematical
statements are unchanged. Source: E. Fedorov, 'Симметрія правильныхъ системъ фигуръ' (Symmetry of regular systems of figures), Trans. Min. Soc. St. Petersburg 28 (1891) 1–146; A. Schoenflies, *Krystallsysteme und Krystallstructur*, Teubner 1891, independently. Listed as §94 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Geometry.CrystallographicShared
public import Mathlib

@[expose] public section

open MathlibExt.Geometry.CrystallographicShared

namespace MathlibExt.Geometry.SpaceGroupsWanted
namespace Geometry
namespace SpaceGroupsProblem

/-!
# 230 space groups (Fedorov 1891 / Schoenflies 1891)

In dimension 3, there are exactly 230 space groups, reducing to 219 if
enantiomorphic (chiral) pairs are identified, with 65 of the 230 being
*Sohncke* groups — those whose isometries are all orientation-
preserving. §94 in Knill's *Some Fundamental Theorems in Mathematics*;
main work due to E. Fedorov (1891) and A. Schoenflies (1891),
independently.

The three counts correspond to two equivalences on crystallographic
groups: `AffinelyEquivalent` (Aff(ℝ³)-conjugacy, count = 219) and
`AffOPEquivalent` (orientation-preserving Aff(ℝ³)-conjugacy, count =
230). The "65 Sohncke groups" count restricts the underlying groups to
those whose elements are all orientation-preserving isometries.
-/

/-- The Euclidean model space `ℝᵈ`. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

/- The Euclidean motion group `E_d`. -/
/- The affine group `Aff(ℝᵈ)`. -/
/- `g ∈ E_d` is **translation by `v`**. -/
/- A subgroup `G ≤ E_d` is **discrete** in the proper-discontinuity
sense. -/
/- A subgroup `G ≤ E_d` is **crystallographic**: discrete and contains
`d` linearly independent translations. -/
/- The set of crystallographic groups in dimension `d`. -/
/-- An affine isometry is **orientation-preserving** if its linear part
has positive determinant. -/
def IsOrientationPreservingIsom {d : ℕ} (g : EuclideanIsom d) : Prop :=
  0 < (g.toAffineEquiv.linear.det : ℝ)

/- Two subgroups `G₁, G₂ ≤ E_d` are **affinely equivalent**. -/
/-- Two subgroups `G₁, G₂ ≤ E_d` are **orientation-preserving affinely
equivalent**: conjugation by a positive-determinant affine map takes
one to the other. -/
def AffOPEquivalent {d : ℕ} (G₁ G₂ : Subgroup (EuclideanIsom d)) : Prop :=
  ∃ φ : AffineGroup d, 0 < (φ.linear.det : ℝ) ∧
    {h : AffineGroup d | ∃ g ∈ G₁, h = φ * g.toAffineEquiv * φ⁻¹} =
    {h : AffineGroup d | ∃ g ∈ G₂, h = g.toAffineEquiv}

/- Count of crystallographic groups modulo affine equivalence. -/
/-- Count of crystallographic groups modulo orientation-preserving
affine equivalence. -/
noncomputable def crystallographicCountOP (d : ℕ) : ℕ∞ :=
  Set.encard {S : Set (CrystallographicGroup d) |
    ∃ G₀ : CrystallographicGroup d,
      S = {H : CrystallographicGroup d | AffOPEquivalent G₀.1 H.1}}

/-- Count of orientation-preserving crystallographic groups modulo
orientation-preserving affine equivalence. -/
noncomputable def crystallographicCountOPOnly (d : ℕ) : ℕ∞ :=
  Set.encard {S : Set { G : CrystallographicGroup d //
                          ∀ g, g ∈ G.1 → IsOrientationPreservingIsom g } |
    ∃ G₀ : { G : CrystallographicGroup d //
              ∀ g, g ∈ G.1 → IsOrientationPreservingIsom g },
      S = {H | AffOPEquivalent G₀.1.1 H.1.1}}

/- **230 space groups** (Fedorov 1891; Schoenflies 1891). In
dimension 3 there are 230 space groups (orientation-preserving
equivalence), 219 (general affine equivalence), and 65 orientation-
preserving subfamily. -/
/-- Source: E. Fedorov, 'Симметрія правильныхъ системъ фигуръ' (Symmetry of regular systems of figures), Trans. Min. Soc. St. Petersburg 28 (1891) 1–146; A. Schoenflies, *Krystallsysteme und Krystallstructur*, Teubner 1891, independently. Listed as §94 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `space_groups_230`. -/
public theorem_wanted space_groups :
    crystallographicCountOP 3 = 230 ∧
      crystallographicCount 3 = 219 ∧
        crystallographicCountOPOnly 3 = 65

end SpaceGroupsProblem
end Geometry

end MathlibExt.Geometry.SpaceGroupsWanted
