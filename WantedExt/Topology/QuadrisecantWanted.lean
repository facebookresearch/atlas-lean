/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Pannwitz–Kuperberg quadrisecant theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.KnotTheory.Quadrisecant` — smooth_knot_has_quadrisecant (manifest `manifests/problems/smooth_knot_has_quadrisecant.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.QuadrisecantWanted` namespace. The theorem is restated over the shared knot type `MathlibExt.Topology.ConwayKnotShared.KnotTheory.Knot` (the upstream curve predicate repeats that type's fields), with only the quadrisecant/unknot predicates defined here. Mathematical statements are unchanged otherwise. Source: E. Pannwitz (1933); G. Kuperberg, *Quadrisecants of knots and links*, J. Knot Theory Ramif. 3 (1994). Knill, §161.
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Topology.ConwayKnotShared
public import Mathlib

@[expose] public section

namespace MathlibExt.Topology.QuadrisecantWanted
namespace KnotTheory.Quadrisecant

open MathlibExt.Topology.ConwayKnotShared.KnotTheory

/-!
# The Pannwitz–Kuperberg quadrisecant theorem

`smooth_knot_has_quadrisecant`: every smooth knot that is not the unknot has a
quadrisecant (a line meeting it in four points). Trusted helpers (`IsSmoothKnot`,
`IsUnknotted`, `HasQuadrisecant`, …) are non-holes. Mathlib has no knot theory.
(The Fáry–Milnor total-curvature theorem of §161 is a separate lean-eval problem.)
Category-(b) candidate from §161 of the Knill survey.
-/

/-- The `2π` period. -/
noncomputable def period : ℝ := 2 * Real.pi

/-- The standard round unknot curve in the `xy`-plane. -/
noncomputable def standardCircle (t : ℝ) : R3 :=
  !₂[Real.cos t, Real.sin t, 0]

/-- A knot is *unknotted* if it is ambient-isotopic (in the shared
`Knot.Isotopic` sense) to a knot parametrized by the standard circle. -/
def IsUnknotted (K : Knot) : Prop :=
  ∃ J : Knot, J.curve = standardCircle ∧ K.Isotopic J

/-- A quadrisecant: four distinct parameter values whose image points are
collinear. -/
def HasQuadrisecant (K : Knot) : Prop :=
  ∃ t0 t1 t2 t3 : ℝ, ∃ p v : R3, ∃ a0 a1 a2 a3 : ℝ,
    t0 ∈ Set.Ico (0 : ℝ) period ∧ t1 ∈ Set.Ico (0 : ℝ) period ∧
      t2 ∈ Set.Ico (0 : ℝ) period ∧ t3 ∈ Set.Ico (0 : ℝ) period ∧
      [t0, t1, t2, t3].Nodup ∧ v ≠ 0 ∧
      K.curve t0 = p + a0 • v ∧ K.curve t1 = p + a1 • v ∧
      K.curve t2 = p + a2 • v ∧ K.curve t3 = p + a3 • v

/- **Quadrisecant theorem** (Pannwitz–Kuperberg). Every smooth nontrivial knot
has a quadrisecant. -/
/-- Source: E. Pannwitz (1933); G. Kuperberg, *Quadrisecants of knots and links*, J. Knot Theory Ramif. 3 (1994). Knill, §161. Via leanprover/lean-eval@38361be, problem `smooth_knot_has_quadrisecant`. -/
public theorem_wanted smooth_knot_has_quadrisecant
    (K : Knot) (_hnontrivial : ¬ IsUnknotted K) :
    HasQuadrisecant K

end KnotTheory.Quadrisecant

end MathlibExt.Topology.QuadrisecantWanted
