/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Pardon's lower bound for torus-knot distortion

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.KnotTheory.PardonDistortion` — pardon_torus_knot_distortion (manifest `manifests/problems/pardon_torus_knot_distortion.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.PardonDistortionWanted` namespace. Mathematical
statements are unchanged. Source: John Pardon, 'On the distortion of knots on embedded surfaces', Annals of Mathematics (2) 174 (2011), no. 1, 637-646, Theorem 1.1. https://doi.org/10.4007/annals.2011.174.1.21
-/
module

public import Batteries.Util.ProofWanted
public import WantedExt.Topology.ConwayKnotShared
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

@[expose] public section

namespace MathlibExt.Topology.PardonDistortionWanted
namespace KnotTheory
namespace PardonDistortion

/-!
# Pardon's lower bound for the distortion of torus knots

For a rectifiable simple closed curve `γ` in `ℝ³`, its distortion is the
supremum of the intrinsic arclength distance between two points of `γ` divided
by their Euclidean distance.  John Pardon proved that the infimum of this
quantity over all rectifiable representatives of the `(p, q)`-torus-knot
isotopy class is at least `min(p, q) / 160`.

The shared knot model in `LeanEval.KnotTheory.Prelude` describes smooth knots,
not arbitrary rectifiable curves.  The theorem below is therefore the faithful
smooth specialization of Pardon's result: every smooth representative smoothly
ambient-isotopic to the explicitly parametrized standard torus knot obeys the
same bound.  The isotopy and circle reparametrization are orientation-preserving,
as in the shared prelude; this only narrows the collection of representatives
covered by the published, unoriented statement.
-/

noncomputable section

open Set
open scoped ENNReal

open MathlibExt.Topology.ConwayKnotShared.KnotTheory

/-! The knot-theory model (`R3`, `Knot`, `TwoLink`, `AmbientIsotopy`,
`CircleReparam`, isotopy, `reflectZ`, chirality) is shared with the other
knot entries via `WantedExt.Topology.ConwayKnotShared` and is not copied
here, so all knot entries speak about the same `Knot` type. -/

/-- The speed of a smooth knot with its given parametrization. -/
def speed (K : Knot) (t : ℝ) : ℝ :=
  ‖deriv K.curve t‖

/-- Arclength of the parametrized arc between `s` and `t`.  The absolute value
makes this independent of the order of the endpoints. -/
def parameterArcLength (K : Knot) (s t : ℝ) : ℝ :=
  |∫ u in s..t, speed K u|

/-- Total arclength over the fundamental interval `[0, 2π]`. -/
def totalArcLength (K : Knot) : ℝ :=
  parameterArcLength K 0 (2 * Real.pi)

/-- Intrinsic distance along the closed curve, for parameters in one
fundamental interval: the shorter of the two complementary arc lengths. -/
def intrinsicDistance (K : Knot) (s t : ℝ) : ℝ :=
  min (parameterArcLength K s t) (totalArcLength K - parameterArcLength K s t)

/-- The distortion ratio for the two points with parameters `s` and `t`. -/
def distortionRatio (K : Knot) (s t : ℝ) : ℝ :=
  intrinsicDistance K s t / dist (K.curve s) (K.curve t)

/-- Distortion of a smooth knot as an extended nonnegative real: the supremum
of the distortion ratios over distinct parameters in the half-open fundamental
interval `[0, 2π)`. The extended codomain also represents infinite
distortion. -/
def distortion (K : Knot) : ℝ≥0∞ :=
  sSup {d : ℝ≥0∞ | ∃ s ∈ Ico (0 : ℝ) (2 * Real.pi),
    ∃ t ∈ Ico (0 : ℝ) (2 * Real.pi),
      s ≠ t ∧ d = ENNReal.ofReal (distortionRatio K s t)}

/-- The standard `(p, q)`-torus curve on the torus of revolution with major
radius `2` and minor radius `1`.  It winds `p` times around the axis of the
torus and `q` times around a meridian. -/
def standardTorusCurve (p q : ℕ) (t : ℝ) : R3 :=
  WithLp.toLp 2 (fun i : Fin 3 =>
    if i.val = 0 then
      (2 + Real.cos ((q : ℝ) * t)) * Real.cos ((p : ℝ) * t)
    else if i.val = 1 then
      (2 + Real.cos ((q : ℝ) * t)) * Real.sin ((p : ℝ) * t)
    else
      Real.sin ((q : ℝ) * t))

/- **Pardon's torus-knot distortion bound (smooth specialization).**

If `p` and `q` are positive and coprime, every smooth knot in the
orientation-preserving smooth ambient-isotopy class of the explicit standard
`(p, q)`-torus curve has distortion at least `min(p, q) / 160`. -/
/-- Source: John Pardon, 'On the distortion of knots on embedded surfaces', Annals of Mathematics (2) 174 (2011), no. 1, 637-646, Theorem 1.1. https://doi.org/10.4007/annals.2011.174.1.21 Via leanprover/lean-eval@38361be, problem `pardon_torus_knot_distortion`. -/
public theorem_wanted pardon_torus_knot_distortion
    (p q : ℕ) (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (K : Knot)
    (_hclass : ∃ Φ : AmbientIsotopy, ∃ σ : CircleReparam,
      ∀ t, Φ.H 1 (K.curve t) = standardTorusCurve p q (σ.f t)) :
    (1 / 160 : ℝ≥0∞) * (Nat.min p q : ℝ≥0∞) ≤ distortion K

end

end PardonDistortion
end KnotTheory

end MathlibExt.Topology.PardonDistortionWanted
