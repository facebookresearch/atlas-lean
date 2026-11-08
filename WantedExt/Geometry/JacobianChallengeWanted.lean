/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Jacobian of a compact Riemann surface (Buzzard challenge)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.JacobianChallenge` — jacobian_challenge_diffgeo (manifest `manifests/problems/jacobian_challenge_diffgeo.toml`, rev 1, submitter Kevin Buzzard, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.JacobianChallengeWanted` namespace. Mathematical
statements are unchanged. Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Geometry.JacobianChallengeWanted
/-!
# Jacobians of compact Riemann surfaces

Kevin Buzzard's "Jacobian Challenge" v0.3, posted to leanprover Zulip
(`#Autoformalization > Jacobian challenge`):
<https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge>.
The original source uses anonymous instances; here every `instance` is
named explicitly so the eval-problem pipeline can address it.

## Main missing definitions

* `genus` -- genus of a compact Riemann surface
* `Jacobian` -- the Jacobian of a compact Riemann surface
* `Jacobian.ofCurve` -- the Abel-Jacobi map from a compact Riemann surface to its Jacobian
* `ContMDiff.degree` -- the degree of a holomorphic map between compact Riemann surfaces.
    Equal to 0 if the map is constant, otherwise equal to the usual degree.
* `Jacobian.pushforward` -- the pushforward map on Jacobians induced by a holomorphic map between
  compact Riemann surfaces.
* `Jacobian.pullback` -- the pullback map on Jacobians induced by a holomorphic map between
  compact Riemann surfaces.

## Main missing theorems

* `genus_eq_zero_iff_homeo` -- a compact Riemann surface has genus 0 iff it is homeomorphic to the sphere
* `ofCurve_inj` -- the Abel-Jacobi map is injective if the genus is positive
* `Jacobian.ofCurve_contMDiff` -- the Abel-Jacobi map is holomorphic
* `Jacobian.pushforward_contMDiff` -- the pushforward map is holomorphic
* `Jacobian.pullback_contMDiff` -- the pullback map is holomorphic
* `pushforward_pullback` -- pullback then pushforward is multiplication by degree
-/

open scoped ContDiff -- for ω notation

namespace JacobianChallenge

universe u v w

-- let X be a compact Riemann surface
variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) ω X]

-- data
/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public def_wanted genus (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) ω X] : ℕ

-- this proof avoids the hack answer `∀ X, genus X = 0`
-- Prop
/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public theorem_wanted genus_eq_zero_iff_homeo :
    ❰genus❱ X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))

-- data
/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public def_wanted Jacobian (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) ω X] : Type u

namespace Jacobian

-- data
/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public instance_wanted instAddCommGroup : AddCommGroup (❰Jacobian❱ X)

-- data
/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public instance_wanted instTopologicalSpace : TopologicalSpace (❰Jacobian❱ X)

-- Prop
/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public instance_wanted instT2Space : T2Space (❰Jacobian❱ X)

-- Prop
/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public instance_wanted instCompactSpace : CompactSpace (❰Jacobian❱ X)

/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public instance_wanted instChartedSpace :
    ChartedSpace (Fin (❰genus❱ X) → ℂ) (❰Jacobian❱ X)

-- Prop
/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public instance_wanted instIsManifold :
    IsManifold (modelWithCornersSelf ℂ (Fin (❰genus❱ X) → ℂ)) ω (❰Jacobian❱ X)

-- Prop
/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public instance_wanted instLieAddGroup :
    LieAddGroup (modelWithCornersSelf ℂ (Fin (❰genus❱ X) → ℂ)) ω (❰Jacobian❱ X)

/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public def_wanted ofCurve (P : X) : X → ❰Jacobian❱ X

/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public theorem_wanted ofCurve_contMDiff (P : X) :
    ContMDiff (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ (Fin (❰genus❱ X) → ℂ)) ω (❰ofCurve❱ P)

/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public theorem_wanted ofCurve_self (P : X) : ❰ofCurve❱ P P = 0

-- this is the lemma which stops the hack answer "J(X)=0 for all X"
/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public theorem_wanted ofCurve_inj (P : X) : 0 < ❰genus❱ X → Function.Injective (❰ofCurve❱ P)

-- Lean variant (recorded in `WantedExt/Sources/LeanEval.md`): `Y` and `Z` below are
-- specialized from the source's independent universes `Type v` / `Type w` to `Type u`.
-- The current proof-wanted elaborator surfaces one universe per wanted reference in a
-- declaration, so a single statement cannot reference `Jacobian`/`genus` at two distinct
-- universes (explicit-universe reference syntax is not supported inside `❰…❱`).
variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold (modelWithCornersSelf ℂ ℂ) ω Y]

variable (f : X → Y) (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f)

/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public def_wanted pushforward (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    ❰Jacobian❱ X →ₜ+ ❰Jacobian❱ Y

/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public theorem_wanted pushforward_contMDiff (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (❰genus❱ X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (❰genus❱ Y) → ℂ)) ω (❰pushforward❱ f hf)

-- functoriality
/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public theorem_wanted pushforward_id_apply :
    ∀ P : ❰Jacobian❱ X, ❰pushforward❱ id contMDiff_id P = P

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold (modelWithCornersSelf ℂ ℂ) ω Z]

variable (g : Y → Z) (hg : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω g)

/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public theorem_wanted pushforward_comp_apply (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω g) :
    ∀ P : ❰Jacobian❱ X,
      ❰pushforward❱ (g ∘ f) (hg.comp hf) P = ❰pushforward❱ g hg (❰pushforward❱ f hf P)

-- if f is constant then the pullback should be the zero map, otherwise it's
-- the usual pullback
/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public def_wanted pullback (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    ❰Jacobian❱ Y →ₜ+ ❰Jacobian❱ X

/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public theorem_wanted pullback_contMDiff (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (❰genus❱ Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (❰genus❱ X) → ℂ)) ω (❰pullback❱ f hf)

/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public theorem_wanted pullback_id_apply :
    ∀ P : ❰Jacobian❱ X, ❰pullback❱ id contMDiff_id P = P

/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public theorem_wanted pullback_comp_apply (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω g) :
    ∀ P : ❰Jacobian❱ Z,
      ❰pullback❱ (g.comp f) (hg.comp hf) P = ❰pullback❱ f hf (❰pullback❱ g hg P)

/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public def_wanted degree (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) : ℕ  -- 0 for constant case

/-- Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public theorem_wanted pushforward_pullback (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    ∀ P : ❰Jacobian❱ Y, ❰pushforward❱ f hf (❰pullback❱ f hf P) = (❰degree❱ f hf) • P

end Jacobian

end JacobianChallenge

end MathlibExt.Geometry.JacobianChallengeWanted
