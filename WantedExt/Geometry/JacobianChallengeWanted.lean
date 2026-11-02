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
/-- **Genus of a compact Riemann surface.** For a compact Riemann surface $X$, that is, a compact
connected Hausdorff space with a complex-analytic atlas modelled on $\mathbb{C}$, the genus of $X$
is a natural number.

Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public def_wanted genus (X : Type u) [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
    [Nonempty X] [ChartedSpace ℂ X] [IsManifold (modelWithCornersSelf ℂ ℂ) ω X] : ℕ

-- this proof avoids the hack answer `∀ X, genus X = 0`
-- Prop
/-- **A compact Riemann surface has genus zero iff it is a sphere.** Let $X$ be a compact
Riemann surface, that is, a compact connected Hausdorff space with a complex-analytic atlas
modelled on $\mathbb{C}$. The genus of $X$ is $0$ if and only if $X$ is homeomorphic to the unit
sphere in Euclidean space $\mathbb{R}^3$.

Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public theorem_wanted genus_eq_zero_iff_homeo :
    ❰genus❱ X = 0 ↔ Nonempty (X ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1))

-- data
/-- **Jacobian of a compact Riemann surface.** For a compact Riemann surface $X$, that is, a
compact connected Hausdorff space with a complex-analytic atlas modelled on $\mathbb{C}$, the
Jacobian $J(X)$ of $X$ is a type in the same universe as $X$.

Separate wanted instances make $J(X)$ a compact Hausdorff commutative complex Lie group modelled
on $\mathbb{C}^g$, where $g$ is the genus of $X$.

Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
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

/-- **Abel–Jacobi map.** Let $X$ be a compact Riemann surface with Jacobian $J(X)$. Each point
$P \in X$ gives a map $X \to J(X)$, the Abel–Jacobi map based at $P$.

Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public def_wanted ofCurve (P : X) : X → ❰Jacobian❱ X

/-- **The Abel–Jacobi map is holomorphic.** Let $X$ be a compact Riemann surface of genus $g$,
and let $J(X)$ be its Jacobian, a complex manifold modelled on $\mathbb{C}^g$. For every point
$P \in X$, the Abel–Jacobi map $X \to J(X)$ based at $P$ is holomorphic.

Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public theorem_wanted ofCurve_contMDiff (P : X) :
    ContMDiff (modelWithCornersSelf ℂ ℂ)
      (modelWithCornersSelf ℂ (Fin (❰genus❱ X) → ℂ)) ω (❰ofCurve❱ P)

/-- **The Abel–Jacobi map sends the base point to zero.** Let $X$ be a compact Riemann surface
with Jacobian $J(X)$, an abelian group. For every point $P \in X$, the Abel–Jacobi map
$X \to J(X)$ based at $P$ sends $P$ to $0$.

Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public theorem_wanted ofCurve_self (P : X) : ❰ofCurve❱ P P = 0

-- this is the lemma which stops the hack answer "J(X)=0 for all X"
/-- **The Abel–Jacobi map is injective in positive genus.** Let $X$ be a compact Riemann surface
with Jacobian $J(X)$, and let $P \in X$. If the genus of $X$ is positive, then the Abel–Jacobi map
$X \to J(X)$ based at $P$ is injective.

Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public theorem_wanted ofCurve_inj (P : X) : 0 < ❰genus❱ X → Function.Injective (❰ofCurve❱ P)

-- Lean variant (recorded in `WantedExt/Sources/LeanEval.md`): `Y` and `Z` below are
-- specialized from the source's independent universes `Type v` / `Type w` to `Type u`.
-- The current proof-wanted elaborator surfaces one universe per wanted reference in a
-- declaration, so a single statement cannot reference `Jacobian`/`genus` at two distinct
-- universes (explicit-universe reference syntax is not supported inside `❰…❱`).
variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [Nonempty Y] [ChartedSpace ℂ Y] [IsManifold (modelWithCornersSelf ℂ ℂ) ω Y]

variable (f : X → Y) (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f)

/-- **Pushforward on Jacobians.** Let $X$ and $Y$ be compact Riemann surfaces, that is, compact,
connected, Hausdorff complex-analytic manifolds of dimension one, and write $J(X)$ for the
Jacobian of $X$, an abelian group with a topology. For a holomorphic map $f : X \to Y$, the
pushforward $f_*$ is a continuous group homomorphism from $J(X)$ to $J(Y)$. It is meant to be
the homomorphism induced by $f$; its properties are stated separately.

Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public def_wanted pushforward (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    ❰Jacobian❱ X →ₜ+ ❰Jacobian❱ Y

/-- **The pushforward on Jacobians is holomorphic.** Let $X$ and $Y$ be compact Riemann surfaces,
that is, compact, connected, Hausdorff complex-analytic manifolds of dimension one, of genera
$g_X$ and $g_Y$. The Jacobian $J(X)$ of $X$ is a complex-analytic manifold modeled on
$\mathbb{C}^{g_X}$, and likewise $J(Y)$ on $\mathbb{C}^{g_Y}$. For every holomorphic map
$f : X \to Y$, the pushforward $f_* : J(X) \to J(Y)$ is holomorphic.

Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public theorem_wanted pushforward_contMDiff (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (❰genus❱ X) → ℂ))
      (modelWithCornersSelf ℂ (Fin (❰genus❱ Y) → ℂ)) ω (❰pushforward❱ f hf)

-- functoriality
/-- **Pushforward along the identity.** Let $X$ be a compact Riemann surface, that is, a compact,
connected, Hausdorff complex-analytic manifold of dimension one, and write $J(X)$ for its
Jacobian. For every $P \in J(X)$, the pushforward of $P$ along the identity map of $X$ is $P$:
$(\mathrm{id}_X)_*(P) = P$.

Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public theorem_wanted pushforward_id_apply :
    ∀ P : ❰Jacobian❱ X, ❰pushforward❱ id contMDiff_id P = P

variable {Z : Type u} [TopologicalSpace Z] [T2Space Z] [CompactSpace Z] [ConnectedSpace Z]
  [Nonempty Z] [ChartedSpace ℂ Z] [IsManifold (modelWithCornersSelf ℂ ℂ) ω Z]

variable (g : Y → Z) (hg : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω g)

/-- **Pushforward respects composition.** Let $X$, $Y$ and $Z$ be compact Riemann surfaces, that
is, compact, connected, Hausdorff complex-analytic manifolds of dimension one, and write $J(X)$
for the Jacobian of $X$. For all holomorphic maps $f : X \to Y$ and $g : Y \to Z$ and every
$P \in J(X)$, the pushforwards satisfy $(g \circ f)_*(P) = g_*(f_*(P))$.

Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public theorem_wanted pushforward_comp_apply (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω g) :
    ∀ P : ❰Jacobian❱ X,
      ❰pushforward❱ (g ∘ f) (hg.comp hf) P = ❰pushforward❱ g hg (❰pushforward❱ f hf P)

-- if f is constant then the pullback should be the zero map, otherwise it's
-- the usual pullback
/-- **Pullback on Jacobians.** Let $X$ and $Y$ be compact Riemann surfaces, that is, compact,
connected, Hausdorff complex-analytic manifolds of dimension one, and write $J(X)$ for the
Jacobian of $X$, an abelian group with a topology. For a holomorphic map $f : X \to Y$, the
pullback $f^*$ is a continuous group homomorphism from $J(Y)$ to $J(X)$. It is meant to be the
zero map when $f$ is constant and the usual pullback along $f$ otherwise; its properties are
stated separately.

Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public def_wanted pullback (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    ❰Jacobian❱ Y →ₜ+ ❰Jacobian❱ X

/-- **The pullback map on Jacobians is holomorphic.** Let $X$ and $Y$ be compact Riemann surfaces
of genus $g_X$ and $g_Y$, with Jacobians $J(X)$ and $J(Y)$, complex manifolds modelled on
$\mathbb{C}^{g_X}$ and $\mathbb{C}^{g_Y}$. For every holomorphic map $f : X \to Y$, the induced
pullback map $f^* : J(Y) \to J(X)$ is holomorphic.

Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public theorem_wanted pullback_contMDiff (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    ContMDiff (modelWithCornersSelf ℂ (Fin (❰genus❱ Y) → ℂ))
      (modelWithCornersSelf ℂ (Fin (❰genus❱ X) → ℂ)) ω (❰pullback❱ f hf)

/-- **Pullback along the identity.** Let $X$ be a compact Riemann surface, that is, a compact,
connected, Hausdorff complex-analytic manifold of dimension one, and write $J(X)$ for its
Jacobian. For every $P \in J(X)$, the pullback of $P$ along the identity map of $X$ is $P$:
$(\mathrm{id}_X)^*(P) = P$.

Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public theorem_wanted pullback_id_apply :
    ∀ P : ❰Jacobian❱ X, ❰pullback❱ id contMDiff_id P = P

/-- **Pullback on Jacobians is compatible with composition.** Let $X$, $Y$ and $Z$ be compact
Riemann surfaces, and for a holomorphic map $h$ between compact Riemann surfaces write $h^*$ for
the induced pullback map on Jacobians. For all holomorphic maps $f : X \to Y$ and $g : Y \to Z$
and every point $P$ of the Jacobian $J(Z)$, we have $(g \circ f)^*(P) = f^*(g^*(P))$.

Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public theorem_wanted pullback_comp_apply (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f)
    (g : Y → Z) (hg : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω g) :
    ∀ P : ❰Jacobian❱ Z,
      ❰pullback❱ (g.comp f) (hg.comp hf) P = ❰pullback❱ f hf (❰pullback❱ g hg P)

/-- **Degree of a holomorphic map.** Let $X$ and $Y$ be compact Riemann surfaces, that is,
compact connected Hausdorff spaces with a complex-analytic atlas modelled on $\mathbb{C}$. Every
holomorphic map $f : X \to Y$ has a degree, which is a natural number.

The intended value is $0$ when $f$ is constant and the usual degree of $f$ otherwise.

Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public def_wanted degree (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) : ℕ  -- 0 for constant case

/-- **Pushforward of a pullback is multiplication by the degree.** Let $X$ and $Y$ be compact
Riemann surfaces, that is, compact, connected, Hausdorff complex-analytic manifolds of dimension
one, and write $J(Y)$ for the Jacobian of $Y$, an abelian group. For every holomorphic map
$f : X \to Y$ and every $P \in J(Y)$, the pushforward along $f$ of the pullback of $P$ along $f$
is $\deg(f) \cdot P$, where the degree $\deg(f)$ is a natural number:
$f_*(f^*(P)) = \deg(f) \cdot P$.

Source: https://leanprover.zulipchat.com/#narrow/stream/583336-Autoformalization/topic/Jacobian%20challenge Via leanprover/lean-eval@38361be, problem `jacobian_challenge_diffgeo`. -/
public theorem_wanted pushforward_pullback (f : X → Y)
    (hf : ContMDiff (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) ω f) :
    ∀ P : ❰Jacobian❱ Y, ❰pushforward❱ f hf (❰pullback❱ f hf P) = (❰degree❱ f hf) • P

end Jacobian

end JacobianChallenge

end MathlibExt.Geometry.JacobianChallengeWanted
