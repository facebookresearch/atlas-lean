/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Weinstein conjecture in dimension three (Taubes 2007)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Geometry.WeinsteinConjecture3D` — weinstein_conjecture_dim3 (manifest `manifests/problems/weinstein_conjecture_dim3.toml`, rev 1, submitter Kim Morrison, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Geometry.WeinsteinConjecture3DWanted` namespace. Mathematical
statements are unchanged. Source: C.H. Taubes, 'The Seiberg–Witten equations and the Weinstein conjecture', Geom. Topol. 11 (2007) 2117–2202; arXiv:math/0611007. Conjecture: A. Weinstein, 'On the hypotheses of Rabinowitz' periodic orbit theorems', J. Differential Equations 33 (1979) 353–358. §141 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Geometry.WeinsteinConjecture3DWanted
namespace Geometry
namespace WeinsteinConjecture3DProblem

/-!
# Weinstein conjecture in dimension three (Taubes 2007)

On a closed contact 3-manifold, every Reeb vector field of a contact
form has a closed periodic orbit. Cliff Taubes (2007), via Seiberg–
Witten Floer homology / embedded contact homology. §141 in Knill's
*Some Fundamental Theorems in Mathematics*.

mathlib has smooth manifolds, tangent spaces, manifold derivatives
(`mfderiv`), and Lie brackets (`VectorField.mlieBracket`), but no
contact-geometry API and only an exterior derivative on normed spaces
(`extDeriv`), not on manifolds. The local encoding below pins the
exterior derivative `dα` by the intrinsic, coordinate-free identity
`dα(X, Y) = X(α(Y)) − Y(α(X)) − α([X, Y])` for all smooth vector fields
`X, Y`, which uniquely determines `dα`. The pointwise contact condition
in dimension 3 — `α` nowhere zero, `dα` nondegenerate on `ker α` — is
equivalent to `α ∧ dα` nowhere zero.

`[I.Boundaryless]` is essential: on the cube `[0,1]³` with `α = dz +
x·dy`, Reeb field `R = ∂/∂z`, every integral curve has affine
`z`-component with `|z'| = 1`, hence escapes the cube and there is no
closed orbit.
-/

open Set
open scoped Manifold ContDiff

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] [TopologicalSpace M]
  [ChartedSpace H M]
variable (I : ModelWithCorners ℝ E H)
variable [IsManifold I ∞ M]

/-- **Smooth one-forms.** Let $M$ be a smooth manifold (possibly with boundary or corners).
A smooth one-form on $M$ is a smooth section of the cotangent bundle of $M$: a smooth choice of
a linear map $\alpha_x : T_xM \to \mathbb{R}$ at each point $x \in M$. -/
abbrev OneForm :=
  Cₛ^∞⟮I; E →L[ℝ] ℝ, fun x : M => TangentSpace I x →L[ℝ] ℝ⟯

/-- **Two-forms as fields of bilinear forms.** Let $M$ be a smooth manifold (possibly with
boundary or corners). A two-form on $M$ is here a smooth section of the bundle whose fiber at
$x \in M$ is the space of bilinear maps $T_xM \times T_xM \to \mathbb{R}$; antisymmetry is not
required. -/
abbrev TwoForm :=
  Cₛ^∞⟮I; E →L[ℝ] E →L[ℝ] ℝ,
    fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ⟯

/-- **Smooth vector fields.** Let $M$ be a smooth manifold (possibly with boundary or
corners). A smooth vector field on $M$ is a smooth section of the tangent bundle of $M$: a smooth
choice of a tangent vector $X_x \in T_xM$ at each point $x \in M$. -/
abbrev SmoothVectorField :=
  Cₛ^∞⟮I; E, fun x : M => TangentSpace I x⟯

/-- **Exterior derivative of a one-form.** A two-form $d\alpha$ on $M$ is the exterior derivative
of a one-form $\alpha$ on $M$ when, for all smooth vector fields $X, Y$ on $M$ and every point
$x \in M$,
$$
d\alpha_x(X_x, Y_x) = X_x\big(\alpha(Y)\big) - Y_x\big(\alpha(X)\big) - \alpha_x\big([X, Y]_x\big),
$$
where $\alpha(Y)$ is the function $y \mapsto \alpha_y(Y_y)$, $X_x(f)$ is the derivative of a
function $f$ at $x$ in the direction $X_x$, and $[X, Y]$ is the Lie bracket of $X$ and $Y$.

This coordinate-free identity determines $d\alpha$ uniquely. -/
def IsExteriorDerivative (α : OneForm I (M := M)) (dα : TwoForm I (M := M)) : Prop :=
  ∀ (X Y : SmoothVectorField I (M := M)) (x : M),
    let dXαY : ℝ := mfderiv I 𝓘(ℝ, ℝ) (fun y => α y (Y y)) x (X x)
    let dYαX : ℝ := mfderiv I 𝓘(ℝ, ℝ) (fun y => α y (X y)) x (Y x)
    dα x (X x) (Y x) = dXαY - dYαX - α x (VectorField.mlieBracket I (⇑X) (⇑Y) x)

/-- **Contact condition for a one-form.** Let $\alpha$ be a one-form and $d\alpha$ a two-form on
$M$. The pair satisfies the contact condition when $d\alpha$ is the exterior derivative of
$\alpha$ and, at every point $x \in M$, the covector $\alpha_x$ is nonzero and there are tangent
vectors $u, v \in T_xM$ with $\alpha_x(u) = \alpha_x(v) = 0$ and $d\alpha_x(u, v) \ne 0$.

When $M$ has dimension $3$, this says that $\alpha$ vanishes nowhere and $d\alpha$ is
nondegenerate on the plane $\ker \alpha_x$, which is equivalent to $\alpha \wedge d\alpha$
vanishing nowhere. -/
def IsContactForm3 (α : OneForm I (M := M)) (dα : TwoForm I (M := M)) : Prop :=
  IsExteriorDerivative I α dα ∧
    ∀ x : M, α x ≠ 0 ∧ ∃ u v : TangentSpace I x,
      α x u = 0 ∧ α x v = 0 ∧ dα x u v ≠ 0

/-- **Reeb vector fields.** Let $\alpha$ be a one-form and $d\alpha$ a two-form on $M$. An
assignment $R$ of a tangent vector $R(x) \in T_xM$ to each point $x \in M$ is a Reeb vector field
for $(\alpha, d\alpha)$ when, at every point $x \in M$, $\alpha_x(R(x)) = 1$ and
$d\alpha_x(R(x), v) = 0$ for all $v \in T_xM$. -/
def IsReebVectorField (α : OneForm I (M := M)) (dα : TwoForm I (M := M))
    (R : ∀ x : M, TangentSpace I x) : Prop :=
  ∀ x : M, α x (R x) = 1 ∧ ∀ v : TangentSpace I x, dα x (R x) v = 0

/-- **Integral curves.** Let $M$ be a smooth manifold (possibly with boundary or corners) and let
$R$ assign to each point $x \in M$ a tangent vector $R(x) \in T_xM$. A curve
$\gamma : \mathbb{R} \to M$ is an integral curve of $R$ when $\gamma$ is smooth and
$\gamma'(t) = R(\gamma(t))$ for every $t \in \mathbb{R}$. -/
def IsIntegralCurve (R : ∀ x : M, TangentSpace I x) (γ : ℝ → M) : Prop :=
  ContMDiff 𝓘(ℝ) I ∞ γ ∧
    ∀ t : ℝ, mfderiv 𝓘(ℝ) I γ t (1 : TangentSpace 𝓘(ℝ) t) = R (γ t)

/-- **Vector fields with a closed orbit.** Let $M$ be a smooth manifold (possibly with boundary or
corners) and let $R$ assign to each point $x \in M$ a tangent vector $R(x) \in T_xM$. We say that
$R$ has a closed orbit when there are a curve $\gamma : \mathbb{R} \to M$ and a real number
$T > 0$ such that $\gamma$ is $T$-periodic, $\gamma$ is a smooth integral curve of $R$, and
$\gamma$ is not constant.

The main theorem applies this to a Reeb vector field, whence the name closed Reeb orbit. -/
def HasClosedReebOrbit (R : ∀ x : M, TangentSpace I x) : Prop :=
  ∃ γ : ℝ → M, ∃ T : ℝ,
    0 < T ∧ Function.Periodic γ T ∧ IsIntegralCurve I R γ ∧ ∃ s t : ℝ, γ s ≠ γ t

/- **Weinstein conjecture in dimension three** (Taubes 2007). Every
Reeb vector field of a contact form on a closed smooth 3-manifold has
a closed periodic orbit. -/
/-- **Weinstein conjecture in dimension three (Taubes).** Let $M$ be a nonempty compact Hausdorff
smooth manifold without boundary, modelled on a real vector space of dimension $3$. Let $\alpha$
be a smooth one-form and $d\alpha$ a smooth two-form on $M$ satisfying the contact condition:
$d\alpha$ is the exterior derivative of $\alpha$ and, at every point $x$, $\alpha_x \ne 0$ and
$d\alpha_x(u, v) \ne 0$ for some $u, v \in \ker \alpha_x$. Let $R$ be a Reeb vector field for
$(\alpha, d\alpha)$. Then $R$ has a closed orbit: a nonconstant smooth integral curve of $R$
that is periodic with some positive period.

Source: C.H. Taubes, 'The Seiberg–Witten equations and the Weinstein conjecture', Geom. Topol. 11 (2007) 2117–2202; arXiv:math/0611007. Conjecture: A. Weinstein, 'On the hypotheses of Rabinowitz' periodic orbit theorems', J. Differential Equations 33 (1979) 353–358. §141 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `weinstein_conjecture_dim3`. -/
public theorem_wanted weinstein_conjecture_dim_three
    (E' : Type*) [NormedAddCommGroup E'] [NormedSpace ℝ E']
    [FiniteDimensional ℝ E']
    (H' : Type*) [TopologicalSpace H']
    (I' : ModelWithCorners ℝ E' H')
    (M' : Type*) [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M']
    [T2Space M'] [CompactSpace M'] [Nonempty M'] [Fact (Module.finrank ℝ E' = 3)]
    [I'.Boundaryless]
    (α : OneForm I' (M := M')) (dα : TwoForm I' (M := M'))
    (R : ∀ x : M', TangentSpace I' x)
    (_hcontact : IsContactForm3 I' α dα)
    (_hReeb : IsReebVectorField I' α dα R) :
    HasClosedReebOrbit I' R

end WeinsteinConjecture3DProblem
end Geometry

end MathlibExt.Geometry.WeinsteinConjecture3DWanted
