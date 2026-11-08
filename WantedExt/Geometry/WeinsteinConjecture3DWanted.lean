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

/-- A smooth one-form on `M`. -/
abbrev OneForm :=
  Cₛ^∞⟮I; E →L[ℝ] ℝ, fun x : M => TangentSpace I x →L[ℝ] ℝ⟯

/-- A smooth two-form on `M`, represented pointwise as a bilinear form. -/
abbrev TwoForm :=
  Cₛ^∞⟮I; E →L[ℝ] E →L[ℝ] ℝ,
    fun x : M => TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ⟯

/-- A smooth vector field on `M`. -/
abbrev SmoothVectorField :=
  Cₛ^∞⟮I; E, fun x : M => TangentSpace I x⟯

/-- `dα` is the exterior derivative of `α`: the intrinsic
coordinate-free identity uniquely tying `dα` to `α`. -/
def IsExteriorDerivative (α : OneForm I (M := M)) (dα : TwoForm I (M := M)) : Prop :=
  ∀ (X Y : SmoothVectorField I (M := M)) (x : M),
    let dXαY : ℝ := mfderiv I 𝓘(ℝ, ℝ) (fun y => α y (Y y)) x (X x)
    let dYαX : ℝ := mfderiv I 𝓘(ℝ, ℝ) (fun y => α y (X y)) x (Y x)
    dα x (X x) (Y x) = dXαY - dYαX - α x (VectorField.mlieBracket I (⇑X) (⇑Y) x)

/-- The pointwise contact condition in dimension 3: `α` nowhere zero
and `dα` nondegenerate on the two-plane `ker α`. -/
def IsContactForm3 (α : OneForm I (M := M)) (dα : TwoForm I (M := M)) : Prop :=
  IsExteriorDerivative I α dα ∧
    ∀ x : M, α x ≠ 0 ∧ ∃ u v : TangentSpace I x,
      α x u = 0 ∧ α x v = 0 ∧ dα x u v ≠ 0

/-- The Reeb vector field: `α(R) = 1` and `dα(R, ·) = 0`. -/
def IsReebVectorField (α : OneForm I (M := M)) (dα : TwoForm I (M := M))
    (R : ∀ x : M, TangentSpace I x) : Prop :=
  ∀ x : M, α x (R x) = 1 ∧ ∀ v : TangentSpace I x, dα x (R x) v = 0

/-- A smooth integral curve of a vector field on `M`. -/
def IsIntegralCurve (R : ∀ x : M, TangentSpace I x) (γ : ℝ → M) : Prop :=
  ContMDiff 𝓘(ℝ) I ∞ γ ∧
    ∀ t : ℝ, mfderiv 𝓘(ℝ) I γ t (1 : TangentSpace 𝓘(ℝ) t) = R (γ t)

/-- A closed Reeb orbit: a nonconstant periodic integral curve. -/
def HasClosedReebOrbit (R : ∀ x : M, TangentSpace I x) : Prop :=
  ∃ γ : ℝ → M, ∃ T : ℝ,
    0 < T ∧ Function.Periodic γ T ∧ IsIntegralCurve I R γ ∧ ∃ s t : ℝ, γ s ≠ γ t

/- **Weinstein conjecture in dimension three** (Taubes 2007). Every
Reeb vector field of a contact form on a closed smooth 3-manifold has
a closed periodic orbit. -/
/-- Source: C.H. Taubes, 'The Seiberg–Witten equations and the Weinstein conjecture', Geom. Topol. 11 (2007) 2117–2202; arXiv:math/0611007. Conjecture: A. Weinstein, 'On the hypotheses of Rabinowitz' periodic orbit theorems', J. Differential Equations 33 (1979) 353–358. §141 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `weinstein_conjecture_dim3`. -/
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
