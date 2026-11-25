/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Finite-time singularity formation for C^{1,α} solutions to the incompressible Euler equations on ℝ³

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.FiniteTimeSingularity` — annals_finite_time_singularity (manifest `manifests/problems/annals_finite_time_singularity.toml`, rev 1, submitter David Ledvinka, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.FiniteTimeSingularityWanted` namespace. Mathematical
statements are unchanged. Source: T. M. Elgindi, `Finite-time singularity formation for C^{1,α} solutions to the incompressible Euler equations on ℝ³`, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-3-FiniteTimeSingularity.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.LinearAlgebra.CrossProduct
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.MetricSpace.Holder

@[expose] public section

namespace MathlibExt.Analysis.FiniteTimeSingularityWanted
/-!
# Main Statement from Finite-time singularity formation for C^{1,α} solutions to
# the incompressible Euler equations on ℝ³

We formalise the statement of the main result from T. M. Elgindi,
`Finite-time singularity formation for C^{1,α} solutions to the incompressible
Euler equations on ℝ³`, Annals of Math, 194 (3) 2021.
-/

set_option autoImplicit false

section

open NNReal Bornology

variable {α β : Type*} [Bornology α]

/-- **Functions bounded on a set.** A function $f : \beta \to \alpha$ into a space $\alpha$ with a
bornology is bounded on a set $s \subseteq \beta$ if the image $f(s)$ is a bounded subset of
$\alpha$. -/
abbrev IsBoundedFunOn (f : β → α) (s : Set β) : Prop := IsBounded (f '' s)

/-- **Bounded functions.** A function $f : \beta \to \alpha$ into a space $\alpha$ with a
bornology is bounded if its range $f(\beta)$ is a bounded subset of $\alpha$. -/
abbrev IsBoundedFun (f : β → α) : Prop := IsBoundedFunOn f Set.univ

variable {X Y Z : Type*} [PseudoEMetricSpace X] [PseudoEMetricSpace Y] [PseudoEMetricSpace Z]

/-- **Hölder continuity.** Let $X$ and $Y$ be pseudo-extended metric spaces (distances take
values in $[0, \infty]$), let $r \ge 0$ be a real number and $f : X \to Y$. Then $f$ is
$r$-Hölder if there is a constant $C \ge 0$ such that
$d_Y(f(x_1), f(x_2)) \le C \, d_X(x_1, x_2)^r$ for all $x_1, x_2 \in X$. -/
abbrev Holder (r : ℝ≥0) (f : X → Y) : Prop := ∃ C : ℝ≥0, HolderWith C r f

/-- **Hölder continuity on a set.** Let $X$ and $Y$ be pseudo-extended metric spaces (distances
take values in $[0, \infty]$), let $r \ge 0$ be a real number, $s \subseteq X$ and $f : X \to Y$.
Then $f$ is $r$-Hölder on $s$ if there is a constant $C \ge 0$ such that
$d_Y(f(x_1), f(x_2)) \le C \, d_X(x_1, x_2)^r$ for all $x_1, x_2 \in s$. -/
abbrev HolderOn (r : ℝ≥0) (f : X → Y) (s : Set X) : Prop := ∃ C : ℝ≥0, HolderOnWith C r f s

variable (𝕜 : Type*) {E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]

/-- **Continuously differentiable functions with Hölder derivative.** Let $\mathbb{k}$ be a
nontrivially normed field, $E$ and $F$ normed spaces over $\mathbb{k}$ and $\alpha \ge 0$ a real
number. A function $f : E \to F$ is in $C^{1,\alpha}(E)$ if $f$ is continuously differentiable
over $\mathbb{k}$ and its derivative $Df$, a map from $E$ to the space $L(E, F)$ of continuous
$\mathbb{k}$-linear maps with the operator norm, is bounded and $\alpha$-Hölder. -/
def IsContDiffHolder (α : ℝ≥0) (f : E → F) : Prop :=
  ContDiff 𝕜 1 f ∧ IsBoundedFun (fderiv 𝕜 f) ∧ Holder α (fderiv 𝕜 f)

/-- **Continuously differentiable functions with Hölder derivative on a set.** Let $\mathbb{k}$
be a nontrivially normed field, $E$ and $F$ normed spaces over $\mathbb{k}$, $s \subseteq E$ and
$\alpha \ge 0$ a real number. A function $f : E \to F$ is in $C^{1,\alpha}(s)$ if $f$ is
continuously differentiable on $s$ over $\mathbb{k}$ and its derivative within $s$, a map from
$E$ to the space $L(E, F)$ of continuous $\mathbb{k}$-linear maps with the operator norm, is
bounded on $s$ and $\alpha$-Hölder on $s$. -/
def IsContDiffHolderOn (α : ℝ≥0) (f : E → F) (s : Set E) : Prop :=
  ContDiffOn 𝕜 1 f s ∧ IsBoundedFunOn (fderivWithin 𝕜 f s) s ∧ HolderOn α (fderivWithin 𝕜 f s) s

end

namespace FiniteTimeSingularity

open Set Gradient Matrix Filter Topology

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- **Spatial directional derivative of a time-dependent vector field.** Given
$u, v : \mathbb{R}^3 \times \mathbb{R} \to \mathbb{R}^3$, the spatial directional derivative
$(u \cdot \nabla_x) v$ of $v$ in the direction of $u$ is the function
$(x, t) \mapsto D_x v(x, t)\,[u(x, t)]$, where $D_x v(x, t)$ is the Fréchet derivative of
$y \mapsto v(y, t)$ at $x$ (taken to be $0$ if this map is not differentiable at $x$). -/
noncomputable def directionalDeriv (v : ℝ³ → ℝ → ℝ³) (u : ℝ³ → ℝ → ℝ³) (x : ℝ³) (t : ℝ) : ℝ³ :=
  fderiv ℝ (v · t) x (u x t)

local notation u "·∇ₓ" v => directionalDeriv v u

/-- **Time derivative.** For a function $u(x, t) \in \mathbb{R}^3$ of a point $x \in \mathbb{R}^3$
and a time $t \in \mathbb{R}$, the time derivative $\partial_t u(x, t) \in \mathbb{R}^3$ is the
derivative at $t$ of the function $s \mapsto u(x, s)$, taken to be $0$ when that function is not
differentiable at $t$. -/
noncomputable def timeDeriv (u : ℝ³ → ℝ → ℝ³) (x : ℝ³) (t : ℝ) : ℝ³ :=
  deriv (u x) t

local notation "∂ₜ" u => timeDeriv u

/-- **Spatial gradient.** For a function $p(x, t)$ of a point $x \in \mathbb{R}^3$ and a time
$t \in \mathbb{R}$, the spatial gradient $\nabla_x p(x, t) \in \mathbb{R}^3$ is the gradient at $x$
of the function $y \mapsto p(y, t)$, taken to be $0$ when that function is not differentiable
at $x$. -/
noncomputable def spaceGrad (p : ℝ³ → ℝ → ℝ) (x : ℝ³) (t : ℝ) : ℝ³ :=
  ∇ (p · t) x

local notation "∇ₓ" p => spaceGrad p

/-- **Divergence.** The divergence of a vector field $u : \mathbb{R}^3 \to \mathbb{R}^3$ at a point
$x \in \mathbb{R}^3$ is the trace of the Fréchet derivative $Du(x)$, a linear map from
$\mathbb{R}^3$ to $\mathbb{R}^3$ (taken to be $0$ if $u$ is not differentiable at $x$). -/
noncomputable def div (u : ℝ³ → ℝ³) (x : ℝ³) : ℝ :=
  (fderiv ℝ u x).trace ℝ ℝ³

/-- **Standard basis vectors of ℝ³.** For $i \in \{0, 1, 2\}$, $e_i \in \mathbb{R}^3$ is the
$i$-th standard basis vector: its $i$-th coordinate is $1$ and its other coordinates are $0$. -/
def e (i : Fin 3) : ℝ³ := WithLp.toLp 2 (Pi.single i 1)

/-- **Vorticity.** The vorticity of a vector field $u : \mathbb{R}^3 \to \mathbb{R}^3$ is its curl
$(\nabla \times u)(x) = \sum_{i=1}^{3} e_i \times Du(x)\,e_i$, where $e_1, e_2, e_3$ is the
standard basis of $\mathbb{R}^3$, $\times$ is the cross product and $Du(x)\,e_i$ is the partial
derivative of $u$ at $x$ in direction $e_i$ (all taken to be $0$ when $u$ is not differentiable
at $x$). -/
noncomputable def vorticity (u : ℝ³ → ℝ³) (x : ℝ³) : ℝ³ :=
  WithLp.toLp 2 (∑ i, e i ⨯₃ (fderiv ℝ u x (e i)))

local notation "∇×" u => vorticity u

/-- **Local solutions of the incompressible Euler equations.** Let $T \in \mathbb{R}$, let
$u_0 : \mathbb{R}^3 \to \mathbb{R}^3$, and let $p : \mathbb{R}^3 \times \mathbb{R} \to \mathbb{R}$
and $u : \mathbb{R}^3 \times \mathbb{R} \to \mathbb{R}^3$. Write $\partial_t u$ for the time
derivative of $u$, $(u \cdot \nabla_x) u$ for the spatial directional derivative of $u$ in the
direction of $u$, and $\nabla_x p$ for the spatial gradient of $p$. Then $u$ is a local solution
of the incompressible Euler equations up to time $T$, with pressure $p$ and initial data $u_0$,
if $u$ and $p$ are continuously differentiable, as functions of $(x, t)$, on
$\mathbb{R}^3 \times [0, T)$, if for all $x \in \mathbb{R}^3$ and $t \in (0, T)$

$$\partial_t u(x, t) + (u \cdot \nabla_x) u(x, t) + \nabla_x p(x, t) = 0,$$

if for every $t \in (0, T)$ the divergence of $u(\cdot, t)$ is $0$ at every point of
$\mathbb{R}^3$, and if $u(\cdot, 0) = u_0$. -/
structure IsLocalEulerEquationSolution
    (p : ℝ³ → ℝ → ℝ) (u₀ : ℝ³ → ℝ³) (T : ℝ) (u : ℝ³ → ℝ → ℝ³) where
  solContDiff : ContDiffOn ℝ 1 u.uncurry (univ ×ˢ Ico 0 T)
  pressureContDiff : ContDiffOn ℝ 1 p.uncurry (univ ×ˢ Ico 0 T)
  eq : ∀ x, ∀ t ∈ Ioo 0 T, (∂ₜ u) x t + (u ·∇ₓ u) x t + (∇ₓ p) x t = 0
  div_free : ∀ t ∈ Ioo 0 T, div (u · t) = 0
  init : (u · 0) = u₀

/-- **Odd vector fields in three dimensions.** A vector field $u : \mathbb{R}^3 \to \mathbb{R}^3$
with components $u_1, u_2, u_3$ is odd if, for each $i \in \{1, 2, 3\}$, the component $u_i$ is an
odd function of the $i$-th coordinate and an even function of each of the other two coordinates,
when the remaining coordinates are held fixed. -/
def IsOdd (u : ℝ³ → ℝ³) : Prop :=
  (∀ x₁ x₂, (u !₂[·, x₁, x₂] 0).Odd ∧ (u !₂[·, x₁, x₂] 1).Even ∧ (u !₂[·, x₁, x₂] 2).Even) ∧
  (∀ x₀ x₂, (u !₂[x₀, ·, x₂] 0).Even ∧ (u !₂[x₀, ·, x₂] 1).Odd ∧ (u !₂[x₀, ·, x₂] 2).Even) ∧
  (∀ x₀ x₁, (u !₂[x₀, x₁, ·] 0).Even ∧ (u !₂[x₀, x₁, ·] 1).Even ∧ (u !₂[x₀, x₁, ·] 2).Odd)

/-- **Elgindi's theorem: finite-time singularity of $C^{1,\alpha}$ Euler flows.** There exist a
real number $\alpha > 0$ and a vector field $u_0 : \mathbb{R}^3 \to \mathbb{R}^3$ that is odd,
has divergence $0$ at every point and lies in $C^{1,\alpha}(\mathbb{R}^3)$, together with a
constant $C > 0$ such that its vorticity satisfies
$|(\nabla \times u_0)(x)| \le C / (|x|^\alpha + 1)$ for every $x \in \mathbb{R}^3$, and there
exist functions $p : \mathbb{R}^3 \times \mathbb{R} \to \mathbb{R}$ and
$u : \mathbb{R}^3 \times \mathbb{R} \to \mathbb{R}^3$ such that $u(\cdot, t)$ is odd for every
$t \in [0, 1)$, $u$ is a local solution of the incompressible Euler equations up to time $1$
with pressure $p$ and initial data $u_0$, $u$ lies in $C^{1,\alpha}(\mathbb{R}^3 \times [0, T])$
as a function of $(x, t)$ for every $T \in (0, 1)$, and
$$\int_0^t \sup_{x \in \mathbb{R}^3} |(\nabla \times u(\cdot, s))(x)| \, ds \to +\infty$$
as $t \to 1^-$. Here $|\cdot|$ is the Euclidean norm, differentiability is over $\mathbb{R}$, and
$\mathbb{R}^3 \times \mathbb{R}$ carries the norm $\max(|x|, |t|)$.

Elgindi states the conclusion for the unique local odd solution in this class. Uniqueness of
solutions up to any time $T$ at which they exist was already known, so only existence is
asserted here.

Source: T. M. Elgindi, `Finite-time singularity formation for C^{1,α} solutions to the incompressible Euler equations on ℝ³`, Annals of Math, 194 (3) 2021. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2021-194-3-FiniteTimeSingularity.lean Via leanprover/lean-eval@38361be, problem `annals_finite_time_singularity`.
-/
public theorem_wanted theorem_1 :
    ∃ α > 0, ∃ u₀, div u₀ = 0 ∧ IsOdd u₀ ∧ IsContDiffHolder ℝ α u₀ ∧
      (∃ C > 0, ∀ x, ‖(∇×u₀) x‖ ≤ C / (‖x‖ ^ (α : ℝ) + 1)) ∧
        ∃ p, ∃ u, (∀ t ∈ Ico 0 1, IsOdd (u · t)) ∧
            IsLocalEulerEquationSolution p u₀ 1 u ∧
              (∀ T ∈ Ioo 0 1, IsContDiffHolderOn ℝ α u.uncurry (univ ×ˢ Icc 0 T)) ∧
                Tendsto (fun t ↦ ∫ s in 0..t, ⨆ x, ‖(∇×(u · s)) x‖) (𝓝[<] 1) atTop

end FiniteTimeSingularity

end MathlibExt.Analysis.FiniteTimeSingularityWanted
