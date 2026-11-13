/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Anosov–Bowen shadowing lemma

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Dynamics.HyperbolicShadowing` — anosov_bowen_shadowing (manifest `manifests/problems/anosov_bowen_shadowing.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Dynamics.HyperbolicShadowingWanted` namespace. Mathematical
statements are unchanged. Source: D.V. Anosov, 'Geodesic flows on closed Riemannian manifolds with negative curvature', Trudy Mat. Inst. Steklov. 90 (1967); R. Bowen, 'ω-limit sets for Axiom A diffeomorphisms', J. Differential Equations 18 (1975) 333–339. Listed as §67 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Dynamics.HyperbolicShadowingWanted
namespace Dynamics
namespace HyperbolicShadowingProblem

/-!
# Anosov–Bowen shadowing lemma

Every compact hyperbolic invariant set of a `C¹` diffeomorphism admits
an open neighbourhood on which every approximate orbit is `δ`-close to
a true `T`-orbit. Anosov 1967; Bowen 1975. §67 in Knill's *Some
Fundamental Theorems in Mathematics*.

The statement here is the Euclidean special case on
`E d := EuclideanSpace ℝ (Fin d)` — a faithful finite-dimensional local
model that captures the hyperbolic-dynamics content while avoiding the
smooth-manifold and tangent-bundle infrastructure mathlib does not yet
package. The hyperbolic-set predicate is bundled as a `HyperbolicStructure`:
a pointwise stable/unstable splitting with the uniform exponential
contraction/expansion estimates of Anosov's original definition. The
textbook definition additionally asks for the splitting to be continuous
in `x`; we encode only the pointwise content with uniform constants,
which is the minimal data the shadowing proof depends on.
-/

open scoped Topology

/-- **Euclidean model space for the shadowing lemma.** For a natural number $d$, $E_d$ is the
Euclidean space $\mathbb{R}^d$, the real $d$-tuples with the Euclidean norm. -/
abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

variable {d : ℕ}

/-- **Hyperbolic structure.** Let $T : \mathbb{R}^d \to \mathbb{R}^d$ be a homeomorphism and let
$K \subseteq \mathbb{R}^d$. Write $DF_x$ for the derivative of a map $F$ at $x$, $T^n$ for the
$n$-fold iterate of $T$ and $T^{-n}$ for the $n$-fold iterate of $T^{-1}$. A hyperbolic structure
for $T$ on $K$ consists of the following: $T$ and $T^{-1}$ are $C^1$; $T(K) = K$; to every
$x \in \mathbb{R}^d$ are assigned linear subspaces $E^s(x)$ and $E^u(x)$ of $\mathbb{R}^d$ such that
for every $x \in K$ we have $\mathbb{R}^d = E^s(x) \oplus E^u(x)$, $DT_x(E^s(x)) = E^s(T(x))$ and
$DT_x(E^u(x)) = E^u(T(x))$; and there are real numbers $\lambda$ with $0 < \lambda < 1$ and
$C > 0$ such that for every $x \in K$ and every $n \in \mathbb{N}$,
$\|D(T^n)_x v\| \le C \lambda^n \|v\|$ for all $v \in E^s(x)$ and
$\|D(T^{-n})_x v\| \le C \lambda^n \|v\|$ for all $v \in E^u(x)$. -/
structure HyperbolicStructure (T : E d ≃ₜ E d) (K : Set (E d)) where
  contDiff_fwd : ContDiff ℝ 1 (T : E d → E d)
  contDiff_bwd : ContDiff ℝ 1 (T.symm : E d → E d)
  invariant : (T : E d → E d) '' K = K
  stable : E d → Submodule ℝ (E d)
  unstable : E d → Submodule ℝ (E d)
  isCompl_stable_unstable : ∀ x ∈ K, IsCompl (stable x) (unstable x)
  stable_invariant : ∀ x ∈ K,
    (stable x).map (fderiv ℝ (T : E d → E d) x : E d →ₗ[ℝ] E d) = stable (T x)
  unstable_invariant : ∀ x ∈ K,
    (unstable x).map (fderiv ℝ (T : E d → E d) x : E d →ₗ[ℝ] E d) = unstable (T x)
  rate : ℝ
  rate_pos : 0 < rate
  rate_lt_one : rate < 1
  const : ℝ
  const_pos : 0 < const
  contract_stable : ∀ x ∈ K, ∀ v : E d, v ∈ stable x → ∀ n : ℕ,
    ‖fderiv ℝ ((T : E d → E d)^[n]) x v‖ ≤ const * rate ^ n * ‖v‖
  contract_unstable : ∀ x ∈ K, ∀ v : E d, v ∈ unstable x → ∀ n : ℕ,
    ‖fderiv ℝ ((T.symm : E d → E d)^[n]) x v‖ ≤ const * rate ^ n * ‖v‖

/-- **Hyperbolic invariant set.** Let $T : \mathbb{R}^d \to \mathbb{R}^d$ be a homeomorphism. A set
$K \subseteq \mathbb{R}^d$ is a hyperbolic invariant set for $T$ if there exists a hyperbolic
structure for $T$ on $K$. -/
def IsHyperbolic (T : E d ≃ₜ E d) (K : Set (E d)) : Prop :=
  Nonempty (HyperbolicStructure T K)

/-- **Pseudo-orbit.** Let $d$ be a natural number, let $\mathbb{R}^d$ carry the Euclidean norm,
let $T : \mathbb{R}^d \to \mathbb{R}^d$ be a map and let $\varepsilon$ be a real number. A
sequence $(x_n)_{n \in \mathbb{N}}$ in $\mathbb{R}^d$ is an $\varepsilon$-pseudo orbit of $T$
if $\|x_{n+1} - T(x_n)\| < \varepsilon$ for every $n \in \mathbb{N}$. -/
def IsPseudoOrbit (T : E d → E d) (ε : ℝ) (x : ℕ → E d) : Prop :=
  ∀ n : ℕ, ‖x (n + 1) - T (x n)‖ < ε

/-- **Shadowing property.** Let $T : \mathbb{R}^d \to \mathbb{R}^d$ be a map, write $T^n$ for its
$n$-fold iterate, and let $K \subseteq \mathbb{R}^d$. The set $K$ has the shadowing property for
$T$ if there is an open set $U \subseteq \mathbb{R}^d$ containing $K$ such that for every
$\delta > 0$ there is $\varepsilon > 0$ with the following property: for every $\varepsilon$-pseudo
orbit $(x_n)_{n \in \mathbb{N}}$ of $T$ with $x_n \in U$ for all $n$, there is a point
$y \in \mathbb{R}^d$ with $\|x_n - T^n(y)\| < \delta$ for all $n \in \mathbb{N}$. -/
def HasShadowing (T : E d → E d) (K : Set (E d)) : Prop :=
  ∃ U : Set (E d), IsOpen U ∧ K ⊆ U ∧
    ∀ δ > 0, ∃ ε > 0, ∀ x : ℕ → E d,
      (∀ n, x n ∈ U) → IsPseudoOrbit T ε x →
      ∃ y : E d, ∀ n : ℕ, ‖x n - T^[n] y‖ < δ

/- **Anosov–Bowen shadowing lemma** (Anosov 1967; Bowen 1975). Every
compact hyperbolic invariant set has the shadowing property. -/
/-- **Anosov–Bowen shadowing lemma.** Let $T : \mathbb{R}^d \to \mathbb{R}^d$ be a homeomorphism and
let $K \subseteq \mathbb{R}^d$ be a compact set that is a hyperbolic invariant set for $T$. Then $K$
has the shadowing property for $T$.

Source: D.V. Anosov, 'Geodesic flows on closed Riemannian manifolds with negative curvature', Trudy Mat. Inst. Steklov. 90 (1967); R. Bowen, 'ω-limit sets for Axiom A diffeomorphisms', J. Differential Equations 18 (1975) 333–339. Listed as §67 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `anosov_bowen_shadowing`. -/
public theorem_wanted hyperbolic_has_shadowing
    (T : E d ≃ₜ E d) (K : Set (E d))
    (_hKc : IsCompact K) (_hK : IsHyperbolic T K) :
    HasShadowing (T : E d → E d) K

end HyperbolicShadowingProblem
end Dynamics

end MathlibExt.Dynamics.HyperbolicShadowingWanted
