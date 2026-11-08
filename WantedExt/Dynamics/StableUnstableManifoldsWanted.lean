/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Local stable/unstable sets at a hyperbolic fixed point (set-level Hadamard–Perron)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Dynamics.StableUnstableManifolds` — stable_unstable_manifolds (manifest `manifests/problems/stable_unstable_manifolds.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Dynamics.StableUnstableManifoldsWanted` namespace. Mathematical
statements are unchanged. Source: J. Hadamard, 'Sur l'itération et les solutions asymptotiques des équations différentielles', Bull. Soc. Math. France 29 (1901); O. Perron, 'Über Stabilität und asymptotisches Verhalten der Integrale von Differentialgleichungssystemen', Math. Z. 29 (1929) 129–160. Listed as §104 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Dynamics.StableUnstableManifoldsWanted
namespace Dynamics
namespace StableUnstableManifoldsProblem

/-!
# Local stable and unstable sets at a hyperbolic fixed point

For a `C¹` map `f : ℝⁿ → ℝⁿ` with a hyperbolic invertible fixed point at
`x₀`, some open neighbourhood `U ∋ x₀` carries genuinely local stable
and unstable sets — orbits required to stay inside `U` while converging
to `x₀` — meeting only at `x₀`. This is the set-level (topological)
shadow of the Hadamard–Perron theorem; the full theorem additionally
asserts that the local stable and unstable sets are immersed `C¹`
submanifolds tangent to the stable / unstable eigenspaces. §104 in
Knill's *Some Fundamental Theorems in Mathematics*.

The "orbit stays in `U`" requirement is essential: without it, homoclinic
points (forward and backward limits at `x₀`, but excursions outside any
small neighbourhood) would falsify `Wˢ ∩ Wᵘ = {x₀}` in systems with
homoclinic dynamics. With it, after shrinking `U`, the only point with
both forward and backward orbits remaining in `U` and converging to
`x₀` is `x₀` itself.
-/

open scoped Topology
open Filter Polynomial

/-- The Euclidean model space `ℝⁿ`. -/
abbrev E (n : ℕ) : Type := EuclideanSpace ℝ (Fin n)

/-- Multiset of complex eigenvalues of `L : ℝⁿ →L[ℝ] ℝⁿ`. -/
noncomputable def complexEigenvalues {n : ℕ} (L : E n →L[ℝ] E n) : Multiset ℂ :=
  ((L : E n →ₗ[ℝ] E n).charpoly.map (algebraMap ℝ ℂ)).roots

/-- `L` is **hyperbolic**: no complex eigenvalue lies on the unit
circle. -/
def IsHyperbolicLinear {n : ℕ} (L : E n →L[ℝ] E n) : Prop :=
  ∀ μ ∈ complexEigenvalues L, ‖μ‖ ≠ 1

/- **Local stable and unstable sets at a hyperbolic fixed point**
(set-level Hadamard–Perron). For a `C¹` map `f` with an invertible
hyperbolic fixed point at `x₀`, some open neighbourhood `U ∋ x₀`
carries the local stable set `Wˢ` (points whose forward orbit stays in
`U` and converges to `x₀`) and the local unstable set `Wᵘ` (points
admitting a backward orbit staying in `U` and converging to `x₀`), and
`Wˢ ∩ Wᵘ = {x₀}`. -/
/-- Source: J. Hadamard, 'Sur l'itération et les solutions asymptotiques des équations différentielles', Bull. Soc. Math. France 29 (1901); O. Perron, 'Über Stabilität und asymptotisches Verhalten der Integrale von Differentialgleichungssystemen', Math. Z. 29 (1929) 129–160. Listed as §104 in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `stable_unstable_manifolds`. -/
public theorem_wanted stable_unstable_manifolds_exist (n : ℕ) (f : E n → E n) (x₀ : E n)
    (_hf : ContDiffAt ℝ 1 f x₀)
    (_hfix : f x₀ = x₀)
    (_hhyp : IsHyperbolicLinear (fderiv ℝ f x₀))
    (_hf_inv : (fderiv ℝ f x₀).IsInvertible) :
    ∃ U : Set (E n), IsOpen U ∧ x₀ ∈ U ∧
      ∃ Ws Wu : Set (E n),
        Ws = {x | (∀ k : ℕ, f^[k] x ∈ U) ∧
                  Tendsto (fun k => f^[k] x) atTop (𝓝 x₀)} ∧
        Wu = {x | ∃ y : ℕ → E n,
                    y 0 = x ∧
                    (∀ k : ℕ, y k ∈ U) ∧
                    (∀ k : ℕ, f (y (k + 1)) = y k) ∧
                    Tendsto y atTop (𝓝 x₀)} ∧
        Ws ∩ Wu = {x₀}

end StableUnstableManifoldsProblem
end Dynamics

end MathlibExt.Dynamics.StableUnstableManifoldsWanted
