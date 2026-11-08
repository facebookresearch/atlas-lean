/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Lax's approximation theorem for toral homeomorphisms

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Dynamics.LaxApproximation` — lax_approximation (manifest `manifests/problems/lax_approximation.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Dynamics.LaxApproximationWanted` namespace. Mathematical
statements are unchanged. Source: P. D. Lax, *Approximation of measure preserving transformations*, Comm. Pure Appl. Math. 24 (1971). Knill, *Some fundamental theorems in mathematics*, §110.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Dynamics.LaxApproximationWanted
namespace Dynamics.LaxApproximation

/-!
# Lax's approximation theorem for toral homeomorphisms

`lax_approximation` (Peter Lax 1971): every volume-preserving homeomorphism of
the `d`-torus (`d ≥ 1`) can be approximated arbitrarily well, in the
`L∞`-metric `δ`, by cyclic cube exchange transformations. The trusted helpers
(`Torus`, `VolumePreservingEquiv`, `deltaDist`, `ToralDynamicalSystem`, `cube`,
`cubeShift`, `IsCyclicCubeExchange`, …) are non-holes. Mathlib has the torus,
measure-preserving maps, and Hall's marriage theorem (the combinatorial
ingredient) but not Lax's theorem, cube exchanges, or the metric `δ`.

Category-(b) candidate from §110 of the Knill survey. "Cyclic" is encoded as a
single full `nᵈ`-cycle (`σ.IsCycle ∧ σ.support = univ`), and `0 < d` is required
(for `d = 0` no non-identity cycle exists).
-/

open MeasureTheory
open scoped ENNReal

instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- The standard `d`-dimensional torus `𝕋^d = (ℝ/ℤ)^d`. -/
abbrev Torus (d : ℕ) : Type := Fin d → AddCircle (1 : ℝ)

/-- The group of measurable, invertible, volume-preserving transformations of
the `d`-torus. -/
structure VolumePreservingEquiv (d : ℕ) where
  toMeasurableEquiv : Torus d ≃ᵐ Torus d
  measurePreserving :
    MeasurePreserving toMeasurableEquiv (volume : Measure (Torus d)) volume


/-- Knill's metric `δ`: the essential supremum of the pointwise torus-distance
`d(T x, S x)`. -/
noncomputable def deltaDist {d : ℕ} (T S : VolumePreservingEquiv d) : ℝ≥0∞ :=
  essSup (fun x => edist (T.toMeasurableEquiv x) (S.toMeasurableEquiv x)) (volume : Measure (Torus d))

/-- A **toral dynamical system**: a volume-preserving homeomorphism of `𝕋^d`. -/
structure ToralDynamicalSystem (d : ℕ) where
  toHomeomorph : Torus d ≃ₜ Torus d
  measurePreserving :
    MeasurePreserving toHomeomorph (volume : Measure (Torus d)) volume

/-- A toral dynamical system as an element of `𝒳`. -/
noncomputable def ToralDynamicalSystem.toVolumePreservingEquiv {d : ℕ}
    (T : ToralDynamicalSystem d) : VolumePreservingEquiv d where
  toMeasurableEquiv := T.toHomeomorph.toMeasurableEquiv
  measurePreserving := T.measurePreserving

/-- The half-open cube `cube n k ⊆ 𝕋^d` for `k : Fin d → Fin n`. -/
def cube (n : ℕ) {d : ℕ} (k : Fin d → Fin n) : Set (Torus d) :=
  { x | ∀ i, ∃ r : ℝ, (k i : ℝ) / n ≤ r ∧ r < ((k i : ℝ) + 1) / n ∧
        x i = ((r : ℝ) : AddCircle (1 : ℝ)) }

/-- The axis-`i` shift carrying cube `k` onto cube `σ k`. -/
noncomputable def cubeShift (n : ℕ) {d : ℕ}
    (σ : Equiv.Perm (Fin d → Fin n))
    (k : Fin d → Fin n) (i : Fin d) : AddCircle (1 : ℝ) :=
  ((((((σ k) i : ℤ) - (k i : ℤ) : ℝ) / (n : ℝ)) : ℝ) : AddCircle (1 : ℝ))

/-- A **cyclic cube exchange**: a single full `nᵈ`-cycle `σ` acting on each
cube `k` by the rigid translation carrying it to cube `σ k`. -/
def IsCyclicCubeExchange {d : ℕ} (T : VolumePreservingEquiv d) (n : ℕ) : Prop :=
  0 < n ∧ ∃ σ : Equiv.Perm (Fin d → Fin n),
    σ.IsCycle ∧ σ.support = Finset.univ ∧
    ∀ k : Fin d → Fin n, ∀ x ∈ cube n k, ∀ i,
      T.toMeasurableEquiv x i = x i + cubeShift n σ k i

/- **Lax's approximation theorem.** Every toral dynamical system on `𝕋^d`
(`d ≥ 1`) is approximated arbitrarily well in the metric `δ` by cyclic cube
exchange transformations. -/
/-- Source: P. D. Lax, *Approximation of measure preserving transformations*, Comm. Pure Appl. Math. 24 (1971). Knill, *Some fundamental theorems in mathematics*, §110. Via leanprover/lean-eval@38361be, problem `lax_approximation`. -/
public theorem_wanted lax_approximation {d : ℕ} (hd : 0 < d) (T : ToralDynamicalSystem d)
    {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ (n : ℕ) (S : VolumePreservingEquiv d),
      IsCyclicCubeExchange S n ∧ deltaDist T.toVolumePreservingEquiv S < ε

end Dynamics.LaxApproximation

end MathlibExt.Dynamics.LaxApproximationWanted
