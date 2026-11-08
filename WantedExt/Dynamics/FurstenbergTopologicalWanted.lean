/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Furstenberg–Weiss topological multiple recurrence (single-transformation form)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Dynamics.FurstenbergTopological` — furstenberg_topological (manifest `manifests/problems/furstenberg_topological.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Dynamics.FurstenbergTopologicalWanted` namespace. Mathematical
statements are unchanged. Source: H. Furstenberg and B. Weiss, *Topological dynamics and combinatorial number theory*, Journal d'Analyse Mathématique 34 (1978), 61-85. Listed as §56 (main theorem) in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.Dynamics.FurstenbergTopologicalWanted
namespace Dynamics

/-!
# Furstenberg–Weiss topological multiple recurrence (single-transformation form)

For every homeomorphism `T` of a nonempty compact metric space `X`,
there is a point `x ∈ X` that is **multiply recurrent**: for every
`d ≥ 1`, the iterates `T, T², …, T^d` of `x` return arbitrarily close
to `x` along a single common time sequence — `T^{j · n_k}(x) → x` as
`k → ∞` for every `j ∈ {1, …, d}`, with a strictly increasing
`n : ℕ → ℕ` shared across `j`.

This is the single-transformation formulation in Knill §56, which
specialises the full Furstenberg–Weiss recurrence theorem to the
family `T, T², …, T^d` instead of arbitrary commuting homeomorphisms.

Compact-Hausdorff alone is insufficient for this sequential
formulation: on the shift over `Ultrafilter ℤ` (compact Hausdorff, not
first-countable), every convergent sequence is eventually constant, so
`T^{j · n_k}(x) → x` along a strictly increasing `n_k` would force
`n_k = 0` eventually. First-countability would suffice as a hypothesis;
the compact-metric form is the standard Furstenberg–Weiss statement.
-/

open Filter Topology

/-- A point `x : X` is **multiply recurrent** for `T : X → X` if for
every `d ≥ 1` there is a strictly increasing `n : ℕ → ℕ` such that
`T^{j · n_k}(x) → x` for every `j ∈ {1, …, d}`. -/
def IsMultiplyRecurrent {X : Type*} [TopologicalSpace X]
    (T : X → X) (x : X) : Prop :=
  ∀ d : ℕ, 1 ≤ d →
    ∃ n : ℕ → ℕ, StrictMono n ∧
      ∀ j : ℕ, 1 ≤ j → j ≤ d →
        Tendsto (fun k : ℕ => T^[j * n k] x) atTop (𝓝 x)

/- **Furstenberg–Weiss topological multiple recurrence** (single-
transformation form). Every homeomorphism `T` of a nonempty compact
metric space `X` has a multiply recurrent point. -/
/-- Source: H. Furstenberg and B. Weiss, *Topological dynamics and combinatorial number theory*, Journal d'Analyse Mathématique 34 (1978), 61-85. Listed as §56 (main theorem) in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Via leanprover/lean-eval@38361be, problem `furstenberg_topological`. -/
public theorem_wanted furstenberg_topological_recurrence {X : Type*} [MetricSpace X]
    [CompactSpace X] [Nonempty X] (T : X ≃ₜ X) :
    ∃ x : X, IsMultiplyRecurrent (T : X → X) x

end Dynamics

end MathlibExt.Dynamics.FurstenbergTopologicalWanted
