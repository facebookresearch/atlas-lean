/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# No continuous faithful ℤ_p action on a connected 3-manifold (Pardon 2013)

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Topology.HilbertSmith3D` — hilbert_smith_padic_dimension_three (manifest `manifests/problems/hilbert_smith_padic_dimension_three.toml`, rev 1, submitter Jack McCarthy, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Topology.HilbertSmith3DWanted` namespace. Mathematical
statements are unchanged. Source: John Pardon, 'The Hilbert-Smith conjecture for three-manifolds', Journal of the American Mathematical Society 26 (2013), no. 3, 879-899, Theorem 1.5. https://doi.org/10.1090/S0894-0347-2013-00766-3
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Group.Action.Faithful
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Geometry.Manifold.ChartedSpace
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.MulAction

@[expose] public section

namespace MathlibExt.Topology.HilbertSmith3DWanted
namespace Topology

/-!
# No continuous faithful ℤ_p action on a connected 3-manifold (Pardon 2013)

John Pardon proved that the additive group of `p`-adic integers cannot act
continuously and faithfully on a connected three-dimensional topological
manifold. By the standard reduction of Hilbert–Smith to `p`-adic actions, this
establishes the Hilbert–Smith conjecture in dimension three.

The statement below is Pardon’s Theorem 1.5. The manifold is represented by a
Hausdorff, second-countable charted space modelled on `ℝ³`; no differentiable
structure is assumed.
-/

/- **No continuous faithful `ℤ_p` action on a connected 3-manifold** (Pardon
2013, Theorem 1.5). The additive group of `p`-adic integers cannot act
continuously and faithfully on a connected topological three-manifold.

This is the `p`-adic step, not the full Hilbert–Smith conjecture: deducing that
every locally compact group acting faithfully on a connected three-manifold is
a Lie group additionally requires the classical reduction to `ℤ_p` actions,
which is not part of this statement. -/
/-- **Pardon's theorem: the p-adic integers cannot act faithfully and continuously on a
connected 3-manifold.** Let $p$ be a prime and $M$ a connected, Hausdorff, second-countable
topological space with an atlas of charts modelled on $\mathbb{R}^3$, that is, a connected
topological 3-manifold without boundary. Then there is no faithful action of the additive group
$\mathbb{Z}_p$ of $p$-adic integers on $M$ that is jointly continuous as a map
$\mathbb{Z}_p \times M \to M$.

This is the $p$-adic case of the Hilbert–Smith conjecture in dimension three; deducing that every
locally compact group acting faithfully on a connected 3-manifold is a Lie group also needs the
classical reduction to $\mathbb{Z}_p$-actions, which is not part of this statement.

Source: John Pardon, 'The Hilbert-Smith conjecture for three-manifolds', Journal of the American Mathematical Society 26 (2013), no. 3, 879-899, Theorem 1.5. https://doi.org/10.1090/S0894-0347-2013-00766-3 Via leanprover/lean-eval@38361be, problem `hilbert_smith_padic_dimension_three`. -/
public theorem_wanted hilbert_smith_padic_dimension_three
    (p : ℕ) [Fact p.Prime]
    (M : Type*) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
    [ConnectedSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
    [AddAction (PadicInt p) M] [ContinuousVAdd (PadicInt p) M]
    [FaithfulVAdd (PadicInt p) M] :
    False

end Topology

end MathlibExt.Topology.HilbertSmith3DWanted
