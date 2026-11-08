/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# von Neumann double commutant theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.VonNeumannDoubleCommutant` — vonNeumann_doubleCommutant_tfae (manifest `manifests/problems/vonNeumann_doubleCommutant_tfae.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.VonNeumannDoubleCommutantWanted` namespace. Mathematical
statements are unchanged. Source: J. von Neumann, Zur Algebra der Funktionaloperationen und Theorie der normalen Operatoren, Math. Ann. 102 (1930), 370-427.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.VonNeumannAlgebra.Basic
public import Mathlib.Analysis.InnerProductSpace.WeakOperatorTopology
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM

@[expose] public section

namespace MathlibExt.Analysis.VonNeumannDoubleCommutantWanted
namespace Analysis

/-!
Von Neumann's double commutant theorem.

For a unital *-subalgebra `S` of bounded operators on a complex Hilbert space `H`, the
following are equivalent:

1. `S` equals its double commutant `S''`.
2. `S` is closed in the weak operator topology.
3. `S` is closed in the strong operator topology (in Mathlib, the topology of pointwise
   convergence on continuous linear maps).

The WOT and SOT live on irreducible type copies of `H →L[ℂ] H`, so each closed-ness
condition is stated as the closedness of the image of `S` under the canonical inclusion
into the corresponding type copy.
-/
/-- Source: J. von Neumann, *Zur Algebra der Funktionaloperationen und Theorie der normalen Operatoren*, Math. Ann. 102 (1929) (double commutant theorem). Via leanprover/lean-eval@38361be, problem `vonneumann_double_commutant`. -/
public theorem_wanted vonNeumann_doubleCommutant_tfae
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    List.TFAE
      [ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) = S
      , IsClosed
          (ContinuousLinearMapWOT.ofCLM '' (S : Set (H →L[ℂ] H)))
      , IsClosed
          (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
            (S : Set (H →L[ℂ] H))) ]

end Analysis

end MathlibExt.Analysis.VonNeumannDoubleCommutantWanted
