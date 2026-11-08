/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# No bounded projection from L^1 onto H^1

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Analysis.HardySpace` — H1_not_closedComplemented (manifest `manifests/problems/H1_not_closedComplemented.toml`, rev 1, submitter Yongxi Lin, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Analysis.HardySpaceWanted` namespace. Mathematical
statements are unchanged. Source: D. J. Newman, 'The nonexistence of projections from L^1 to H^1', Proc. Amer. Math. Soc.; W. Rudin, Fourier Analysis on Groups; Yongxi Lin, Hardy Space and Hartogs Triangle, Theorem 2.8.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Analysis.Fourier.AddCircle
public import Mathlib.MeasureTheory.Function.L1Space.Integrable
public import Mathlib.Topology.Algebra.Module.Complement

@[expose] public section

namespace MathlibExt.Analysis.HardySpaceWanted
namespace Analysis

/-!
# Nonexistence of bounded projections from `L^1` onto `H^1`

The Hardy space `H^1` consists of those `L^1` functions on the unit circle whose
negative Fourier coefficients vanish. D. J. Newman showed that there is no bounded
linear projection from `L^1` onto `H^1`. The theorem below phrases the result
using `Submodule.ClosedComplemented`.
-/

open MeasureTheory Submodule

/-- The boundary Hardy space `H^1`: those `L^1` functions whose negative Fourier
coefficients vanish. -/
def H1 : Submodule ℂ (Lp ℂ 1 (AddCircle.haarAddCircle (T := 1))) where
  carrier := {f | ∀ n : ℤ, n < 0 → fourierCoeff f n = 0}
  zero_mem' := by simp [fourierCoeff]
  add_mem' := by
    intro f g hf hg n hn
    rw [fourierCoeff_congr_ae (Lp.coeFn_add f g),
      fourierCoeff.add (L1.integrable_coeFn f) (L1.integrable_coeFn g)]
    simp_all
  smul_mem' := by
    intro c f n hn
    rw [fourierCoeff_congr_ae (Lp.coeFn_smul c f), fourierCoeff.const_smul]
    simp_all

/- There is no bounded projection from `L^1` onto `H^1`. In the language of
topological vector spaces, `H^1` has no topological complement in `L^1`. -/
/-- Source: D. J. Newman, 'The nonexistence of projections from L^1 to H^1', Proc. Amer. Math. Soc.; W. Rudin, Fourier Analysis on Groups; Yongxi Lin, Hardy Space and Hartogs Triangle, Theorem 2.8. Via leanprover/lean-eval@38361be, problem `H1_not_closedComplemented`. -/
public theorem_wanted H1_not_closedComplemented :
    ¬ H1.ClosedComplemented

end Analysis

end MathlibExt.Analysis.HardySpaceWanted
