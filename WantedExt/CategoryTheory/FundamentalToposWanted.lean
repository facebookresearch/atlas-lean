/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Fundamental theorem of topos theory

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.CategoryTheory.FundamentalTopos` — fundamental_topos_theory (manifest `manifests/problems/fundamental_topos_theory.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.CategoryTheory.FundamentalToposWanted` namespace. Mathematical
statements are unchanged. Source: F. W. Lawvere & M. Tierney (elementary topos, 1970); see S. Mac Lane & I. Moerdijk, *Sheaves in Geometry and Logic*, IV.7. Knill, *Some fundamental theorems in mathematics*, §54.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.CategoryTheory.FundamentalToposWanted
namespace ToposTheory

/-!
# The fundamental theorem of topos theory

`fundamental_topos_theory`: the slice category `E/X` of an elementary topos `E`
is again an elementary topos. The trusted helper `IsTopos` (a non-hole) bundles
the four Mathlib classes that make up "elementary topos". Mathlib has finite
limits and cartesian-monoidal structure on `Over X` and a subobject-classifier
class, but neither `MonoidalClosed (Over X)` (the locally-cartesian-closed
upgrade) nor `HasSubobjectClassifier (Over X)` — so no fundamental theorem.

Category-(b) candidate from §54 of the Knill survey.
-/


open _root_.CategoryTheory _root_.CategoryTheory.Limits

/-- **Elementary topos.** A category $E$ is an elementary topos if it has all finite limits, it
admits a cartesian monoidal structure for which it is monoidal closed (that is, $E$ is cartesian
closed), and it has a subobject classifier. -/
def IsTopos (E : Type*) [Category E] : Prop :=
  HasFiniteLimits E ∧
  ∃ cm : CartesianMonoidalCategory E,
    (letI : MonoidalCategory E := cm.toMonoidalCategory
     Nonempty (MonoidalClosed E)) ∧
    HasSubobjectClassifier E

/- **Fundamental theorem of topos theory.** The slice category `E/X` of an
elementary topos `E` is again an elementary topos. -/
/-- **Fundamental theorem of topos theory.** If $E$ is an elementary topos and $X$ is an object
of $E$, then the slice category $E/X$ of objects of $E$ over $X$ is again an elementary topos.

Source: F. W. Lawvere & M. Tierney (elementary topos, 1970); see S. Mac Lane & I. Moerdijk, *Sheaves in Geometry and Logic*, IV.7. Knill, *Some fundamental theorems in mathematics*, §54. Via leanprover/lean-eval@38361be, problem `fundamental_topos_theory`. -/
public theorem_wanted fundamental_topos_theory {E : Type*} [Category E]
    (hE : IsTopos E) (X : E) : IsTopos (Over X)

end ToposTheory

end MathlibExt.CategoryTheory.FundamentalToposWanted
