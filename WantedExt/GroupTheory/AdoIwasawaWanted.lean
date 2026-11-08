/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Ado's theorem in characteristic zero, Ado–Iwasawa theorem over an arbitrary field

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.RepresentationTheory.AdoIwasawa` — adoIwasawa (manifest `manifests/problems/adoIwasawa.toml`, rev 1, submitter Kim Morrison, status archived). The companion problem `adoCharZero` from the same module is omitted here because it is already proved as `MathlibExt.Algebra.Lie.LandmarkWanted.ado` —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.GroupTheory.AdoIwasawaWanted` namespace. Mathematical
statements are unchanged. Source: Classical Ado theorem; W. Fulton and J. Harris, Representation Theory: A First Course, Appendix E. See also the Tau Ceti Ado–Iwasawa roadmap, https://github.com/TauCetiProject/TauCetiRoadmap/pull/102. K. Iwasawa, On the representation of Lie algebras, Japanese Journal of Mathematics 19 (1948), 405–426. See also the Tau Ceti Ado–Iwasawa roadmap, https://github.com/TauCetiProject/TauCetiRoadmap/pull/102.
-/
module


public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Lie.Basic
public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Order.RelSeries
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.AdoIwasawaWanted
namespace RepresentationTheory.AdoIwasawa

/-!
# Ado's theorem and the Ado–Iwasawa theorem

This problem asks for a faithful finite-dimensional representation of a
finite-dimensional Lie algebra over an arbitrary field (the Ado–Iwasawa
theorem). The companion characteristic-zero Ado problem from the same
lean-eval module is omitted here because it is already proved in
MathlibExt; only this arbitrary-characteristic entry remains.
-/

universe u v

/-- Endomorphisms carry the commutator Lie bracket used in the representation
targets below. Mathlib exposes this as a local instance, but the workspace
generator carries named same-module dependencies rather than `attribute`
commands, so a named instance is needed in generated challenge workspaces. -/
instance moduleEndLieRing (K : Type u) (V : Type v)
    [Field K] [AddCommGroup V] [Module K V] :
    LieRing (Module.End K V) :=
  LieRing.ofAssociativeRing

variable {K L : Type u} [Field K] [LieRing L] [LieAlgebra K L]


/- **The Ado–Iwasawa theorem.** Every finite-dimensional Lie algebra over an
arbitrary field has a faithful finite-dimensional representation. -/
/-- Source: K. Iwasawa, On the representation of Lie algebras, Japanese Journal of Mathematics 19 (1948), 405–426. See also the Tau Ceti Ado–Iwasawa roadmap, https://github.com/TauCetiProject/TauCetiRoadmap/pull/102. Via leanprover/lean-eval@38361be, problem `adoIwasawa`. -/
public theorem_wanted adoIwasawa [FiniteDimensional K L] :
    ∃ (V : Type u) (_ : AddCommGroup V) (_ : Module K V) (_ : FiniteDimensional K V)
      (ρ : L →ₗ⁅K⁆ Module.End K V), Function.Injective ρ

end RepresentationTheory.AdoIwasawa

end MathlibExt.GroupTheory.AdoIwasawaWanted
