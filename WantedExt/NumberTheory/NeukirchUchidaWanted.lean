/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Neukirch–Uchida theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.NumberTheory.NeukirchUchida` — neukirch_uchida (manifest `manifests/problems/neukirch_uchida.toml`, rev 1, submitter Junyan Xu, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.NumberTheory.NeukirchUchidaWanted` namespace. Mathematical
statements are unchanged. Source: Jürgen Neukirch, Alexander Schmidt, Kay Wingberg. *Cohomology of Number Fields*, Theorem 12.2.1.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.NumberTheory.NumberField.Basic

@[expose] public section

namespace MathlibExt.NumberTheory.NeukirchUchidaWanted
/-!
# The Neukirch–Uchida theorem

Every topological group isomorphism between absolute Galois groups of two number fields is induced
by a unique isomorphism between their separable closures that sends one field to the other.
A foundational result of anabelian geometry.

References:
https://en.wikipedia.org/wiki/Neukirch%E2%80%93Uchida_theorem
Jürgen Neukirch, Alexander Schmidt, Kay Wingberg. *Cohomology of Number Fields*, Theorem 12.2.1.
-/

namespace NumberTheory

/-- **Neukirch–Uchida theorem.** Let $K_1$ and $K_2$ be number fields with separable closures
$\overline{K_1}$ and $\overline{K_2}$, and let
$\varphi \colon \mathrm{Gal}(\overline{K_1}/K_1) \to \mathrm{Gal}(\overline{K_2}/K_2)$ be a group
isomorphism that is a homeomorphism for the Krull topologies. Then there is a unique field
isomorphism $\sigma \colon \overline{K_2} \to \overline{K_1}$ that maps the image of $K_2$ in
$\overline{K_2}$ onto the image of $K_1$ in $\overline{K_1}$ and satisfies
$\varphi(g) = \sigma^{-1} \circ g \circ \sigma$ for every $g \in \mathrm{Gal}(\overline{K_1}/K_1)$.

Source: Jürgen Neukirch, Alexander Schmidt, Kay Wingberg. *Cohomology of Number Fields*, Theorem 12.2.1. Via leanprover/lean-eval@38361be, problem `neukirch_uchida`. -/
public theorem_wanted neukirch_uchida {K₁ K₂ K₁' K₂' : Type*} [Field K₁] [Field K₂] [Field K₁'] [Field K₂']
    [NumberField K₁] [NumberField K₂] [Algebra K₁ K₁'] [Algebra K₂ K₂'] [IsSepClosure K₁ K₁']
    [IsSepClosure K₂ K₂'] (ϕ : Gal(K₁'/K₁) ≃* Gal(K₂'/K₂)) (he : IsHomeomorph ϕ) :
    ∃! σ : K₂' ≃+* K₁', (algebraMap K₂ K₂').range.map σ.toRingHom = (algebraMap K₁ K₁').range ∧
      ∀ g : Gal(K₁'/K₁), ϕ g = σ.trans (g.toRingEquiv.trans σ.symm)

end NumberTheory

end MathlibExt.NumberTheory.NeukirchUchidaWanted
