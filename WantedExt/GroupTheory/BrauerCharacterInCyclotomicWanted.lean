/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Character values of finite groups lie in cyclotomic fields

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.RepresentationTheory.BrauerCharacterInCyclotomic` — brauer_character_in_cyclotomic (manifest `manifests/problems/brauer_character_in_cyclotomic.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.GroupTheory.BrauerCharacterInCyclotomicWanted` namespace. Mathematical
statements are unchanged. Source: R. Brauer, On the representation of a group of order g in the field of g-th roots of unity, Amer. J. Math. 67 (1945).
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.RepresentationTheory.Character
public import Mathlib.NumberTheory.Cyclotomic.Basic

@[expose] public section

namespace MathlibExt.GroupTheory.BrauerCharacterInCyclotomicWanted
namespace RepresentationTheory

/-!
Brauer's theorem on character values.

For a finite group `G` of exponent `n`, every value of every complex
character of `G` lies in (the image of) the cyclotomic field `ℚ(ζₙ)`.
Concretely: there is a ring embedding `φ : ℚ(ζₙ) →+* ℂ` whose range
contains `tr ρ(g)` for every finite-dimensional complex representation
`ρ` of `G` and every `g ∈ G`.

This is a consequence of Brauer's induction theorem (every character is a
ℤ-combination of characters induced from elementary subgroups, whose values
are visibly cyclotomic).

The full Brauer "splitting field" theorem says more — that `ℚ(ζₙ)` is in fact
a *splitting field* for the group algebra, i.e. every irreducible complex
representation admits a `ℚ(ζₙ)`-form. The character-value statement below
is implied by the splitting-field statement and is the part most cleanly
expressible in Mathlib's current API; the full splitting-field statement
would additionally require scalar-extension scaffolding around
`CyclotomicField n ℚ → ℂ`.
-/

/-- Source: R. Brauer, On the representation of a group of order g in the field of g-th roots of unity, Amer. J. Math. 67 (1945). Via leanprover/lean-eval@38361be, problem `brauer_character_in_cyclotomic`. -/
public theorem_wanted brauer_character_in_cyclotomic
    (G : Type) [Group G] [Fintype G] :
    ∃ φ : CyclotomicField (Monoid.exponent G) ℚ →+* ℂ,
      ∀ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
        (ρ : Representation ℂ G V) (g : G),
        LinearMap.trace ℂ V (ρ g) ∈ φ.range

end RepresentationTheory

end MathlibExt.GroupTheory.BrauerCharacterInCyclotomicWanted
