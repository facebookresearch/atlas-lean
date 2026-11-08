/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A proof of the Erdős–Faber–Lovász conjecture

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.ErdosFaberLovaszConjecture` — annals_erdos_faber_lovasz_conjecture (manifest `manifests/problems/annals_erdos_faber_lovasz_conjecture.toml`, rev 1, submitter David Ledvinka, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.ErdosFaberLovaszConjectureWanted` namespace. Mathematical
statements are unchanged. Source: D. Y. Kang, T. Kelly, D. Kühn, A. Methuku, and D. Osthus, `A proof of the Erdős–Faber–Lovász conjecture`, Annals of Math, 198 (2) 2023. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2023-198-2-ErdosFaberLovaszConjecture.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Data.Set.Card
public import Mathlib.Order.Filter.AtTopBot.Defs

@[expose] public section

namespace MathlibExt.Combinatorics.ErdosFaberLovaszConjectureWanted
/-!
# Main Statement from A proof of the Erdős–Faber–Lovász conjecture

We formalise the statement of the main result from D. Y. Kang, T. Kelly, D. Kühn, A. Methuku, and
D. Osthus, `A proof of the Erdős–Faber–Lovász conjecture`, Annals of Math, 198 (2) 2023.
-/

set_option autoImplicit false

namespace ErdosFaberLovaszConjecture

open Filter

variable {V : Type*}

/-- We define a `Hypergraph` on a type of vertices `V` to be a set of sets of `V`
(an edge of a `Hypergraph` is a subset of `V`). -/
abbrev Hypergraph (V : Type*) := Set (Set V)

/-- An `α`-coloring of a hypergraph `𝓗` is a map from the edges of `𝓗` (its elements)
to `α`, such that any two distinct edges which share a vertex are mapped to distinct colors. -/
structure Hypergraph.Coloring (α : Type*) (𝓗 : Hypergraph V) where
  /-- The labeling of a hypergraph coloring. -/
  labels : 𝓗 → α
  isColoring (e₁ e₂ : 𝓗) (h : e₁ ≠ e₂) (h' : (e₁ ∩ e₂ : Set V).Nonempty) : labels e₁ ≠ labels e₂

/-- We say that a hypergraph `𝓗` is linear if any two distinct edges share at most one vertex. -/
def Hypergraph.IsLinear (𝓗 : Hypergraph V) :=
  𝓗.Pairwise fun e₁ e₂ ↦ (e₁ ∩ e₂).Subsingleton

/-- We define the chromatic index of a hypergraph `𝓗` to be the smallest natural number `n` such
that there exists a `(Fin n)`-coloring of `𝓗` (a coloring using `n` colors). -/
noncomputable def Hypergraph.chromaticIndex (𝓗 : Hypergraph V) : ℕ :=
  sInf {n : ℕ | Nonempty (𝓗.Coloring (Fin n))}

/--
Statement of Theorem 1.1:

For sufficiently large `n : ℕ`, every linear hypergraph on `n` vertices has chromatic index
at most `n`.
Source: D. Y. Kang, T. Kelly, D. Kühn, A. Methuku, and D. Osthus, `A proof of the Erdős–Faber–Lovász conjecture`, Annals of Math, 198 (2) 2023. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2023-198-2-ErdosFaberLovaszConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_erdos_faber_lovasz_conjecture`.
-/
public theorem_wanted theorem_1_1 :
    ∀ᶠ n in atTop, ∀ 𝓗 : Hypergraph (Fin n), 𝓗.IsLinear → 𝓗.chromaticIndex ≤ n

end ErdosFaberLovaszConjecture

end MathlibExt.Combinatorics.ErdosFaberLovaszConjectureWanted
