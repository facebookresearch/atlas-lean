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

/-- **Hypergraph.** A hypergraph on a type $V$ of vertices is a set of subsets of $V$; its elements
are the edges of the hypergraph. Edges may be empty, and no finiteness condition is imposed. -/
abbrev Hypergraph (V : Type*) := Set (Set V)

/-- **Edge coloring of a hypergraph.** Let $\mathcal{H}$ be a hypergraph on a vertex type $V$ and
let $\alpha$ be a type. An $\alpha$-coloring of $\mathcal{H}$ is a map $c$ from the set of edges of
$\mathcal{H}$ to $\alpha$ such that $c(e_1) \ne c(e_2)$ for any two distinct edges $e_1$ and $e_2$
of $\mathcal{H}$ that have a vertex in common. -/
structure Hypergraph.Coloring (α : Type*) (𝓗 : Hypergraph V) where
  /-- The labeling of a hypergraph coloring. -/
  labels : 𝓗 → α
  isColoring (e₁ e₂ : 𝓗) (h : e₁ ≠ e₂) (h' : (e₁ ∩ e₂ : Set V).Nonempty) : labels e₁ ≠ labels e₂

/-- **Linear hypergraph.** A hypergraph $\mathcal{H}$ is linear if any two distinct edges of
$\mathcal{H}$ have at most one vertex in common. -/
def Hypergraph.IsLinear (𝓗 : Hypergraph V) :=
  𝓗.Pairwise fun e₁ e₂ ↦ (e₁ ∩ e₂).Subsingleton

/-- **Chromatic index of a hypergraph.** The chromatic index of a hypergraph $\mathcal{H}$ is the
least natural number $n$ such that $\mathcal{H}$ has a coloring with colors in
$\{0, 1, \dots, n-1\}$, and $0$ if there is no such $n$. -/
noncomputable def Hypergraph.chromaticIndex (𝓗 : Hypergraph V) : ℕ :=
  sInf {n : ℕ | Nonempty (𝓗.Coloring (Fin n))}

/--
**Erdős–Faber–Lovász conjecture for sufficiently many vertices.** For every sufficiently large
natural number $n$, every linear hypergraph on the vertex set $\{0, 1, \dots, n-1\}$ has chromatic
index at most $n$.

Source: D. Y. Kang, T. Kelly, D. Kühn, A. Methuku, and D. Osthus, `A proof of the Erdős–Faber–Lovász conjecture`, Annals of Math, 198 (2) 2023. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2023-198-2-ErdosFaberLovaszConjecture.lean Via leanprover/lean-eval@38361be, problem `annals_erdos_faber_lovasz_conjecture`.
-/
public theorem_wanted theorem_1_1 :
    ∀ᶠ n in atTop, ∀ 𝓗 : Hypergraph (Fin n), 𝓗.IsLinear → 𝓗.chromaticIndex ≤ n

end ErdosFaberLovaszConjecture

end MathlibExt.Combinatorics.ErdosFaberLovaszConjectureWanted
