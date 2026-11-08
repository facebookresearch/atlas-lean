/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Pseudorandom sets in Grassmann graph have near-perfect expansion

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.Combinatorics.PseudorandomGrassmann` — annals_pseudorandom_grassmann (manifest `manifests/problems/annals_pseudorandom_grassmann.toml`, rev 1, submitter Justus Springer, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.Combinatorics.PseudorandomGrassmannWanted` namespace. Mathematical
statements are unchanged. Source: S. Khot, D. Minzer, and M. Safra, `Pseudorandom sets in Grassmann graph have near-perfect expansion`, Annals of Math, 198 (1) 2023. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2023-198-1-PseudorandomGrassmann.lean
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Combinatorics.SimpleGraph.Density
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.SetLike.Fintype
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.Order.Filter.AtTopBot.Defs

@[expose] public section

namespace MathlibExt.Combinatorics.PseudorandomGrassmannWanted
/-!
# Main Statement from Pseudorandom sets in Grassmann graph have near-perfect expansion

We formalise the statement of the main result from S. Khot, D. Minzer, and M. Safra,
`Pseudorandom sets in Grassmann graph have near-perfect expansion`, Annals of Math, 198 (1) 2023.
-/

set_option autoImplicit false

namespace PseudorandomGrassmann

open Module Finset Filter

local notation "𝔽₂" => ZMod 2

/-- The vertex type of the Grassmann graph `Grₖₗ`: the `ℓ`-dimensional subspaces of `𝔽₂ᵏ`. -/
abbrev GrVertex (k ℓ : ℕ) : Type :=
  {L : Submodule 𝔽₂ (Fin k → 𝔽₂) // finrank 𝔽₂ L = ℓ}

/-- The Grassmann graph `Grₖₗ`: vertices are `ℓ`-dimensional subspaces of `𝔽₂ᵏ`,
and two subspaces are adjacent when their intersection has dimension `ℓ - 1`. -/
def Gr (k ℓ : ℕ) : SimpleGraph (GrVertex k ℓ) :=
  .fromRel (fun L L' ↦ finrank 𝔽₂ (L.val ⊓ L'.val :) = ℓ - 1)

open Classical in
/-- The subset of vertices `Grₖₗ[A,B] = {L | A ⊆ L ⊆ B}`, where `A, B ⊆ 𝔽₂ᵏ` are subspaces.
See page 13 of the paper. -/
noncomputable def SubGr (k ℓ : ℕ) (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) : Finset (GrVertex k ℓ) :=
  {L | A ≤ L ∧ L ≤ B}

open Classical in
/-- Definition 1.8 from the paper: Let `G = (V,E)` be an `n`-vertex, `d`-regular graph.
For a non-empty set of vertices `S ⊆ V` with `|S| ≤ n/2`, its (edge-)expansion is defined
as `Φ(S) = |E(S,S̄)| / (d·|S|)`, where `E(S,S̄)` denotes the set of edges with one endpoint
in S and the other in `S̄ = V\S`.
In Lean, we don't require the conditions `d`-regular and `|S| ≤ n/2` for this definition.
However, we need `S` nonempty to define the degree `d` as the degree of an arbitrary element
of `S`. Note that this only gives the correct definition for regular graphs. -/
noncomputable def Φ {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (h : S.Nonempty) : ℚ :=
  #(G.interedges S Sᶜ) / (G.degree h.choose * #S)

open Classical in
/--
Statement of Theorem 1.12:

For every constant `0 < α < 1`, there exist a constant `ε > 0` and an
integer `r ≥ 0` such that for all sufficiently large integers `ℓ` and (after fixing it)
for all sufficiently large integers `k`, the following holds. Let `S ⊆ Grₖₗ` be such that
`Φ(S) ≤ α`. Then there exist subspaces `A ⊆ B ⊆ 𝔽₂ᵏ` such that `dim(A) = a`, `codim(B) = b`,
`a + b ≤ r` and `|S ∩ Grₖₗ[A,B]| / |Grₖₗ[A,B]| ≥ ε`.
Source: S. Khot, D. Minzer, and M. Safra, `Pseudorandom sets in Grassmann graph have near-perfect expansion`, Annals of Math, 198 (1) 2023. Statement taken from https://github.com/ImperialCollegeLondon/AnnalsChallenge (v1.0.0, e32eb14), AnnalsChallenge/AnnalsOfMathematics/2023-198-1-PseudorandomGrassmann.lean Via leanprover/lean-eval@38361be, problem `annals_pseudorandom_grassmann`.
-/
public theorem_wanted theorem_1_12 (α : ℝ) (hα : α ∈ Set.Ioo 0 1) :
    ∃ ε > 0, ∃ r, ∀ᶠ (ℓ : ℕ) (k : ℕ) in atTop, ∀ S : Finset (GrVertex k ℓ),
      (hS : S.Nonempty) → 2 * #S ≤ Fintype.card (GrVertex k ℓ) →
        Φ (Gr k ℓ) S hS ≤ α → ∃ (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)), A ≤ B ∧
          letI a := finrank 𝔽₂ A; letI b := k - finrank 𝔽₂ B
          a + b ≤ r ∧ #(S ∩ SubGr k ℓ A B) / #(SubGr k ℓ A B) ≥ (ε : ℝ)

end PseudorandomGrassmann

end MathlibExt.Combinatorics.PseudorandomGrassmannWanted
