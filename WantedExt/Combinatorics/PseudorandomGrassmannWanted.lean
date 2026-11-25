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

/-- **Vertices of the Grassmann graph.** For natural numbers $k$ and $\ell$, the vertices of the
Grassmann graph $\mathrm{Gr}(k, \ell)$ are the $\ell$-dimensional linear subspaces of
$\mathbb{F}_2^k$. -/
abbrev GrVertex (k ℓ : ℕ) : Type :=
  {L : Submodule 𝔽₂ (Fin k → 𝔽₂) // finrank 𝔽₂ L = ℓ}

/-- **Grassmann graph over $\mathbb{F}_2$.** For natural numbers $k$ and $\ell$, the Grassmann
graph $\mathrm{Gr}(k, \ell)$ has as vertices the $\ell$-dimensional linear subspaces of
$\mathbb{F}_2^k$, and two distinct such subspaces $L$ and $L'$ are adjacent when
$\dim(L \cap L') = \ell - 1$. -/
def Gr (k ℓ : ℕ) : SimpleGraph (GrVertex k ℓ) :=
  .fromRel (fun L L' ↦ finrank 𝔽₂ (L.val ⊓ L'.val :) = ℓ - 1)

open Classical in
/-- **Grassmann vertices between two subspaces.** For natural numbers $k$ and $\ell$ and linear
subspaces $A$ and $B$ of $\mathbb{F}_2^k$, $\mathrm{Gr}(k, \ell)[A, B]$ is the finite set of
vertices $L$ of the Grassmann graph $\mathrm{Gr}(k, \ell)$, that is of $\ell$-dimensional
subspaces of $\mathbb{F}_2^k$, with $A \subseteq L \subseteq B$. If $A \not\subseteq B$ the set
is empty.

This is the set $\mathrm{Gr}_{k,\ell}[A, B]$ on page 13 of Khot, Minzer and Safra, Pseudorandom
sets in Grassmann graph have near-perfect expansion. -/
noncomputable def SubGr (k ℓ : ℕ) (A B : Submodule 𝔽₂ (Fin k → 𝔽₂)) : Finset (GrVertex k ℓ) :=
  {L | A ≤ L ∧ L ≤ B}

open Classical in
/-- **Edge expansion of a vertex set.** Let $G$ be a simple graph on a finite vertex set $V$ and
let $S \subseteq V$ be nonempty. Let $d$ be the degree in $G$ of a fixed vertex of $S$, chosen
once for each $S$. The expansion of $S$ is the rational number
$\Phi_G(S) = |E(S, V \setminus S)| / (d \cdot |S|)$, where $E(S, V \setminus S)$ is the set of
edges of $G$ with one endpoint in $S$ and the other in $V \setminus S$; it is $0$ when $d = 0$.

For a $d$-regular graph, $d$ is the common degree and this is Definition 1.8 of Khot, Minzer and
Safra, which also asks that $|S| \le |V|/2$; neither regularity nor that bound is assumed here.
-/
noncomputable def Φ {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) (h : S.Nonempty) : ℚ :=
  #(G.interedges S Sᶜ) / (G.degree h.choose * #S)

open Classical in
/--
**Non-expanding sets in the Grassmann graph (Khot–Minzer–Safra).** For every real $\alpha$
with $0 < \alpha < 1$ there are a real $\varepsilon > 0$ and a natural number $r$ such that for
all sufficiently large natural numbers $\ell$ and, for each such $\ell$, all sufficiently large
natural numbers $k$, the following holds. For subspaces $A$ and $B$ of $\mathbb{F}_2^k$, let
$\mathrm{Gr}(k, \ell)[A, B]$ be the set of vertices $L$ of the Grassmann graph
$\mathrm{Gr}(k, \ell)$ with $A \subseteq L \subseteq B$. Let $S$ be a nonempty set of at most
half of the vertices of $\mathrm{Gr}(k, \ell)$ whose edge expansion in $\mathrm{Gr}(k, \ell)$
satisfies $\Phi(S) \le \alpha$. Then there are subspaces $A \subseteq B$ of $\mathbb{F}_2^k$
such that the dimension of $A$ plus the codimension $k - \dim B$ of $B$ is at most $r$ and
$|S \cap \mathrm{Gr}(k, \ell)[A, B]| / |\mathrm{Gr}(k, \ell)[A, B]| \ge \varepsilon$.

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
