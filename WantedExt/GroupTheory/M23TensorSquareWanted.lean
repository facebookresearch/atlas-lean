/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Existence of a simple group of order 10200960 with a 22-dim irrep whose tensor square has 4 isotypic components

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.RepresentationTheory.M23TensorSquare` — m23_irrep_tensor_square_decomp (manifest `manifests/problems/m23_irrep_tensor_square_decomp.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.GroupTheory.M23TensorSquareWanted` namespace. Mathematical
statements are unchanged. Source: É. Mathieu, Sur les fonctions cinq fois transitives de 24 quantités, J. Math. Pures Appl. (1873); ATLAS of Finite Groups, M₂₃ character table.
-/
module


public import Batteries.Util.ProofWanted
public import Mathlib.RepresentationTheory.Character
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.Basic.Complex.Basic
public import Mathlib.RingTheory.SimpleModule.Isotypic

@[expose] public section

namespace MathlibExt.GroupTheory.M23TensorSquareWanted
namespace RepresentationTheory

open scoped TensorProduct

/-!
Existential tensor-square problem for the Mathieu group `M₂₃`.

We assert the existence of a finite group `G` of order `|M₂₃| = 10 200 960`,
together with a `22`-dimensional irreducible complex representation `V`,
such that the tensor square `V ⊗ V` (with the diagonal `G`-action) decomposes
into exactly `4` isotypic components.

Mathematical witness. Take `G = M₂₃` acting on the deleted permutation
representation of its 4-transitive action on 23 points. Let `V` be the
corresponding 22-dimensional irreducible. Then
* `Sym² V` is the permutation representation on the `(23 choose 2) = 253`
  unordered pairs, decomposing as `1 ⊕ V ⊕ W` where `W` is a 230-dimensional
  irreducible.
* `Λ² V` is irreducible of dimension `231` (one of the three 231-dim irreps).

So `V ⊗ V = 1 ⊕ V ⊕ W ⊕ Λ²V` has exactly four pairwise non-isomorphic
irreducible summands.

Mathlib does not yet construct `M₂₃` directly, so any solution must build the
group from scratch (e.g. as a subgroup of `S₂₃` via generators of the Steiner
system `S(4,7,23)`, or from the automorphism group of an extended ternary Golay
code, etc.).

This statement was corrected on 2026-06-27. An earlier version omitted the
`IsSimpleGroup G` hypothesis and constrained `G` only by its order. That version
did *not* pin down `M₂₃`: Lorenzo Luccioli, using Harmonic's Aristotle, found a
clever solution that never builds `M₂₃` at all, exploiting that every quantity in
the conclusion is multiplicative under external tensor product. Taking
`G = SL(2, 𝔽₃) × (C₂₃ ⋊ C₁₁) × C₁₆₈₀` — a *solvable* group of order
`24 · 253 · 1680 = 10 200 960` — and `V` the external tensor product of a 2-,
11-, and 1-dimensional irreducible yields `dim V = 2 · 11 · 1 = 22` and a
tensor-square isotypic count of `2 · 2 · 1 = 4`, satisfying the old existential
with none of the intended `M₂₃` content. Our thanks to Lorenzo and Aristotle for
the disproof.

The repair adds `IsSimpleGroup G`. A nontrivial direct product is never simple,
so every such decomposable witness is excluded; and by the classification of
finite simple groups the unique simple group of order `10 200 960` is `M₂₃`, so
the statement now genuinely requires constructing `M₂₃` and studying its
representation theory.

The `G`-action is carried by a `Representation ℂ G V`. The diagonal action on
the tensor square is `ρ.tprod ρ` (`(ρ.tprod ρ) g = TensorProduct.map (ρ g) (ρ g)`),
which is pinned directly rather than relying on a constraint typeclass
resolution would not respect. (An earlier version bound a bare
`Module (MonoidAlgebra ℂ G) (V ⊗[ℂ] V)` witness and tried to pin it to the
diagonal action via the equation `g • (v ⊗ w) = (g • v) ⊗ (g • w)`; but the `•`
on `V ⊗[ℂ] V` resolves to `TensorProduct.leftModule`, the left-factor action,
not the bound witness, so that conjunct forces a trivial action and the whole
statement is vacuously false.)

The tensor-square module instance is supplied explicitly via `Module.compHom`
from `ρ.tprod ρ` on the carrier `V ⊗[ℂ] V`. This avoids both the
`TensorProduct.leftModule` ambiguity above and the `AddCommMonoid`/`AddCommGroup`
diamond in `Representation.asModule` (which would otherwise force a
`set_option backward.isDefEq.respectTransparency false`, a modifier the workspace
extractor does not carry onto the generated `Challenge.lean`).
-/

/-- **Four isotypic components in a tensor square for a simple group of order 10200960.** There
exist a finite simple group $G$ of order $10200960$ and an irreducible complex representation
$\rho$ of $G$ on a vector space $V$ of dimension $22$ such that the tensor square $V \otimes V$,
regarded as a module over the group algebra $\mathbb{C}[G]$ through the diagonal action
$g \mapsto \rho(g) \otimes \rho(g)$, has exactly $4$ isotypic components.

Source: É. Mathieu, Sur les fonctions cinq fois transitives de 24 quantités, J. Math. Pures Appl. (1873); ATLAS of Finite Groups, M₂₃ character table. Via leanprover/lean-eval@38361be, problem `m23_irrep_tensor_square_decomp`. -/
public theorem_wanted m23_irrep_tensor_square_decomp :
    ∃ (G : Type) (_ : Group G) (_ : Fintype G),
      Fintype.card G = 10200960 ∧
      IsSimpleGroup G ∧
      ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (ρ : Representation ℂ G V),
        Module.finrank ℂ V = 22 ∧
        ρ.IsIrreducible ∧
        (@isotypicComponents (MonoidAlgebra ℂ G) (V ⊗[ℂ] V) _ _
          (Module.compHom (V ⊗[ℂ] V)
            (Representation.asAlgebraHom (ρ.tprod ρ)).toRingHom)).ncard = 4

end RepresentationTheory

end MathlibExt.GroupTheory.M23TensorSquareWanted
