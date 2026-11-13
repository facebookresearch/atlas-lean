/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Existence of a 779247-dim irreducible e₈-representation with 40 tensor-square isotypic components, Existence of a 64-dim irreducible g₂-representation with 14 tensor-square isotypic components

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.RepresentationTheory.ExceptionalLieTensorSquare` — e8_irrep_tensor_square_decomp (manifest `manifests/problems/e8_irrep_tensor_square_decomp.toml`, rev 1, submitter Kim Morrison, status active); g2_irrep_tensor_square_decomp (manifest `manifests/problems/g2_irrep_tensor_square_decomp.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.GroupTheory.ExceptionalLieTensorSquareWanted` namespace. Mathematical
statements are unchanged. Source: Classical: representation theory of the exceptional Lie algebra e₈. Classical: representation theory of the exceptional Lie algebra g₂.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib

@[expose] public section

namespace MathlibExt.GroupTheory.ExceptionalLieTensorSquareWanted
namespace RepresentationTheory

open scoped TensorProduct

/-!
Existential tensor-square problems for irreducible representations of g₂ and e₈
defined by the Serre construction.

For each of the exceptional Lie algebras g₂ and e₈ over ℂ, we ask only for the
existence of an irreducible representation `V` of a specified dimension whose
tensor square has a specified number of isotypic components (counted as
distinct isomorphism classes of irreducible Lie submodules):

* g₂: dim V = 64,     `V ⊗ V` has 14 isotypic components
* e₈: dim V = 779247, `V ⊗ V` has 40 isotypic components

In the intended solution, one exhibits `V` as the highest-weight
representation `ω₁ + ω_n` (the sum of the first and last fundamental weights,
in Bourbaki labelling):

* g₂: highest weight `ω₁ + ω₂`
* e₈: highest weight `ω₁ + ω₈`

Mathlib does not yet package the highest-weight classification needed to state
those descriptions directly, so they serve here as mathematical guidance for
constructing a witness rather than as part of the formal theorem statement.

Mathlib's `isotypicComponents` is defined for modules over a ring. To use it on
a Lie module `M`, we transport the action through the universal enveloping
algebra: a `LieModule R L M` extends to a
`Module (UniversalEnvelopingAlgebra R L) M` via the universal property.
-/

scoped instance lieModuleToEnvelopingModule
    (R L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
    [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M] :
    Module (UniversalEnvelopingAlgebra R L) M :=
  Module.compHom M
    (UniversalEnvelopingAlgebra.lift R (LieModule.toEnd R L M)).toRingHom

/-- **Tensor square of an irreducible $\mathfrak{g}_2$-representation of dimension $64$.**
There exist a complex vector space $V$ and a representation of the exceptional Lie algebra
$\mathfrak{g}_2$ over $\mathbb{C}$ on $V$ such that $V$ has dimension $64$ over $\mathbb{C}$,
$V$ is irreducible, and the tensor square $V \otimes_{\mathbb{C}} V$, with the representation
$x \cdot (v \otimes w) = (x \cdot v) \otimes w + v \otimes (x \cdot w)$ viewed as a module over the
universal enveloping algebra of $\mathfrak{g}_2$, has exactly $14$ isotypic components.

Source: Classical: representation theory of the exceptional Lie algebra g₂. Via leanprover/lean-eval@38361be, problem `g2_irrep_tensor_square_decomp`. -/
public theorem_wanted g2_irrep_tensor_square_decomp :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
      (_ : LieRingModule (LieAlgebra.g₂ ℂ) V) (_ : LieModule ℂ (LieAlgebra.g₂ ℂ) V),
      Module.finrank ℂ V = 64 ∧
      LieModule.IsIrreducible ℂ (LieAlgebra.g₂ ℂ) V ∧
      (isotypicComponents (UniversalEnvelopingAlgebra ℂ (LieAlgebra.g₂ ℂ))
        (V ⊗[ℂ] V)).ncard = 14

/-- **Tensor square of an irreducible $\mathfrak{e}_8$-representation of dimension $779247$.**
There exist a complex vector space $V$ and a representation of the exceptional Lie algebra
$\mathfrak{e}_8$ over $\mathbb{C}$ on $V$ such that $V$ has dimension $779247$ over $\mathbb{C}$,
$V$ is irreducible, and the tensor square $V \otimes_{\mathbb{C}} V$, with the representation
$x \cdot (v \otimes w) = (x \cdot v) \otimes w + v \otimes (x \cdot w)$ viewed as a module over the
universal enveloping algebra of $\mathfrak{e}_8$, has exactly $40$ isotypic components.

Source: Classical: representation theory of the exceptional Lie algebra e₈. Via leanprover/lean-eval@38361be, problem `e8_irrep_tensor_square_decomp`. -/
public theorem_wanted e8_irrep_tensor_square_decomp :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V)
      (_ : LieRingModule (LieAlgebra.e₈ ℂ) V) (_ : LieModule ℂ (LieAlgebra.e₈ ℂ) V),
      Module.finrank ℂ V = 779247 ∧
      LieModule.IsIrreducible ℂ (LieAlgebra.e₈ ℂ) V ∧
      (isotypicComponents (UniversalEnvelopingAlgebra ℂ (LieAlgebra.e₈ ℂ))
        (V ⊗[ℂ] V)).ncard = 40

end RepresentationTheory

end MathlibExt.GroupTheory.ExceptionalLieTensorSquareWanted
