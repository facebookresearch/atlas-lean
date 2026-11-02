/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Brauer's splitting field theorem

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.RepresentationTheory.BrauerSplittingField` — brauer_splitting_field (manifest `manifests/problems/brauer_splitting_field.toml`, rev 1, submitter Kim Morrison, status archived) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.GroupTheory.BrauerSplittingFieldWanted` namespace. Mathematical
statements are unchanged. Source: R. Brauer, On the representation of a group of order g in the field of g-th roots of unity, Amer. J. Math. 67 (1945), 461–471.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.RepresentationTheory.Character
public import Mathlib.NumberTheory.Cyclotomic.Basic
public import Mathlib.FieldTheory.SplittingField.Construction

@[expose] public section

namespace MathlibExt.GroupTheory.BrauerSplittingFieldWanted
namespace RepresentationTheory

open scoped TensorProduct

/-!
Brauer's splitting field theorem.

For a finite group `G` of exponent `n`, every finite-dimensional complex
representation of `G` descends to `ℚ(ζₙ)`. Concretely: there is a ring
embedding `φ : CyclotomicField n ℚ →+* ℂ`, a `ℚ(ζₙ)`-representation
`(W, σ)` of `G`, and a `ℂ`-linear, `G`-equivariant isomorphism
`ℂ ⊗[ℚ(ζₙ)] W ≃ V`, where ℂ is regarded as a `ℚ(ζₙ)`-algebra via `φ`.

Brauer (1945) proved this using his induction theorem.

The weaker "character values lie in `φ.range`" statement
(`brauer_character_in_cyclotomic`) is a corollary, and is in fact
elementary: `ρ g ^ n = 1` makes `ρ g` diagonalisable with `n`-th-root-of-
unity eigenvalues, so its trace is already a sum of `n`-th roots of unity.
The descent statement here is the deep content (Schur index 1 over
`ℚ(ζₙ)` for every irreducible complex representation of `G`).
-/

/-- **Brauer's splitting field theorem.** Let $G$ be a finite group of exponent $n$, let
$K = \mathbb{Q}(\zeta_n)$ be the $n$-th cyclotomic field, and let $\rho$ be a representation of
$G$ on a finite-dimensional complex vector space $V$. Then there are a ring homomorphism
$\varphi \colon K \to \mathbb{C}$, a $K$-vector space $W$ with a representation $\sigma$ of $G$
on $W$, and a $\mathbb{C}$-linear isomorphism $f \colon \mathbb{C} \otimes_K W \to V$, where
$\mathbb{C}$ is regarded as a $K$-algebra via $\varphi$, such that
$f((\mathrm{id}_{\mathbb{C}} \otimes \sigma(g))(x)) = \rho(g)(f(x))$ for all $g \in G$ and all
$x \in \mathbb{C} \otimes_K W$.

Source: R. Brauer, On the representation of a group of order g in the field of g-th roots of unity, Amer. J. Math. 67 (1945), 461–471. Via leanprover/lean-eval@38361be, problem `brauer_splitting_field`. -/
public theorem_wanted brauer_splitting_field
    (G : Type) [Group G] [Fintype G]
    (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) :
    ∃ (φ : CyclotomicField (Monoid.exponent G) ℚ →+* ℂ)
      (W : Type) (_ : AddCommGroup W)
      (_ : Module (CyclotomicField (Monoid.exponent G) ℚ) W)
      (σ : Representation (CyclotomicField (Monoid.exponent G) ℚ) G W),
      letI : Algebra (CyclotomicField (Monoid.exponent G) ℚ) ℂ := φ.toAlgebra
      ∃ (f : (ℂ ⊗[CyclotomicField (Monoid.exponent G) ℚ] W) ≃ₗ[ℂ] V),
        ∀ (g : G) (x : ℂ ⊗[CyclotomicField (Monoid.exponent G) ℚ] W),
          f ((σ g).baseChange ℂ x) = ρ g (f x)

end RepresentationTheory

end MathlibExt.GroupTheory.BrauerSplittingFieldWanted
