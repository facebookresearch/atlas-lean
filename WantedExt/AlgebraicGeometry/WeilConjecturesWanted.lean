/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Weil conjectures in terms of point counts

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
38361be884302c7edce1908c4aef8296eb2cb27e, module `LeanEval.AlgebraicGeometry.WeilConjectures` — weil_conjectures (manifest `manifests/problems/weil_conjectures.toml`, rev 1, submitter Junyan Xu, status active) —
distributed under the Apache License, Version 2.0. lean-eval ships no
`NOTICE` file. Changes made: converted each `@[eval_problem]` theorem
into a Batteries `theorem_wanted` (data/instance holes into
`def_wanted`), replaced `EvalTools.Markers` with
`Batteries.Util.ProofWanted`, inlined any `LeanEval` helper modules,
and placed the declarations in the `MathlibExt.AlgebraicGeometry.WeilConjecturesWanted` namespace. Mathematical
statements are unchanged. Source: P. Deligne, 'La conjecture de Weil. I', Publications Mathématiques de l'Institut des Hautes Études Scientifiques, Volume 43, pages 273–307 (1974), https://www.numdam.org/item/PMIHES_1974__43__273_0.pdf. See also references in the Lean file.
-/
module


public import Batteries.Util.ProofWanted
public import Mathlib.AlgebraicGeometry.Scheme
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.Order.Ideal
open AlgebraicGeometry

@[expose] public section

namespace MathlibExt.AlgebraicGeometry.WeilConjecturesWanted
/-!
# Weil conjectures in terms of point counts

References:
* P. Deligne. La conjecture de Weil : I. https://www.numdam.org/item/PMIHES_1974__43__273_0.pdf
* P. Deligne. La Conjecture de Weil : II. https://www.numdam.org/item/PMIHES_1980__52__137_0.pdf
* J.S. Milne. Lectures on Étale Cohomology. https://www.jmilne.org/math/CourseNotes/LEC.pdf
* E. Freitag, R. Kiehl. Étale cohomology and the Weil conjecture.
* N. Katz. L-functions and monodromy: four lectures on Weil II.
  https://doi.org/10.1006/aima.2000.1979 or https://web.math.princeton.edu/~nmk/arizona34.pdf
* K. Kedlaya. Fourier transforms and p-adic "Weil II". https://arxiv.org/abs/math/0210149
-/

open CategoryTheory AlgebraicGeometry

namespace AlgebraicGeometry.WeilConjectures

/- The **Weil conjectures** in terms of point counts: if `X` is a smooth complete
algebraic variety (geometrically irreducible) over a finite field `F` of dimension `d`,
then there exists multisets `Aᵢ` of Frobenius eigenvalues (which are algebraic integers)
such that for the finite extension `E / F` of degree `m`, we have
`#X(E) = ∑_{0 ≤ i ≤ 2d} (-1)ⁱ ∑_{α ∈ Aᵢ} αᵐ` (rationality of the zeta series).
Moreover, the multisets satisfy `A₀ = {1}`, the Poincaré duality (functional equation)
`A_{2d-i} = #Fᵈ / Aᵢ`, the "Riemann hypothesis" `|α| = #F^{i/2}` for all `α ∈ Aᵢ`,
and are invariant under all automorphisms of ℂ.

This statement does not include the identities between sizes of the multisets and
the Betti numbers of a complex variety defined over a number field whose reduction
modulo a prime ideal is `X`.

The Riemann hypothesis was first proved by Deligne while the rest were already established
by Grothendieck (with Artin, Verdier and earlier work of Dwork) using the theory of ℓ-adic
cohomology. -/
/-- **The Weil conjectures.** Let $F$ be a finite field with $q$ elements, and let $X$ be a scheme
over $\operatorname{Spec} F$ whose structure morphism is proper, geometrically irreducible and
smooth of relative dimension $d$. Then there is a sequence $A_0, A_1, A_2, \dots$ of finite
multisets of complex numbers with $A_0 = \{1\}$ such that, for every $0 \le i \le 2d$, the
multiset $A_{2d-i}$ is the image of $A_i$ under $\alpha \mapsto q^d/\alpha$, the multiset $A_i$
is invariant under every field automorphism of $\mathbb{C}$, and every $\alpha \in A_i$ is an
algebraic integer with $|\alpha| = \sqrt{q^i}$. Moreover, for every finite field extension $E$
of $F$ of degree $m$, the number of morphisms $\operatorname{Spec} E \to X$ over
$\operatorname{Spec} F$ equals $\sum_{i=0}^{2d} (-1)^i \sum_{\alpha \in A_i} \alpha^m$, where
the inner sums count multiplicities.

Source: P. Deligne, 'La conjecture de Weil. I', Publications Mathématiques de l'Institut des Hautes Études Scientifiques, Volume 43, pages 273–307 (1974), https://www.numdam.org/item/PMIHES_1974__43__273_0.pdf. See also references in the Lean file. Via leanprover/lean-eval@38361be, problem `weil_conjectures`. -/
public theorem_wanted weil_conjectures (F : Type*) [Finite F] [Field F]
    (X : Over (Spec (.of F))) [GeometricallyIrreducible X.hom] [IsProper X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom] :
    ∃ A : ℕ → Multiset ℂ, A 0 = {1} ∧
      (∀ i ≤ 2 * d, A (2 * d - i) = (A i).map (Nat.card F ^ d / · : ℂ → ℂ) ∧
        (∀ φ : ℂ ≃+* ℂ, (A i).map φ = A i) ∧
        ∀ α ∈ A i, IsIntegral ℤ α ∧ ‖α‖ = √(Nat.card F ^ i)) ∧
      ∀ (E : Type _) [Field E] [Algebra F E] [FiniteDimensional F E],
        Nat.card (.mk (Spec.map <| CommRingCat.ofHom <| algebraMap F E) ⟶ X) =
        ∑ i ∈ Finset.Iic (2 * d), (-1) ^ i * ((A i).map (· ^ Module.finrank F E)).sum

end AlgebraicGeometry.WeilConjectures

end MathlibExt.AlgebraicGeometry.WeilConjecturesWanted
