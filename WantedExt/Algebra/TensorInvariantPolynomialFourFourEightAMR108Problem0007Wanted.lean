/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# A non-constant SL₄ × SL₄ × SL₈-invariant on ℂ⁴ ⊗ ℂ⁴ ⊗ ℂ⁸ (Cooper's question)

J. Delp, D. Hoffoss and J. F. Manning, Problems in Groups, Geometry, and Three-Manifolds (2015),
item 2.2 (D. Cooper): does anyone know of a non-zero polynomial on `U ⊗ V ⊗ W` invariant under
`SL(U) × SL(V) × SL(W)` when `dim U = dim V = 4` and `dim W = 8`?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

@[expose] public section

namespace MathlibExt.Algebra.TensorInvariantPolynomialFourFourEightAMR108Problem0007Wanted

/-!
Source: J. Delp, D. Hoffoss and J. F. Manning, Problems in Groups, Geometry, and Three-Manifolds
(2015), arXiv:1512.04620, item 2.2 (D. Cooper). UnsolvedMath record UM-10900007 (`AMR-108-0007`),
dataset ulamai/UnsolvedMath v1.8.0.

"Non-zero" is read as non-constant (constants are invariant), stated as: the polynomial function
takes two different values. The field is `ℂ`, the setting of the resolving result; polynomials in
the `4 · 4 · 8 = 128` coordinates `T (i, j, k)` of a tensor, with `(A, B, C)` acting by `(A ⊗ B ⊗ C)
T`, and invariance as equality of polynomial functions.
-/

/-- The action of `(A, B, C) ∈ SL₄(ℂ) × SL₄(ℂ) × SL₈(ℂ)` on `ℂ⁴ ⊗ ℂ⁴ ⊗ ℂ⁸`, in the coordinates
`T (i, j, k)` of a tensor: `(A ⊗ B ⊗ C) T`. -/
def tensorAction (A B : Matrix.SpecialLinearGroup (Fin 4) ℂ)
    (C : Matrix.SpecialLinearGroup (Fin 8) ℂ) (T : Fin 4 × Fin 4 × Fin 8 → ℂ) :
    Fin 4 × Fin 4 × Fin 8 → ℂ :=
  fun p => ∑ i, ∑ j, ∑ k, (A : Matrix (Fin 4) (Fin 4) ℂ) p.1 i *
    (B : Matrix (Fin 4) (Fin 4) ℂ) p.2.1 j * (C : Matrix (Fin 8) (Fin 8) ℂ) p.2.2 k * T (i, j, k)

/-- Cooper's question (Delp–Hoffoss–Manning, Problems in Groups, Geometry, and Three-Manifolds,
item 2.2), answered: there is a non-constant polynomial function on `ℂ⁴ ⊗ ℂ⁴ ⊗ ℂ⁸` invariant under
`SL₄(ℂ) × SL₄(ℂ) × SL₈(ℂ)`. -/
def nonconstantInvariantExists : Prop :=
  ∃ P : MvPolynomial (Fin 4 × Fin 4 × Fin 8) ℂ,
    (∀ A B C T, MvPolynomial.eval (tensorAction A B C T) P = MvPolynomial.eval T P) ∧
      ∃ T₁ T₂, MvPolynomial.eval T₁ P ≠ MvPolynomial.eval T₂ P

/--
Resolved true: by Bryan–Reichstein–Van Raamsdonk, Corollary 3.3 (Sato–Kimura), a semisimple group
acting on a space of larger dimension has a non-constant invariant polynomial (`ℂ[V]^G ≠ ℂ`,
Corollary 3.2); `SL₄ × SL₄ × SL₈` has dimension `93 < 128`. Source: J. Delp, D. Hoffoss and J. F.
Manning, Problems in Groups, Geometry, and Three-Manifolds (2015), arXiv:1512.04620, item 2.2 (D.
Cooper); resolution: J. Bryan, Z. Reichstein and M. Van Raamsdonk, Existence of locally maximally
entangled quantum states via geometric invariant theory, Ann. Henri Poincaré 19 (2018),
arXiv:1708.01645 (after M. Sato and T. Kimura, Nagoya Math. J. 65 (1977), §3, Proposition 1),
Corollary 3.3: for a representation V of a semisimple linear algebraic group G with dim V > dim G,
P(V)//G ≠ ∅, and by Corollary 3.2 ((c) ⟺ (d)) this means ℂ[V]^G ≠ ℂ; here G = SL₄ × SL₄ × SL₈ has
dimension 15 + 15 + 63 = 93 < 128 = dim(ℂ⁴ ⊗ ℂ⁴ ⊗ ℂ⁸), https://arxiv.org/abs/1708.01645.
-/
public theorem_wanted nonconstantInvariantExists_holds : nonconstantInvariantExists

end MathlibExt.Algebra.TensorInvariantPolynomialFourFourEightAMR108Problem0007Wanted
