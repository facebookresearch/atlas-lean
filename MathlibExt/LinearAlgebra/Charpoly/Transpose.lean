/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic

/-!
# Characteristic polynomial of the transpose of an endomorphism of a finite free module

For a free module `M` of finite rank over a commutative ring `A` and an `A`-linear map
`f : M → M`, the transpose `Module.Dual.transpose f : ψ ↦ ψ ∘ f` of `f` on the dual
`Hom_A(M, A)` has the same characteristic polynomial as `f`
(`LinearMap.charpoly_dualTranspose`).

## Proof

For a basis `(e_i)` of `M`, the matrix of the transpose in the dual basis `(e_i^∨)` is the
transpose of the matrix of `f` in `(e_i)` (`LinearMap.toMatrix_transpose`); both characteristic
polynomials are those of these matrices (`LinearMap.charpoly_toMatrix`), and a square matrix and
its transpose have the same characteristic polynomial (`Matrix.charpoly_transpose`).

## References

* B. Conrad, *The Shimura construction in weight 2*, appendix to K. A. Ribet and W. A. Stein,
  *Lectures on Serre's conjectures*, IAS/Park City Math. Ser.: §5.3, proof of Lemma 5.17, p. 71
  ("These e_i^* are an A-basis of M^* and we compute matrices over A:
  Mat_{e_i}(f) = Mat_{e_i^*}(f^*)^t").
-/

@[expose] public section

set_option autoImplicit false

namespace LinearMap

/-- **Characteristic polynomial of the transpose of an endomorphism of a finite free module.**
Let $A$ be a commutative ring, $M$ a free $A$-module of finite rank and $f \colon M \to M$ an
$A$-linear map. Let $M^{\vee} = \operatorname{Hom}_A(M, A)$, a free $A$-module of the same rank,
and let $f^{\vee} \colon M^{\vee} \to M^{\vee}$, $\psi \mapsto \psi \circ f$, be the transpose of
$f$ (`Module.Dual.transpose f`). Then $f$ and $f^{\vee}$ have the same characteristic polynomial:
$$\operatorname{char}_A(f^{\vee}) = \operatorname{char}_A(f) \quad \text{in } A[X].$$

Source: B. Conrad, *The Shimura construction in weight 2*, appendix to K. A. Ribet and
W. A. Stein, *Lectures on Serre's conjectures*, §5.3, proof of Lemma 5.17, p. 71. -/
theorem charpoly_dualTranspose {A M : Type*} [CommRing A] [AddCommGroup M] [Module A M]
    [Module.Free A M] [Module.Finite A M] (f : Module.End A M) :
    (Module.Dual.transpose (R := A) f).charpoly = f.charpoly := by
  let b := Module.Free.chooseBasis A M
  rw [← LinearMap.charpoly_toMatrix f b, ← LinearMap.charpoly_toMatrix _ b.dualBasis,
    LinearMap.toMatrix_transpose, Matrix.charpoly_transpose]

end LinearMap

end
