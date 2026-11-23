/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.LinearAlgebra.UnitaryGroup
public import Mathlib.LinearAlgebra.Matrix.PosDef
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Complex.Order
import MathlibExt.LinearAlgebra.Matrix.Factorizations.Polar

/-!
# Polar decomposition of invertible real and complex matrices

This file specializes the bundled `RCLike` polar decomposition to real orthogonal and complex
unitary matrices.
-/

@[expose] public section

open scoped ComplexOrder

namespace MathlibExt.LinearAlgebra.Matrix.PolarDecompositionGLWanted

variable {n : Type*} [Fintype n] [DecidableEq n]

/--
**Polar decomposition of invertible real matrices.** Let $A$ be a real square matrix with rows
and columns indexed by a finite set, and suppose $\det A \ne 0$. Then there are an orthogonal
matrix $O$ and a positive-definite symmetric matrix $S$ with $A = OS$, and they are unique: if
$O'$ is orthogonal, $S'$ is positive-definite symmetric and $A = O'S'$, then $O' = O$ and
$S' = S$.

Proof: take $S$ to be the positive-definite square root of $A^{\mathsf{T}} A$ and $O = AS^{-1}$,
the construction in Wikipedia, "Polar decomposition".

Proves `Wanted` entry `polar_decomposition_gl_real`.

Sources: Mathlib `docs/undergrad.yaml`, Bilinear and Quadratic Forms Over a Vector Space /
Endomorphisms / polar decompositions in GL(n, ℝ); R. A. Horn and C. R. Johnson, Matrix Analysis,
2nd ed., Cambridge University Press (2013), Theorem 7.3.1.
-/
theorem polar_decomposition_gl_real (A : Matrix n n ℝ) (hA : IsUnit A.det) :
    ∃ O S : Matrix n n ℝ,
      O ∈ Matrix.orthogonalGroup n ℝ ∧ S.PosDef ∧ A = O * S ∧
        ∀ O' S' : Matrix n n ℝ,
          O' ∈ Matrix.orthogonalGroup n ℝ → S'.PosDef → A = O' * S' → O' = O ∧ S' = S := by
  obtain ⟨U, P, hP, hdecomp, huniq⟩ :=
    Matrix.exists_unique_unitaryGroup_posDef_of_isUnit_det A hA
  refine ⟨U, P, U.property, hP, hdecomp, ?_⟩
  intro O' S' hO' hS' hdecomp'
  obtain ⟨hO, hS⟩ := huniq ⟨O', hO'⟩ S' hS' hdecomp'
  exact ⟨congrArg Subtype.val hO, hS⟩

/--
**Polar decomposition of invertible complex matrices.** Let $A$ be a complex square matrix with
rows and columns indexed by a finite set, and suppose $\det A \ne 0$. Then there are a unitary
matrix $U$ and a positive-definite Hermitian matrix $P$ with $A = UP$, and they are unique: if
$U'$ is unitary, $P'$ is positive-definite Hermitian and $A = U'P'$, then $U' = U$ and $P' = P$.

Proof: take $P$ to be the positive-definite square root of $A^* A$ and $U = AP^{-1}$, the
construction in Wikipedia, "Polar decomposition".

Proves `Wanted` entry `polar_decomposition_gl_complex`.

Sources: Mathlib `docs/undergrad.yaml`, Bilinear and Quadratic Forms Over a Vector Space /
Endomorphisms / polar decompositions in GL(n, ℂ); R. A. Horn and C. R. Johnson, Matrix Analysis,
2nd ed., Cambridge University Press (2013), Theorem 7.3.1.
-/
theorem polar_decomposition_gl_complex (A : Matrix n n ℂ) (hA : IsUnit A.det) :
    ∃ U P : Matrix n n ℂ,
      U ∈ Matrix.unitaryGroup n ℂ ∧ P.PosDef ∧ A = U * P ∧
        ∀ U' P' : Matrix n n ℂ,
          U' ∈ Matrix.unitaryGroup n ℂ → P'.PosDef → A = U' * P' → U' = U ∧ P' = P := by
  obtain ⟨V, Q, hQ, hdecomp, huniq⟩ :=
    Matrix.exists_unique_unitaryGroup_posDef_of_isUnit_det (n := n) (𝕜 := ℂ) A hA
  refine ⟨V, Q, V.property, hQ, hdecomp, ?_⟩
  intro U' P' hU' hP' hdecomp'
  obtain ⟨hU, hP⟩ := huniq ⟨U', hU'⟩ P' hP' hdecomp'
  exact ⟨congrArg Subtype.val hU, hP⟩

end MathlibExt.LinearAlgebra.Matrix.PolarDecompositionGLWanted
