/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Portions of this file are adapted from:

`LeanEval/Analysis/WignerSemicircle.lean` (leanprover/lean-eval):
the definition of `wignerMatrix` at commit 38361be884302c7edce1908c4aef8296eb2cb27e.
Copyright 2026 Lean FRO, LLC.
Licensed under the Apache License, Version 2.0 (https://www.apache.org/licenses/LICENSE-2.0).
Authors: Kim Morrison
ATLAS placed the definition in its present namespace and documented it.
-/

module

public import Mathlib.Basic.Complex.Basic
public import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Wigner matrices

`wignerMatrix` reflects an upper-triangular real array across the diagonal.
The resulting complex matrix is Hermitian.
-/

@[expose] public section

namespace MathlibExt.Analysis.WignerSemicircleWanted.Analysis.WignerSemicircleProblem

set_option linter.dupNamespace false in
/-- **Wigner matrix.** Let $X_{ij} : \Omega \to \mathbb{R}$, for $i, j \in \mathbb{N}$, be real
functions on a set $\Omega$. For $n \in \mathbb{N}$ and $\omega \in \Omega$, the Wigner matrix
$W_n(\omega)$ is the $n \times n$ complex matrix, with rows and columns indexed by
$\{0, \dots, n - 1\}$, whose entry at $(i, j)$ is the real number
$X_{\min(i, j)\, \max(i, j)}(\omega)$. Only the $X_{ij}$ with $i \le j$ are used, and the matrix
is real symmetric. -/
noncomputable def wignerMatrix {Ω : Type*} (X : ℕ → ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ((X (min (i : ℕ) j) (max (i : ℕ) j) ω : ℝ) : ℂ)

set_option linter.dupNamespace false in
/-- **Wigner matrices are Hermitian.** For every family of real functions
$X_{ij} : \Omega \to \mathbb{R}$, $i, j \in \mathbb{N}$, on a set $\Omega$, every $n \in \mathbb{N}$
and every $\omega \in \Omega$, the Wigner matrix $W_n(\omega)$ is Hermitian.

The matrix is in fact real symmetric: its entry at $(i, j)$ is the real number
$X_{\min(i, j)\, \max(i, j)}(\omega)$, and $\min$ and $\max$ are symmetric in their arguments. -/
lemma wignerMatrix_isHermitian {Ω : Type*} (X : ℕ → ℕ → Ω → ℝ) (n : ℕ)
    (ω : Ω) : (wignerMatrix X n ω).IsHermitian := by
  ext i j
  simp [wignerMatrix, Matrix.conjTranspose_apply, Complex.conj_ofReal,
    min_comm (i : ℕ) j, max_comm (i : ℕ) j]

end MathlibExt.Analysis.WignerSemicircleWanted.Analysis.WignerSemicircleProblem
