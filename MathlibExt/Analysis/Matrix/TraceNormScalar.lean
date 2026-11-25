/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
  Author: @toskua, Avocado
-/
module

public import MathlibExt.Analysis.Matrix.TraceNorm
public import MathlibExt.Analysis.InnerProductSpace.SingularValuesScalar
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Basic.Complex.Basic
public import Mathlib.Data.Multiset.Defs
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.FinRange

/-!
# Complex scalar homogeneity of trace norm

For every complex scalar `c` and finite square complex matrix `M`, the
trace norm of `cM` is `|c|` times the trace norm of `M`. Applying this to
`M-N` gives the corresponding scaled-difference formula. The singular values
and matrix coordinate maps are the Euclidean ones used in the trace-norm
definition. Zero scalars, zero matrices and an empty finite index type are
included; neither Hermitianity nor invertibility is required.
-/

@[expose] public section
open Matrix LinearMap ComplexConjugate Polynomial
open scoped InnerProductSpace
namespace Matrix
variable {n : Type*} [Fintype n] [DecidableEq n]

private lemma adj_smul_comp (c : ℂ) {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] (f : E →ₗ[ℂ] F) :
    adjoint (c • f) ∘ₗ (c • f) = ((‖c‖ ^ 2 : ℝ) : ℂ) • (adjoint f ∘ₗ f) := by
  exact LinearMap.adjoint_smul_comp_self c f

private lemma eig_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (r : ℝ) (hr : 0 ≤ r)
    (m) (hm : Module.finrank ℂ E = m) (j : Fin m) :
    let rC : ℂ := (r : ℂ)
    let U : E →ₗ[ℂ] E := rC • T
    have hU : U.IsSymmetric := hT.smul (Complex.conj_ofReal r)
    hU.eigenvalues hm j = r * hT.eigenvalues hm j := by
  exact LinearMap.IsSymmetric.eigenvalues_smul_nonneg hT r hr m hm j

private lemma sv_smul (c : ℂ) {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] (f : E →ₗ[ℂ] F) (i : ℕ) :
    (c • f).singularValues i = ‖c‖ * f.singularValues i := by
  exact LinearMap.singularValues_smul c f i

/-- Complex scalar multiplication scales trace norm by the scalar absolute value, including a zero
scalar.

Here `n` is any finite index type with decidable equality. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem singularValueTraceNorm_smul (c : ℂ) (M : Matrix n n ℂ) :
    (c • M).singularValueTraceNorm = ‖c‖ * M.singularValueTraceNorm
``` -/
theorem singularValueTraceNorm_smul (c : ℂ) (M : Matrix n n ℂ) :
    (c • M).singularValueTraceNorm = ‖c‖ * M.singularValueTraceNorm := by
  unfold singularValueTraceNorm
  rw [show toEuclideanLin (c • M) = c • toEuclideanLin M from by
    simp [map_smul]]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [sv_smul]

/-- Negating a finite square complex matrix preserves its trace norm.
The index type is finite with decidable equality, and an empty index type
or zero matrix is included.

```lean
theorem singularValueTraceNorm_neg (M : Matrix n n ℂ) :
    (-M).singularValueTraceNorm = M.singularValueTraceNorm
``` -/
@[simp, nolint simpNF] theorem singularValueTraceNorm_neg (M : Matrix n n ℂ) :
    (-M).singularValueTraceNorm = M.singularValueTraceNorm := by
  have h := singularValueTraceNorm_smul (-1 : ℂ) M
  have h1 : ((-1 : ℂ) • M) = -M := by ext i j; simp
  rw [h1] at h; rw [h]; simp

/-- Scaling both matrices in a difference scales its trace norm by the complex scalar absolute
value.

Here `n` is any finite index type with decidable equality. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem singularValueTraceNorm_smul_sub (c : ℂ) (M N : Matrix n n ℂ) :
    (c • M - c • N).singularValueTraceNorm = ‖c‖ * (M - N).singularValueTraceNorm
``` -/
theorem singularValueTraceNorm_smul_sub (c : ℂ) (M N : Matrix n n ℂ) :
    (c • M - c • N).singularValueTraceNorm = ‖c‖ * (M - N).singularValueTraceNorm := by
  have : c • M - c • N = c • (M - N) := by ext i j; simp; ring
  rw [this, singularValueTraceNorm_smul]

end Matrix
