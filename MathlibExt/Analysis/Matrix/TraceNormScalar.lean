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
  let r : ℂ := ((‖c‖ ^ 2 : ℝ) : ℂ)
  have h_conj_mul : c * conj c = r := by
    calc c * conj c = (Complex.normSq c : ℂ) := by
            rw [Complex.normSq_eq_conj_mul_self, mul_comm]
         _ = ((‖c‖ ^ 2 : ℝ) : ℂ) := by
            rw [Complex.normSq_eq_norm_sq]
  have h_adj : adjoint (c • f) = (conj c) • adjoint f := by
    ext y
    apply ext_inner_right ℂ
    intro x
    calc ⟪adjoint (c • f) y, x⟫_ℂ = ⟪y, (c • f) x⟫_ℂ := by
            rw [adjoint_inner_left]
         _ = c * ⟪y, f x⟫_ℂ := by
            rw [LinearMap.smul_apply, inner_smul_right]
         _ = c * ⟪adjoint f y, x⟫_ℂ := by
            rw [← adjoint_inner_left]
         _ = conj (conj c) * ⟪adjoint f y, x⟫_ℂ := by
            rw [Complex.conj_conj]
         _ = ⟪(conj c • adjoint f) y, x⟫_ℂ := by
            rw [LinearMap.smul_apply, inner_smul_left]
  calc adjoint (c • f) ∘ₗ (c • f)
      = (conj c • adjoint f) ∘ₗ (c • f) := by rw [h_adj]
    _ = r • (adjoint f ∘ₗ f) := by
      ext x
      simp only [LinearMap.coe_comp, Function.comp_apply,
        LinearMap.smul_apply, map_smul, smul_smul, h_conj_mul]

private lemma eig_smul {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] {T : E →ₗ[ℂ] E} (hT : T.IsSymmetric) (r : ℝ) (hr : 0 ≤ r)
    (m) (hm : Module.finrank ℂ E = m) (j : Fin m) :
    let rC : ℂ := (r : ℂ)
    let U : E →ₗ[ℂ] E := rC • T
    have hU : U.IsSymmetric := hT.smul (Complex.conj_ofReal r)
    hU.eigenvalues hm j = r * hT.eigenvalues hm j := by
  intro rC U hU
  let b := hT.eigenvectorBasis hm
  have hTmat0 : T.toMatrix b.toBasis b.toBasis =
      Matrix.diagonal (RCLike.ofReal ∘ hT.eigenvalues hm) :=
    IsSymmetric.toMatrix_eigenvectorBasis hT hm
  have hRCLike_eq : (RCLike.ofReal ∘ hT.eigenvalues hm : Fin m → ℂ) =
      fun i => (hT.eigenvalues hm i : ℂ) := rfl
  have hTmat : T.toMatrix b.toBasis b.toBasis =
      Matrix.diagonal (fun i => (hT.eigenvalues hm i : ℂ)) := by
    rw [hTmat0, hRCLike_eq]
  have hUeq : U.toMatrix b.toBasis b.toBasis =
      rC • T.toMatrix b.toBasis b.toBasis := by
    have h := (LinearMap.toMatrix b.toBasis b.toBasis :
      (E →ₗ[ℂ] E) ≃ₗ[ℂ] Matrix (Fin m) (Fin m) ℂ).map_smul rC T
    calc U.toMatrix b.toBasis b.toBasis
        = (rC • T).toMatrix b.toBasis b.toBasis := rfl
      _ = rC • T.toMatrix b.toBasis b.toBasis := h
  have hInner : rC • (fun i => (hT.eigenvalues hm i : ℂ)) =
      fun i => ((r * hT.eigenvalues hm i : ℝ) : ℂ) := by
    ext i
    simp only [rC, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul]
  have hUmat : U.toMatrix b.toBasis b.toBasis =
      Matrix.diagonal (fun i => ((r * hT.eigenvalues hm i : ℝ) : ℂ)) := by
    calc U.toMatrix b.toBasis b.toBasis
        = rC • Matrix.diagonal (fun i => (hT.eigenvalues hm i : ℂ)) := by
          rw [hUeq, hTmat]
      _ = Matrix.diagonal (rC • fun i => (hT.eigenvalues hm i : ℂ)) := by
          rw [Matrix.diagonal_smul]
      _ = _ := by rw [hInner]
  have hC1 : U.charpoly = Finset.univ.prod fun i : Fin m =>
      (X - C ((hU.eigenvalues hm i : ℂ)) : ℂ[X]) := hU.charpoly_eq hm
  have hC2 : U.charpoly = Finset.univ.prod fun i : Fin m =>
      (X - C (((r * hT.eigenvalues hm i : ℝ) : ℂ)) : ℂ[X]) := by
    calc U.charpoly = (U.toMatrix b.toBasis b.toBasis).charpoly := by
          rw [LinearMap.charpoly_toMatrix]
      _ = (Matrix.diagonal
          (fun i => ((r * hT.eigenvalues hm i : ℝ) : ℂ))).charpoly := by
          rw [hUmat]
      _ = _ := by rw [Matrix.charpoly_diagonal]
  have hP :
      Finset.univ.prod
          (fun i : Fin m => (X - C ((hU.eigenvalues hm i : ℂ)) : ℂ[X])) =
        Finset.univ.prod fun i : Fin m =>
          (X - C (((r * hT.eigenvalues hm i : ℝ) : ℂ)) : ℂ[X]) := by
    rw [← hC1, ← hC2]
  have hR1 :
      (Finset.univ.prod fun i : Fin m =>
          (X - C ((hU.eigenvalues hm i : ℂ)) : ℂ[X])).roots =
        (Finset.univ.val.map fun i : Fin m =>
          (hU.eigenvalues hm i : ℂ)) := by
    have heq :
        Finset.univ.prod
            (fun i : Fin m => (X - C ((hU.eigenvalues hm i : ℂ)) : ℂ[X])) =
          ((Finset.univ.val.map fun i : Fin m =>
              (hU.eigenvalues hm i : ℂ)).map fun a => X - C a).prod := by
      rw [Finset.prod_eq_multiset_prod, Multiset.map_map]; rfl
    rw [heq, Polynomial.roots_multiset_prod_X_sub_C]
  have hR2 :
      (Finset.univ.prod fun i : Fin m =>
          (X - C (((r * hT.eigenvalues hm i : ℝ) : ℂ)) : ℂ[X])).roots =
        (Finset.univ.val.map fun i : Fin m =>
          ((r * hT.eigenvalues hm i : ℝ) : ℂ)) := by
    have heq :
        Finset.univ.prod (fun i : Fin m =>
            (X - C (((r * hT.eigenvalues hm i : ℝ) : ℂ)) : ℂ[X])) =
          ((Finset.univ.val.map fun i : Fin m =>
              ((r * hT.eigenvalues hm i : ℝ) : ℂ)).map
            fun a => X - C a).prod := by
      rw [Finset.prod_eq_multiset_prod, Multiset.map_map]; rfl
    rw [heq, Polynomial.roots_multiset_prod_X_sub_C]
  have hRoots :
      (Finset.univ.val.map fun i : Fin m =>
          (hU.eigenvalues hm i : ℂ) : Multiset ℂ) =
        (Finset.univ.val.map fun i : Fin m =>
          ((r * hT.eigenvalues hm i : ℝ) : ℂ)) := by
    rw [← hR1, ← hR2, hP]
  have hOf :
      (Finset.univ.val.map fun i : Fin m =>
          hU.eigenvalues hm i : Multiset ℝ).map ((↑) : ℝ → ℂ) =
        (Finset.univ.val.map fun i : Fin m =>
            r * hT.eigenvalues hm i).map ((↑) : ℝ → ℂ) := by
    have hl :
        (Finset.univ.val.map fun i : Fin m =>
            hU.eigenvalues hm i).map ((↑) : ℝ → ℂ) =
          Finset.univ.val.map fun i : Fin m =>
            (hU.eigenvalues hm i : ℂ) := by
      rw [Multiset.map_map]; rfl
    have hr2 :
        (Finset.univ.val.map fun i : Fin m =>
            r * hT.eigenvalues hm i).map ((↑) : ℝ → ℂ) =
          Finset.univ.val.map fun i : Fin m =>
            ((r * hT.eigenvalues hm i : ℝ) : ℂ) := by
      rw [Multiset.map_map]; rfl
    rw [hl, hr2, hRoots]
  have hRe :
      (Finset.univ.val.map fun i : Fin m =>
          hU.eigenvalues hm i : Multiset ℝ) =
        (Finset.univ.val.map fun i : Fin m =>
          r * hT.eigenvalues hm i) :=
    (Multiset.map_injective Complex.ofReal_injective) hOf
  have h_ofFn1 :
      (List.ofFn (hU.eigenvalues hm) : Multiset ℝ) =
        Finset.univ.val.map fun i : Fin m => hU.eigenvalues hm i := by
    calc (List.ofFn (hU.eigenvalues hm) : Multiset ℝ)
        = ↑(List.ofFn (hU.eigenvalues hm)) := rfl
      _ = ↑((List.finRange m).map (hU.eigenvalues hm)) := by
          rw [List.ofFn_eq_map]
      _ = (↑(List.finRange m) : Multiset (Fin m)).map
          (hU.eigenvalues hm) := rfl
      _ = Finset.univ.val.map fun i : Fin m =>
          hU.eigenvalues hm i := by
          rw [← Finset.val_univ_fin]
  have h_ofFn2 :
      (List.ofFn (fun i => r * hT.eigenvalues hm i) : Multiset ℝ) =
        Finset.univ.val.map fun i : Fin m =>
          r * hT.eigenvalues hm i := by
    calc (List.ofFn (fun i => r * hT.eigenvalues hm i) : Multiset ℝ)
        = ↑(List.ofFn (fun i => r * hT.eigenvalues hm i)) := rfl
      _ = ↑((List.finRange m).map
          (fun i => r * hT.eigenvalues hm i)) := by
          rw [List.ofFn_eq_map]
      _ = (↑(List.finRange m) : Multiset (Fin m)).map
          (fun i => r * hT.eigenvalues hm i) := rfl
      _ = Finset.univ.val.map fun i : Fin m =>
          r * hT.eigenvalues hm i := by
          rw [← Finset.val_univ_fin]
  have hPerm : List.Perm (List.ofFn (hU.eigenvalues hm))
      (List.ofFn fun i => r * hT.eigenvalues hm i) := by
    rw [← Multiset.coe_eq_coe]
    calc (List.ofFn (hU.eigenvalues hm) : Multiset ℝ)
        = Finset.univ.val.map _ := h_ofFn1
       _ = Finset.univ.val.map fun i => r * hT.eigenvalues hm i := hRe
       _ = (List.ofFn fun i => r * hT.eigenvalues hm i : Multiset ℝ) :=
          h_ofFn2.symm
  have hs1 : (List.ofFn (hU.eigenvalues hm)).SortedGE := by
    exact (hU.eigenvalues_antitone hm).sortedGE_ofFn
  have hs2 : (List.ofFn fun i => r * hT.eigenvalues hm i).SortedGE := by
    apply Antitone.sortedGE_ofFn
    intro i j hij
    exact mul_le_mul_of_nonneg_left (hT.eigenvalues_antitone hm hij) hr
  have hEqList := hPerm.eq_of_sortedGE hs1 hs2
  have hEqFun : hU.eigenvalues hm = fun i => r * hT.eigenvalues hm i := by
    rw [← List.ofFn_inj]
    exact hEqList
  calc hU.eigenvalues hm j = (fun i => r * hT.eigenvalues hm i) j := by
        rw [hEqFun]
     _ = r * hT.eigenvalues hm j := rfl

private lemma sv_smul (c : ℂ) {E F : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] [FiniteDimensional ℂ F] (f : E →ₗ[ℂ] F) (i : ℕ) :
    (c • f).singularValues i = ‖c‖ * f.singularValues i := by
  let T := adjoint f ∘ₗ f
  have hT : T.IsSymmetric := f.isSymmetric_adjoint_comp_self
  have hU : adjoint (c • f) ∘ₗ (c • f) = ((‖c‖ ^ 2 : ℝ) : ℂ) • T :=
    adj_smul_comp c f
  by_cases hc : c = 0
  · subst hc; simp [zero_smul, singularValues_zero, norm_zero]
  · have hs : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
    by_cases hi : Module.finrank ℂ E ≤ i
    · rw [f.singularValues_of_finrank_le hi,
        (c • f).singularValues_of_finrank_le hi, mul_zero]
    · have hi' : i < Module.finrank ℂ E := Nat.not_le.mp hi
      let m := Module.finrank ℂ E
      have hm : Module.finrank ℂ E = m := rfl
      have hE : f.singularValues i =
          Real.sqrt (hT.eigenvalues hm ⟨i, hi'⟩) := by
        rw [f.singularValues_of_lt hm hi']
      let rC : ℂ := ((‖c‖ ^ 2 : ℝ) : ℂ)
      have hTr : (rC • T).IsSymmetric := hT.smul (Complex.conj_ofReal _)
      have hUs : (adjoint (c • f) ∘ₗ (c • f)).IsSymmetric := by
        rw [hU]; exact hTr
      have hF : (c • f).singularValues i =
          Real.sqrt (hUs.eigenvalues hm ⟨i, hi'⟩) := by
        rw [(c • f).singularValues_of_lt hm hi']
      have hChar :
          (adjoint (c • f) ∘ₗ (c • f)).charpoly = (rC • T).charpoly := by
        rw [hU]
      have hEq : hUs.eigenvalues hm = hTr.eigenvalues hm := by
        rw [IsSymmetric.eigenvalues_eq_eigenvalues_iff _ hm _ hm]
        exact hChar
      have hSmul : hTr.eigenvalues hm ⟨i, hi'⟩ =
          (‖c‖ ^ 2) * hT.eigenvalues hm ⟨i, hi'⟩ :=
        eig_smul hT _ hs m hm ⟨i, hi'⟩
      have hU' : (c • f).singularValues i =
          Real.sqrt ((‖c‖ ^ 2) * hT.eigenvalues hm ⟨i, hi'⟩) := by
        rw [hF, hEq, hSmul]
      rw [hE, hU', Real.sqrt_mul hs, Real.sqrt_sq (norm_nonneg _)]

/-- Complex scalar multiplication scales trace norm by the scalar absolute value, including a zero
scalar.

Here `n` is any finite index type with decidable equality. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceNorm_smul (c : ℂ) (M : Matrix n n ℂ) :
    (c • M).traceNorm = ‖c‖ * M.traceNorm
``` -/
theorem traceNorm_smul (c : ℂ) (M : Matrix n n ℂ) :
    (c • M).traceNorm = ‖c‖ * M.traceNorm := by
  unfold traceNorm
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
theorem traceNorm_neg (M : Matrix n n ℂ) :
    (-M).traceNorm = M.traceNorm
``` -/
@[simp, nolint simpNF] theorem traceNorm_neg (M : Matrix n n ℂ) :
    (-M).traceNorm = M.traceNorm := by
  have h := traceNorm_smul (-1 : ℂ) M
  have h1 : ((-1 : ℂ) • M) = -M := by ext i j; simp
  rw [h1] at h; rw [h]; simp

/-- Scaling both matrices in a difference scales its trace norm by the complex scalar absolute
value.

Here `n` is any finite index type with decidable equality. The matrices are arbitrary square
complex matrices, and the empty-index case is included.

```lean
theorem traceNorm_smul_sub (c : ℂ) (M N : Matrix n n ℂ) :
    (c • M - c • N).traceNorm = ‖c‖ * (M - N).traceNorm
``` -/
theorem traceNorm_smul_sub (c : ℂ) (M N : Matrix n n ℂ) :
    (c • M - c • N).traceNorm = ‖c‖ * (M - N).traceNorm := by
  have : c • M - c • N = c • (M - N) := by ext i j; simp; ring
  rw [this, traceNorm_smul]

end Matrix
