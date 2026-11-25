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

public import Mathlib.Analysis.InnerProductSpace.SingularValues
public import Mathlib.Analysis.InnerProductSpace.Spectrum
public import Mathlib.Analysis.InnerProductSpace.Symmetric
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Data.Multiset.Defs
public import Mathlib.Data.List.Sort
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.FinRange

/-!
# Scalar multiplication and ordered spectral values

These results describe the actual adjoint-square, ordered real eigenvalues, and
singular values of finite-dimensional real or complex Hilbert-space linear maps.
Nonnegative real factors preserve the descending eigenvalue order, while an
arbitrary real or complex scalar multiplies every singular value by its norm.

Source and target universes and dimensions are independent. The theorems retain
zero scalars and zero-dimensional spaces and require no explicit completeness
hypothesis beyond the original finite-dimensional RCLike inner-product structure.
-/

@[expose] public section

universe uK uE uF

variable {𝕜 : Type uK} [RCLike 𝕜]

open Matrix LinearMap Polynomial
open scoped InnerProductSpace ComplexConjugate

namespace LinearMap

/-- Multiplying a rectangular linear map by `c : 𝕜` multiplies its adjoint-square
by the real scalar `‖c‖²`, embedded in the scalar field `𝕜`. The finite-dimensional RCLike inner-product
spaces have independent universes; no explicit completeness or nonzero-map premise
is required. In particular, `c = 0` and zero-dimensional source/target spaces are
included. -/
theorem adjoint_smul_comp_self (c : 𝕜) {E : Type uE} {F : Type uF} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] (f : E →ₗ[𝕜] F) :
    adjoint (c • f) ∘ₗ (c • f) = ((‖c‖ ^ 2 : ℝ) : 𝕜) • (adjoint f ∘ₗ f) := by
  let r : 𝕜 := ((‖c‖ ^ 2 : ℝ) : 𝕜)
  have h_conj_mul : c * conj c = r := by
    simpa only [r, RCLike.ofReal_pow] using (RCLike.mul_conj c)
  have h_adj : adjoint (c • f) = (conj c) • adjoint f := by
    change adjoint (c • f) = (starRingEnd 𝕜 c) • adjoint f
    exact LinearEquiv.map_smulₛₗ
      (LinearMap.adjoint : (E →ₗ[𝕜] F) ≃ₗ⋆[𝕜] (F →ₗ[𝕜] E)) c f
  calc adjoint (c • f) ∘ₗ (c • f)
      = (conj c • adjoint f) ∘ₗ (c • f) := by rw [h_adj]
    _ = r • (adjoint f ∘ₗ f) := by
      ext x
      simp only [LinearMap.coe_comp, Function.comp_apply,
        LinearMap.smul_apply, map_smul, smul_smul, h_conj_mul]

/-- A nonnegative real multiple of a symmetric RCLike linear endomorphism
has the correspondingly scaled descending eigenvalue list, with multiplicities.
`m` is the dimension over `𝕜` and `j : Fin m` indexes the same ordered list.
The hypothesis `0 ≤ r` is essential for preserving that order; it includes `r = 0`.
No nonzero eigenvalue, positive dimension or explicit completeness assumption is
added. -/
theorem IsSymmetric.eigenvalues_smul_nonneg {E : Type uE} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E]
    [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E} (hT : T.IsSymmetric) (r : ℝ) (hr : 0 ≤ r)
    (m : ℕ) (hm : Module.finrank 𝕜 E = m) (j : Fin m) :
    let rC : 𝕜 := (r : 𝕜)
    let U : E →ₗ[𝕜] E := rC • T
    have hU : U.IsSymmetric := hT.smul (RCLike.conj_ofReal r)
    hU.eigenvalues hm j = r * hT.eigenvalues hm j := by
  intro rC U hU
  let b := hT.eigenvectorBasis hm
  have hTmat0 : T.toMatrix b.toBasis b.toBasis =
      Matrix.diagonal (RCLike.ofReal ∘ hT.eigenvalues hm) :=
    IsSymmetric.toMatrix_eigenvectorBasis hT hm
  have hRCLike_eq : (RCLike.ofReal ∘ hT.eigenvalues hm : Fin m → 𝕜) =
      fun i => (hT.eigenvalues hm i : 𝕜) := rfl
  have hTmat : T.toMatrix b.toBasis b.toBasis =
      Matrix.diagonal (fun i => (hT.eigenvalues hm i : 𝕜)) := by
    rw [hTmat0, hRCLike_eq]
  have hUeq : U.toMatrix b.toBasis b.toBasis =
      rC • T.toMatrix b.toBasis b.toBasis := by
    have h := (LinearMap.toMatrix b.toBasis b.toBasis :
      (E →ₗ[𝕜] E) ≃ₗ[𝕜] Matrix (Fin m) (Fin m) 𝕜).map_smul rC T
    calc U.toMatrix b.toBasis b.toBasis
        = (rC • T).toMatrix b.toBasis b.toBasis := rfl
      _ = rC • T.toMatrix b.toBasis b.toBasis := h
  have hInner : rC • (fun i => (hT.eigenvalues hm i : 𝕜)) =
      fun i => ((r * hT.eigenvalues hm i : ℝ) : 𝕜) := by
    ext i
    simp only [rC, Pi.smul_apply, smul_eq_mul, RCLike.ofReal_mul]
  have hUmat : U.toMatrix b.toBasis b.toBasis =
      Matrix.diagonal (fun i => ((r * hT.eigenvalues hm i : ℝ) : 𝕜)) := by
    calc U.toMatrix b.toBasis b.toBasis
        = rC • Matrix.diagonal (fun i => (hT.eigenvalues hm i : 𝕜)) := by
          rw [hUeq, hTmat]
      _ = Matrix.diagonal (rC • fun i => (hT.eigenvalues hm i : 𝕜)) := by
          rw [Matrix.diagonal_smul]
      _ = _ := by rw [hInner]
  have hC1 : U.charpoly = Finset.univ.prod fun i : Fin m =>
      (X - C ((hU.eigenvalues hm i : 𝕜)) : 𝕜[X]) := hU.charpoly_eq hm
  have hC2 : U.charpoly = Finset.univ.prod fun i : Fin m =>
      (X - C (((r * hT.eigenvalues hm i : ℝ) : 𝕜)) : 𝕜[X]) := by
    calc U.charpoly = (U.toMatrix b.toBasis b.toBasis).charpoly := by
          rw [LinearMap.charpoly_toMatrix]
      _ = (Matrix.diagonal
          (fun i => ((r * hT.eigenvalues hm i : ℝ) : 𝕜))).charpoly := by
          rw [hUmat]
      _ = _ := by rw [Matrix.charpoly_diagonal]
  have hP :
      Finset.univ.prod
          (fun i : Fin m => (X - C ((hU.eigenvalues hm i : 𝕜)) : 𝕜[X])) =
        Finset.univ.prod fun i : Fin m =>
          (X - C (((r * hT.eigenvalues hm i : ℝ) : 𝕜)) : 𝕜[X]) := by
    rw [← hC1, ← hC2]
  have hR1 :
      (Finset.univ.prod fun i : Fin m =>
          (X - C ((hU.eigenvalues hm i : 𝕜)) : 𝕜[X])).roots =
        (Finset.univ.val.map fun i : Fin m =>
          (hU.eigenvalues hm i : 𝕜)) := by
    have heq :
        Finset.univ.prod
            (fun i : Fin m => (X - C ((hU.eigenvalues hm i : 𝕜)) : 𝕜[X])) =
          ((Finset.univ.val.map fun i : Fin m =>
              (hU.eigenvalues hm i : 𝕜)).map fun a => X - C a).prod := by
      rw [Finset.prod_eq_multiset_prod, Multiset.map_map]; rfl
    rw [heq, Polynomial.roots_multiset_prod_X_sub_C]
  have hR2 :
      (Finset.univ.prod fun i : Fin m =>
          (X - C (((r * hT.eigenvalues hm i : ℝ) : 𝕜)) : 𝕜[X])).roots =
        (Finset.univ.val.map fun i : Fin m =>
          ((r * hT.eigenvalues hm i : ℝ) : 𝕜)) := by
    have heq :
        Finset.univ.prod (fun i : Fin m =>
            (X - C (((r * hT.eigenvalues hm i : ℝ) : 𝕜)) : 𝕜[X])) =
          ((Finset.univ.val.map fun i : Fin m =>
              ((r * hT.eigenvalues hm i : ℝ) : 𝕜)).map
            fun a => X - C a).prod := by
      rw [Finset.prod_eq_multiset_prod, Multiset.map_map]; rfl
    rw [heq, Polynomial.roots_multiset_prod_X_sub_C]
  have hRoots :
      (Finset.univ.val.map fun i : Fin m =>
          (hU.eigenvalues hm i : 𝕜) : Multiset 𝕜) =
        (Finset.univ.val.map fun i : Fin m =>
          ((r * hT.eigenvalues hm i : ℝ) : 𝕜)) := by
    rw [← hR1, ← hR2, hP]
  have hOf :
      (Finset.univ.val.map fun i : Fin m =>
          hU.eigenvalues hm i : Multiset ℝ).map ((↑) : ℝ → 𝕜) =
        (Finset.univ.val.map fun i : Fin m =>
            r * hT.eigenvalues hm i).map ((↑) : ℝ → 𝕜) := by
    have hl :
        (Finset.univ.val.map fun i : Fin m =>
            hU.eigenvalues hm i).map ((↑) : ℝ → 𝕜) =
          Finset.univ.val.map fun i : Fin m =>
            (hU.eigenvalues hm i : 𝕜) := by
      rw [Multiset.map_map]; rfl
    have hr2 :
        (Finset.univ.val.map fun i : Fin m =>
            r * hT.eigenvalues hm i).map ((↑) : ℝ → 𝕜) =
          Finset.univ.val.map fun i : Fin m =>
            ((r * hT.eigenvalues hm i : ℝ) : 𝕜) := by
      rw [Multiset.map_map]; rfl
    rw [hl, hr2, hRoots]
  have hRe :
      (Finset.univ.val.map fun i : Fin m =>
          hU.eigenvalues hm i : Multiset ℝ) =
        (Finset.univ.val.map fun i : Fin m =>
          r * hT.eigenvalues hm i) :=
    (Multiset.map_injective RCLike.ofReal_injective) hOf
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

/-- Every singular value of an RCLike scalar multiple of a rectangular linear
map is scaled by `‖c‖`. The statement uses the stock nonnegative descending sequence
`singularValues`, including its zero tail. Source and target may have different
finite dimensions and independent universes. Zero scalars, zero maps and
zero-dimensional spaces are included without an extra hypothesis. -/
theorem singularValues_smul (c : 𝕜) {E : Type uE} {F : Type uF} [NormedAddCommGroup E]
    [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F] (f : E →ₗ[𝕜] F) (i : ℕ) :
    (c • f).singularValues i = ‖c‖ * f.singularValues i := by
  let T := adjoint f ∘ₗ f
  have hT : T.IsSymmetric := f.isSymmetric_adjoint_comp_self
  have hU : adjoint (c • f) ∘ₗ (c • f) = ((‖c‖ ^ 2 : ℝ) : 𝕜) • T :=
    adjoint_smul_comp_self c f
  by_cases hc : c = 0
  · subst hc; simp [zero_smul, singularValues_zero, norm_zero]
  · have hs : 0 ≤ ‖c‖ ^ 2 := sq_nonneg _
    by_cases hi : Module.finrank 𝕜 E ≤ i
    · rw [f.singularValues_of_finrank_le hi,
        (c • f).singularValues_of_finrank_le hi, mul_zero]
    · have hi' : i < Module.finrank 𝕜 E := Nat.not_le.mp hi
      let m := Module.finrank 𝕜 E
      have hm : Module.finrank 𝕜 E = m := rfl
      have hE : f.singularValues i =
          Real.sqrt (hT.eigenvalues hm ⟨i, hi'⟩) := by
        rw [f.singularValues_of_lt hm hi']
      let rC : 𝕜 := ((‖c‖ ^ 2 : ℝ) : 𝕜)
      have hTr : (rC • T).IsSymmetric := hT.smul (RCLike.conj_ofReal _)
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
        IsSymmetric.eigenvalues_smul_nonneg hT _ hs m hm ⟨i, hi'⟩
      have hU' : (c • f).singularValues i =
          Real.sqrt ((‖c‖ ^ 2) * hT.eigenvalues hm ⟨i, hi'⟩) := by
        rw [hF, hEq, hSmul]
      rw [hE, hU', Real.sqrt_mul hs, Real.sqrt_sq (norm_nonneg _)]

end LinearMap
