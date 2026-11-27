/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DeterminantalTangent
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.ToLin
import MathlibExt.LinearAlgebra.Matrix.RankManifold
import Mathlib.Algebra.TrivSqZeroExt.Basic
import Mathlib.Data.Fin.SuccPred
import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.Mul
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Tangent spaces to determinantal varieties

For a field `k`, the tangent space at a matrix `A` of rank exactly `r` to the scheme cut out
by the `(r+1)`-minors consists of those matrices `B` sending the kernel of `A` into its range.
The proof reduces to a diagonal matrix by an explicit rank factorization, transports the
vanishing of minor differentials along it via the dual numbers, and computes both sides
directly in the diagonal case.

## Main results

* `mem_tangent_iff`: `B` lies in `tangent r A` if and only if `B` sends `ker A` into the
  range of `A`.

References:
* Harris, *Algebraic Geometry: A First Course*, Example 14.16 (tangent spaces
  to determinantal varieties).
* Bruns–Vetter, *Determinantal Rings*, Chapter 2,
  https://doi.org/10.1007/BFb0080378.
-/

@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.DeterminantalTangentWanted

open MathlibExt.AlgebraicGeometry.DeterminantalTangent
open MathlibExt.AlgebraicGeometry.AffineTangent
open Matrix
open scoped RightActions Matrix

private theorem eval_minor_eq_zero {K : Type*} [Field K] {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (hA : Matrix.rank A = r)
    (rows : Fin (r + 1) ↪ Fin m) (cols : Fin (r + 1) ↪ Fin n) :
    MvPolynomial.eval (fun ij ↦ A ij.1 ij.2) (minorPolynomial r rows cols) = 0 := by
  rw [eval_minorPolynomial]
  by_contra hne
  have h1 : (A.submatrix rows cols).rank = Fintype.card (Fin (r + 1)) :=
    Matrix.rank_of_det_ne_zero hne
  rw [Fintype.card_fin] at h1
  have hle : (A.submatrix rows cols).rank ≤ Matrix.rank A :=
    Matrix.rank_submatrix_le A rows cols
  rw [hA] at hle
  omega

private theorem mem_tangent_iff_forall {K : Type*} [Field K] {m n r : ℕ}
    (A B : Matrix (Fin m) (Fin n) K) (hA : Matrix.rank A = r) :
    (fun ij ↦ B ij.1 ij.2) ∈ tangent r A ↔
      ∀ (rows : Fin (r + 1) ↪ Fin m) (cols : Fin (r + 1) ↪ Fin n),
        differential (minorPolynomial r rows cols) (fun ij ↦ A ij.1 ij.2)
          (fun ij ↦ B ij.1 ij.2) = 0 := by
  have hp : ∀ f ∈ Set.range (fun p :
      (Fin (r + 1) ↪ Fin m) × (Fin (r + 1) ↪ Fin n) ↦
      minorPolynomial r p.1 p.2),
      MvPolynomial.eval (fun ij ↦ A ij.1 ij.2) f = 0 := by
    intro f hf
    obtain ⟨p, rfl⟩ := hf
    exact eval_minor_eq_zero A hA p.1 p.2
  have ht : tangent r A =
      ⨅ f ∈ Set.range (fun p :
        (Fin (r + 1) ↪ Fin m) × (Fin (r + 1) ↪ Fin n) ↦
        minorPolynomial r p.1 p.2),
        LinearMap.ker (differential f (fun ij ↦ A ij.1 ij.2)) := by
    rw [tangent, minorIdeal, tangentIdeal_span hp]
  rw [ht]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h rows cols
    exact h _ ⟨(rows, cols), rfl⟩
  · intro h f hf
    obtain ⟨p, rfl⟩ := hf
    exact h p.1 p.2

private theorem differential_prod_X {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    {ι : Type*} [DecidableEq ι]
    (e : ι → σ) (s : Finset ι) (p v : σ → K) :
    differential (∏ i ∈ s, MvPolynomial.X (e i) : MvPolynomial σ K) p v =
      ∑ k ∈ s, (∏ i ∈ s \ {k}, p (e i)) * v (e k) := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp
  | @insert a t hat ih =>
    rw [Finset.prod_insert hat, Finset.sum_insert hat]
    have hmul := differential_mul (MvPolynomial.X (e a) : MvPolynomial σ K)
      (∏ i ∈ t, MvPolynomial.X (e i)) p
    have happ := congrArg (fun L : (σ → K) →ₗ[K] K => L v) hmul
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at happ
    rw [happ, ih]
    simp only [MvPolynomial.eval_X]
    have heval : MvPolynomial.eval p (∏ i ∈ t, MvPolynomial.X (e i) : MvPolynomial σ K)
        = ∏ i ∈ t, p (e i) := by
      simp [map_prod]
    rw [heval]
    have hX : differential (MvPolynomial.X (e a) : MvPolynomial σ K) p v = v (e a) := by
      simp
    rw [hX]
    have hsdiff_a : (insert a t \ {a} : Finset ι) = t := by
      have h1 : (insert a t \ {a} : Finset ι) = t \ {a} :=
        Finset.insert_sdiff_of_mem t (Finset.mem_singleton_self a)
      rw [h1, Finset.sdiff_singleton_eq_erase, Finset.erase_eq_of_notMem hat]
    rw [hsdiff_a, add_comm (p (e a) * _ : K) _]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have hak : a ≠ k := fun h => hat (h ▸ hk)
    have hsdiff_k : (insert a t \ {k} : Finset ι) = insert a (t \ {k}) := by
      apply Finset.insert_sdiff_of_notMem
      simp [hak]
    rw [hsdiff_k, Finset.prod_insert]
    · ring
    · simp only [hak, Finset.mem_sdiff, Finset.mem_singleton, not_and, Decidable.not_not]
      intro hmem
      exact hat hmem

private theorem differential_sum {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial σ K) (p : σ → K) :
    differential (∑ i ∈ s, f i) p = ∑ i ∈ s, differential (f i) p := by
  classical
  induction s using Finset.induction with
  | empty =>
    simp [differential_zero]
  | @insert a t hat ih =>
    rw [Finset.sum_insert hat, Finset.sum_insert hat, differential_add, ih]

private theorem differential_C_mul {K : Type*} [Field K] {σ : Type*} [Fintype σ]
    (c : K) (f : MvPolynomial σ K) (p : σ → K) :
    differential (MvPolynomial.C c * f) p = c • differential f p := by
  rw [differential_mul, differential_C]
  simp

/-- Leibniz expansion of the differential of a (not necessarily injective) minor. -/
private def leibnizDiff {K : Type*} [Field K] {m n r : ℕ}
    (F : Fin (r + 1) → Fin m) (G : Fin (r + 1) → Fin n)
    (A B : Matrix (Fin m) (Fin n) K) : K :=
  ∑ σ : Equiv.Perm (Fin (r + 1)),
    ((Equiv.Perm.sign σ : ℤ) : K) *
      ∑ t : Fin (r + 1),
        (∏ i ∈ Finset.univ \ {t}, A (F (σ i)) (G i)) *
          B (F (σ t)) (G t)

private theorem differential_minorFun_apply {K : Type*} [Field K] {m n r : ℕ}
    (F : Fin (r + 1) → Fin m) (G : Fin (r + 1) → Fin n)
    (A B : Matrix (Fin m) (Fin n) K) :
    differential (Matrix.det (Matrix.of fun i j : Fin (r + 1) ↦
        (MvPolynomial.X (F i, G j) : MvPolynomial (Fin m × Fin n) K)))
        (fun ij ↦ A ij.1 ij.2) (fun ij ↦ B ij.1 ij.2) =
      leibnizDiff F G A B := by
  rw [Matrix.det_apply']
  have hcast : ∀ σ : Equiv.Perm (Fin (r + 1)),
      (((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin m × Fin n) K)) =
        MvPolynomial.C (((Equiv.Perm.sign σ : ℤ) : K)) := by
    intro σ
    simp
  simp_rw [hcast]
  rw [differential_sum Finset.univ _ _]
  simp only [differential_C_mul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro σ _
  congr 1
  have hmon : (∏ i : Fin (r + 1),
      (Matrix.of fun i j : Fin (r + 1) ↦
        (MvPolynomial.X (F i, G j) : MvPolynomial (Fin m × Fin n) K)) (σ i) i)
      = ∏ i ∈ Finset.univ, MvPolynomial.X ((fun i ↦ (F (σ i), G i)) i) := by
    rfl
  rw [hmon, differential_prod_X]

private theorem differential_minor_apply {K : Type*} [Field K] {m n r : ℕ}
    (rows : Fin (r + 1) ↪ Fin m) (cols : Fin (r + 1) ↪ Fin n)
    (A B : Matrix (Fin m) (Fin n) K) :
    differential (minorPolynomial r rows cols) (fun ij ↦ A ij.1 ij.2)
        (fun ij ↦ B ij.1 ij.2) =
      leibnizDiff (fun i ↦ rows i) (fun i ↦ cols i) A B := by
  rw [minorPolynomial]
  exact differential_minorFun_apply _ _ _ _

private theorem det_aux_eq_zero_of_row_eq {K : Type*} [Field K] {m n r : ℕ}
    (F : Fin (r + 1) → Fin m) (G : Fin (r + 1) → Fin n)
    {a₁ a₂ : Fin (r + 1)} (h1 : F a₁ = F a₂) (h2 : a₁ ≠ a₂) :
    Matrix.det (Matrix.of fun i j : Fin (r + 1) ↦
      (MvPolynomial.X (F i, G j) : MvPolynomial (Fin m × Fin n) K)) = 0 := by
  apply Matrix.det_eq_zero_of_not_linearIndependent_rows
  intro hli
  have hinj := hli.injective
  apply h2
  apply hinj
  funext j
  change MvPolynomial.X (F a₁, G j) = MvPolynomial.X (F a₂, G j)
  rw [h1]

private theorem det_aux_eq_zero_of_col_eq {K : Type*} [Field K] {m n r : ℕ}
    (F : Fin (r + 1) → Fin m) (G : Fin (r + 1) → Fin n)
    {b₁ b₂ : Fin (r + 1)} (h1 : G b₁ = G b₂) (h2 : b₁ ≠ b₂) :
    Matrix.det (Matrix.of fun i j : Fin (r + 1) ↦
      (MvPolynomial.X (F i, G j) : MvPolynomial (Fin m × Fin n) K)) = 0 := by
  apply Matrix.det_eq_zero_of_not_linearIndependent_cols
  intro hli
  have hinj := hli.injective
  apply h2
  apply hinj
  funext i
  change MvPolynomial.X (F i, G b₁) = MvPolynomial.X (F i, G b₂)
  rw [h1]

private theorem leibnizDiff_eq_zero_of_not_injective_left {K : Type*} [Field K] {m n r : ℕ}
    (F : Fin (r + 1) → Fin m) (G : Fin (r + 1) → Fin n)
    (A B : Matrix (Fin m) (Fin n) K) (hn : ¬ Function.Injective F) :
    leibnizDiff F G A B = 0 := by
  have hw : ∃ a₁ a₂, a₁ ≠ a₂ ∧ F a₁ = F a₂ := by
    by_contra hw
    apply hn
    intro a₁ a₂ heq
    by_contra hne
    exact hw ⟨_, _, hne, heq⟩
  obtain ⟨a₁, a₂, h2, h1⟩ := hw
  rw [← differential_minorFun_apply _ _ _ _,
    det_aux_eq_zero_of_row_eq F G h1 h2, differential_zero]
  rfl

private theorem leibnizDiff_eq_zero_of_not_injective_right {K : Type*} [Field K] {m n r : ℕ}
    (F : Fin (r + 1) → Fin m) (G : Fin (r + 1) → Fin n)
    (A B : Matrix (Fin m) (Fin n) K) (hn : ¬ Function.Injective G) :
    leibnizDiff F G A B = 0 := by
  have hw : ∃ b₁ b₂, b₁ ≠ b₂ ∧ G b₁ = G b₂ := by
    by_contra hw
    apply hn
    intro b₁ b₂ heq
    by_contra hne
    exact hw ⟨_, _, hne, heq⟩
  obtain ⟨b₁, b₂, h2, h1⟩ := hw
  rw [← differential_minorFun_apply _ _ _ _,
    det_aux_eq_zero_of_col_eq F G h1 h2, differential_zero]
  rfl


private theorem tsze_fst_prod {K : Type*} [Field K] {ι : Type*}
    (s : Finset ι) (x : ι → TrivSqZeroExt K K) :
    TrivSqZeroExt.fst (∏ i ∈ s, x i) = ∏ i ∈ s, TrivSqZeroExt.fst (x i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, TrivSqZeroExt.fst_mul, ih]

private theorem tsze_snd_mul {K : Type*} [Field K] (x₁ x₂ : TrivSqZeroExt K K) :
    TrivSqZeroExt.snd (x₁ * x₂) =
      x₁.fst * x₂.snd + x₁.snd * x₂.fst := by
  simp [TrivSqZeroExt.snd_mul]

private theorem tsze_snd_prod {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (x : ι → TrivSqZeroExt K K) :
    TrivSqZeroExt.snd (∏ i ∈ s, x i) =
      ∑ t ∈ s, (∏ i ∈ s \ {t}, TrivSqZeroExt.fst (x i)) * TrivSqZeroExt.snd (x t) := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, tsze_snd_mul, ih, tsze_fst_prod,
      Finset.sum_insert ha]
    have hsdiff_a : (insert a s \ {a} : Finset ι) = s := by
      have h1 : (insert a s \ {a} : Finset ι) = s \ {a} :=
        Finset.insert_sdiff_of_mem s (Finset.mem_singleton_self a)
      rw [h1, Finset.sdiff_singleton_eq_erase, Finset.erase_eq_of_notMem ha]
    rw [hsdiff_a, add_comm ((x a).fst * _ : K) _,
      mul_comm (TrivSqZeroExt.snd (x a)) (∏ i ∈ s, TrivSqZeroExt.fst (x i))]
    congr 1
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t ht
    have hat : a ≠ t := fun h => ha (h ▸ ht)
    have hsdiff_t : (insert a s \ {t} : Finset ι) = insert a (s \ {t}) := by
      apply Finset.insert_sdiff_of_notMem
      simp [hat]
    rw [hsdiff_t, Finset.prod_insert]
    · ring
    · simp only [hat, Finset.mem_sdiff, Finset.mem_singleton, not_and, Decidable.not_not]
      intro hmem
      exact ha hmem

private theorem dual_det_snd {K : Type*} [Field K] {m n r : ℕ}
    (F : Fin (r + 1) → Fin m) (G : Fin (r + 1) → Fin n)
    (M Y : Matrix (Fin m) (Fin n) K) :
    TrivSqZeroExt.snd (Matrix.det (Matrix.of fun a b : Fin (r + 1) ↦
      ((M (F a) (G b), Y (F a) (G b)) : TrivSqZeroExt K K))) =
      leibnizDiff F G M Y := by
  rw [Matrix.det_apply', TrivSqZeroExt.snd_sum]
  apply Finset.sum_congr rfl
  intro σ _
  rw [tsze_snd_mul, TrivSqZeroExt.fst_intCast, TrivSqZeroExt.snd_intCast]
  simp only [zero_mul, add_zero]
  rw [tsze_snd_prod]
  rfl

private theorem det_mul_eq_sum_det_submatrix_mul_prod_tsze {K : Type*} [Field K]
    {r n : ℕ} (A : Matrix (Fin r) (Fin n) (TrivSqZeroExt K K))
    (B : Matrix (Fin n) (Fin r) (TrivSqZeroExt K K)) :
    (A * B).det = ∑ f : Fin r → Fin n, (A.submatrix id f).det * ∏ i, B (f i) i := by
  simp only [Matrix.det_apply, Matrix.mul_apply, Matrix.submatrix_apply, id_eq]
  have key : ∀ σ : Equiv.Perm (Fin r),
      (∏ i, ∑ j, A (σ i) j * B j i)
        = ∑ f : Fin r → Fin n, (∏ i, A (σ i) (f i)) * (∏ i, B (f i) i) := by
    intro σ
    rw [Finset.prod_univ_sum]
    rw [show (Fintype.piFinset (fun _ : Fin r => (Finset.univ : Finset (Fin n))))
          = (Finset.univ : Finset (Fin r → Fin n)) by ext f; simp]
    apply Finset.sum_congr rfl
    intro f _
    rw [Finset.prod_mul_distrib]
  simp only [key]
  simp only [Finset.smul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro σ _
  rw [smul_mul_assoc]

private theorem det_mul_eq_sum_prod_mul_det_submatrix_tsze {K : Type*} [Field K]
    {r n : ℕ} (A : Matrix (Fin r) (Fin n) (TrivSqZeroExt K K))
    (B : Matrix (Fin n) (Fin r) (TrivSqZeroExt K K)) :
    (A * B).det = ∑ f : Fin r → Fin n, (∏ i, A i (f i)) * (B.submatrix f id).det := by
  have h := det_mul_eq_sum_det_submatrix_mul_prod_tsze Bᵀ Aᵀ
  rw [← Matrix.transpose_mul, Matrix.det_transpose] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro f _
  rw [mul_comm]
  congr 1
  rw [← Matrix.det_transpose (B.submatrix f id)]
  congr 1

private theorem minor_mul_left_tsze {K : Type*} [Field K] {m n r : ℕ}
    (A : Matrix (Fin n) (Fin n) (TrivSqZeroExt K K))
    (φ : Matrix (Fin n) (Fin m) (TrivSqZeroExt K K))
    (ρ : Fin r → Fin n) (γ : Fin r → Fin m) :
    ((A * φ).submatrix ρ γ).det
      = ∑ f : Fin r → Fin n, (∏ i, A (ρ i) (f i)) * (φ.submatrix f γ).det := by
  have hsub : (A * φ).submatrix ρ γ = (A.submatrix ρ id) * (φ.submatrix id γ) := by
    have := Matrix.submatrix_mul_equiv A φ ρ (Equiv.refl (Fin n)) γ
    simpa using this.symm
  rw [hsub, det_mul_eq_sum_prod_mul_det_submatrix_tsze]
  apply Finset.sum_congr rfl
  intro f _
  rfl

private theorem minor_mul_right_tsze {K : Type*} [Field K] {m n r : ℕ}
    (φ : Matrix (Fin n) (Fin m) (TrivSqZeroExt K K))
    (B : Matrix (Fin m) (Fin m) (TrivSqZeroExt K K))
    (ρ : Fin r → Fin n) (γ : Fin r → Fin m) :
    ((φ * B).submatrix ρ γ).det
      = ∑ g : Fin r → Fin m, (φ.submatrix ρ g).det * (∏ i, B (g i) (γ i)) := by
  have hsub : (φ * B).submatrix ρ γ = (φ.submatrix ρ id) * (B.submatrix id γ) := by
    have := Matrix.submatrix_mul_equiv φ B ρ (Equiv.refl (Fin m)) γ
    simpa using this.symm
  rw [hsub, det_mul_eq_sum_det_submatrix_mul_prod_tsze]
  apply Finset.sum_congr rfl
  intro g _
  rfl

private theorem dual_transport_identity {K : Type*} [Field K] {m n r : ℕ}
    (U : Matrix (Fin m) (Fin m) K) (V : Matrix (Fin n) (Fin n) K)
    (M Y : Matrix (Fin m) (Fin n) K)
    (R : Fin (r + 1) → Fin m) (C : Fin (r + 1) → Fin n) :
    leibnizDiff R C (U * M * V) (U * Y * V) =
      ∑ F : Fin (r + 1) → Fin m, ∑ G : Fin (r + 1) → Fin n,
        (∏ t, U (R t) (F t)) * ((∏ t, V (G t) (C t)) * leibnizDiff F G M Y) := by
  classical
  set Uu : Matrix (Fin m) (Fin m) (TrivSqZeroExt K K) :=
    U.map TrivSqZeroExt.inl with hUu
  set Vv : Matrix (Fin n) (Fin n) (TrivSqZeroExt K K) :=
    V.map TrivSqZeroExt.inl with hVv
  set Mm : Matrix (Fin m) (Fin n) (TrivSqZeroExt K K) :=
    Matrix.of fun p q ↦ ((M p q, Y p q) : TrivSqZeroExt K K) with hMm
  have hMm_apply : ∀ p q,
      Mm p q = ((M p q, Y p q) : TrivSqZeroExt K K) := by
    intro p q
    rw [hMm]
    rfl
  have hinner_fst : ∀ p q,
      TrivSqZeroExt.fst ((Uu * Mm) p q) = (U * M) p q := by
    intro p q
    rw [Matrix.mul_apply, TrivSqZeroExt.fst_sum, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [TrivSqZeroExt.fst_mul, hUu, hMm_apply]
    simp [Matrix.map_apply]
  have hinner_snd : ∀ p q,
      TrivSqZeroExt.snd ((Uu * Mm) p q) = (U * Y) p q := by
    intro p q
    rw [Matrix.mul_apply, TrivSqZeroExt.snd_sum, Matrix.mul_apply]
    apply Finset.sum_congr rfl
    intro j _
    rw [tsze_snd_mul, hUu, hMm_apply]
    simp [Matrix.map_apply]
  have hentry : ∀ a b : Fin (r + 1),
      (Uu * Mm * Vv) (R a) (C b) =
        (((U * M * V) (R a) (C b), (U * Y * V) (R a) (C b)) :
          TrivSqZeroExt K K) := by
    intro a b
    apply TrivSqZeroExt.ext
    · simp only [TrivSqZeroExt.fst_mk]
      rw [show Uu * Mm * Vv = (Uu * Mm) * Vv from rfl,
        Matrix.mul_apply, TrivSqZeroExt.fst_sum]
      simp only [TrivSqZeroExt.fst_mul, hinner_fst, hVv, Matrix.map_apply,
        TrivSqZeroExt.fst_inl]
      rw [Matrix.mul_apply]
    · simp only [TrivSqZeroExt.snd_mk]
      rw [show Uu * Mm * Vv = (Uu * Mm) * Vv from rfl,
        Matrix.mul_apply, TrivSqZeroExt.snd_sum]
      simp only [tsze_snd_mul, hinner_fst, hinner_snd, hVv, Matrix.map_apply,
        TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, mul_zero, zero_add]
      rw [Matrix.mul_apply]
  have hmat : (Uu * Mm * Vv).submatrix R C =
      Matrix.of fun a b : Fin (r + 1) ↦
        ((((U * M * V) (R a) (C b), (U * Y * V) (R a) (C b))) :
          TrivSqZeroExt K K) := by
    apply Matrix.ext
    intro a b
    simp only [Matrix.submatrix_apply]
    exact hentry a b
  have hexpand : ((Uu * Mm * Vv).submatrix R C).det =
      ∑ F : Fin (r + 1) → Fin m, ∑ G : Fin (r + 1) → Fin n,
        (∏ t, Uu (R t) (F t)) * ((Mm.submatrix F G).det * (∏ t, Vv (G t) (C t))) := by
    rw [show Uu * Mm * Vv = Uu * (Mm * Vv) by rw [Matrix.mul_assoc]]
    rw [minor_mul_left_tsze]
    apply Finset.sum_congr rfl
    intro F _
    rw [minor_mul_right_tsze, Finset.mul_sum]
  have hcoeffU : ∀ F : Fin (r + 1) → Fin m,
      TrivSqZeroExt.snd (∏ t, Uu (R t) (F t)) = 0 ∧
        TrivSqZeroExt.fst (∏ t, Uu (R t) (F t)) = ∏ t, U (R t) (F t) := by
    intro F
    constructor
    · rw [tsze_snd_prod]
      apply Finset.sum_eq_zero
      intro t _
      simp only [hUu, Matrix.map_apply, TrivSqZeroExt.snd_inl, mul_zero]
    · rw [tsze_fst_prod]
      apply Finset.prod_congr rfl
      intro t _
      simp [hUu]
  have hcoeffV : ∀ G : Fin (r + 1) → Fin n,
      TrivSqZeroExt.snd (∏ t, Vv (G t) (C t)) = 0 ∧
        TrivSqZeroExt.fst (∏ t, Vv (G t) (C t)) = ∏ t, V (G t) (C t) := by
    intro G
    constructor
    · rw [tsze_snd_prod]
      apply Finset.sum_eq_zero
      intro t _
      simp only [hVv, Matrix.map_apply, TrivSqZeroExt.snd_inl, mul_zero]
    · rw [tsze_fst_prod]
      apply Finset.prod_congr rfl
      intro t _
      simp [hVv]
  have hmain : leibnizDiff R C (U * M * V) (U * Y * V) =
      TrivSqZeroExt.snd (((Uu * Mm * Vv).submatrix R C).det) := by
    rw [hmat]
    exact (dual_det_snd R C (U * M * V) (U * Y * V)).symm
  have hd : ∀ F : Fin (r + 1) → Fin m, ∀ G : Fin (r + 1) → Fin n,
      TrivSqZeroExt.snd ((Mm.submatrix F G).det) = leibnizDiff F G M Y := by
    intro F G
    have hsub : Mm.submatrix F G = Matrix.of fun a b : Fin (r + 1) ↦
        ((M (F a) (G b), Y (F a) (G b)) : TrivSqZeroExt K K) := by
      apply Matrix.ext
      intro a b
      rw [Matrix.submatrix_apply, hMm_apply]
      rfl
    rw [hsub]
    exact dual_det_snd F G M Y
  rw [hmain, hexpand, TrivSqZeroExt.snd_sum]
  apply Finset.sum_congr rfl
  intro F _
  rw [TrivSqZeroExt.snd_sum]
  apply Finset.sum_congr rfl
  intro G _
  have hU0 := (hcoeffU F).1
  have hU1 := (hcoeffU F).2
  have hV0 := (hcoeffV G).1
  have hV1 := (hcoeffV G).2
  have hdFG := hd F G
  rw [tsze_snd_mul, tsze_snd_mul, hU0, hU1, hdFG, hV0, hV1]
  ring

private theorem leibnizDiff_transport_vanishing {K : Type*} [Field K] {m n r : ℕ}
    (U : Matrix (Fin m) (Fin m) K) (V : Matrix (Fin n) (Fin n) K)
    (M Y : Matrix (Fin m) (Fin n) K)
    (h : ∀ (I : Fin (r + 1) ↪ Fin m) (J : Fin (r + 1) ↪ Fin n),
      leibnizDiff (fun i ↦ I i) (fun i ↦ J i) M Y = 0)
    (R : Fin (r + 1) → Fin m) (C : Fin (r + 1) → Fin n) :
    leibnizDiff R C (U * M * V) (U * Y * V) = 0 := by
  rw [dual_transport_identity]
  apply Finset.sum_eq_zero
  intro F _
  apply Finset.sum_eq_zero
  intro G _
  by_cases hF : Function.Injective F
  · by_cases hG : Function.Injective G
    · have h0 := h ⟨F, hF⟩ ⟨G, hG⟩
      simp only [Function.Embedding.coeFn_mk] at h0
      rw [h0, mul_zero, mul_zero]
    · rw [leibnizDiff_eq_zero_of_not_injective_right F G M Y hG, mul_zero, mul_zero]
  · rw [leibnizDiff_eq_zero_of_not_injective_left F G M Y hF, mul_zero, mul_zero]


private def canonicalMatrix {K : Type*} [Field K] (m n r : ℕ) :
    Matrix (Fin m) (Fin n) K :=
  fun i j ↦ if i.val = j.val ∧ i.val < r then 1 else 0

private theorem exists_normalForm_sum {K : Type*} [Field K] {m n r : ℕ}
    (M : Matrix (Fin m) (Fin n) K) (hM : Matrix.rank M = r) :
    ∃ (P : Matrix (Fin r ⊕ Fin (m - r)) (Fin m) K)
      (P' : Matrix (Fin m) (Fin r ⊕ Fin (m - r)) K)
      (Q : Matrix (Fin n) (Fin r ⊕ Fin (n - r)) K)
      (Q' : Matrix (Fin r ⊕ Fin (n - r)) (Fin n) K),
      P * P' = 1 ∧ P' * P = 1 ∧ Q * Q' = 1 ∧ Q' * Q = 1 ∧
        P * M * Q = Matrix.fromBlocks 1 0 0 0 := by
  classical
  obtain ⟨e₁, e₂, hAu⟩ := Matrix.exists_reindex_isUnit_det_toBlocks₁₁ M hM
  set G := reindex e₁ e₂ M with hG
  have hGrank : G.rank = Fintype.card (Fin r) := by
    rw [hG, rank_reindex, hM, Fintype.card_fin]
  have hD :=
    (Matrix.RankManifold.rank_eq_iff_toBlocks₂₂_eq_of_isUnit_det_toBlocks₁₁ G hAu).mp
      hGrank
  set A := G.toBlocks₁₁ with hAdef
  set B := G.toBlocks₁₂ with hBdef
  set C := G.toBlocks₂₁ with hCdef
  set D := G.toBlocks₂₂ with hDdef
  have hGblk : G = fromBlocks A B C D := (fromBlocks_toBlocks G).symm
  let P₀ : Matrix (Fin r ⊕ Fin (m - r)) (Fin m) K :=
    (1 : Matrix (Fin m) (Fin m) K).submatrix e₁.symm id
  let P₀' : Matrix (Fin m) (Fin r ⊕ Fin (m - r)) K :=
    (1 : Matrix (Fin m) (Fin m) K).submatrix id e₁.symm
  let Q₀ : Matrix (Fin n) (Fin r ⊕ Fin (n - r)) K :=
    (1 : Matrix (Fin n) (Fin n) K).submatrix id e₂.symm
  let Q₀' : Matrix (Fin r ⊕ Fin (n - r)) (Fin n) K :=
    (1 : Matrix (Fin n) (Fin n) K).submatrix e₂.symm id
  have hP₀ : P₀ * P₀' = 1 := by
    ext a b
    simp [P₀, P₀', Matrix.mul_apply, Matrix.one_apply]
  have hP₀' : P₀' * P₀ = 1 := by
    simp only [P₀, P₀']
    rw [submatrix_mul_equiv, Matrix.one_mul, submatrix_id_id]
  have hQ₀ : Q₀ * Q₀' = 1 := by
    simp only [Q₀, Q₀']
    rw [submatrix_mul_equiv, Matrix.one_mul, submatrix_id_id]
  have hQ₀' : Q₀' * Q₀ = 1 := by
    ext a b
    simp [Q₀, Q₀', Matrix.mul_apply, Matrix.one_apply]
  have hPFQ : P₀ * M * Q₀ = G := by
    ext a b
    simp [P₀, Q₀, G, Matrix.mul_apply, Matrix.one_apply]
  have hinv : A⁻¹ * A = 1 := nonsing_inv_mul A hAu
  have hinv' : A * A⁻¹ = 1 := mul_nonsing_inv A hAu
  let L : Matrix (Fin r ⊕ Fin (m - r)) (Fin r ⊕ Fin (m - r)) K :=
    fromBlocks A⁻¹ 0 (-(C * A⁻¹)) 1
  let L' : Matrix (Fin r ⊕ Fin (m - r)) (Fin r ⊕ Fin (m - r)) K :=
    fromBlocks A 0 C 1
  let R : Matrix (Fin r ⊕ Fin (n - r)) (Fin r ⊕ Fin (n - r)) K :=
    fromBlocks 1 (-(A⁻¹ * B)) 0 1
  let R' : Matrix (Fin r ⊕ Fin (n - r)) (Fin r ⊕ Fin (n - r)) K :=
    fromBlocks 1 (A⁻¹ * B) 0 1
  have hL : L * L' = 1 := by
    simp [L, L', fromBlocks_multiply, hinv, Matrix.mul_assoc]
  have hL' : L' * L = 1 := by
    simp [L, L', fromBlocks_multiply, hinv']
  have hR : R * R' = 1 := by
    simp [R, R', fromBlocks_multiply]
  have hR' : R' * R = 1 := by
    simp [R, R', fromBlocks_multiply]
  have hLGR : L * G * R = fromBlocks 1 0 0 0 := by
    rw [hGblk, hD]
    simp [L, R, fromBlocks_multiply, hinv, Matrix.mul_assoc]
  refine ⟨L * P₀, P₀' * L', Q₀ * R, R' * Q₀', ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc P₀, hP₀, Matrix.one_mul, hL]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc L', hL', Matrix.one_mul, hP₀']
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc R, hR, Matrix.one_mul, hQ₀]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q₀', hQ₀', Matrix.one_mul, hR']
  · rw [show L * P₀ * M * (Q₀ * R) = L * (P₀ * M * Q₀) * R by
      simp only [Matrix.mul_assoc],
      hPFQ, hLGR]


private theorem exists_normalForm_fin {K : Type*} [Field K] {m n r : ℕ}
    (A : Matrix (Fin m) (Fin n) K) (hA : Matrix.rank A = r)
    (hrm : r < m) (hrn : r < n) :
    ∃ (P P' : Matrix (Fin m) (Fin m) K) (Q Q' : Matrix (Fin n) (Fin n) K),
      P * P' = 1 ∧ P' * P = 1 ∧ Q * Q' = 1 ∧ Q' * Q = 1 ∧
        P * A * Q = canonicalMatrix m n r := by
  classical
  obtain ⟨P₀, P₀', Q₀, Q₀', hP₀, hP₀', hQ₀, hQ₀', hPAQ⟩ :=
    exists_normalForm_sum A hA
  have hm : r + (m - r) = m := by omega
  have hn : r + (n - r) = n := by omega
  set f₁ : (Fin r ⊕ Fin (m - r)) ≃ Fin m :=
    finSumFinEquiv.trans (finCongr hm) with hf₁
  set f₂ : (Fin r ⊕ Fin (n - r)) ≃ Fin n :=
    finSumFinEquiv.trans (finCongr hn) with hf₂
  have hf₁_inl : ∀ s : Fin r, (f₁ (Sum.inl s)).val = s.val := by
    intro s
    simp [hf₁, finSumFinEquiv_apply_left]
  have hf₁_inr : ∀ u : Fin (m - r), r ≤ (f₁ (Sum.inr u)).val := by
    intro u
    simp [hf₁, finSumFinEquiv_apply_right]
  have hf₂_inl : ∀ t : Fin r, (f₂ (Sum.inl t)).val = t.val := by
    intro t
    simp [hf₂, finSumFinEquiv_apply_left]
  have hf₂_inr : ∀ v : Fin (n - r), r ≤ (f₂ (Sum.inr v)).val := by
    intro v
    simp [hf₂, finSumFinEquiv_apply_right]
  set S₁ : Matrix (Fin m) (Fin r ⊕ Fin (m - r)) K :=
    (1 : Matrix (Fin m) (Fin m) K).submatrix id ⇑f₁ with hS₁def
  set S₁' : Matrix (Fin r ⊕ Fin (m - r)) (Fin m) K :=
    (1 : Matrix (Fin m) (Fin m) K).submatrix ⇑f₁ id with hS₁'def
  set S₂ : Matrix (Fin r ⊕ Fin (n - r)) (Fin n) K :=
    (1 : Matrix (Fin n) (Fin n) K).submatrix ⇑f₂ id with hS₂def
  set S₂' : Matrix (Fin n) (Fin r ⊕ Fin (n - r)) K :=
    (1 : Matrix (Fin n) (Fin n) K).submatrix id ⇑f₂ with hS₂'def
  have hS₁ : S₁ * S₁' = 1 := by
    simp only [hS₁def, hS₁'def]
    rw [submatrix_mul_equiv, Matrix.one_mul, submatrix_id_id]
  have hS₁' : S₁' * S₁ = 1 := by
    ext a b
    simp [S₁, S₁', Matrix.mul_apply, Matrix.one_apply]
  have hS₂ : S₂ * S₂' = 1 := by
    ext a b
    simp [S₂, S₂', Matrix.mul_apply, Matrix.one_apply]
  have hS₂' : S₂' * S₂ = 1 := by
    simp only [hS₂def, hS₂'def]
    rw [submatrix_mul_equiv, Matrix.one_mul, submatrix_id_id]
  set F₀ : Matrix (Fin r ⊕ Fin (m - r)) (Fin r ⊕ Fin (n - r)) K :=
    Matrix.fromBlocks 1 0 0 0 with hF₀
  have hS₁_apply : ∀ (a : Fin m) (s : Fin r ⊕ Fin (m - r)),
      S₁ a s = (if a = f₁ s then 1 else 0 : K) := by
    intro a s
    simp [hS₁def, Matrix.one_apply]
  have hS₂_apply : ∀ (t : Fin r ⊕ Fin (n - r)) (b : Fin n),
      S₂ t b = (if f₂ t = b then 1 else 0 : K) := by
    intro t b
    simp [hS₂def, Matrix.one_apply]
  have hre : S₁ * F₀ * S₂ = Matrix.reindex f₁ f₂ F₀ := by
    apply Matrix.ext
    intro a b
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.mul_apply]
    have hinner : ∀ i, (S₁ * F₀) a i = F₀ (f₁.symm a) i := by
      intro i
      rw [Matrix.mul_apply]
      have hsum : (∑ s, S₁ a s * F₀ s i) =
          S₁ a (f₁.symm a) * F₀ (f₁.symm a) i :=
        Finset.sum_eq_single_of_mem (f₁.symm a) (Finset.mem_univ _) (fun s _ hs => by
          rw [hS₁_apply]
          have hne : a ≠ f₁ s := by
            intro hcon
            apply hs
            have h2 := Equiv.symm_apply_apply f₁ s
            rw [← hcon] at h2
            exact h2.symm
          simp [hne])
      rw [hsum, hS₁_apply]
      simp [Equiv.apply_symm_apply]
    simp_rw [hinner]
    have hsum : (∑ i, F₀ (f₁.symm a) i * S₂ i b) =
        F₀ (f₁.symm a) (f₂.symm b) * S₂ (f₂.symm b) b :=
      Finset.sum_eq_single_of_mem (f₂.symm b) (Finset.mem_univ _) (fun i _ hi => by
        rw [hS₂_apply]
        have hne : f₂ i ≠ b := by
          intro hcon
          apply hi
          have h2 := Equiv.symm_apply_apply f₂ i
          rw [hcon] at h2
          exact h2.symm
        simp [hne])
    rw [hsum, hS₂_apply]
    simp [Equiv.apply_symm_apply]
  have hcanon : Matrix.reindex f₁ f₂ F₀ = canonicalMatrix m n r := by
    apply Matrix.ext
    intro i j
    rw [Matrix.reindex_apply, Matrix.submatrix_apply]
    cases hs1 : f₁.symm i with
    | inl s' =>
      cases hs2 : f₂.symm j with
      | inl t' =>
        have hi := Equiv.apply_symm_apply f₁ i
        rw [hs1] at hi
        have hj := Equiv.apply_symm_apply f₂ j
        rw [hs2] at hj
        have hival : i.val = s'.val := by rw [← hi]; exact hf₁_inl s'
        have hjval : j.val = t'.val := by rw [← hj]; exact hf₂_inl t'
        have hF : F₀ (Sum.inl s') (Sum.inl t') =
            (1 : Matrix (Fin r) (Fin r) K) s' t' := rfl
        rw [hF, Matrix.one_apply]
        unfold canonicalMatrix
        rw [hival, hjval]
        by_cases hst : s' = t'
        · subst hst
          simp [s'.2]
        · have hval : s'.val ≠ t'.val := fun h => hst (Fin.ext h)
          simp [hst, hval]
      | inr v =>
        have hj := Equiv.apply_symm_apply f₂ j
        rw [hs2] at hj
        have hjval : r ≤ j.val := by rw [← hj]; exact hf₂_inr v
        have hi := Equiv.apply_symm_apply f₁ i
        rw [hs1] at hi
        have hival : i.val = s'.val := by rw [← hi]; exact hf₁_inl s'
        have hlt : i.val < r := by rw [hival]; exact s'.2
        have hne : i.val ≠ j.val := by omega
        have hF : F₀ (Sum.inl s') (Sum.inr v) = (0 : K) := rfl
        rw [hF]
        unfold canonicalMatrix
        simp [hne]
    | inr u =>
      cases hs2 : f₂.symm j with
      | inl t' =>
        have hi := Equiv.apply_symm_apply f₁ i
        rw [hs1] at hi
        have hival : r ≤ i.val := by rw [← hi]; exact hf₁_inr u
        have hlt : ¬ i.val < r := by omega
        have hF : F₀ (Sum.inr u) (Sum.inl t') = (0 : K) := rfl
        rw [hF]
        unfold canonicalMatrix
        simp [hlt]
      | inr v =>
        have hi := Equiv.apply_symm_apply f₁ i
        rw [hs1] at hi
        have hival : r ≤ i.val := by rw [← hi]; exact hf₁_inr u
        have hlt : ¬ i.val < r := by omega
        have hF : F₀ (Sum.inr u) (Sum.inr v) = (0 : K) := rfl
        rw [hF]
        unfold canonicalMatrix
        simp [hlt]
  refine ⟨S₁ * P₀, P₀' * S₁', Q₀ * S₂, S₂' * Q₀', ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc P₀, hP₀, Matrix.one_mul, hS₁]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc S₁', hS₁', Matrix.one_mul, hP₀']
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc S₂, hS₂, Matrix.one_mul, hQ₀]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc Q₀', hQ₀', Matrix.one_mul, hS₂']
  · rw [show S₁ * P₀ * A * (Q₀ * S₂) = S₁ * (P₀ * A * Q₀) * S₂ by
      simp only [Matrix.mul_assoc],
      hPAQ, hre, hcanon]


private theorem canonicalMatrix_eq_zero_of_ge_left {K : Type*} [Field K] {m n r : ℕ}
    {a : Fin m} {b : Fin n} (ha : r ≤ a.val) :
    canonicalMatrix (K := K) m n r a b = 0 := by
  unfold canonicalMatrix
  have h : ¬ (a.val = b.val ∧ a.val < r) := by
    intro hcon
    omega
  simp [h]

private theorem canonicalMatrix_eq_zero_of_ge_right {K : Type*} [Field K] {m n r : ℕ}
    {a : Fin m} {b : Fin n} (hb : r ≤ b.val) :
    canonicalMatrix (K := K) m n r a b = 0 := by
  unfold canonicalMatrix
  have h : ¬ (a.val = b.val ∧ a.val < r) := by
    intro hcon
    omega
  simp [h]

private theorem canonicalMatrix_eq_one_of_lt {K : Type*} [Field K] {m n r : ℕ}
    {a : Fin m} {b : Fin n} (heq : a.val = b.val) (hlt : a.val < r) :
    canonicalMatrix (K := K) m n r a b = 1 := by
  unfold canonicalMatrix
  rw [ite_eq_left ⟨heq, hlt⟩]

private theorem canonicalMatrix_eq_one_of_ne_zero {K : Type*} [Field K] {m n r : ℕ}
    {a : Fin m} {b : Fin n} (h : canonicalMatrix (K := K) m n r a b ≠ 0) :
    canonicalMatrix (K := K) m n r a b = 1 ∧ a.val = b.val ∧ a.val < r := by
  unfold canonicalMatrix at h ⊢
  by_cases hcond : a.val = b.val ∧ a.val < r
  · rw [ite_eq_left hcond]
    exact ⟨rfl, hcond.1, hcond.2⟩
  · simp [hcond] at h

private theorem exists_ge_of_embedding {m r : ℕ} (rows : Fin (r + 1) ↪ Fin m) :
    ∃ i0 : Fin (r + 1), r ≤ (rows i0).val := by
  by_contra hnone
  push Not at hnone
  let f : Fin (r + 1) → Fin r := fun i ↦ ⟨(rows i).val, hnone i⟩
  have hf_inj : Function.Injective f := by
    intro i1 i2 heq
    have hval : (rows i1).val = (rows i2).val := by
      have h := congrArg Fin.val heq
      simpa [f] using h
    have hrows : rows i1 = rows i2 := Fin.ext hval
    exact rows.injective hrows
  let e : Fin (r + 1) ↪ Fin r := ⟨f, hf_inj⟩
  have hcard := Fintype.card_le_of_embedding e
  simp [Fintype.card_fin] at hcard

private theorem eval_canonical_minor_eq_zero {K : Type*} [Field K] {m n r : ℕ}
    (rows : Fin (r + 1) ↪ Fin m) (cols : Fin (r + 1) ↪ Fin n) :
    MvPolynomial.eval (fun ij ↦ (canonicalMatrix (K := K) m n r) ij.1 ij.2)
      (minorPolynomial r rows cols) = 0 := by
  rw [eval_minorPolynomial]
  obtain ⟨i0, hi0⟩ := exists_ge_of_embedding rows
  apply Matrix.det_eq_zero_of_row_eq_zero i0
  intro j
  simp only [Matrix.submatrix_apply]
  exact canonicalMatrix_eq_zero_of_ge_left hi0

private theorem mem_canonical_tangent_iff_forall {K : Type*} [Field K] {m n r : ℕ}
    (B : Matrix (Fin m) (Fin n) K) :
    (fun ij ↦ B ij.1 ij.2) ∈ tangent r (canonicalMatrix (K := K) m n r) ↔
      ∀ (rows : Fin (r + 1) ↪ Fin m) (cols : Fin (r + 1) ↪ Fin n),
        differential (minorPolynomial r rows cols)
          (fun ij ↦ (canonicalMatrix (K := K) m n r) ij.1 ij.2)
          (fun ij ↦ B ij.1 ij.2) = 0 := by
  have hp : ∀ f ∈ Set.range (fun p :
      (Fin (r + 1) ↪ Fin m) × (Fin (r + 1) ↪ Fin n) ↦
      minorPolynomial r p.1 p.2),
      MvPolynomial.eval (fun ij ↦ (canonicalMatrix (K := K) m n r) ij.1 ij.2) f = 0 := by
    intro f hf
    obtain ⟨p, rfl⟩ := hf
    exact eval_canonical_minor_eq_zero p.1 p.2
  have ht : tangent r (canonicalMatrix (K := K) m n r) =
      ⨅ f ∈ Set.range (fun p :
        (Fin (r + 1) ↪ Fin m) × (Fin (r + 1) ↪ Fin n) ↦
        minorPolynomial r p.1 p.2),
        LinearMap.ker (differential f
          (fun ij ↦ (canonicalMatrix (K := K) m n r) ij.1 ij.2)) := by
    rw [tangent, minorIdeal, tangentIdeal_span hp]
  rw [ht]
  simp only [Submodule.mem_iInf, LinearMap.mem_ker]
  constructor
  · intro h rows cols
    exact h _ ⟨(rows, cols), rfl⟩
  · intro h f hf
    obtain ⟨p, rfl⟩ := hf
    exact h p.1 p.2

private theorem canonical_diff_of_bottom_zero {K : Type*} [Field K] {m n r : ℕ}
    (B : Matrix (Fin m) (Fin n) K)
    (hB : ∀ i : Fin m, ∀ j : Fin n, r ≤ i.val → r ≤ j.val → B i j = 0)
    (rows : Fin (r + 1) ↪ Fin m) (cols : Fin (r + 1) ↪ Fin n) :
    differential (minorPolynomial r rows cols)
      (fun ij ↦ (canonicalMatrix (K := K) m n r) ij.1 ij.2)
      (fun ij ↦ B ij.1 ij.2) = 0 := by
  rw [differential_minor_apply]
  unfold leibnizDiff
  apply Finset.sum_eq_zero
  intro σ _
  rw [mul_eq_zero]
  right
  apply Finset.sum_eq_zero
  intro t _
  by_cases hP : (∏ i ∈ Finset.univ \ {t},
      (canonicalMatrix (K := K) m n r) (rows (σ i)) (cols i)) = 0
  · simp [hP]
  · have hall : ∀ i ∈ Finset.univ \ {t},
        (canonicalMatrix (K := K) m n r) (rows (σ i)) (cols i) ≠ 0 := by
      intro i hi hzero
      exact hP (Finset.prod_eq_zero hi hzero)
    have hval : ∀ i ∈ Finset.univ \ {t},
        (rows (σ i)).val = (cols i).val ∧ (rows (σ i)).val < r := by
      intro i hi
      exact (canonicalMatrix_eq_one_of_ne_zero (hall i hi)).2
    have hlt_rows : ∀ i ∈ Finset.univ \ {t}, (rows (σ i)).val < r :=
      fun i hi => (hval i hi).2
    have hlt_cols : ∀ i ∈ Finset.univ \ {t}, (cols i).val < r := by
      intro i hi
      obtain ⟨heq, hlt⟩ := hval i hi
      rw [← heq]
      exact hlt
    have hge_rows : r ≤ (rows (σ t)).val := by
      by_contra hlt
      push Not at hlt
      have hall_lt : ∀ i : Fin (r + 1), (rows (σ i)).val < r := by
        intro i
        by_cases hik : i = t
        · subst hik
          exact hlt
        · apply hlt_rows i
          simp [hik]
      let f : Fin (r + 1) → Fin m := fun i ↦ rows (σ i)
      have hf_inj : Function.Injective f := rows.injective.comp σ.injective
      let e : Fin (r + 1) ↪ Fin m := ⟨f, hf_inj⟩
      obtain ⟨i0, hi0⟩ := exists_ge_of_embedding e
      have hi0' : r ≤ (rows (σ i0)).val := hi0
      exact absurd (hall_lt i0) (by omega)
    have hge_cols : r ≤ (cols t).val := by
      by_contra hlt
      push Not at hlt
      have hall_lt : ∀ i : Fin (r + 1), (cols i).val < r := by
        intro i
        by_cases hik : i = t
        · subst hik
          exact hlt
        · apply hlt_cols i
          simp [hik]
      obtain ⟨i0, hi0⟩ := exists_ge_of_embedding cols
      exact absurd (hall_lt i0) (by omega)
    have hB0 : B (rows (σ t)) (cols t) = 0 := hB _ _ hge_rows hge_cols
    simp [hB0]


private theorem exists_extend_embedding {m r : ℕ} (hrm : r < m)
    (i : Fin m) (hi : r ≤ i.val) :
    ∃ R : Fin (r + 1) ↪ Fin m,
      (∀ t : Fin (r + 1), t.val < r → (R t).val = t.val) ∧
        (∀ t : Fin (r + 1), r ≤ t.val → R t = i) := by
  refine ⟨⟨fun t ↦ if h : t.val < r then
    (⟨t.val, Nat.lt_of_lt_of_le h hrm.le⟩ : Fin m) else i, ?_⟩,
    ?_, ?_⟩
  · intro t1 t2 h
    by_cases h1 : t1.val < r
    · by_cases h2 : t2.val < r
      · simp only [dite_eq_left h1, dite_eq_left h2] at h
        have h3 := congrArg Fin.val h
        have h4 : t1.val = t2.val := h3
        exact Fin.ext h4
      · simp only [dite_eq_left h1, dite_eq_right h2] at h
        exfalso
        have h3 := congrArg Fin.val h
        have h4 : t1.val = i.val := h3
        omega
    · by_cases h2 : t2.val < r
      · simp only [dite_eq_right h1, dite_eq_left h2] at h
        exfalso
        have h3 := congrArg Fin.val h
        have h4 : i.val = t2.val := h3
        omega
      · have e1 : t1.val = r := by
          have t1lt := t1.isLt
          omega
        have e2 : t2.val = r := by
          have t2lt := t2.isLt
          omega
        exact Fin.ext (e1.trans e2.symm)
  · intro t h
    change ((if h' : t.val < r then
      (⟨t.val, Nat.lt_of_lt_of_le h' hrm.le⟩ : Fin m) else i)).val = t.val
    rw [dite_eq_left h]
  · intro t h
    change (if h' : t.val < r then
      (⟨t.val, Nat.lt_of_lt_of_le h' hrm.le⟩ : Fin m) else i) = i
    rw [dite_eq_right (by omega : ¬ t.val < r)]

private theorem canonical_bottom_zero_of_diff_zero {K : Type*} [Field K] {m n r : ℕ}
    (hrm : r < m) (hrn : r < n) (B : Matrix (Fin m) (Fin n) K)
    (hB : ∀ (rows : Fin (r + 1) ↪ Fin m) (cols : Fin (r + 1) ↪ Fin n),
      differential (minorPolynomial r rows cols)
        (fun ij ↦ (canonicalMatrix (K := K) m n r) ij.1 ij.2)
        (fun ij ↦ B ij.1 ij.2) = 0)
    (i : Fin m) (j : Fin n) (hi : r ≤ i.val) (hj : r ≤ j.val) : B i j = 0 := by
  obtain ⟨R, hRval, hRge⟩ := exists_extend_embedding hrm i hi
  obtain ⟨C, hCval, hCge⟩ := exists_extend_embedding hrn j hj
  have hRlast : R (Fin.last r) = i := hRge _ le_rfl
  have hClast : C (Fin.last r) = j := hCge _ le_rfl
  have hdiff := hB R C
  rw [differential_minor_apply] at hdiff
  have hval : leibnizDiff (fun t ↦ R t) (fun t ↦ C t)
      (canonicalMatrix (K := K) m n r) B = B i j := by
    unfold leibnizDiff
    have hsingle : ∀ σ : Equiv.Perm (Fin (r + 1)), ∀ t : Fin (r + 1),
        t ≠ Fin.last r →
          (∏ t' ∈ Finset.univ \ {t},
            (canonicalMatrix (K := K) m n r) (R (σ t')) (C t')) *
            B (R (σ t)) (C t) = 0 := by
      intro σ t ht
      have hmem : Fin.last r ∈ Finset.univ \ {t} := by
        simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton, true_and]
        exact Ne.symm ht
      have hfac : (canonicalMatrix (K := K) m n r) (R (σ (Fin.last r)))
          (C (Fin.last r)) = 0 := by
        rw [hClast]
        exact canonicalMatrix_eq_zero_of_ge_right hj
      have hprod : (∏ t' ∈ Finset.univ \ {t},
          (canonicalMatrix (K := K) m n r) (R (σ t')) (C t')) = 0 :=
        Finset.prod_eq_zero hmem hfac
      simp [hprod]
    have hterm : ∀ σ : Equiv.Perm (Fin (r + 1)),
        ((σ.sign : ℤ) : K) *
          (∑ t : Fin (r + 1), (∏ t' ∈ Finset.univ \ {t},
            (canonicalMatrix (K := K) m n r) (R (σ t')) (C t')) *
            B (R (σ t)) (C t)) =
          (if σ = 1 then B i j else 0) := by
      intro σ
      have hinner : (∑ t : Fin (r + 1), (∏ t' ∈ Finset.univ \ {t},
          (canonicalMatrix (K := K) m n r) (R (σ t')) (C t')) *
          B (R (σ t)) (C t)) =
          (∏ t' ∈ Finset.univ \ {Fin.last r},
            (canonicalMatrix (K := K) m n r) (R (σ t')) (C t')) *
          B (R (σ (Fin.last r))) (C (Fin.last r)) :=
        Finset.sum_eq_single_of_mem (Fin.last r) (Finset.mem_univ _)
          (fun t _ ht => hsingle σ t ht)
      rw [hinner]
      by_cases hσ : σ = 1
      · subst hσ
        rw [ite_eq_left rfl]
        simp only [Equiv.Perm.sign_one, Units.val_one, Int.cast_one, one_mul]
        have hprod1 : (∏ t' ∈ Finset.univ \ {Fin.last r},
            (canonicalMatrix (K := K) m n r)
              (R ((1 : Equiv.Perm (Fin (r + 1))) t')) (C t')) = 1 := by
          apply Finset.prod_eq_one
          intro t' ht'
          simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_singleton,
            true_and] at ht'
          have hlt : t'.val < r := by
            have hne : t'.val ≠ r := by
              intro hcon
              apply ht'
              have htv : t'.val = (Fin.last r).val := hcon
              exact Fin.ext htv
            have tlt := t'.isLt
            omega
          have eR : (R ((1 : Equiv.Perm (Fin (r + 1))) t')).val = t'.val :=
            hRval _ hlt
          have eC : (C t').val = t'.val := hCval t' hlt
          exact canonicalMatrix_eq_one_of_lt (eR.trans eC.symm) (by omega)
        rw [hprod1]
        change 1 * B (R (Fin.last r)) (C (Fin.last r)) = B i j
        rw [hRlast, hClast, one_mul]
      · rw [ite_eq_right hσ]
        have hprod0 : (∏ t' ∈ Finset.univ \ {Fin.last r},
            (canonicalMatrix (K := K) m n r) (R (σ t')) (C t')) = 0 := by
          by_contra hne
          have hall : ∀ t' ∈ Finset.univ \ {Fin.last r},
              (canonicalMatrix (K := K) m n r) (R (σ t')) (C t') ≠ 0 := by
            intro t' ht' hzero
            exact hne (Finset.prod_eq_zero ht' hzero)
          have hfix : ∀ t' : Fin (r + 1), t' ≠ Fin.last r → σ t' = t' := by
            intro t' ht'
            have hmem : t' ∈ Finset.univ \ {Fin.last r} := by simp [ht']
            obtain ⟨-, heq, hlt⟩ :=
              canonicalMatrix_eq_one_of_ne_zero (hall t' hmem)
            have hlt' : t'.val < r := by
              have hne' : t'.val ≠ r := by
                intro hcon
                apply ht'
                have htv : t'.val = (Fin.last r).val := hcon
                exact Fin.ext htv
              have tlt := t'.isLt
              omega
            have eC : (C t').val = t'.val := hCval t' hlt'
            have hσlt : (σ t').val < r := by
              by_contra hge
              push Not at hge
              have hReq : R (σ t') = i := hRge _ hge
              rw [hReq] at hlt
              omega
            have eR : (R (σ t')).val = (σ t').val := hRval _ hσlt
            have hveq : (σ t').val = t'.val := by omega
            exact Fin.ext hveq
          have hlast : σ (Fin.last r) = Fin.last r := by
            by_contra hne'
            have hfix_y : σ (σ (Fin.last r)) = σ (Fin.last r) := hfix _ hne'
            have h3 := congrArg (⇑σ.symm) hfix_y
            simp only [Equiv.symm_apply_apply] at h3
            exact hne' h3
          have hσ1 : σ = 1 := by
            refine Equiv.Perm.ext fun x => ?_
            by_cases hx : x = Fin.last r
            · subst hx
              exact hlast.trans (Equiv.Perm.one_apply _).symm
            · exact (hfix x hx).trans (Equiv.Perm.one_apply _).symm
          exact hσ hσ1
        simp [hprod0]
    simp_rw [hterm]
    rw [Finset.sum_ite_eq']
    simp
  rw [hval] at hdiff
  exact hdiff


private theorem canonicalMatrix_eq_zero_of_ne {K : Type*} [Field K] {m n r : ℕ}
    {a : Fin m} {b : Fin n} (hne : a.val ≠ b.val) :
    canonicalMatrix (K := K) m n r a b = 0 := by
  unfold canonicalMatrix
  have h : ¬ (a.val = b.val ∧ a.val < r) := by
    intro hcon
    exact hne hcon.1
  simp [h]

private theorem canonical_mulVec_of_lt {K : Type*} [Field K] {m n r : ℕ}
    (hrn : r < n) (v : Fin n → K) (i : Fin m) (hi : i.val < r) :
    ((canonicalMatrix (K := K) m n r) *ᵥ v) i = v ⟨i.val, lt_trans hi hrn⟩ := by
  change ∑ j, (canonicalMatrix (K := K) m n r) i j * v j = _
  have hsum : (∑ j, (canonicalMatrix (K := K) m n r) i j * v j) =
      (canonicalMatrix (K := K) m n r) i ⟨i.val, lt_trans hi hrn⟩ *
        v ⟨i.val, lt_trans hi hrn⟩ :=
    Finset.sum_eq_single_of_mem _ (Finset.mem_univ _) (fun j _ hj => by
      have hne : i.val ≠ j.val := by
        intro hcon
        apply hj
        have htv : j.val = (⟨i.val, lt_trans hi hrn⟩ : Fin n).val := hcon.symm
        exact Fin.ext htv
      simp [canonicalMatrix_eq_zero_of_ne hne])
  rw [hsum]
  have hC : (canonicalMatrix (K := K) m n r) i ⟨i.val, lt_trans hi hrn⟩ = 1 :=
    canonicalMatrix_eq_one_of_lt rfl hi
  rw [hC, one_mul]

private theorem canonical_mulVec_of_ge {K : Type*} [Field K] {m n r : ℕ}
    (v : Fin n → K) (i : Fin m) (hi : r ≤ i.val) :
    ((canonicalMatrix (K := K) m n r) *ᵥ v) i = 0 := by
  change ∑ j, (canonicalMatrix (K := K) m n r) i j * v j = 0
  apply Finset.sum_eq_zero
  intro j _
  simp [canonicalMatrix_eq_zero_of_ge_left hi]

private theorem canonical_ker_iff {K : Type*} [Field K] {m n r : ℕ}
    (hrm : r < m) (hrn : r < n) (v : Fin n → K) :
    Matrix.toLin' (canonicalMatrix (K := K) m n r) v = 0 ↔
      ∀ j : Fin n, j.val < r → v j = 0 := by
  rw [Matrix.toLin'_apply]
  constructor
  · intro h j hj
    have hC := canonical_mulVec_of_lt hrn v ⟨j.val, lt_trans hj hrm⟩ hj
    have hz : ((canonicalMatrix (K := K) m n r) *ᵥ v) ⟨j.val, lt_trans hj hrm⟩ = 0 :=
      congrFun h _
    rw [hC] at hz
    exact hz
  · intro h
    funext i
    change ((canonicalMatrix (K := K) m n r) *ᵥ v) i = 0
    by_cases hi : i.val < r
    · have hC := canonical_mulVec_of_lt hrn v i hi
      rw [hC]
      exact h _ hi
    · push Not at hi
      exact canonical_mulVec_of_ge v i hi

private theorem canonical_range_iff {K : Type*} [Field K] {m n r : ℕ}
    (hrm : r < m) (hrn : r < n) (y : Fin m → K) :
    y ∈ LinearMap.range (Matrix.toLin' (canonicalMatrix (K := K) m n r)) ↔
      ∀ i : Fin m, r ≤ i.val → y i = 0 := by
  constructor
  · intro h i hi
    obtain ⟨v, hv⟩ := h
    have heq : y i = ((canonicalMatrix (K := K) m n r) *ᵥ v) i := by
      rw [← hv, Matrix.toLin'_apply]
    rw [heq]
    exact canonical_mulVec_of_ge v i hi
  · intro h
    rw [LinearMap.mem_range]
    refine ⟨fun j ↦ if hj : j.val < r then y ⟨j.val, lt_trans hj hrm⟩ else 0, ?_⟩
    funext i
    by_cases hi : i.val < r
    · rw [Matrix.toLin'_apply]
      have hC := canonical_mulVec_of_lt hrn
        (fun j ↦ if hj : j.val < r then y ⟨j.val, lt_trans hj hrm⟩ else 0) i hi
      rw [hC]
      change (if hj : (⟨i.val, lt_trans hi hrn⟩ : Fin n).val < r then
        y ⟨(⟨i.val, lt_trans hi hrn⟩ : Fin n).val, lt_trans hj hrm⟩ else 0) = y i
      rw [dite_eq_left hi]
    · push Not at hi
      rw [Matrix.toLin'_apply]
      have h0 := canonical_mulVec_of_ge
        (fun j : Fin n ↦ if hj : j.val < r then y ⟨j.val, lt_trans hj hrm⟩ else 0)
        i hi
      rw [h0]
      exact (h i hi).symm

private theorem canonical_kerIm_iff_bottom_zero {K : Type*} [Field K] {m n r : ℕ}
    (hrm : r < m) (hrn : r < n) (B : Matrix (Fin m) (Fin n) K) :
    (∀ v : Fin n → K, Matrix.toLin' (canonicalMatrix (K := K) m n r) v = 0 →
      Matrix.toLin' B v ∈ LinearMap.range (Matrix.toLin' (canonicalMatrix (K := K) m n r))) ↔
      (∀ i : Fin m, ∀ j : Fin n, r ≤ i.val → r ≤ j.val → B i j = 0) := by
  constructor
  · intro h i j hi hj
    have hvker : Matrix.toLin' (canonicalMatrix (K := K) m n r) (Pi.single j 1) = 0 := by
      rw [canonical_ker_iff hrm hrn]
      intro j' hj'
      have hne : j' ≠ j := by
        intro hcon
        subst hcon
        omega
      exact Pi.single_eq_of_ne hne _
    have hrange := h _ hvker
    rw [canonical_range_iff hrm hrn] at hrange
    have h0 := hrange i hi
    rw [Matrix.toLin'_apply, Matrix.mulVec_single_one] at h0
    exact h0
  · intro hB v hv
    rw [canonical_range_iff hrm hrn]
    intro i hi
    rw [Matrix.toLin'_apply]
    change ∑ j, B i j * v j = 0
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j.val < r
    · have hv0 : v j = 0 := by
        have hker := (canonical_ker_iff hrm hrn v).mp hv
        exact hker j hj
      simp [hv0]
    · push Not at hj
      simp [hB i j hi hj]

private theorem canonical_mem_tangent_iff {K : Type*} [Field K] {m n r : ℕ}
    (hrm : r < m) (hrn : r < n) (B : Matrix (Fin m) (Fin n) K) :
    (fun ij ↦ B ij.1 ij.2) ∈ tangent r (canonicalMatrix (K := K) m n r) ↔
      ∀ v : Fin n → K, Matrix.toLin' (canonicalMatrix (K := K) m n r) v = 0 →
        Matrix.toLin' B v ∈
          LinearMap.range (Matrix.toLin' (canonicalMatrix (K := K) m n r)) := by
  rw [mem_canonical_tangent_iff_forall, canonical_kerIm_iff_bottom_zero hrm hrn]
  constructor
  · intro h i j hi hj
    exact canonical_bottom_zero_of_diff_zero hrm hrn B h i j hi hj
  · intro h rows cols
    exact canonical_diff_of_bottom_zero B h rows cols


private theorem kerIm_transport {K : Type*} [Field K] {m n : ℕ}
    (P P' : Matrix (Fin m) (Fin m) K) (Q Q' : Matrix (Fin n) (Fin n) K)
    (hP : P * P' = 1) (hP' : P' * P = 1) (hQ : Q * Q' = 1) (hQ' : Q' * Q = 1)
    (A X : Matrix (Fin m) (Fin n) K) :
    (∀ v : Fin n → K, Matrix.toLin' A v = 0 →
      Matrix.toLin' X v ∈ LinearMap.range (Matrix.toLin' A)) ↔
    (∀ w : Fin n → K, Matrix.toLin' (P * A * Q) w = 0 →
      Matrix.toLin' (P * X * Q) w ∈
        LinearMap.range (Matrix.toLin' (P * A * Q))) := by
  have hAeq : P' * (P * A * Q) * Q' = A := by
    have h1 : P' * (P * A * Q) * Q' = (P' * P) * A * (Q * Q') := by
      simp only [Matrix.mul_assoc]
    rw [h1, hP', hQ, Matrix.one_mul, Matrix.mul_one]
  have hXeq : P' * (P * X * Q) * Q' = X := by
    have h1 : P' * (P * X * Q) * Q' = (P' * P) * X * (Q * Q') := by
      simp only [Matrix.mul_assoc]
    rw [h1, hP', hQ, Matrix.one_mul, Matrix.mul_one]
  have hAapply : ∀ v, Matrix.toLin' A v =
      Matrix.toLin' P' (Matrix.toLin' (P * A * Q) (Matrix.toLin' Q' v)) := by
    intro v
    conv_lhs => rw [← hAeq]
    simp only [Matrix.toLin'_mul, LinearMap.comp_apply]
  have hXapply : ∀ v, Matrix.toLin' X v =
      Matrix.toLin' P' (Matrix.toLin' (P * X * Q) (Matrix.toLin' Q' v)) := by
    intro v
    conv_lhs => rw [← hXeq]
    simp only [Matrix.toLin'_mul, LinearMap.comp_apply]
  have hPP' : ∀ z, Matrix.toLin' P (Matrix.toLin' P' z) = z := by
    intro z
    have hcomp : (Matrix.toLin' P).comp (Matrix.toLin' P') = LinearMap.id := by
      rw [← Matrix.toLin'_mul, hP, Matrix.toLin'_one]
    have h2 := congrArg (fun f => f z) hcomp
    simpa using h2
  have hQ'Q : ∀ z, Matrix.toLin' Q' (Matrix.toLin' Q z) = z := by
    intro z
    have hcomp : (Matrix.toLin' Q').comp (Matrix.toLin' Q) = LinearMap.id := by
      rw [← Matrix.toLin'_mul, hQ', Matrix.toLin'_one]
    have h2 := congrArg (fun f => f z) hcomp
    simpa using h2
  have hP'ker : ∀ Y, Matrix.toLin' P' Y = 0 ↔ Y = 0 := by
    intro Y
    constructor
    · intro h0
      have hPY := hPP' Y
      rw [h0] at hPY
      simpa using hPY.symm
    · intro hY
      rw [hY, map_zero]
  constructor
  · intro hAker w hwC
    have hvker : Matrix.toLin' A (Matrix.toLin' Q w) = 0 := by
      rw [hAapply, hQ'Q, hwC, map_zero]
    have hXrange := hAker _ hvker
    have hXeq' : Matrix.toLin' X (Matrix.toLin' Q w) =
        Matrix.toLin' P' (Matrix.toLin' (P * X * Q) w) := by
      rw [hXapply, hQ'Q]
    rw [hXeq'] at hXrange
    rw [LinearMap.mem_range] at hXrange
    obtain ⟨u, hu⟩ := hXrange
    rw [hAapply] at hu
    have hCX : Matrix.toLin' (P * A * Q) (Matrix.toLin' Q' u) =
        Matrix.toLin' (P * X * Q) w := by
      have h2 := congrArg (Matrix.toLin' P) hu
      simp only [hPP'] at h2
      exact h2
    rw [LinearMap.mem_range]
    exact ⟨Matrix.toLin' Q' u, hCX⟩
  · intro hCker v hvA
    have hwker : Matrix.toLin' (P * A * Q) (Matrix.toLin' Q' v) = 0 := by
      have h0 : Matrix.toLin' P' (Matrix.toLin' (P * A * Q) (Matrix.toLin' Q' v))
          = 0 := by
        rw [← hAapply]
        exact hvA
      exact (hP'ker _).mp h0
    have hX'range := hCker _ hwker
    rw [LinearMap.mem_range] at hX'range
    obtain ⟨z, hz⟩ := hX'range
    rw [LinearMap.mem_range]
    refine ⟨Matrix.toLin' Q z, ?_⟩
    rw [hAapply, hQ'Q, hXapply, hz]

/-- The explicit kernel-to-image condition for first-order rank preservation. -/
theorem mem_tangent_iff {k : Type*} [Field k] {m n r : ℕ}
    (A B : Matrix (Fin m) (Fin n) k)
    (hA : Matrix.rank A = r) (hrm : r < m) (hrn : r < n) :
    (fun ij ↦ B ij.1 ij.2) ∈ tangent r A ↔
      ∀ v : Fin n → k, (Matrix.toLin' A) v = 0 →
        (Matrix.toLin' B) v ∈ LinearMap.range (Matrix.toLin' A) := by
  obtain ⟨P, P', Q, Q', hP, hP', hQ, hQ', hPAQ⟩ :=
    exists_normalForm_fin A hA hrm hrn
  have htanA : (fun ij ↦ B ij.1 ij.2) ∈ tangent r A ↔
      ∀ (I : Fin (r + 1) ↪ Fin m) (J : Fin (r + 1) ↪ Fin n),
        leibnizDiff (fun i ↦ I i) (fun i ↦ J i) A B = 0 := by
    rw [mem_tangent_iff_forall A B hA]
    constructor
    · intro h I J
      rw [← differential_minor_apply]
      exact h I J
    · intro h I J
      rw [differential_minor_apply]
      exact h I J
  have htanC : (fun ij ↦ (P * B * Q) ij.1 ij.2) ∈
      tangent r (canonicalMatrix (K := k) m n r) ↔
      ∀ (I : Fin (r + 1) ↪ Fin m) (J : Fin (r + 1) ↪ Fin n),
        leibnizDiff (fun i ↦ I i) (fun i ↦ J i)
          (canonicalMatrix (K := k) m n r) (P * B * Q) = 0 := by
    rw [mem_canonical_tangent_iff_forall]
    constructor
    · intro h I J
      rw [← differential_minor_apply]
      exact h I J
    · intro h I J
      rw [differential_minor_apply]
      exact h I J
  have hAeqM : P' * (P * A * Q) * Q' = A := by
    have h1 : P' * (P * A * Q) * Q' = (P' * P) * A * (Q * Q') := by
      simp only [Matrix.mul_assoc]
    rw [h1, hP', hQ, Matrix.one_mul, Matrix.mul_one]
  have hXeqM : P' * (P * B * Q) * Q' = B := by
    have h1 : P' * (P * B * Q) * Q' = (P' * P) * B * (Q * Q') := by
      simp only [Matrix.mul_assoc]
    rw [h1, hP', hQ, Matrix.one_mul, Matrix.mul_one]
  have htrans : (∀ (I : Fin (r + 1) ↪ Fin m) (J : Fin (r + 1) ↪ Fin n),
      leibnizDiff (fun i ↦ I i) (fun i ↦ J i) A B = 0) ↔
      (∀ (I : Fin (r + 1) ↪ Fin m) (J : Fin (r + 1) ↪ Fin n),
        leibnizDiff (fun i ↦ I i) (fun i ↦ J i) (P * A * Q) (P * B * Q) = 0) := by
    constructor
    · intro h I J
      exact leibnizDiff_transport_vanishing P Q A B h _ _
    · intro h I J
      rw [← hAeqM, ← hXeqM]
      exact leibnizDiff_transport_vanishing P' Q' (P * A * Q) (P * B * Q) h _ _
  have hLiff : (∀ (I : Fin (r + 1) ↪ Fin m) (J : Fin (r + 1) ↪ Fin n),
      leibnizDiff (fun i ↦ I i) (fun i ↦ J i) A B = 0) ↔
      (fun ij ↦ (P * B * Q) ij.1 ij.2) ∈
        tangent r (canonicalMatrix (K := k) m n r) := by
    rw [htrans, hPAQ]
    exact htanC.symm
  rw [htanA, hLiff, canonical_mem_tangent_iff hrm hrn, ← hPAQ]
  exact (kerIm_transport P P' Q Q' hP hP' hQ hQ' A B).symm

end WantedExt.AlgebraicGeometry.DeterminantalTangentWanted
