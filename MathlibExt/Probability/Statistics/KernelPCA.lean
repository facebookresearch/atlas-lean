/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# Kernel principal component analysis

Kernel PCA (Schölkopf, Smola and Müller 1998) performs principal component analysis in a
feature space `F`, a real inner product space reached through a feature map `Φ : X → F`, using
only the kernel `k(x, y) = ⟪Φ(x), Φ(y)⟫`. For feature vectors `Φ(x₁), …, Φ(x_M)` the
covariance operator is `C̄ V = (1/M) ∑ⱼ ⟪Φ(xⱼ), V⟫ Φ(xⱼ)` (`covOp`, equation (2.5)), and the
Gram matrix is `K i j = k(xᵢ, xⱼ)` (`gram`, equation (2.10)). The paper assumes the feature
vectors centred, so that `C̄` is their covariance; the algebra below does not use centring, and
centred data are handled by applying it to the centred feature vectors (the paper's
Appendix B).

## Main results

* `mem_span_of_covOp_eq_smul`: an eigenvector of `C̄` with nonzero eigenvalue lies in the span
  of the feature vectors (the claim before equation (2.8)).
* `gram_mulVec_eq_of_covOp_eq_smul`: for `V = ∑ᵢ αᵢ Φ(xᵢ)`, `λ V = C̄ V` implies
  `M λ K α = K² α` (equation (2.11)).
* `covOp_eq_smul_of_gram_mulVec_eq`: conversely, a solution of `M λ α = K α` (equation (2.12))
  gives an eigenvector `V = ∑ᵢ αᵢ Φ(xᵢ)` of `C̄` with eigenvalue `λ`.
* `exists_gram_mulVec_eq_of_covOp_eq_smul`: every eigenvector with `λ ≠ 0` is of that form
  (the justification of Appendix A), so the nonzero spectrum of `C̄` is computed from `K`.
* `norm_sq_expansion` and `norm_sq_expansion_of_gram_mulVec_eq`: `‖V‖² = α ⬝ K α`, which equals
  `M λ (α ⬝ α)` for a solution of (2.12) (equation (2.14)).
* `inner_expansion_featureMap`: the principal-component projections
  `⟪V, Φ(x)⟫ = ∑ᵢ αᵢ k(xᵢ, x)` need only kernel evaluations (equation (2.15)).
* `centredFeature`, `sum_centredFeature` and `gram_centredFeature`: centring in feature space,
  `K̃ = K - 1_M K - K 1_M + 1_M K 1_M` (Appendix B, equations (B.1) and (B.3)).

## References

* B. Schölkopf, A. Smola and K.-R. Müller, "Nonlinear component analysis as a kernel
  eigenvalue problem", *Neural Comput.* **10** (1998), 1299–1319, Section 2.
-/

@[expose] public section

open Matrix
open scoped InnerProductSpace

namespace MathlibExt.Probability.Statistics.KernelPCA

variable {X F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {M : ℕ}

/-- **Covariance operator in feature space** (Schölkopf, Smola and Müller, *Nonlinear component
analysis as a kernel eigenvalue problem*, Neural Comput. 10 (1998), equation (2.5)). For feature
vectors `Φ(x₁), …, Φ(x_M)` it is `C̄ V = (1/M) ∑ⱼ ⟪Φ(xⱼ), V⟫ Φ(xⱼ)`. For an empty sample
(`M = 0`) it is the zero map (`0⁻¹ = 0`), not the covariance of any data. -/
noncomputable def covOp (Φ : X → F) (x : Fin M → X) (V : F) : F :=
  (M : ℝ)⁻¹ • ∑ j, ⟪Φ (x j), V⟫_ℝ • Φ (x j)

/-- **Kernel Gram matrix** (Schölkopf, Smola and Müller, *Nonlinear component analysis as a
kernel eigenvalue problem*, Neural Comput. 10 (1998), equation (2.10)): `K i j = ⟪Φ(xᵢ), Φ(xⱼ)⟫`,
the kernel `k(xᵢ, xⱼ)`. It agrees with Mathlib's `Matrix.gram` (`gram_eq_matrixGram`). -/
def gram (Φ : X → F) (x : Fin M → X) : Matrix (Fin M) (Fin M) ℝ :=
  Matrix.of fun i j => ⟪Φ (x i), Φ (x j)⟫_ℝ

/-- **The kernel PCA Gram matrix is Mathlib's Gram matrix.** `gram Φ x` is
`Matrix.gram ℝ (fun i => Φ (xᵢ))`, the matrix of inner products of the feature vectors
(Schölkopf, Smola and Müller, *Nonlinear component analysis as a kernel eigenvalue problem*,
Neural Comput. 10 (1998), equation (2.10)); in particular it is positive semidefinite. -/
theorem gram_eq_matrixGram (Φ : X → F) (x : Fin M → X) :
    gram Φ x = Matrix.gram ℝ (fun i => Φ (x i)) :=
  rfl

/-- **The kernel PCA Gram matrix is positive semidefinite**, as a Gram matrix of feature
vectors (Schölkopf, Smola and Müller, *Nonlinear component analysis as a kernel eigenvalue
problem*, Neural Comput. 10 (1998), equations (2.10) and (2.12): the eigenvalues `M λ` of `K`
are nonnegative). -/
theorem posSemidef_gram (Φ : X → F) (x : Fin M → X) : (gram Φ x).PosSemidef := by
  rw [gram_eq_matrixGram]
  exact Matrix.posSemidef_gram ℝ _

/-- **Kernel expansion in feature space** (Schölkopf, Smola and Müller, *Nonlinear component
analysis as a kernel eigenvalue problem*, Neural Comput. 10 (1998), equation (2.8)):
`V = ∑ᵢ αᵢ Φ(xᵢ)`. -/
def expansion (Φ : X → F) (x : Fin M → X) (α : Fin M → ℝ) : F :=
  ∑ i, α i • Φ (x i)

/-- **Inner products of a kernel expansion.** `⟪∑ᵢ αᵢ Φ(xᵢ), W⟫ = ∑ᵢ αᵢ ⟪Φ(xᵢ), W⟫`
(Schölkopf, Smola and Müller, *Nonlinear component analysis as a kernel eigenvalue problem*,
Neural Comput. 10 (1998), equations (2.9) and (2.14)). -/
theorem inner_expansion_left (Φ : X → F) (x : Fin M → X) (α : Fin M → ℝ) (W : F) :
    ⟪expansion Φ x α, W⟫_ℝ = ∑ i, α i * ⟪Φ (x i), W⟫_ℝ := by
  simp [expansion, sum_inner, real_inner_smul_left]

/-- **Kernel PCA projections** (Schölkopf, Smola and Müller, *Nonlinear component analysis as a
kernel eigenvalue problem*, Neural Comput. 10 (1998), equation (2.15)). The projection of a
test point onto `V = ∑ᵢ αᵢ Φ(xᵢ)` is `⟪V, Φ(t)⟫ = ∑ᵢ αᵢ k(xᵢ, t)`, computed from kernel values
only. -/
theorem inner_expansion_featureMap (Φ : X → F) (x : Fin M → X) (α : Fin M → ℝ) (t : X) :
    ⟪expansion Φ x α, Φ t⟫_ℝ = ∑ i, α i * ⟪Φ (x i), Φ t⟫_ℝ :=
  inner_expansion_left Φ x α (Φ t)

/-- **Feature vectors against a kernel expansion.** `⟪Φ(x_k), ∑ᵢ αᵢ Φ(xᵢ)⟫ = (K α)_k`
(Schölkopf, Smola and Müller, *Nonlinear component analysis as a kernel eigenvalue problem*,
Neural Comput. 10 (1998), equations (2.9)–(2.10)). -/
theorem inner_featureMap_expansion (Φ : X → F) (x : Fin M → X) (α : Fin M → ℝ) (k : Fin M) :
    ⟪Φ (x k), expansion Φ x α⟫_ℝ = (gram Φ x *ᵥ α) k := by
  simp [expansion, inner_sum, real_inner_smul_right, gram, mulVec, dotProduct, mul_comm]

/-- **The covariance operator on kernel expansions.**
`C̄ (∑ᵢ αᵢ Φ(xᵢ)) = (1/M) ∑ᵢ (K α)ᵢ Φ(xᵢ)` (Schölkopf, Smola and Müller, *Nonlinear component
analysis as a kernel eigenvalue problem*, Neural Comput. 10 (1998), equation (2.9)). -/
theorem covOp_expansion (Φ : X → F) (x : Fin M → X) (α : Fin M → ℝ) :
    covOp Φ x (expansion Φ x α) = (M : ℝ)⁻¹ • expansion Φ x (gram Φ x *ᵥ α) := by
  simp only [covOp, inner_featureMap_expansion]
  rfl

/-- **Eigenvectors with nonzero eigenvalue lie in the span of the data** (Schölkopf, Smola and
Müller, *Nonlinear component analysis as a kernel eigenvalue problem*, Neural Comput. 10 (1998),
Section 2, before equation (2.8)). If `C̄ V = λ V` with `λ ≠ 0`, then `V` lies in the span of
`Φ(x₁), …, Φ(x_M)`. -/
theorem mem_span_of_covOp_eq_smul (Φ : X → F) (x : Fin M → X) {V : F} {lam : ℝ}
    (hlam : lam ≠ 0) (hV : covOp Φ x V = lam • V) :
    V ∈ Submodule.span ℝ (Set.range fun i => Φ (x i)) := by
  have hV' : V = lam⁻¹ • covOp Φ x V := by
    rw [hV, smul_smul, inv_mul_cancel₀ hlam, one_smul]
  rw [hV', covOp]
  refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun j _ => ?_))
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

/-- **The kernel PCA eigenvalue equation in coefficient form** (Schölkopf, Smola and Müller,
*Nonlinear component analysis as a kernel eigenvalue problem*, Neural Comput. 10 (1998),
equations (2.9)–(2.11)). For `V = ∑ᵢ αᵢ Φ(xᵢ)`, `λ V = C̄ V` implies `M λ K α = K² α`. -/
theorem gram_mulVec_eq_of_covOp_eq_smul (Φ : X → F) (x : Fin M → X) {α : Fin M → ℝ}
    {lam : ℝ} (hV : covOp Φ x (expansion Φ x α) = lam • expansion Φ x α) :
    ((M : ℝ) * lam) • (gram Φ x *ᵥ α) = gram Φ x *ᵥ (gram Φ x *ᵥ α) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · funext k
    exact k.elim0
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  funext k
  have h := congrArg (fun W => ⟪Φ (x k), W⟫_ℝ) hV
  simp only [covOp_expansion, real_inner_smul_right, inner_featureMap_expansion] at h
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [mul_assoc, ← h, ← mul_assoc, mul_inv_cancel₀ hM', one_mul]

/-- **Solutions of the Gram-matrix eigenproblem are kernel principal axes** (Schölkopf, Smola
and Müller, *Nonlinear component analysis as a kernel eigenvalue problem*, Neural Comput. 10
(1998), equation (2.12)). If `M λ α = K α`, then `V = ∑ᵢ αᵢ Φ(xᵢ)` satisfies `C̄ V = λ V`. -/
theorem covOp_eq_smul_of_gram_mulVec_eq (Φ : X → F) (x : Fin M → X) {α : Fin M → ℝ}
    {lam : ℝ} (hα : ((M : ℝ) * lam) • α = gram Φ x *ᵥ α) :
    covOp Φ x (expansion Φ x α) = lam • expansion Φ x α := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp [covOp, expansion]
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  rw [covOp_expansion, ← hα]
  simp only [expansion, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1
  field_simp

/-- **Every kernel principal axis comes from the Gram-matrix eigenproblem** (Schölkopf, Smola
and Müller, *Nonlinear component analysis as a kernel eigenvalue problem*, Neural Comput. 10
(1998), Appendix A). If `C̄ V = λ V` with `λ ≠ 0`, then `V = ∑ᵢ αᵢ Φ(xᵢ)` for some `α` with
`M λ α = K α`. -/
theorem exists_gram_mulVec_eq_of_covOp_eq_smul (Φ : X → F) (x : Fin M → X) {V : F} {lam : ℝ}
    (hlam : lam ≠ 0) (hV : covOp Φ x V = lam • V) :
    ∃ α : Fin M → ℝ, V = expansion Φ x α ∧ ((M : ℝ) * lam) • α = gram Φ x *ᵥ α := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · refine ⟨0, ?_, by funext k; exact k.elim0⟩
    have h0 : lam • V = 0 := by rw [← hV]; simp [covOp]
    simpa [expansion, hlam] using h0
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  -- the coefficients `αᵢ = ⟪Φ(xᵢ), V⟫ / (M λ)`
  set β : Fin M → ℝ := fun i => ⟪Φ (x i), V⟫_ℝ
  have hVβ : V = expansion Φ x (((M : ℝ) * lam)⁻¹ • β) := by
    have : covOp Φ x V = (M : ℝ)⁻¹ • expansion Φ x β := by
      simp only [covOp, expansion, β]
    have h2 : V = lam⁻¹ • covOp Φ x V := by
      rw [hV, smul_smul, inv_mul_cancel₀ hlam, one_smul]
    rw [h2, this]
    simp only [expansion, Pi.smul_apply, smul_eq_mul, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    field_simp
  refine ⟨((M : ℝ) * lam)⁻¹ • β, hVβ, ?_⟩
  have hβ : β = gram Φ x *ᵥ (((M : ℝ) * lam)⁻¹ • β) := by
    funext k
    rw [← inner_featureMap_expansion, ← hVβ]
  have hβ' : gram Φ x *ᵥ (((M : ℝ) * lam)⁻¹ • β) = β := hβ.symm
  rw [hβ', smul_smul, mul_inv_cancel₀ (mul_ne_zero hM' hlam), one_smul]

/-- **Squared norm of a kernel expansion** (Schölkopf, Smola and Müller, *Nonlinear component
analysis as a kernel eigenvalue problem*, Neural Comput. 10 (1998), equation (2.14), first
equality): `‖∑ᵢ αᵢ Φ(xᵢ)‖² = α ⬝ K α`. -/
theorem norm_sq_expansion (Φ : X → F) (x : Fin M → X) (α : Fin M → ℝ) :
    ‖expansion Φ x α‖ ^ 2 = α ⬝ᵥ (gram Φ x *ᵥ α) := by
  rw [← real_inner_self_eq_norm_sq, inner_expansion_left]
  simp only [inner_featureMap_expansion, dotProduct]

/-- **Normalization of kernel principal axes** (Schölkopf, Smola and Müller, *Nonlinear
component analysis as a kernel eigenvalue problem*, Neural Comput. 10 (1998), equation (2.14)).
If `M λ α = K α`, then `‖∑ᵢ αᵢ Φ(xᵢ)‖² = M λ (α ⬝ α)`; so `V` has unit norm exactly when
`M λ (α ⬝ α) = 1`. -/
theorem norm_sq_expansion_of_gram_mulVec_eq (Φ : X → F) (x : Fin M → X) {α : Fin M → ℝ}
    {lam : ℝ} (hα : ((M : ℝ) * lam) • α = gram Φ x *ᵥ α) :
    ‖expansion Φ x α‖ ^ 2 = ((M : ℝ) * lam) * (α ⬝ᵥ α) := by
  rw [norm_sq_expansion, ← hα, dotProduct_smul, smul_eq_mul]

/-! ### Centring in feature space -/

/-- **Centred feature vectors** (Schölkopf, Smola and Müller, *Nonlinear component analysis as a
kernel eigenvalue problem*, Neural Comput. 10 (1998), Appendix B, equation (B.1)):
`Φ̃(xᵢ) = Φ(xᵢ) - (1/M) ∑ₘ Φ(xₘ)`. -/
noncomputable def centredFeature (Φ : X → F) (x : Fin M → X) (i : Fin M) : F :=
  Φ (x i) - (M : ℝ)⁻¹ • ∑ m, Φ (x m)

/-- **The centred feature vectors are centred** (Schölkopf, Smola and Müller, *Nonlinear
component analysis as a kernel eigenvalue problem*, Neural Comput. 10 (1998), Appendix B):
`∑ᵢ Φ̃(xᵢ) = 0`. -/
theorem sum_centredFeature (Φ : X → F) (x : Fin M → X) : ∑ i, centredFeature Φ x i = 0 := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · simp
  have hM' : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  simp only [centredFeature, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin]
  rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, mul_inv_cancel₀ hM', one_smul, sub_self]

/-- **The centred Gram matrix** (Schölkopf, Smola and Müller, *Nonlinear component analysis as a
kernel eigenvalue problem*, Neural Comput. 10 (1998), Appendix B, equation (B.3)). With
`(1_M)ᵢⱼ = 1/M`, the Gram matrix of the centred feature vectors is
`K̃ = K - 1_M K - K 1_M + 1_M K 1_M`, computed from the kernel values alone. -/
theorem gram_centredFeature (Φ : X → F) (x : Fin M → X) :
    gram (centredFeature Φ x) id =
      gram Φ x - Matrix.of (fun _ _ => (M : ℝ)⁻¹) * gram Φ x -
        gram Φ x * Matrix.of (fun _ _ => (M : ℝ)⁻¹) +
        Matrix.of (fun _ _ => (M : ℝ)⁻¹) * gram Φ x * Matrix.of (fun _ _ => (M : ℝ)⁻¹) := by
  ext i j
  simp only [gram, centredFeature, id, Matrix.of_apply, Matrix.sub_apply, Matrix.add_apply,
    Matrix.mul_apply, inner_sub_left, inner_sub_right, real_inner_smul_left,
    real_inner_smul_right, sum_inner, inner_sum, Finset.sum_mul, Finset.mul_sum]
  ring_nf

end MathlibExt.Probability.Statistics.KernelPCA
