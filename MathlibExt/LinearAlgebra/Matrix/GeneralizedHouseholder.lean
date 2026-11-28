/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.InnerProductSpace.Projection.Reflection
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
public import MathlibExt.LinearAlgebra.Matrix.DeterminantLemma

/-!
# Generalized Householder matrices

For a real vector `v` indexed by a finite type `n` and a real number `β`, the matrix
`1 - β • vecMulVec v v` is `H = I - β v vᵀ`. It multiplies `v` by `1 - β (vᵀ v)` and fixes every
vector orthogonal to `v`; the results below follow from these two facts. No hypothesis on `v` is
needed: for a unit vector, `vᵀ v = 1`.

## Main results

* `Matrix.one_sub_smul_vecMulVec_mulVec_self` and
  `Matrix.one_sub_smul_vecMulVec_mulVec_of_dotProduct_eq_zero`: `H v = (1 - β vᵀ v) v`, and
  `H w = w` when `vᵀ w = 0`.
* `Matrix.det_one_sub_smul_vecMulVec`: `det H = 1 - β vᵀ v`, from the matrix determinant lemma
  `Matrix.det_add_vecMulVec`.
* `Matrix.charpoly_one_sub_smul_vecMulVec`: on a nonempty index type, the characteristic
  polynomial of `H` is `(X - 1) ^ (card n - 1) * (X - (1 - β vᵀ v))`, from
  `Matrix.charpoly_vecMulVec` and `Matrix.charpoly_sub_scalar`.
* `Matrix.spectrum_one_sub_smul_vecMulVec`: with at least two indices, the spectrum of `H` is
  `{1, 1 - β vᵀ v}`.
* `Matrix.eigenspace_toEuclideanLin_one_sub_smul_vecMulVec_one` and
  `Matrix.eigenspace_toEuclideanLin_one_sub_smul_vecMulVec_one_sub`: for `β ≠ 0`, the eigenspace
  of `H`, acting on `EuclideanSpace ℝ n`, at the scalar `1` (the subspace `H` fixes) is the
  orthogonal complement of `v`, which is zero in dimension one when `v ≠ 0`; for `v ≠ 0` the
  eigenspace for the eigenvalue `1 - β vᵀ v` is the line spanned by `v`.
* `Matrix.norm_toLp_one_sub_smul_vecMulVec_mulVec_sq`: in the Euclidean norm,
  `‖H x‖² = ‖x‖² - β (2 - β vᵀ v) (vᵀ x)²`.
* `Matrix.l2_opNorm_one_sub_smul_vecMulVec_le_one_iff`: the operator norm of `H` for the
  Euclidean norm (`Matrix.Norms.L2Operator`) is at most `1` if and only if `0 ≤ β vᵀ v ≤ 2`.
* `Matrix.toEuclideanLin_one_sub_smul_vecMulVec_eq_starProjection` and
  `Matrix.toEuclideanLin_one_sub_smul_vecMulVec_eq_reflection`: `H` is the orthogonal projection
  onto the orthogonal complement of `v` when `β vᵀ v = 1`, and the reflection across it
  (`Submodule.reflection`) when `β vᵀ v = 2`.

## References

* R. Grazzi, J. Siems, A. Zela, J. K. H. Franke, F. Hutter and M. Pontil, "Unlocking
  State-Tracking in Linear RNNs Through Negative Eigenvalues", ICLR 2025, arXiv:2411.12537
  (version 5). For a unit vector `v`, Section 4.2 states the eigenvalues of `I - β v vᵀ` for
  `β = φ` and, in its equation (2), `β = 2 φ`, where `φ ∈ [0, 1]`. Section 4.3, equation (3),
  defines products of such matrices and notes that `β = 2` gives a reflection, and
  Proposition 1, item 1, bounds the norm of these products by `1` when each `1 - β` lies in
  `[-1, 1]`. The statements here, for any `v`, and the converse of the norm bound for one matrix
  are derived directly.
-/

@[expose] public section

namespace Matrix

open Polynomial WithLp

variable {n : Type*} [Fintype n] [DecidableEq n]

private theorem one_sub_smul_vecMulVec_mulVec (β : ℝ) (v x : n → ℝ) :
    (1 - β • vecMulVec v v) *ᵥ x = x - (β * (v ⬝ᵥ x)) • v := by
  rw [sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul, smul_smul]

/-- **A generalized Householder matrix scales its vector.** Let $v$ be a real vector indexed by a
finite set, let $\beta \in \mathbb{R}$ and let $H = I - \beta v v^{\mathsf{T}}$. Then
$H v = (1 - \beta\, v^{\mathsf{T}} v)\, v$. -/
theorem one_sub_smul_vecMulVec_mulVec_self (β : ℝ) (v : n → ℝ) :
    (1 - β • vecMulVec v v) *ᵥ v = (1 - β * (v ⬝ᵥ v)) • v := by
  rw [one_sub_smul_vecMulVec_mulVec, sub_smul, one_smul]

/-- **A generalized Householder matrix fixes the vectors orthogonal to its vector.** Let $v$ be a
real vector indexed by a finite set, let $\beta \in \mathbb{R}$ and let
$H = I - \beta v v^{\mathsf{T}}$. Every real vector $w$ with the same index set and
$v^{\mathsf{T}} w = 0$ satisfies $H w = w$. -/
theorem one_sub_smul_vecMulVec_mulVec_of_dotProduct_eq_zero (β : ℝ) {v w : n → ℝ}
    (h : v ⬝ᵥ w = 0) : (1 - β • vecMulVec v v) *ᵥ w = w := by
  rw [one_sub_smul_vecMulVec_mulVec, h, mul_zero, zero_smul, sub_zero]

/-- **Determinant of a generalized Householder matrix.** Let $v$ be a real vector indexed by a
finite set, let $\beta \in \mathbb{R}$ and let $H = I - \beta v v^{\mathsf{T}}$. Then
$\det H = 1 - \beta\, v^{\mathsf{T}} v$. -/
theorem det_one_sub_smul_vecMulVec (β : ℝ) (v : n → ℝ) :
    (1 - β • vecMulVec v v).det = 1 - β * (v ⬝ᵥ v) := by
  rw [sub_eq_add_neg, ← neg_smul, ← smul_vecMulVec, det_add_vecMulVec, det_one, adjugate_one,
    one_mulVec, dotProduct_smul, smul_eq_mul, neg_mul, ← sub_eq_add_neg]

/-- **Characteristic polynomial of a generalized Householder matrix.** Let $v$ be a real vector
indexed by a finite set with $n \ge 1$ elements, let $\beta \in \mathbb{R}$ and let
$H = I - \beta v v^{\mathsf{T}}$. The characteristic polynomial of $H$ is
$(X - 1)^{n - 1} \bigl(X - (1 - \beta\, v^{\mathsf{T}} v)\bigr)$. -/
theorem charpoly_one_sub_smul_vecMulVec [Nonempty n] (β : ℝ) (v : n → ℝ) :
    (1 - β • vecMulVec v v).charpoly =
      (X - 1) ^ (Fintype.card n - 1) * (X - C (1 - β * (v ⬝ᵥ v))) := by
  have h : (1 - β • vecMulVec v v : Matrix n n ℝ) = vecMulVec (-β • v) v - scalar n (-1) := by
    rw [map_neg, map_one, sub_neg_eq_add, smul_vecMulVec, neg_smul]
    abel
  obtain ⟨k, hk⟩ : ∃ k, Fintype.card n = k + 1 :=
    ⟨_, (Nat.sub_add_cancel Fintype.card_pos).symm⟩
  rw [h, charpoly_sub_scalar, charpoly_vecMulVec, hk, Nat.add_sub_cancel]
  simp only [sub_comp, pow_comp, X_comp, smul_comp, smul_dotProduct, smul_eq_mul, map_neg,
    map_one]
  simp only [smul_eq_C_mul, map_neg, map_mul, map_sub, map_one]
  ring

/-- **Spectrum of a generalized Householder matrix.** Let $v$ be a real vector indexed by a finite
set with $n \ge 2$ elements, let $\beta \in \mathbb{R}$ and let $H = I - \beta v v^{\mathsf{T}}$.
The real spectrum of $H$ is $\{1, 1 - \beta\, v^{\mathsf{T}} v\}$.

Source: R. Grazzi, J. Siems, A. Zela, J. K. H. Franke, F. Hutter and M. Pontil, "Unlocking
State-Tracking in Linear RNNs Through Negative Eigenvalues", ICLR 2025, arXiv:2411.12537
(version 5), Section 4.2, for a unit vector $v$ and $\beta \in [0, 2]$. -/
theorem spectrum_one_sub_smul_vecMulVec (hn : 1 < Fintype.card n) (β : ℝ) (v : n → ℝ) :
    spectrum ℝ (1 - β • vecMulVec v v) = {1, 1 - β * (v ⬝ᵥ v)} := by
  have : Nonempty n := Fintype.card_pos_iff.mp (by omega)
  ext μ
  rw [mem_spectrum_iff_isRoot_charpoly, charpoly_one_sub_smul_vecMulVec, IsRoot.def]
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_one, eval_C]
  rw [mul_eq_zero, pow_eq_zero_iff (by omega), sub_eq_zero, sub_eq_zero, Set.mem_insert_iff,
    Set.mem_singleton_iff]

omit [DecidableEq n] in
private theorem norm_toLp_sq (y : n → ℝ) : ‖toLp 2 y‖ ^ 2 = y ⬝ᵥ y := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp, star_trivial]

omit [DecidableEq n] in
private theorem inner_toLp (v y : n → ℝ) : inner ℝ (toLp 2 v) (toLp 2 y) = v ⬝ᵥ y := by
  rw [EuclideanSpace.inner_toLp_toLp, star_trivial, dotProduct_comm]

/-- **Fixed subspace of a generalized Householder matrix.** Let $v$ be a real vector indexed by a
finite set, let $\beta \ne 0$ and let $H = I - \beta v v^{\mathsf{T}}$, acting on the Euclidean
space of the same index set. The eigenspace of $H$ at the scalar $1$, that is the subspace of
vectors fixed by $H$, is the orthogonal complement $v^{\perp}$ of $v$. With one index and
$v \ne 0$ it is zero, and $1$ is then not an eigenvalue of $H$. -/
theorem eigenspace_toEuclideanLin_one_sub_smul_vecMulVec_one {β : ℝ} (hβ : β ≠ 0)
    (v : n → ℝ) :
    Module.End.eigenspace (toEuclideanLin (1 - β • vecMulVec v v)) 1 = (ℝ ∙ toLp 2 v)ᗮ := by
  ext x
  obtain ⟨y, rfl⟩ : ∃ y, toLp 2 y = x := ⟨ofLp x, rfl⟩
  rw [Module.End.mem_eigenspace_iff, one_smul, toLpLin_toLp, toLin'_apply,
    (toLp_injective 2).eq_iff, Submodule.mem_orthogonal_singleton_iff_inner_right, inner_toLp,
    one_sub_smul_vecMulVec_mulVec, sub_eq_self, smul_eq_zero, mul_eq_zero]
  constructor
  · rintro ((h | h) | rfl)
    · exact absurd h hβ
    · exact h
    · exact zero_dotProduct y
  · exact fun h => Or.inl (Or.inr h)

/-- **Eigenspace of a generalized Householder matrix for its other eigenvalue.** Let $v \ne 0$ be a
real vector indexed by a finite set, let $\beta \ne 0$ and let $H = I - \beta v v^{\mathsf{T}}$,
acting on the Euclidean space of the same index set. The eigenspace of $H$ for the eigenvalue
$1 - \beta\, v^{\mathsf{T}} v$ is the line spanned by $v$. -/
theorem eigenspace_toEuclideanLin_one_sub_smul_vecMulVec_one_sub {β : ℝ} (hβ : β ≠ 0)
    {v : n → ℝ} (hv : v ≠ 0) :
    Module.End.eigenspace (toEuclideanLin (1 - β • vecMulVec v v)) (1 - β * (v ⬝ᵥ v)) =
      ℝ ∙ toLp 2 v := by
  have hc : v ⬝ᵥ v ≠ 0 := fun h0 => hv (dotProduct_self_eq_zero.mp h0)
  ext x
  obtain ⟨y, rfl⟩ : ∃ y, toLp 2 y = x := ⟨ofLp x, rfl⟩
  rw [Module.End.mem_eigenspace_iff, toLpLin_toLp, toLin'_apply, ← toLp_smul,
    (toLp_injective 2).eq_iff, Submodule.mem_span_singleton, one_sub_smul_vecMulVec_mulVec]
  simp only [← toLp_smul, (toLp_injective 2).eq_iff]
  constructor
  · intro h
    refine ⟨(v ⬝ᵥ y) / (v ⬝ᵥ v), ?_⟩
    ext i
    have hi := congrFun h i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hi ⊢
    have h1 : β * ((v ⬝ᵥ v) * y i - (v ⬝ᵥ y) * v i) = 0 := by linear_combination hi
    have h2 := (mul_eq_zero.mp h1).resolve_left hβ
    rw [div_mul_eq_mul_div, div_eq_iff hc]
    linear_combination -h2
  · rintro ⟨a, rfl⟩
    ext i
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, dotProduct_smul]
    ring

/-- **Norm identity for a generalized Householder matrix.** Let $v$ be a real vector indexed by a
finite set, let $\beta \in \mathbb{R}$ and let $H = I - \beta v v^{\mathsf{T}}$. For every real
vector $x$ with the same index set, in the Euclidean norm,
$\|H x\|_2^2 = \|x\|_2^2 - \beta (2 - \beta\, v^{\mathsf{T}} v) (v^{\mathsf{T}} x)^2$. -/
theorem norm_toLp_one_sub_smul_vecMulVec_mulVec_sq (β : ℝ) (v x : n → ℝ) :
    ‖toLp 2 ((1 - β • vecMulVec v v) *ᵥ x)‖ ^ 2 =
      ‖toLp 2 x‖ ^ 2 - β * (2 - β * (v ⬝ᵥ v)) * (v ⬝ᵥ x) ^ 2 := by
  rw [norm_toLp_sq, norm_toLp_sq, one_sub_smul_vecMulVec_mulVec]
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  rw [dotProduct_comm x v]
  ring

open scoped Matrix.Norms.L2Operator in
/-- **When a generalized Householder matrix is a contraction.** Let $v$ be a real vector indexed by
a finite set, let $\beta \in \mathbb{R}$ and let $H = I - \beta v v^{\mathsf{T}}$. The operator
norm of $H$ for the Euclidean norm is at most $1$ if and only if
$0 \le \beta\, v^{\mathsf{T}} v \le 2$. -/
theorem l2_opNorm_one_sub_smul_vecMulVec_le_one_iff (β : ℝ) (v : n → ℝ) :
    ‖(1 - β • vecMulVec v v : Matrix n n ℝ)‖ ≤ 1 ↔
      0 ≤ β * (v ⬝ᵥ v) ∧ β * (v ⬝ᵥ v) ≤ 2 := by
  have hc0 : 0 ≤ v ⬝ᵥ v := Fintype.sum_nonneg fun i => mul_self_nonneg (v i)
  have hop : ∀ x : n → ℝ, ‖toLp 2 ((1 - β • vecMulVec v v) *ᵥ x)‖ ≤
      ‖(1 - β • vecMulVec v v : Matrix n n ℝ)‖ * ‖toLp 2 x‖ := fun x => by
    rw [l2_opNorm_def]
    exact ((toEuclideanLin.trans LinearMap.toContinuousLinearMap)
      (1 - β • vecMulVec v v)).le_opNorm (toLp 2 x)
  constructor
  · intro h
    rcases hc0.eq_or_lt with hc | hc
    · rw [← hc, mul_zero]
      norm_num
    have h1 : ‖toLp 2 ((1 - β • vecMulVec v v) *ᵥ v)‖ ≤ ‖toLp 2 v‖ :=
      (hop v).trans (mul_le_of_le_one_left (norm_nonneg _) h)
    have h2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    rw [norm_toLp_one_sub_smul_vecMulVec_mulVec_sq, norm_toLp_sq] at h2
    have h3 : 0 ≤ β * (v ⬝ᵥ v) * (2 - β * (v ⬝ᵥ v)) * (v ⬝ᵥ v) := by nlinarith
    have h4 : 0 ≤ β * (v ⬝ᵥ v) * (2 - β * (v ⬝ᵥ v)) := nonneg_of_mul_nonneg_left h3 hc
    constructor <;> nlinarith
  · rintro ⟨h0, h2⟩
    rw [l2_opNorm_def]
    refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
    obtain ⟨y, rfl⟩ : ∃ y, toLp 2 y = x := ⟨ofLp x, rfl⟩
    change ‖toLp 2 ((1 - β • vecMulVec v v) *ᵥ y)‖ ≤ 1 * ‖toLp 2 y‖
    rw [one_mul, ← pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero,
      norm_toLp_one_sub_smul_vecMulVec_mulVec_sq, sub_le_self_iff]
    rcases hc0.eq_or_lt with hc | hc
    · rw [(dotProduct_self_eq_zero.mp hc.symm), zero_dotProduct]
      simp
    · have hβ : 0 ≤ β := by
        by_contra! hneg
        nlinarith
      exact mul_nonneg (mul_nonneg hβ (by linarith)) (sq_nonneg _)

/-- **A generalized Householder matrix that is an orthogonal projection.** Let $v$ be a real vector
indexed by a finite set, let $\beta \in \mathbb{R}$ with $\beta\, v^{\mathsf{T}} v = 1$ and let
$H = I - \beta v v^{\mathsf{T}}$. Acting on the Euclidean space of the same index set, $H$ is the
orthogonal projection onto the orthogonal complement $v^{\perp}$ of $v$. -/
theorem toEuclideanLin_one_sub_smul_vecMulVec_eq_starProjection {β : ℝ} {v : n → ℝ}
    (h : β * (v ⬝ᵥ v) = 1) :
    ⇑(toEuclideanLin (1 - β • vecMulVec v v)) = (ℝ ∙ toLp 2 v)ᗮ.starProjection := by
  have hc : v ⬝ᵥ v ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h
    exact zero_ne_one h
  funext x
  obtain ⟨y, rfl⟩ : ∃ y, toLp 2 y = x := ⟨ofLp x, rfl⟩
  rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton,
    toLpLin_toLp, toLin'_apply, one_sub_smul_vecMulVec_mulVec, toLp_sub, toLp_smul, inner_toLp,
    norm_toLp_sq]
  have hβ : β = 1 / (v ⬝ᵥ v) := by rw [eq_div_iff hc, h]
  rw [hβ, RCLike.ofReal_real_eq_id, id, one_div_mul_eq_div]

/-- **A generalized Householder matrix that is a reflection.** Let $v$ be a real vector indexed by
a finite set, let $\beta \in \mathbb{R}$ with $\beta\, v^{\mathsf{T}} v = 2$ and let
$H = I - \beta v v^{\mathsf{T}}$. Acting on the Euclidean space of the same index set, $H$ is the
reflection across the orthogonal complement $v^{\perp}$ of $v$ (the Householder reflection). -/
theorem toEuclideanLin_one_sub_smul_vecMulVec_eq_reflection {β : ℝ} {v : n → ℝ}
    (h : β * (v ⬝ᵥ v) = 2) :
    ⇑(toEuclideanLin (1 - β • vecMulVec v v)) = (ℝ ∙ toLp 2 v)ᗮ.reflection := by
  have hc : v ⬝ᵥ v ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h
    norm_num at h
  funext x
  obtain ⟨y, rfl⟩ : ∃ y, toLp 2 y = x := ⟨ofLp x, rfl⟩
  have hβ : β = 2 / (v ⬝ᵥ v) := by rw [eq_div_iff hc, h]
  rw [Submodule.reflection_apply, two_nsmul, Submodule.starProjection_orthogonal_val,
    Submodule.starProjection_singleton, toLpLin_toLp, toLin'_apply, one_sub_smul_vecMulVec_mulVec,
    inner_toLp, norm_toLp_sq, hβ]
  apply ofLp_injective
  ext i
  simp only [RCLike.ofReal_real_eq_id, id, ofLp_add, ofLp_sub, ofLp_smul,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  field_simp
  ring

end Matrix
