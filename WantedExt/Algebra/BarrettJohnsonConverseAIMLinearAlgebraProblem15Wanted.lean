/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# The converse of the Barrett-Johnson inequalities for totally nonnegative matrices (AimPL 1.55)

AimPL, Theory and applications of total positivity, Problem 1.55 (A. Khare): for partitions `λ =
(λ₁, …, λ_r)`, `μ = (μ₁, …, μ_r)` of `n`, if `μ` majorizes `λ` then for all TN matrices `A`, `λ₁! ⋯
λ_r! ∑_I ∏_k det A_{I_k × I_k} ≥ μ₁! ⋯ μ_r! ∑_J ∏_k det A_{J_k × J_k}`, the sums over partitions `I
= (I₁, …, I_r)`, `J` of `[n]` with `|I_k| = λ_k`, `|J_k| = μ_k`. Is the converse true? The list
adds: this has now been answered affirmatively.
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Basic.Real.Basic
public import Mathlib.LinearAlgebra.Matrix.Determinant.TotallyNonneg

@[expose] public section

namespace MathlibExt.Algebra.BarrettJohnsonConverseAIMLinearAlgebraProblem15Wanted

/-!
Source: AimPL: Theory and applications of total positivity, Problem 1.55 (A. Khare),
http://aimpl.org/totalpos/1/ (remark: 'This has now been answered affirmatively.'). UnsolvedMath
record UM-20002221 (`AIM-LINEAR_ALGEBRA-0015`), dataset ulamai/UnsolvedMath v1.8.0.

`λ` and `μ` are nonincreasing sequences of `r ≥ 1` nonnegative integers summing to `n ≥ 1` (zero
parts let two partitions share the length `r`; they change neither side). The sums run over ordered
set partitions `(I₁, …, I_r)` of `{1, …, n}` with `|I_k| = λ_k`, encoded as maps `f : Fin n → Fin r`
with `|f⁻¹(k)| = λ_k`, as in Skandera and Soskin. Totally nonnegative is Mathlib's
`Matrix.IsTotallyNonneg` (every minor with increasing rows and columns is `≥ 0`). `μ` majorizes `λ`
means `λ₁ + ⋯ + λᵢ ≤ μ₁ + ⋯ + μᵢ` for all `i`. A numerical check with random totally positive and
totally nonnegative matrices for `n ≤ 4` found the forward inequality always and a violating matrix
for every non-majorized pair.
-/

/-- `λ₁! ⋯ λ_r! ∑ det A[I₁] ⋯ det A[I_r]`, the sum over the ordered set partitions `(I₁, …, I_r)`
of `{1, …, n}` with `|I_k| = λ_k` (encoded as the maps `f : Fin n → Fin r` with `|f⁻¹(k)| = λ_k`),
where `A[I]` is the principal submatrix of `A` on the rows and columns in `I`. -/
noncomputable def symmetrizedFischerProduct {n r : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (lam : Fin r → ℕ) : ℝ :=
  (∏ k, ((lam k).factorial : ℝ)) *
    ∑ f : Fin n → Fin r with ∀ k, (Finset.univ.filter fun i => f i = k).card = lam k,
      ∏ k, (A.submatrix (fun i : {i // f i = k} => i.1) (fun i => i.1)).det

/-- AimPL Theory and applications of total positivity, Problem 1.55, as a claim: if `λ` and `μ` are
nonincreasing sequences of `r` nonnegative integers summing to `n ≥ 1` and
`λ₁! ⋯ λ_r! ∑_I ∏ det A[I_k] ≥ μ₁! ⋯ μ_r! ∑_J ∏ det A[J_k]` for every totally nonnegative real
`n × n` matrix `A`, then `μ` majorizes `λ`: `λ₁ + ⋯ + λᵢ ≤ μ₁ + ⋯ + μᵢ` for every `i`. -/
def barrettJohnsonConverse : Prop :=
  ∀ (n r : ℕ) (lam mu : Fin r → ℕ), 1 ≤ n → 1 ≤ r → Antitone lam → Antitone mu →
    ∑ k, lam k = n → ∑ k, mu k = n →
    (∀ A : Matrix (Fin n) (Fin n) ℝ, A.IsTotallyNonneg →
      symmetrizedFischerProduct A mu ≤ symmetrizedFischerProduct A lam) →
    ∀ i : ℕ, ∑ k : Fin r with k.val < i, lam k ≤ ∑ k : Fin r with k.val < i, mu k

/--
Resolved true: Skandera and Soskin proved (Theorem 5.2) that `λ₁! ⋯ λ_r! ∑_I ∏ det A[I_k] ≥ μ₁! ⋯
μ_r! ∑_J ∏ det A[J_k]` holds for every totally nonnegative `A` if and only if `λ` is majorized by
`μ`; for the converse, a totally nonnegative matrix built from `μ` makes the left side `0` and the
right side positive. AimPL records the converse as answered affirmatively. Source: AimPL: Theory and
applications of total positivity, Problem 1.55 (A. Khare), http://aimpl.org/totalpos/1/ (remark:
'This has now been answered affirmatively.'); resolution: M. Skandera and D. Soskin, Barrett-Johnson
inequalities for totally nonnegative matrices, Linear Multilinear Algebra 73 (2025), no. 10,
2320-2343, arXiv:2209.06466, Theorem 5.2 of the journal version (authors' copy
https://www.lehigh.edu/~mas906/papers/fischer.pdf): for partitions λ = (λ₁, …, λ_r), μ = (μ₁, …,
μ_s) of n, λ₁!⋯λ_r! ∑ det(A_{I₁,I₁})⋯det(A_{I_r,I_r}) ≥ μ₁!⋯μ_s! ∑ det(A_{J₁,J₁})⋯det(A_{J_s,J_s})
for all TNN A if and only if λ ⪯ μ, the converse by the matrix A = B(μ^⊤), on which the left side is
0 and the right side positive (Proposition 3.1); arXiv v3 states only the forward direction; AimPL
records the converse as answered affirmatively, https://doi.org/10.1080/03081087.2024.2446784.
-/
public theorem_wanted barrettJohnsonConverse_holds : barrettJohnsonConverse

end MathlibExt.Algebra.BarrettJohnsonConverseAIMLinearAlgebraProblem15Wanted
