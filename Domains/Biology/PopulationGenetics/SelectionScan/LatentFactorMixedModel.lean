/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.UnitaryGroup
public import MathlibExt.Analysis.InnerProductSpace.EckartYoungFrobenius

/-!
# Ridge estimates of the latent factor mixed model

Gene–environment association studies test each of `p` genetic markers, observed in `n`
individuals, for association with `d` primary (environmental) variables. The latent factor mixed
model (LFMM) writes the `n × p` response matrix `Y` as `Y = X Bᵀ + W + E`, with the `n × d`
matrix `X` of primary variables, effect sizes `B` (`p × d`), a latent confounder matrix `W` of
rank at most `K` and residuals `E`. Caye, Jumentier, Lepeule and François (LFMM 2) estimate
`(W, B)` by minimizing the ridge loss `‖Y - W - X Bᵀ‖² + λ ‖B‖²` (Frobenius norms) over
`rank W ≤ K`, and give the minimizer in closed form: for a full singular value decomposition
`X = Q Σ Rᵀ` with singular values `σ₁, …, σ_d` and
`D_λ = diag(√(λ / (λ + σ₁²)), …, √(λ / (λ + σ_d²)), 1, …, 1)`, a minimizer is
`Ŵ = Q D_λ⁻¹ svd_K(D_λ Qᵀ Y)`, `B̂ᵀ = (XᵀX + λ I)⁻¹ Xᵀ (Y - Ŵ)`, unique when the `K`-th and
`(K+1)`-th singular values of `D_λ Qᵀ Y` differ. Here `svd_K` is the rank-`K` truncated singular
value decomposition `Matrix.EckartYoungFrobenius.truncSVD`.

For fixed `W`, minimizing over `B` is ridge regression of `Y - W` on `X`, with minimum value
`‖D_λ Qᵀ (Y - W)‖²`, since `I - X (XᵀX + λ I)⁻¹ Xᵀ = Q D_λ² Qᵀ`. As `D_λ Qᵀ` is invertible,
`D_λ Qᵀ W` ranges over the matrices of rank at most `K`, and the Eckart–Young theorem
(`Matrix.EckartYoungFrobenius.isLeast_frobenius_sub_sq`, and
`Matrix.EckartYoungFrobenius.eq_truncSVD_of_frobenius_sub_sq_le` for uniqueness) gives the best
one.

## Main definitions

* `ridgeLoss` : the ridge loss `‖Y - W - X Bᵀ‖² + λ ‖B‖²`.
* `shrinkage` : the diagonal matrix `D_λ`.
* `latentEstimate`, `effectEstimate` : the estimates `Ŵ` and `B̂`.

## Main results

* `ridge_estimates` : `(Ŵ, B̂)` minimizes the ridge loss over `rank W ≤ K`, and is the only
  minimizer under the singular value gap.

## References

* K. Caye, B. Jumentier, J. Lepeule and O. François, "LFMM 2: fast and accurate inference of
  gene-environment associations in genome-wide studies", Mol. Biol. Evol. 36 (2019), 852–860,
  "L2-Regularized Least-Squares Problem" and "Ridge Estimates" (Equations (2)–(4)).
-/

@[expose] public section

namespace Domains.Biology.PopulationGenetics.LatentFactorMixedModel

open Matrix Matrix.EckartYoungFrobenius
open scoped Matrix.Norms.Frobenius

variable {n p d : ℕ}

/-- The ridge loss of the latent factor mixed model with ridge parameter `lam`:
`‖Y - W - X Bᵀ‖² + lam ‖B‖²` (Frobenius norms) for an `n × p` response matrix `Y`, an `n × d`
matrix `X` of primary variables, an `n × p` latent matrix `W` and `p × d` effect sizes `B`. -/
noncomputable def ridgeLoss (Y : Matrix (Fin n) (Fin p) ℝ) (X : Matrix (Fin n) (Fin d) ℝ)
    (lam : ℝ) (W : Matrix (Fin n) (Fin p) ℝ) (B : Matrix (Fin p) (Fin d) ℝ) : ℝ :=
  ‖Y - W - X * Bᵀ‖ ^ 2 + lam * ‖B‖ ^ 2

/-- The `n × n` shrinkage matrix `D_λ = diag(√(λ / (λ + σ₁²)), …, √(λ / (λ + σ_d²)), 1, …, 1)`
for the ridge parameter `λ = lam` and singular values `σ₁, …, σ_d`, given as
`σ 0, …, σ (d - 1)`: its diagonal entry `i` is `√(λ / (λ + (σ i)²))` for `i < d` and `1` for
`d ≤ i < n`. -/
noncomputable def shrinkage (n : ℕ) (lam : ℝ) (σ : Fin d → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  diagonal fun i => if h : i.val < d then √(lam / (lam + σ ⟨i.val, h⟩ ^ 2)) else 1

/-- The ridge estimate `Ŵ = Q D_λ⁻¹ svd_K(D_λ Qᵀ Y)` of the latent matrix, for an `n × p`
response matrix `Y`, ridge parameter `lam`, the left factor `Q` and singular values `σ` of a
singular value decomposition of the primary variables, and rank `K`, where
`D_λ = shrinkage n lam σ` and `svd_K` is the rank-`K` truncated singular value decomposition
`truncSVD`. -/
noncomputable def latentEstimate (Y : Matrix (Fin n) (Fin p) ℝ) (lam : ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (σ : Fin d → ℝ) (K : ℕ) : Matrix (Fin n) (Fin p) ℝ :=
  Q * (shrinkage n lam σ)⁻¹ * truncSVD (shrinkage n lam σ * Qᵀ * Y) K

/-- The ridge estimate of the effect sizes for a latent matrix `W`: the `p × d` matrix `B̂` with
`B̂ᵀ = (XᵀX + λ I)⁻¹ Xᵀ (Y - W)`, where `λ = lam`, the ridge regression of `Y - W` on `X`. -/
noncomputable def effectEstimate (Y : Matrix (Fin n) (Fin p) ℝ) (X : Matrix (Fin n) (Fin d) ℝ)
    (lam : ℝ) (W : Matrix (Fin n) (Fin p) ℝ) : Matrix (Fin p) (Fin d) ℝ :=
  ((Xᵀ * X + lam • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ * Xᵀ * (Y - W))ᵀ

/-! ### The Frobenius inner product -/

/-- The Frobenius inner product `⟪M, N⟫ = tr(Mᵀ N)` of two real matrices. -/
private noncomputable def fip {a b : ℕ} (M N : Matrix (Fin a) (Fin b) ℝ) : ℝ :=
  trace (Mᵀ * N)

private theorem norm_sq_eq_fip {a b : ℕ} (M : Matrix (Fin a) (Fin b) ℝ) :
    ‖M‖ ^ 2 = fip M M := by
  rw [← frobSq_eq_norm_sq, frobSq, fip, trace, Finset.sum_comm]
  simp [Matrix.mul_apply, sq]

private theorem fip_comm {a b : ℕ} (M N : Matrix (Fin a) (Fin b) ℝ) : fip M N = fip N M := by
  rw [fip, fip, ← trace_transpose, transpose_mul, transpose_transpose]

private theorem fip_sub_left {a b : ℕ} (M N L : Matrix (Fin a) (Fin b) ℝ) :
    fip (M - N) L = fip M L - fip N L := by
  rw [fip, fip, fip, transpose_sub, Matrix.sub_mul, trace_sub]

private theorem fip_add_left {a b : ℕ} (M N L : Matrix (Fin a) (Fin b) ℝ) :
    fip (M + N) L = fip M L + fip N L := by
  rw [fip, fip, fip, transpose_add, Matrix.add_mul, trace_add]

private theorem fip_smul_left {a b : ℕ} (c : ℝ) (M N : Matrix (Fin a) (Fin b) ℝ) :
    fip (c • M) N = c * fip M N := by
  rw [fip, fip, transpose_smul, Matrix.smul_mul, trace_smul, smul_eq_mul]

private theorem fip_mul_left {a b c : ℕ} (X : Matrix (Fin a) (Fin c) ℝ)
    (M : Matrix (Fin c) (Fin b) ℝ) (N : Matrix (Fin a) (Fin b) ℝ) :
    fip (X * M) N = fip M (Xᵀ * N) := by
  rw [fip, fip, transpose_mul, Matrix.mul_assoc]

private theorem fip_sub_sub {a b : ℕ} (M N : Matrix (Fin a) (Fin b) ℝ) :
    fip (M - N) (M - N) = fip M M - 2 * fip M N + fip N N := by
  rw [fip_sub_left, fip_comm M (M - N), fip_comm N (M - N), fip_sub_left, fip_sub_left,
    fip_comm N M]
  ring

private theorem fip_add_add {a b : ℕ} (M N : Matrix (Fin a) (Fin b) ℝ) :
    fip (M + N) (M + N) = fip M M + 2 * fip M N + fip N N := by
  rw [fip_add_left, fip_comm M (M + N), fip_comm N (M + N), fip_add_left, fip_add_left,
    fip_comm N M]
  ring

/-! ### Ridge regression and the profile loss -/

/-- Ridge regression with a profile: if `I - X (XᵀX + λ I)⁻¹ Xᵀ = Pᵀ P`, then the ridge loss of
`(W, B)` is `‖P (Y - W)‖²` plus the excess `‖X E‖² + λ ‖E‖²` of `E = Bᵀ - B̂ᵀ` over the ridge
solution `B̂ = effectEstimate Y X lam W`. -/
private theorem ridgeLoss_eq (Y : Matrix (Fin n) (Fin p) ℝ) (X : Matrix (Fin n) (Fin d) ℝ)
    (lam : ℝ)
    (hA : (Xᵀ * X + lam • (1 : Matrix (Fin d) (Fin d) ℝ)) *
      (Xᵀ * X + lam • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ = 1)
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : 1 - X * (Xᵀ * X + lam • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ * Xᵀ = Pᵀ * P)
    (W : Matrix (Fin n) (Fin p) ℝ) (B : Matrix (Fin p) (Fin d) ℝ) :
    ridgeLoss Y X lam W B =
      ‖P * (Y - W)‖ ^ 2 + ‖X * (Bᵀ - (effectEstimate Y X lam W)ᵀ)‖ ^ 2 +
        lam * ‖Bᵀ - (effectEstimate Y X lam W)ᵀ‖ ^ 2 := by
  set A := Xᵀ * X + lam • (1 : Matrix (Fin d) (Fin d) ℝ) with hAdef
  set Z := Y - W with hZdef
  set C₀ := (effectEstimate Y X lam W)ᵀ with hC₀def
  set E := Bᵀ - C₀ with hEdef
  set R₀ := Z - X * C₀ with hR₀def
  have hC₀ : C₀ = A⁻¹ * Xᵀ * Z := by
    rw [hC₀def, effectEstimate, transpose_transpose]
  -- The normal equations `(XᵀX + λ I) C₀ = Xᵀ Z` leave the residual `Xᵀ R₀ = λ C₀`.
  have hXR₀ : Xᵀ * R₀ = lam • C₀ := by
    have hAC₀ : A * C₀ = Xᵀ * Z := by
      rw [hC₀, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hA, Matrix.one_mul]
    have h : A * C₀ = Xᵀ * (X * C₀) + lam • C₀ := by
      rw [hAdef, Matrix.add_mul, Matrix.smul_mul, Matrix.one_mul, Matrix.mul_assoc]
    rw [hR₀def, Matrix.mul_sub, ← hAC₀, h]
    abel
  have hres : Y - W - X * Bᵀ = R₀ - X * E := by
    rw [hR₀def, hEdef, Matrix.mul_sub, hZdef]
    abel
  have hB : Bᵀ = C₀ + E := by
    rw [hEdef]
    abel
  have hcross : fip R₀ (X * E) = lam * fip C₀ E := by
    rw [fip_comm, fip_mul_left, hXR₀, fip_comm, fip_smul_left]
  -- The value at the ridge solution is `‖P Z‖²`.
  have hvalue : fip R₀ R₀ + lam * fip C₀ C₀ = fip (P * Z) (P * Z) := by
    have h1 : fip R₀ R₀ = fip R₀ Z - lam * fip C₀ C₀ := by
      conv_lhs => rw [show R₀ = Z - X * C₀ from hR₀def]
      rw [fip_comm (Z - X * C₀) (Z - X * C₀), ← hR₀def, fip_sub_left, fip_comm (X * C₀) R₀,
        fip_comm R₀ (X * C₀), fip_mul_left, hXR₀, fip_comm C₀ (lam • C₀), fip_smul_left,
        fip_comm Z R₀]
    have h2 : R₀ = Pᵀ * (P * Z) := by
      rw [← Matrix.mul_assoc, ← hP, hR₀def, hC₀, Matrix.sub_mul, Matrix.one_mul]
      simp only [Matrix.mul_assoc]
    rw [h1, h2, fip_mul_left, transpose_transpose]
    ring
  rw [ridgeLoss, ← frobenius_norm_transpose B, norm_sq_eq_fip, norm_sq_eq_fip, norm_sq_eq_fip,
    norm_sq_eq_fip, norm_sq_eq_fip, hres, hB, fip_sub_sub, fip_add_add, hcross, ← hvalue]
  ring

/-- The singular value decomposition `X = Q Σ Rᵀ` with `d < n` and `λ > 0` makes `XᵀX + λ I`
invertible and gives `I - X (XᵀX + λ I)⁻¹ Xᵀ = (D_λ Qᵀ)ᵀ (D_λ Qᵀ)`. -/
private theorem svd_ridge (X : Matrix (Fin n) (Fin d) ℝ) (hd : d < n) {lam : ℝ} (hlam : 0 < lam)
    {Q : Matrix (Fin n) (Fin n) ℝ} {R : Matrix (Fin d) (Fin d) ℝ} {σ : Fin d → ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) (hR : R ∈ orthogonalGroup (Fin d) ℝ)
    (hX : X = Q * of (fun i j => if i.val = j.val then σ j else 0) * Rᵀ) :
    (Xᵀ * X + lam • (1 : Matrix (Fin d) (Fin d) ℝ)) *
        (Xᵀ * X + lam • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ = 1 ∧
      1 - X * (Xᵀ * X + lam • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ * Xᵀ =
        (shrinkage n lam σ * Qᵀ)ᵀ * (shrinkage n lam σ * Qᵀ) := by
  set S : Matrix (Fin n) (Fin d) ℝ := of (fun i j => if i.val = j.val then σ j else 0) with hS
  have hQtQ : Qᵀ * Q = 1 := (mem_orthogonalGroup_iff' (Fin n) ℝ).mp hQ
  have hQQt : Q * Qᵀ = 1 := (mem_orthogonalGroup_iff (Fin n) ℝ).mp hQ
  have hRtR : Rᵀ * R = 1 := (mem_orthogonalGroup_iff' (Fin d) ℝ).mp hR
  have hRRt : R * Rᵀ = 1 := (mem_orthogonalGroup_iff (Fin d) ℝ).mp hR
  have hpos (j : Fin d) : 0 < σ j ^ 2 + lam := by positivity
  -- `Σᵀ Σ = diag(σⱼ²)`, using `d < n`.
  have hStS : Sᵀ * S = diagonal (fun j => σ j ^ 2) := by
    ext j j'
    rw [Matrix.mul_apply, Finset.sum_eq_single ⟨j.val, lt_trans j.isLt hd⟩]
    · by_cases hjj : j = j'
      · subst hjj
        simp [hS, sq]
      · have hv : j.val ≠ j'.val := fun h => hjj (Fin.ext h)
        simp [hS, hjj, hv]
    · intro i _ hi
      have hv : i.val ≠ j.val := fun h => hi (Fin.ext h)
      simp [hS, hv]
    · simp
  have hA : Xᵀ * X + lam • (1 : Matrix (Fin d) (Fin d) ℝ) =
      R * diagonal (fun j => σ j ^ 2 + lam) * Rᵀ := by
    have hXtX : Xᵀ * X = R * (Sᵀ * S) * Rᵀ := by
      rw [hX]
      simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Qᵀ Q, hQtQ, Matrix.one_mul]
    have hsmul : lam • (1 : Matrix (Fin d) (Fin d) ℝ) = R * (lam • 1) * Rᵀ := by
      rw [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hRRt]
    rw [hXtX, hsmul, ← Matrix.add_mul, ← Matrix.mul_add, hStS, smul_one_eq_diagonal,
      diagonal_add]
  set Δ' : Matrix (Fin d) (Fin d) ℝ := diagonal (fun j => (σ j ^ 2 + lam)⁻¹) with hΔ'
  have hright : (Xᵀ * X + lam • (1 : Matrix (Fin d) (Fin d) ℝ)) * (R * Δ' * Rᵀ) = 1 := by
    rw [hA]
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Rᵀ R, hRtR, Matrix.one_mul, ← Matrix.mul_assoc (diagonal _) Δ',
      hΔ', diagonal_mul_diagonal]
    have h1 : (fun j => (σ j ^ 2 + lam) * (σ j ^ 2 + lam)⁻¹) = fun _ => (1 : ℝ) :=
      funext fun j => mul_inv_cancel₀ (hpos j).ne'
    rw [h1, diagonal_one, Matrix.one_mul, hRRt]
  have hinv : (Xᵀ * X + lam • (1 : Matrix (Fin d) (Fin d) ℝ))⁻¹ = R * Δ' * Rᵀ :=
    inv_eq_right_inv hright
  refine ⟨by rw [hinv, hright], ?_⟩
  -- `Σ (Σᵀ Σ + λ I)⁻¹ Σᵀ = diag(σᵢ² / (σᵢ² + λ), …, 0, …)`.
  have hSΔS : S * Δ' * Sᵀ = diagonal (fun i : Fin n =>
      if h : i.val < d then σ ⟨i.val, h⟩ ^ 2 * (σ ⟨i.val, h⟩ ^ 2 + lam)⁻¹ else 0) := by
    ext i i'
    rw [hΔ', Matrix.mul_apply]
    simp only [mul_diagonal]
    by_cases hi : i.val < d
    · rw [Finset.sum_eq_single ⟨i.val, hi⟩]
      · by_cases hii : i = i'
        · subst hii
          simp [hS, hi, sq]
          ring
        · have hv : i'.val ≠ i.val := fun h => hii (Fin.ext h.symm)
          simp [hS, hii, hv]
      · intro j _ hj
        have hv : i.val ≠ j.val := fun h => hj (Fin.ext h.symm)
        simp [hS, hv]
      · simp
    · rw [Finset.sum_eq_zero]
      · rw [diagonal_apply]
        simp [hi]
      · intro j _
        have hv : i.val ≠ j.val := fun h => hi (h ▸ j.isLt)
        simp [hS, hv]
  have hH : X * (R * Δ' * Rᵀ) * Xᵀ = Q * (S * Δ' * Sᵀ) * Qᵀ := by
    rw [hX]
    simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Rᵀ R, hRtR, Matrix.one_mul, ← Matrix.mul_assoc Rᵀ R, hRtR,
      Matrix.one_mul]
  have hD : (shrinkage n lam σ * Qᵀ)ᵀ * (shrinkage n lam σ * Qᵀ) =
      Q * (shrinkage n lam σ * shrinkage n lam σ) * Qᵀ := by
    rw [transpose_mul, transpose_transpose, shrinkage, diagonal_transpose]
    simp only [Matrix.mul_assoc]
  rw [hinv, hH, hD, hSΔS, shrinkage, diagonal_mul_diagonal]
  have h1 : (1 : Matrix (Fin n) (Fin n) ℝ) = Q * 1 * Qᵀ := by rw [Matrix.mul_one, hQQt]
  rw [h1, ← Matrix.sub_mul, ← Matrix.mul_sub, ← diagonal_one, diagonal_sub]
  congr 3
  funext i
  by_cases hi : i.val < d
  · have hs : 0 ≤ lam / (lam + σ ⟨i.val, hi⟩ ^ 2) := by positivity
    simp only [hi, dite_true]
    rw [Real.mul_self_sqrt hs]
    have := hpos ⟨i.val, hi⟩
    field_simp
    ring
  · simp [hi]

/-! ### The ridge estimates -/

/-- **Ridge estimates of the latent factor mixed model** (Caye, Jumentier, Lepeule and François,
LFMM 2). Let `Y` be an `n × p` response matrix, `X` an `n × d` matrix of primary variables with
`d < n`, `K : ℕ` and `λ = lam > 0`. Let `X = Q Σ Rᵀ` be a full singular value decomposition: `Q`
(`n × n`) and `R` (`d × d`) orthogonal, and `Σ` the `n × d` matrix with `Σⱼⱼ = σ j` and all other
entries zero, so that `σ 0, …, σ (d - 1)` are the singular values `σ₁, …, σ_d` (only their
squares enter, so their signs do not matter). With `D_λ = shrinkage n λ σ`, the pair
`Ŵ = Q D_λ⁻¹ svd_K(D_λ Qᵀ Y)` (`latentEstimate`) and `B̂` with
`B̂ᵀ = (XᵀX + λ I)⁻¹ Xᵀ (Y - Ŵ)` (`effectEstimate`) minimizes the ridge loss
`‖Y - W - X Bᵀ‖² + λ ‖B‖²` (`ridgeLoss`) over all `W` of rank at most `K` and all `B`: `Ŵ` has
rank at most `K`, and no such pair has a smaller loss. It is the only minimizer whenever the
`K`-th and `(K+1)`-th singular values of `D_λ Qᵀ Y` differ. With these singular values written
`s₀ ≥ s₁ ≥ ⋯` (Mathlib's `singularValues`, counted from `0`), the hypothesis reads `sᵢ ≠ s_K` for
all `i < K`: for `K ≥ 1` this is `s_{K-1} ≠ s_K`, as the singular values are nonincreasing, and
for `K = 0` it is no condition. -/
theorem ridge_estimates (Y : Matrix (Fin n) (Fin p) ℝ) (X : Matrix (Fin n) (Fin d) ℝ)
    (hd : d < n) (K : ℕ) {lam : ℝ} (hlam : 0 < lam)
    {Q : Matrix (Fin n) (Fin n) ℝ} {R : Matrix (Fin d) (Fin d) ℝ} {σ : Fin d → ℝ}
    (hQ : Q ∈ orthogonalGroup (Fin n) ℝ) (hR : R ∈ orthogonalGroup (Fin d) ℝ)
    (hX : X = Q * of (fun i j => if i.val = j.val then σ j else 0) * Rᵀ) :
    (latentEstimate Y lam Q σ K).rank ≤ K ∧
      (∀ W B, W.rank ≤ K →
        ridgeLoss Y X lam (latentEstimate Y lam Q σ K)
          (effectEstimate Y X lam (latentEstimate Y lam Q σ K)) ≤ ridgeLoss Y X lam W B) ∧
      ((∀ i < K, (toEuclideanLin (shrinkage n lam σ * Qᵀ * Y)).singularValues i ≠
          (toEuclideanLin (shrinkage n lam σ * Qᵀ * Y)).singularValues K) →
        ∀ W B, W.rank ≤ K →
          ridgeLoss Y X lam W B ≤ ridgeLoss Y X lam (latentEstimate Y lam Q σ K)
            (effectEstimate Y X lam (latentEstimate Y lam Q σ K)) →
          W = latentEstimate Y lam Q σ K ∧
            B = effectEstimate Y X lam (latentEstimate Y lam Q σ K)) := by
  obtain ⟨hA, hP⟩ := svd_ridge X hd hlam hQ hR hX
  have hprof := ridgeLoss_eq Y X lam hA (shrinkage n lam σ * Qᵀ) hP
  set D := shrinkage n lam σ with hDdef
  set M := D * Qᵀ * Y with hMdef
  set T := truncSVD M K with hTdef
  have hQtQ : Qᵀ * Q = 1 := (mem_orthogonalGroup_iff' (Fin n) ℝ).mp hQ
  have hQQt : Q * Qᵀ = 1 := (mem_orthogonalGroup_iff (Fin n) ℝ).mp hQ
  -- `D_λ` is invertible.
  have hDunit : IsUnit D.det := by
    rw [hDdef, shrinkage, det_diagonal, isUnit_iff_ne_zero]
    refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
    by_cases hi : i.val < d
    · simp only [hi, dite_true]
      exact (Real.sqrt_pos.mpr (div_pos hlam (by positivity))).ne'
    · simp [hi]
  have hDD : D * D⁻¹ = 1 := mul_nonsing_inv D hDunit
  have hDD' : D⁻¹ * D = 1 := nonsing_inv_mul D hDunit
  have hŴ : latentEstimate Y lam Q σ K = Q * D⁻¹ * T := rfl
  have hPŴ : D * Qᵀ * (Y - latentEstimate Y lam Q σ K) = M - T := by
    rw [hŴ, Matrix.mul_sub]
    congr 1
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Qᵀ Q, hQtQ, Matrix.one_mul, ← Matrix.mul_assoc D D⁻¹, hDD,
      Matrix.one_mul]
  have hPW (W : Matrix (Fin n) (Fin p) ℝ) : D * Qᵀ * (Y - W) = M - D * Qᵀ * W :=
    Matrix.mul_sub _ _ _
  have hrank (W : Matrix (Fin n) (Fin p) ℝ) (hW : W.rank ≤ K) : (D * Qᵀ * W).rank ≤ K :=
    (rank_mul_le_right _ _).trans hW
  have hT := frobenius_sub_truncSVD_sq M K
  -- The profile loss is at least the Eckart–Young minimum `‖M - T‖²`.
  have hlower (W : Matrix (Fin n) (Fin p) ℝ) (hW : W.rank ≤ K) :
      ‖M - T‖ ^ 2 ≤ ‖D * Qᵀ * (Y - W)‖ ^ 2 := by
    rw [hT, hPW]
    exact (isLeast_frobenius_sub_sq M K).2 ⟨_, hrank W hW, rfl⟩
  have hprofile (W : Matrix (Fin n) (Fin p) ℝ) (B : Matrix (Fin p) (Fin d) ℝ) :
      ‖D * Qᵀ * (Y - W)‖ ^ 2 ≤ ridgeLoss Y X lam W B := by
    rw [hprof W B]
    have h1 := sq_nonneg ‖X * (Bᵀ - (effectEstimate Y X lam W)ᵀ)‖
    have h2 := mul_nonneg hlam.le (sq_nonneg ‖Bᵀ - (effectEstimate Y X lam W)ᵀ‖)
    linarith
  have hlossŴ : ridgeLoss Y X lam (latentEstimate Y lam Q σ K)
      (effectEstimate Y X lam (latentEstimate Y lam Q σ K)) = ‖M - T‖ ^ 2 := by
    rw [hprof, hPŴ, sub_self, Matrix.mul_zero]
    simp
  refine ⟨(rank_mul_le_right _ _).trans (rank_truncSVD_le M K), fun W B hW => ?_, ?_⟩
  · rw [hlossŴ]
    exact (hlower W hW).trans (hprofile W B)
  · intro hgap W B hW hle
    have hgap' : ∀ i < K, (toEuclideanLin M).singularValues K <
        (toEuclideanLin M).singularValues i := fun i hi =>
      lt_of_le_of_ne ((toEuclideanLin M).singularValues_antitone hi.le) (hgap i hi).symm
    have h1 : ‖M - D * Qᵀ * W‖ ^ 2 ≤
        ∑ i ∈ Finset.Ico K p, (toEuclideanLin M).singularValues i ^ 2 := by
      rw [← hT, ← hPW]
      have := hprofile W B
      linarith
    have hPWeq : D * Qᵀ * W = T := eq_truncSVD_of_frobenius_sub_sq_le M hgap' (hrank W hW) h1
    have hWeq : W = latentEstimate Y lam Q σ K := by
      rw [hŴ, ← hPWeq]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc D⁻¹ D, hDD', Matrix.one_mul, ← Matrix.mul_assoc Q Qᵀ, hQQt,
        Matrix.one_mul]
    refine ⟨hWeq, ?_⟩
    subst hWeq
    have h2 := hprof (latentEstimate Y lam Q σ K) B
    rw [hPŴ] at h2
    rw [hlossŴ, h2] at hle
    have h3 := sq_nonneg ‖X * (Bᵀ - (effectEstimate Y X lam (latentEstimate Y lam Q σ K))ᵀ)‖
    have h4 : ‖Bᵀ - (effectEstimate Y X lam (latentEstimate Y lam Q σ K))ᵀ‖ ^ 2 ≤ 0 := by
      by_contra hcon
      have := mul_pos hlam (lt_of_not_ge hcon)
      linarith
    have h5 : Bᵀ - (effectEstimate Y X lam (latentEstimate Y lam Q σ K))ᵀ = 0 :=
      norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp (le_antisymm h4 (sq_nonneg _)))
    rw [sub_eq_zero] at h5
    rw [← transpose_transpose B, h5, transpose_transpose]

end Domains.Biology.PopulationGenetics.LatentFactorMixedModel
