/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Star.Real

/-!
# Twice-Ramanujan sparsifiers: the vector form

`exists_sparse_reweighting` proves the vector form of the linear-size spectral sparsifiers of
Batson, Spielman and Srivastava (*Twice-Ramanujan sparsifiers*, SIAM J. Comput. 41 (2012),
arXiv:0808.0163, Theorem 3.1): if `v₁, …, v_m ∈ ℝⁿ` satisfy `∑ vᵢ vᵢᵀ = I` and `d > 1`, then
some nonnegative weights `sᵢ`, at most `d n` of them nonzero, give
`I ≼ ∑ sᵢ vᵢ vᵢᵀ ≼ κ I` with `κ = (d + 1 + 2√d) / (d + 1 - 2√d)`.

The proof is the barrier argument of Section 3 of the paper. The matrix `A = ∑ sᵢ vᵢ vᵢᵀ` is
built one rank-one term at a time while two potentials stay bounded: the upper potential
`Tr (u I - A)⁻¹` and the lower potential `Tr (A - l I)⁻¹`. The Sherman–Morrison formula computes
the effect of a rank-one update on these traces (Lemmas 3.3 and 3.4 of the paper). Averaging over
the decomposition `∑ vᵢ vᵢᵀ = I`, with the Cauchy–Schwarz inequality for the lower barrier, shows
that a good vector always exists (Lemma 3.5 and Claim 3.6).

The paper runs the construction for `d n` steps, which tacitly takes `d n` to be an integer. Here
`d` is any real number greater than `1`, and the construction runs for `⌊d n⌋` steps. To make up
for the missing fraction of a step, the final bound is sharpened: a potential bounded by `ε` keeps
every eigenvalue at distance at least `1 / ε` from its barrier, not merely on the correct side of
it. With this sharpening, `⌊d n⌋ ≥ d (n - 1)` steps suffice for the ratio `κ`.
-/

@[expose] public section

namespace MathlibExt.GraphTheory.SpectralSparsificationWanted

open Matrix

section Barrier

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ### Spectral calculus for a real symmetric matrix -/

/-- `U * diagonal f * Uᴴ`, where `U` is the eigenvector unitary of the symmetric matrix `A`. Unlike
`Matrix.IsHermitian.cfc`, the diagonal is indexed by the eigenvectors, not given by a function of
the eigenvalues. -/
private noncomputable def specMat {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ι → ℝ) :
    Matrix ι ι ℝ :=
  (hA.eigenvectorUnitary : Matrix ι ι ℝ) * diagonal f *
    star (hA.eigenvectorUnitary : Matrix ι ι ℝ)

private theorem specMat_mul {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f g : ι → ℝ) :
    specMat hA f * specMat hA g = specMat hA (f * g) := by
  simp only [specMat, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (star _) (hA.eigenvectorUnitary : Matrix ι ι ℝ),
    Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2, Matrix.one_mul,
    ← Matrix.mul_assoc (diagonal f), diagonal_mul_diagonal]
  rfl

private theorem specMat_one {A : Matrix ι ι ℝ} (hA : A.IsHermitian) : specMat hA 1 = 1 := by
  simp [specMat, Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2]

private theorem smul_add_smul_one_eq_specMat {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (a b : ℝ) :
    a • A + b • (1 : Matrix ι ι ℝ) = specMat hA (fun j => a * hA.eigenvalues j + b) := by
  have hdiag : diagonal (fun j => a * hA.eigenvalues j + b) =
      a • diagonal hA.eigenvalues + b • (1 : Matrix ι ι ℝ) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  have hspec : A = (hA.eigenvectorUnitary : Matrix ι ι ℝ) * diagonal hA.eigenvalues *
      star (hA.eigenvectorUnitary : Matrix ι ι ℝ) := by
    conv_lhs => rw [hA.spectral_theorem]
    simp [RCLike.ofReal_real_eq_id]
  rw [specMat, hdiag, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
    Unitary.mul_star_self_of_mem hA.eigenvectorUnitary.2, ← hspec]

private theorem trace_specMat {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ι → ℝ) :
    (specMat hA f).trace = ∑ j, f j := by
  rw [specMat, trace_mul_comm, ← Matrix.mul_assoc,
    Unitary.star_mul_self_of_mem hA.eigenvectorUnitary.2, Matrix.one_mul, trace_diagonal]

private theorem posDef_specMat_iff {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ι → ℝ) :
    (specMat hA f).PosDef ↔ ∀ j, 0 < f j := by
  rw [specMat, Matrix.IsUnit.posDef_star_right_conjugate_iff Unitary.isUnit_coe,
    posDef_diagonal_iff]

private theorem posSemidef_specMat_iff {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ι → ℝ) :
    (specMat hA f).PosSemidef ↔ ∀ j, 0 ≤ f j := by
  rw [specMat, Matrix.IsUnit.posSemidef_star_right_conjugate_iff Unitary.isUnit_coe,
    posSemidef_diagonal_iff]

private theorem inv_specMat {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {f : ι → ℝ}
    (hf : ∀ j, f j ≠ 0) : (specMat hA f)⁻¹ = specMat hA (fun j => (f j)⁻¹) := by
  apply Matrix.inv_eq_right_inv
  rw [specMat_mul, ← specMat_one hA]
  congr 1
  ext j
  simp [hf j]

/-- The traces that enter the barrier argument, for a positive definite `specMat hA g`. -/
private theorem specMat_inv_facts {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {g : ι → ℝ}
    (hg : ∀ j, 0 < g j) :
    (specMat hA g).PosDef ∧ ((specMat hA g)⁻¹).trace = ∑ j, (g j)⁻¹ ∧
      ((specMat hA g)⁻¹ * (specMat hA g)⁻¹).trace = ∑ j, ((g j)⁻¹) ^ 2 ∧
      ((specMat hA g)⁻¹ * (specMat hA g)⁻¹).PosDef := by
  rw [inv_specMat hA fun j => (hg j).ne', specMat_mul, trace_specMat, trace_specMat]
  refine ⟨(posDef_specMat_iff hA g).2 hg, rfl, by simp [sq], ?_⟩
  exact (posDef_specMat_iff hA _).2 fun j => mul_pos (inv_pos.2 (hg j)) (inv_pos.2 (hg j))

/-- A positive definite `specMat hA g` whose inverse has trace at most `ε` has all its
eigenvalues `g j` at least `ε⁻¹`. -/
private theorem inv_le_of_trace_inv_le {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {g : ι → ℝ}
    (hg : ∀ j, 0 < g j) {ε : ℝ} (hε : ((specMat hA g)⁻¹).trace ≤ ε) (j : ι) : ε⁻¹ ≤ g j := by
  rw [(specMat_inv_facts hA hg).2.1] at hε
  have h1 : (g j)⁻¹ ≤ ∑ k, (g k)⁻¹ :=
    Finset.single_le_sum (fun k _ => (inv_pos.2 (hg k)).le) (Finset.mem_univ j)
  simpa using inv_anti₀ (inv_pos.2 (hg j)) (h1.trans hε)

/-- A symmetric real matrix is `specMat hA g` for every affine expression `a • A + b • 1` whose
eigenvalues `g j = a λⱼ + b` are given. -/
private theorem eq_specMat {A : Matrix ι ι ℝ} (hA : A.IsHermitian) {M : Matrix ι ι ℝ} (a b : ℝ)
    {g : ι → ℝ} (hM : M = a • A + b • 1) (hg : ∀ j, g j = a * hA.eigenvalues j + b) :
    M = specMat hA g := by
  rw [hM, smul_add_smul_one_eq_specMat hA]
  congr 1
  ext j
  exact (hg j).symm

omit [Fintype ι] in
private theorem isHermitian_of_posDef_sub {A : Matrix ι ι ℝ} {l : ℝ} (hl : (A - l • 1).PosDef) :
    A.IsHermitian := by
  have h : (l • (1 : Matrix ι ι ℝ)).IsHermitian := by simp [IsHermitian]
  simpa using hl.isHermitian.add h

omit [Fintype ι] in
private theorem isHermitian_of_posDef_smul_sub {A : Matrix ι ι ℝ} {u : ℝ}
    (hu : (u • 1 - A).PosDef) : A.IsHermitian := by
  have h : (u • (1 : Matrix ι ι ℝ)).IsHermitian := by simp [IsHermitian]
  simpa using h.sub hu.isHermitian

/-! ### Rank-one updates -/

/-- **Sherman–Morrison formula** for a symmetric rank-one update. This is the rank-one case of the
Woodbury identity `Matrix.add_mul_mul_inv_eq_sub`, checked directly to avoid `1 × 1` matrices. -/
private theorem inv_add_smul_vecMulVec {B : Matrix ι ι ℝ} (hB : IsUnit B) (v : ι → ℝ) (t : ℝ)
    (ht : 1 + t * (v ⬝ᵥ (B⁻¹ *ᵥ v)) ≠ 0) :
    (B + t • vecMulVec v v)⁻¹ =
      B⁻¹ - (t / (1 + t * (v ⬝ᵥ (B⁻¹ *ᵥ v)))) • vecMulVec (B⁻¹ *ᵥ v) (v ᵥ* B⁻¹) := by
  apply Matrix.inv_eq_right_inv
  set β := v ⬝ᵥ (B⁻¹ *ᵥ v) with hβ
  set c := t / (1 + t * β) with hc
  have h1 : B * B⁻¹ = 1 := Matrix.mul_nonsing_inv B ((Matrix.isUnit_iff_isUnit_det B).1 hB)
  have h2 : B * vecMulVec (B⁻¹ *ᵥ v) (v ᵥ* B⁻¹) = vecMulVec v (v ᵥ* B⁻¹) := by
    rw [mul_vecMulVec, mulVec_mulVec, h1, one_mulVec]
  have h3 : vecMulVec v v * B⁻¹ = vecMulVec v (v ᵥ* B⁻¹) := vecMulVec_mul _ _ _
  have h4 : vecMulVec v v * vecMulVec (B⁻¹ *ᵥ v) (v ᵥ* B⁻¹) = β • vecMulVec v (v ᵥ* B⁻¹) := by
    rw [vecMulVec_mul_vecMulVec, ← hβ]
    ext i j
    simp [vecMulVec_apply]
    ring
  have hcoef : t - c - t * c * β = 0 := by
    rw [hc]
    field_simp
    ring
  rw [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, h1, Matrix.mul_smul, h2, Matrix.smul_mul,
    Matrix.smul_mul, h3, Matrix.mul_smul, h4]
  linear_combination (norm := module) hcoef • vecMulVec v (v ᵥ* B⁻¹)

private theorem trace_vecMulVec_inv (B : Matrix ι ι ℝ) (v : ι → ℝ) :
    (vecMulVec (B⁻¹ *ᵥ v) (v ᵥ* B⁻¹)).trace = v ⬝ᵥ ((B⁻¹ * B⁻¹) *ᵥ v) := by
  rw [trace_vecMulVec, dotProduct_comm, ← dotProduct_mulVec, mulVec_mulVec]

private theorem posSemidef_vecMulVec_inv {B : Matrix ι ι ℝ} (hB : B⁻¹.IsHermitian) (v : ι → ℝ) :
    (vecMulVec (B⁻¹ *ᵥ v) (v ᵥ* B⁻¹)).PosSemidef := by
  have h : v ᵥ* B⁻¹ = B⁻¹ *ᵥ v := by
    conv_lhs => rw [← hB.eq, conjTranspose_eq_transpose_of_trivial]
    exact vecMul_transpose _ _
  rw [h]
  simpa using posSemidef_vecMulVec_self_star (B⁻¹ *ᵥ v)

/-- Averaging a quadratic form over a decomposition of the identity gives the trace. -/
private theorem sum_dotProduct_mulVec {m : ℕ} (v : Fin m → ι → ℝ)
    (hv : ∑ i, vecMulVec (v i) (v i) = 1) (M : Matrix ι ι ℝ) :
    ∑ i, v i ⬝ᵥ (M *ᵥ v i) = M.trace := by
  have h (x : ι → ℝ) : x ⬝ᵥ (M *ᵥ x) = (M * vecMulVec x x).trace := by
    rw [mul_vecMulVec, trace_vecMulVec, dotProduct_comm]
  simp_rw [h, ← trace_sum, ← Matrix.mul_sum, hv, Matrix.mul_one]

/-! ### The scalar inequalities behind the two barriers -/

/-- Shifting the upper barrier from `u` to `u + δ` lowers the upper potential, and by at least
`δ` times the trace of `(u + δ - A)⁻²`; here `a j = u - λⱼ`. -/
private theorem upper_ineq {κ : Type*} {s : Finset κ} (hs : s.Nonempty) (a : κ → ℝ) {δ : ℝ}
    (hδ : 0 < δ) (ha : ∀ j ∈ s, 0 < a j) :
    ∑ j ∈ s, (a j + δ)⁻¹ < ∑ j ∈ s, (a j)⁻¹ ∧
      ∑ j ∈ s, ((a j + δ)⁻¹) ^ 2 ≤ (∑ j ∈ s, (a j)⁻¹ - ∑ j ∈ s, (a j + δ)⁻¹) / δ := by
  constructor
  · exact Finset.sum_lt_sum_of_nonempty hs fun j hj =>
      inv_strictAnti₀ (ha j hj) (by linarith [ha j hj])
  · rw [le_div_iff₀ hδ, Finset.sum_mul, ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun j hj => ?_
    have h1 := ha j hj
    have e1 : (a j + δ)⁻¹ ^ 2 * δ = δ / (a j + δ) ^ 2 := by field_simp
    have e2 : (a j)⁻¹ - (a j + δ)⁻¹ = δ / (a j * (a j + δ)) := by field_simp; ring
    rw [e1, e2]
    exact div_le_div_of_nonneg_left hδ.le (by positivity) (by nlinarith)

/-- The scalar inequality behind Claim 3.6 of Batson–Spielman–Srivastava: shifting the lower
barrier from `l` to `l + δ` raises the lower potential, and if the lower potential is at most
`1 / δ` then the averaged lower bound is at least `1 / δ` minus the lower potential; here
`a j = λⱼ - l`. -/
private theorem lower_ineq {κ : Type*} {s : Finset κ} (hs : s.Nonempty) (a : κ → ℝ) {δ : ℝ}
    (hδ : 0 < δ) (ha : ∀ j ∈ s, δ < a j) (hΦ : ∑ j ∈ s, (a j)⁻¹ ≤ δ⁻¹) :
    ∑ j ∈ s, (a j)⁻¹ < ∑ j ∈ s, (a j - δ)⁻¹ ∧
      δ⁻¹ - ∑ j ∈ s, (a j)⁻¹ ≤
        (∑ j ∈ s, ((a j - δ)⁻¹) ^ 2) / (∑ j ∈ s, (a j - δ)⁻¹ - ∑ j ∈ s, (a j)⁻¹) -
          ∑ j ∈ s, (a j - δ)⁻¹ := by
  have hapos : ∀ j ∈ s, 0 < a j := fun j hj => hδ.trans (ha j hj)
  have hbpos : ∀ j ∈ s, 0 < a j - δ := fun j hj => sub_pos.2 (ha j hj)
  set Φ := ∑ j ∈ s, (a j)⁻¹ with hΦdef
  set S := ∑ j ∈ s, (a j * (a j - δ))⁻¹ with hSdef
  set R := ∑ j ∈ s, (a j * (a j - δ) ^ 2)⁻¹ with hRdef
  have hΦpos : 0 < Φ := Finset.sum_pos (fun j hj => inv_pos.2 (hapos j hj)) hs
  have hSpos : 0 < S := Finset.sum_pos (fun j hj => inv_pos.2
    (mul_pos (hapos j hj) (hbpos j hj))) hs
  have h1 : ∑ j ∈ s, (a j - δ)⁻¹ - Φ = δ * S := by
    rw [hΦdef, hSdef, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    have := hapos j hj
    have := hbpos j hj
    field_simp
    ring
  have h2 : ∑ j ∈ s, ((a j - δ)⁻¹) ^ 2 = S + δ * R := by
    rw [hSdef, hRdef, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have := hapos j hj
    have := hbpos j hj
    field_simp
    ring
  -- Cauchy–Schwarz, in the form of Sedrakyan's lemma
  have h3 : S ^ 2 / Φ ≤ R := by
    have := Finset.sq_sum_div_le_sum_sq_div s (fun j => (a j * (a j - δ))⁻¹)
      (g := fun j => (a j)⁻¹) (fun j hj => inv_pos.2 (hapos j hj))
    refine this.trans_eq (Finset.sum_congr rfl fun j hj => ?_)
    have := hapos j hj
    have := hbpos j hj
    field_simp
  have h4 : δ * S ^ 2 ≤ R := by
    refine le_trans ?_ h3
    rw [le_div_iff₀ hΦpos]
    have : δ * Φ ≤ 1 := by
      rw [← le_div_iff₀' hδ, one_div]
      exact hΦ
    nlinarith [sq_nonneg S]
  refine ⟨by linarith [mul_pos hδ hSpos], ?_⟩
  rw [h2, h1]
  have h5 : ∑ j ∈ s, (a j - δ)⁻¹ = Φ + δ * S := by linarith
  rw [h5]
  have hδS : 0 < δ * S := mul_pos hδ hSpos
  rw [div_eq_mul_inv (S + δ * R)]
  have key : δ⁻¹ + δ * S ≤ (S + δ * R) * (δ * S)⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ hδS]
    have : δ⁻¹ * (δ * S) = S := by field_simp
    nlinarith
  linarith

/-! ### One step of the barrier argument -/

/-- **One step of the barrier argument** (Batson–Spielman–Srivastava, Lemmas 3.3–3.5). If the
upper and lower potentials of `A` are at most `εU` and `εL`, and the parameters satisfy
`1 / δU + εU ≤ 1 / δL - εL`, then some rank-one term `t vᵢ vᵢᵀ` with `t > 0` can be added to `A`
while both barriers move, by `δU` and `δL`, and both potentials stay bounded. -/
private theorem barrier_step [Nonempty ι] {m : ℕ} (v : Fin m → ι → ℝ)
    (hv : ∑ i, vecMulVec (v i) (v i) = 1) {εU εL δU δL : ℝ} (hδU : 0 < δU) (hδL : 0 < δL)
    (hεL : εL < δL⁻¹) (hcon : δU⁻¹ + εU ≤ δL⁻¹ - εL) {A : Matrix ι ι ℝ} {u l : ℝ}
    (hu : (u • 1 - A).PosDef) (hl : (A - l • 1).PosDef)
    (hΦu : ((u • 1 - A)⁻¹).trace ≤ εU) (hΦl : ((A - l • 1)⁻¹).trace ≤ εL) :
    ∃ i, ∃ t : ℝ, 0 < t ∧ ((u + δU) • 1 - (A + t • vecMulVec (v i) (v i))).PosDef ∧
      (A + t • vecMulVec (v i) (v i) - (l + δL) • 1).PosDef ∧
      (((u + δU) • 1 - (A + t • vecMulVec (v i) (v i)))⁻¹).trace ≤ εU ∧
      ((A + t • vecMulVec (v i) (v i) - (l + δL) • 1)⁻¹).trace ≤ εL := by
  have hA : A.IsHermitian := isHermitian_of_posDef_sub hl
  set ev := hA.eigenvalues with hev
  -- eigenvalue descriptions of the four matrices involved
  have hU : u • (1 : Matrix ι ι ℝ) - A = specMat hA (fun j => u - ev j) :=
    eq_specMat hA (-1) u (by module) (fun j => by ring)
  have hL : A - l • (1 : Matrix ι ι ℝ) = specMat hA (fun j => ev j - l) :=
    eq_specMat hA 1 (-l) (by module) (fun j => by ring)
  have hevu : ∀ j, 0 < u - ev j := (posDef_specMat_iff hA _).1 (hU ▸ hu)
  have hevl : ∀ j, 0 < ev j - l := (posDef_specMat_iff hA _).1 (hL ▸ hl)
  have hΦu_eq : ((u • 1 - A)⁻¹).trace = ∑ j, (u - ev j)⁻¹ := by
    rw [hU]; exact (specMat_inv_facts hA hevu).2.1
  have hΦl_eq : ((A - l • 1)⁻¹).trace = ∑ j, (ev j - l)⁻¹ := by
    rw [hL]; exact (specMat_inv_facts hA hevl).2.1
  -- the lower potential keeps every eigenvalue more than `δL` above `l`
  have hgap : ∀ j, δL < ev j - l := by
    intro j
    have h1 : (ev j - l)⁻¹ ≤ ∑ k, (ev k - l)⁻¹ :=
      Finset.single_le_sum (fun k _ => (inv_pos.2 (hevl k)).le) (Finset.mem_univ j)
    exact (inv_lt_inv₀ (hevl j) hδL).1 (by linarith)
  set B := (u + δU) • (1 : Matrix ι ι ℝ) - A with hBdef
  set C := A - (l + δL) • (1 : Matrix ι ι ℝ) with hCdef
  have hB : B = specMat hA (fun j => (u - ev j) + δU) :=
    eq_specMat hA (-1) (u + δU) (by rw [hBdef]; module) (fun j => by ring)
  have hC : C = specMat hA (fun j => (ev j - l) - δL) :=
    eq_specMat hA 1 (-(l + δL)) (by rw [hCdef]; module) (fun j => by ring)
  obtain ⟨hBpd, hΦu'_eq, hTu_eq, hB2pd⟩ :=
    specMat_inv_facts hA (g := fun j => (u - ev j) + δU) fun j => add_pos (hevu j) hδU
  obtain ⟨hCpd, hΦl'_eq, hTl_eq, hC2pd⟩ :=
    specMat_inv_facts hA (g := fun j => (ev j - l) - δL) fun j => sub_pos.2 (hgap j)
  rw [← hB] at hBpd hΦu'_eq hTu_eq hB2pd
  rw [← hC] at hCpd hΦl'_eq hTl_eq hC2pd
  -- the scalar inequalities, in terms of traces
  obtain ⟨hU1, hU2⟩ := upper_ineq Finset.univ_nonempty (fun j => u - ev j) hδU fun j _ => hevu j
  obtain ⟨hL1, hL2⟩ := lower_ineq Finset.univ_nonempty (fun j => ev j - l) hδL
    (fun j _ => hgap j) (by rw [← hΦl_eq]; linarith)
  rw [← hΦu_eq, ← hΦu'_eq] at hU1
  rw [← hΦu_eq, ← hΦu'_eq, ← hTu_eq] at hU2
  rw [← hΦl_eq, ← hΦl'_eq] at hL1
  rw [← hΦl_eq, ← hΦl'_eq, ← hTl_eq] at hL2
  set ΦU := ((u • 1 - A)⁻¹).trace with hΦU
  set ΦU' := (B⁻¹).trace with hΦU'
  set ΦL := ((A - l • 1)⁻¹).trace with hΦL
  set ΦL' := (C⁻¹).trace with hΦL'
  have hD : 0 < ΦU - ΦU' := sub_pos.2 hU1
  have hD' : 0 < ΦL' - ΦL := sub_pos.2 hL1
  -- the upper and lower quantities `U_A(v)` and `L_A(v)` of the paper
  set Uf : (ι → ℝ) → ℝ := fun x => x ⬝ᵥ ((B⁻¹ * B⁻¹) *ᵥ x) / (ΦU - ΦU') + x ⬝ᵥ (B⁻¹ *ᵥ x)
    with hUf
  set Lf : (ι → ℝ) → ℝ := fun x => x ⬝ᵥ ((C⁻¹ * C⁻¹) *ᵥ x) / (ΦL' - ΦL) - x ⬝ᵥ (C⁻¹ *ᵥ x)
    with hLf
  have hsumU : ∑ i, Uf (v i) ≤ δU⁻¹ + εU := by
    simp only [hUf, Finset.sum_add_distrib, ← Finset.sum_div, sum_dotProduct_mulVec v hv]
    have : (B⁻¹ * B⁻¹).trace / (ΦU - ΦU') ≤ δU⁻¹ := by
      rw [div_le_iff₀ hD, ← div_eq_inv_mul]
      exact hU2
    linarith
  have hsumL : δL⁻¹ - εL ≤ ∑ i, Lf (v i) := by
    simp only [hLf, Finset.sum_sub_distrib, ← Finset.sum_div, sum_dotProduct_mulVec v hv]
    linarith
  -- some nonzero `vᵢ` has `U_A(vᵢ) ≤ L_A(vᵢ)`
  have hv0 : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    have h0 : ∑ i, vecMulVec (v i) (v i) = 0 := by simp [h]
    exact one_ne_zero (hv.symm.trans h0)
  obtain ⟨i, hvi, hUL⟩ : ∃ i, v i ≠ 0 ∧ Uf (v i) ≤ Lf (v i) := by
    by_contra h
    push Not at h
    have hle : ∀ i ∈ Finset.univ, Lf (v i) ≤ Uf (v i) := by
      intro i _
      by_cases hi : v i = 0
      · simp [hUf, hLf, hi]
      · exact (h i hi).le
    obtain ⟨i₀, hi₀⟩ := hv0
    have hlt : ∑ i, Lf (v i) < ∑ i, Uf (v i) :=
      Finset.sum_lt_sum hle ⟨i₀, Finset.mem_univ _, h i₀ hi₀⟩
    linarith
  set x := v i with hx
  have hβ : 0 < x ⬝ᵥ (B⁻¹ *ᵥ x) := by simpa using hBpd.inv.dotProduct_mulVec_pos hvi
  have hγ : 0 < x ⬝ᵥ ((B⁻¹ * B⁻¹) *ᵥ x) := by simpa using hB2pd.dotProduct_mulVec_pos hvi
  have hβ' : 0 < x ⬝ᵥ (C⁻¹ *ᵥ x) := by simpa using hCpd.inv.dotProduct_mulVec_pos hvi
  have hγ' : 0 < x ⬝ᵥ ((C⁻¹ * C⁻¹) *ᵥ x) := by simpa using hC2pd.dotProduct_mulVec_pos hvi
  set β := x ⬝ᵥ (B⁻¹ *ᵥ x) with hβdef
  set γ := x ⬝ᵥ ((B⁻¹ * B⁻¹) *ᵥ x) with hγdef
  set β' := x ⬝ᵥ (C⁻¹ *ᵥ x) with hβ'def
  set γ' := x ⬝ᵥ ((C⁻¹ * C⁻¹) *ᵥ x) with hγ'def
  have hUx : Uf x = γ / (ΦU - ΦU') + β := rfl
  have hLx : Lf x = γ' / (ΦL' - ΦL) - β' := rfl
  have hUpos : 0 < Uf x := by rw [hUx]; positivity
  refine ⟨i, (Uf x)⁻¹, inv_pos.2 hUpos, ?_, ?_, ?_, ?_⟩
  -- the upper barrier (Lemma 3.3)
  · have hsplit : (u + δU) • 1 - (A + (Uf x)⁻¹ • vecMulVec x x) =
        B + (-(Uf x)⁻¹) • vecMulVec x x := by rw [hBdef]; module
    have hden : 0 < 1 + -(Uf x)⁻¹ * β := by
      rw [neg_mul, ← sub_eq_add_neg, sub_pos, inv_mul_lt_one₀ hUpos, hUx]
      have : 0 < γ / (ΦU - ΦU') := by positivity
      linarith
    rw [hsplit, ← Matrix.posDef_inv_iff, inv_add_smul_vecMulVec hBpd.isUnit x _ hden.ne',
      sub_eq_add_neg, ← neg_smul]
    refine hBpd.inv.add_posSemidef ((posSemidef_vecMulVec_inv hBpd.inv.isHermitian x).smul ?_)
    rw [neg_nonneg]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (inv_pos.2 hUpos).le) hden.le
  -- the lower barrier (Lemma 3.4)
  · have hsplit : A + (Uf x)⁻¹ • vecMulVec x x - (l + δL) • 1 =
        C + (Uf x)⁻¹ • vecMulVec x x := by rw [hCdef]; module
    rw [hsplit]
    exact hCpd.add_posSemidef (by simpa using
      (posSemidef_vecMulVec_self_star x).smul (inv_pos.2 hUpos).le)
  -- the upper potential does not increase
  · have hsplit : (u + δU) • 1 - (A + (Uf x)⁻¹ • vecMulVec x x) =
        B + (-(Uf x)⁻¹) • vecMulVec x x := by rw [hBdef]; module
    have hden : 0 < 1 + -(Uf x)⁻¹ * β := by
      rw [neg_mul, ← sub_eq_add_neg, sub_pos, inv_mul_lt_one₀ hUpos, hUx]
      have : 0 < γ / (ΦU - ΦU') := by positivity
      linarith
    rw [hsplit, inv_add_smul_vecMulVec hBpd.isUnit x _ hden.ne', trace_sub, trace_smul,
      trace_vecMulVec_inv, smul_eq_mul]
    have key : -(Uf x)⁻¹ / (1 + -(Uf x)⁻¹ * β) * γ = -(ΦU - ΦU') := by
      have hγne : γ ≠ 0 := hγ.ne'
      rw [hUx]
      field_simp
      ring_nf
      simp [hγne]
    rw [key]
    linarith
  -- the lower potential does not increase
  · have hsplit : A + (Uf x)⁻¹ • vecMulVec x x - (l + δL) • 1 =
        C + (Uf x)⁻¹ • vecMulVec x x := by rw [hCdef]; module
    have hden : 0 < 1 + (Uf x)⁻¹ * β' := by positivity
    rw [hsplit, inv_add_smul_vecMulVec hCpd.isUnit x _ hden.ne', trace_sub, trace_smul,
      trace_vecMulVec_inv, smul_eq_mul]
    have key : ΦL' - ΦL ≤ (Uf x)⁻¹ / (1 + (Uf x)⁻¹ * β') * γ' := by
      have e : (Uf x)⁻¹ / (1 + (Uf x)⁻¹ * β') * γ' = γ' / (Uf x + β') := by
        field_simp
      rw [e, le_div_iff₀ (by positivity)]
      have h1 : Uf x + β' ≤ γ' / (ΦL' - ΦL) := by linarith
      calc (ΦL' - ΦL) * (Uf x + β') ≤ (ΦL' - ΦL) * (γ' / (ΦL' - ΦL)) := by gcongr
        _ = γ' := by field_simp
    linarith

/-- **Iterating the barrier step.** After `k` steps the matrix is a nonnegative combination of at
most `k` of the `vᵢ vᵢᵀ`, and both potentials, at barriers moved `k` times, stay bounded. -/
private theorem barrier_iterate [Nonempty ι] {m : ℕ} (v : Fin m → ι → ℝ)
    (hv : ∑ i, vecMulVec (v i) (v i) = 1) {εU εL δU δL u₀ l₀ : ℝ} (hδU : 0 < δU)
    (hδL : 0 < δL) (hεL : εL < δL⁻¹) (hcon : δU⁻¹ + εU ≤ δL⁻¹ - εL)
    (hu₀ : (u₀ • (1 : Matrix ι ι ℝ)).PosDef) (hl₀ : (-(l₀ • (1 : Matrix ι ι ℝ))).PosDef)
    (hΦu₀ : ((u₀ • (1 : Matrix ι ι ℝ))⁻¹).trace ≤ εU)
    (hΦl₀ : ((-(l₀ • (1 : Matrix ι ι ℝ)))⁻¹).trace ≤ εL) (k : ℕ) :
    ∃ s : Fin m → ℝ, 0 ≤ s ∧ (Finset.univ.filter fun i => s i ≠ 0).card ≤ k ∧
      ((u₀ + k * δU) • 1 - ∑ i, s i • vecMulVec (v i) (v i)).PosDef ∧
      (∑ i, s i • vecMulVec (v i) (v i) - (l₀ + k * δL) • 1).PosDef ∧
      (((u₀ + k * δU) • 1 - ∑ i, s i • vecMulVec (v i) (v i))⁻¹).trace ≤ εU ∧
      ((∑ i, s i • vecMulVec (v i) (v i) - (l₀ + k * δL) • 1)⁻¹).trace ≤ εL := by
  induction k with
  | zero =>
    refine ⟨0, le_rfl, by simp, ?_⟩
    simpa using ⟨hu₀, hl₀, hΦu₀, hΦl₀⟩
  | succ k ih =>
    obtain ⟨s, hs0, hcard, h1, h2, h3, h4⟩ := ih
    obtain ⟨i, t, ht, h1', h2', h3', h4'⟩ := barrier_step v hv hδU hδL hεL hcon h1 h2 h3 h4
    set s' : Fin m → ℝ := s + Pi.single i t with hs'
    refine ⟨s', ?_, ?_, ?_⟩
    · intro j
      simp only [hs', Pi.add_apply, Pi.zero_apply]
      exact add_nonneg (hs0 j) (by by_cases h : j = i <;> simp [h, ht.le])
    · calc (Finset.univ.filter fun j => s' j ≠ 0).card
          ≤ (insert i (Finset.univ.filter fun j => s j ≠ 0)).card := by
            apply Finset.card_le_card
            intro j hj
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert] at hj ⊢
            by_cases h : j = i
            · exact Or.inl h
            · right
              simpa [hs', h] using hj
        _ ≤ (Finset.univ.filter fun j => s j ≠ 0).card + 1 := Finset.card_insert_le _ _
        _ ≤ k + 1 := by omega
    · have hsum : ∑ j, s' j • vecMulVec (v j) (v j) =
          ∑ j, s j • vecMulVec (v j) (v j) + t • vecMulVec (v i) (v i) := by
        simp [hs', add_smul, Finset.sum_add_distrib, Pi.single_apply, ite_smul]
      have hk : u₀ + ((k + 1 : ℕ) : ℝ) * δU = u₀ + k * δU + δU := by push_cast; ring
      have hk' : l₀ + ((k + 1 : ℕ) : ℝ) * δL = l₀ + k * δL + δL := by push_cast; ring
      rw [hsum, hk, hk']
      exact ⟨h1', h2', h3', h4'⟩

private theorem trace_inv_smul_one {c : ℝ} (hc : c ≠ 0) :
    ((c • (1 : Matrix ι ι ℝ))⁻¹).trace = Fintype.card ι / c := by
  rw [Matrix.inv_eq_right_inv (B := c⁻¹ • (1 : Matrix ι ι ℝ))]
  · rw [trace_smul, trace_one, smul_eq_mul, div_eq_inv_mul]
  · rw [smul_mul_smul_comm, mul_inv_cancel₀ hc, one_smul, Matrix.mul_one]

/-- A bounded upper potential keeps the eigenvalues at distance `1 / ε` below the barrier. -/
private theorem posSemidef_of_upper {A : Matrix ι ι ℝ} {u ε : ℝ} (hu : (u • 1 - A).PosDef)
    (hε : ((u • 1 - A)⁻¹).trace ≤ ε) : ((u - ε⁻¹) • 1 - A).PosSemidef := by
  have hA : A.IsHermitian := isHermitian_of_posDef_smul_sub hu
  have hU : u • (1 : Matrix ι ι ℝ) - A = specMat hA (fun j => u - hA.eigenvalues j) :=
    eq_specMat hA (-1) u (by module) (fun j => by ring)
  have hpos := (posDef_specMat_iff hA _).1 (hU ▸ hu)
  rw [hU] at hε
  rw [eq_specMat hA (M := (u - ε⁻¹) • 1 - A) (-1) (u - ε⁻¹) (by module) (fun j => rfl),
    posSemidef_specMat_iff]
  intro j
  have := inv_le_of_trace_inv_le hA hpos hε j
  linarith

/-- A bounded lower potential keeps the eigenvalues at distance `1 / ε` above the barrier. -/
private theorem posSemidef_of_lower {A : Matrix ι ι ℝ} {l ε : ℝ} (hl : (A - l • 1).PosDef)
    (hε : ((A - l • 1)⁻¹).trace ≤ ε) : (A - (l + ε⁻¹) • 1).PosSemidef := by
  have hA : A.IsHermitian := isHermitian_of_posDef_sub hl
  have hL : A - l • (1 : Matrix ι ι ℝ) = specMat hA (fun j => hA.eigenvalues j - l) :=
    eq_specMat hA 1 (-l) (by module) (fun j => by ring)
  have hpos := (posDef_specMat_iff hA _).1 (hL ▸ hl)
  rw [hL] at hε
  rw [eq_specMat hA (M := A - (l + ε⁻¹) • 1) 1 (-(l + ε⁻¹)) (by module) (fun j => rfl),
    posSemidef_specMat_iff]
  intro j
  have := inv_le_of_trace_inv_le hA hpos hε j
  linarith

end Barrier

/-- **Batson–Spielman–Srivastava, vector form.** Let `d > 1` and let `v₁, …, v_m ∈ ℝⁿ` satisfy
`∑ vᵢ vᵢᵀ = I`. Then there are scalars `sᵢ ≥ 0`, at most `d n` of them nonzero, with
`I ≼ ∑ sᵢ vᵢ vᵢᵀ ≼ κ I` for `κ = (d + 1 + 2√d) / (d + 1 - 2√d)` (Batson, Spielman and
Srivastava, *Twice-Ramanujan sparsifiers*, arXiv:0808.0163, Theorem 3.1). -/
theorem exists_sparse_reweighting {m n : ℕ} {d : ℝ} (hd : 1 < d) (v : Fin m → Fin n → ℝ)
    (hv : ∑ i, vecMulVec (v i) (v i) = 1) :
    ∃ s : Fin m → ℝ, 0 ≤ s ∧ ((Finset.univ.filter fun i => s i ≠ 0).card : ℝ) ≤ d * n ∧
      (∑ i, s i • vecMulVec (v i) (v i) - 1).PosSemidef ∧
      (((d + 1 + 2 * Real.sqrt d) / (d + 1 - 2 * Real.sqrt d)) • (1 : Matrix (Fin n) (Fin n) ℝ) -
        ∑ i, s i • vecMulVec (v i) (v i)).PosSemidef := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : ∀ M : Matrix (Fin 0) (Fin 0) ℝ, M.PosSemidef := fun M => by
      rw [Subsingleton.elim M 0]
      exact PosSemidef.zero
    exact ⟨0, le_rfl, by simp, h0 _, h0 _⟩
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set r := Real.sqrt d with hr
  have hr1 : 1 < r := by
    rw [hr, Real.lt_sqrt zero_le_one]
    simpa using hd
  have hdr : d = r ^ 2 := (Real.sq_sqrt (by linarith)).symm
  have hr0 : 0 < r - 1 := by linarith
  set N : ℝ := (n : ℝ) with hN
  have hN1 : 1 ≤ N := by
    rw [hN]
    exact_mod_cast hn
  -- the number of steps
  set Q : ℕ := ⌊d * N⌋₊ with hQ
  have hQ1 : d * N - 1 < Q := by
    have := Nat.lt_floor_add_one (d * N)
    linarith
  have hQ2 : (Q : ℝ) ≤ d * N := Nat.floor_le (by positivity)
  -- the barrier parameters of the proof of Theorem 3.1
  set δU : ℝ := (r + 1) / (r - 1) with hδU
  set εU : ℝ := (r - 1) / (r * (r + 1)) with hεU
  have hδUpos : 0 < δU := by positivity
  have hεUpos : 0 < εU := by positivity
  have hεL : r⁻¹ < (1 : ℝ)⁻¹ := by
    rw [inv_one]
    exact inv_lt_one_of_one_lt₀ hr1
  have hcon : δU⁻¹ + εU ≤ (1 : ℝ)⁻¹ - r⁻¹ := by
    rw [hδU, hεU, inv_div]
    field_simp
    ring_nf
    rfl
  have hNr : 0 < N * r := by positivity
  have hu₀ : ((N / εU) • (1 : Matrix (Fin n) (Fin n) ℝ)).PosDef :=
    PosDef.one.smul (by positivity)
  have hl₀ : (-((-(N * r)) • (1 : Matrix (Fin n) (Fin n) ℝ))).PosDef := by
    rw [neg_smul, neg_neg]
    exact PosDef.one.smul hNr
  have hΦu₀ : (((N / εU) • (1 : Matrix (Fin n) (Fin n) ℝ))⁻¹).trace ≤ εU := by
    rw [trace_inv_smul_one (by positivity), Fintype.card_fin, ← hN]
    field_simp
    rfl
  have hΦl₀ : ((-((-(N * r)) • (1 : Matrix (Fin n) (Fin n) ℝ)))⁻¹).trace ≤ r⁻¹ := by
    rw [neg_smul, neg_neg, trace_inv_smul_one hNr.ne', Fintype.card_fin, ← hN]
    field_simp
    rfl
  obtain ⟨s, hs0, hcard, h1, h2, h3, h4⟩ :=
    barrier_iterate v hv hδUpos one_pos hεL hcon hu₀ hl₀ hΦu₀ hΦl₀ Q
  set A := ∑ i, s i • vecMulVec (v i) (v i) with hA
  -- sharpened final bounds
  have hup := posSemidef_of_upper h1 h3
  have hlo := posSemidef_of_lower h2 h4
  set M := N / εU + Q * δU - εU⁻¹ with hM
  set μ := -(N * r) + Q * 1 + r⁻¹⁻¹ with hμ
  have hμpos : 0 < μ := by
    rw [hμ, inv_inv, mul_one]
    nlinarith [mul_nonneg (sub_nonneg.2 hN1) (mul_nonneg (by linarith : (0 : ℝ) ≤ r) hr0.le)]
  have hκ : (d + 1 + 2 * r) / (d + 1 - 2 * r) = (r + 1) ^ 2 / (r - 1) ^ 2 := by
    rw [hdr]
    congr 1 <;> ring
  have hMμ : M ≤ (d + 1 + 2 * r) / (d + 1 - 2 * r) * μ := by
    have hM' : M = (r + 1) / (r - 1) * ((N - 1) * r + Q) := by
      rw [hM, hεU, hδU]
      field_simp
      ring
    have hμ' : μ = Q - (N - 1) * r := by
      rw [hμ, inv_inv]
      ring
    have key : (r - 1) * ((N - 1) * r + Q) ≤ (r + 1) * (Q - (N - 1) * r) := by
      nlinarith
    rw [hM', hμ', hκ, div_mul_eq_mul_div, div_mul_eq_mul_div,
      div_le_div_iff₀ hr0 (by positivity)]
    have hpos : 0 ≤ (r + 1) * (r - 1) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left key hpos]
  refine ⟨μ⁻¹ • s, fun j => ?_, ?_, ?_, ?_⟩
  · simpa using mul_nonneg (inv_nonneg.2 hμpos.le) (hs0 j)
  · have hfilter : (Finset.univ.filter fun i => (μ⁻¹ • s) i ≠ 0) =
        Finset.univ.filter fun i => s i ≠ 0 := by
      ext j
      simp [hμpos.ne']
    rw [hfilter]
    exact le_trans (by exact_mod_cast hcard) hQ2
  · have hsum : ∑ i, (μ⁻¹ • s) i • vecMulVec (v i) (v i) = μ⁻¹ • A := by
      rw [hA, Finset.smul_sum]
      simp [smul_smul]
    rw [hsum, show μ⁻¹ • A - 1 = μ⁻¹ • (A - μ • 1) by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hμpos.ne', one_smul]]
    exact hlo.smul (inv_nonneg.2 hμpos.le)
  · have hsum : ∑ i, (μ⁻¹ • s) i • vecMulVec (v i) (v i) = μ⁻¹ • A := by
      rw [hA, Finset.smul_sum]
      simp [smul_smul]
    set κ := (d + 1 + 2 * r) / (d + 1 - 2 * r) with hκdef
    rw [hsum, show κ • (1 : Matrix (Fin n) (Fin n) ℝ) - μ⁻¹ • A =
        μ⁻¹ • ((κ * μ - M) • 1 + (M • 1 - A)) by
      rw [smul_add, smul_sub, smul_smul, smul_smul, ← add_sub_assoc, ← add_smul]
      congr 2
      field_simp
      ring]
    exact ((PosSemidef.one.smul (sub_nonneg.2 hMμ)).add hup).smul (inv_nonneg.2 hμpos.le)

end MathlibExt.GraphTheory.SpectralSparsificationWanted
