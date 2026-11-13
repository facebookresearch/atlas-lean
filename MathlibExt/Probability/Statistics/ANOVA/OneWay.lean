/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Distributions.CochranIndependence
public import MathlibExt.Probability.Distributions.CochranTheorem
public import MathlibExt.Probability.Distributions.SnedecorF

/-!
# One-way analysis of variance: chi-square laws and the `F` test

For i.i.d. `N(μ, v)` observations labelled by groups (all groups nonempty, `v ≠ 0`), under the
null hypothesis of equal group means:

* `ProbabilityTheory.hasLaw_sumSqBetween_div`: `SSB / v ~ χ²_{G-1}` when `G ≥ 2`;
* `ProbabilityTheory.hasLaw_sumSqWithin_div`: `SSW / v ~ χ²_{n-G}` when `n > G`;
* `ProbabilityTheory.hasLaw_oneWay_ANOVA_F`: `(SSB / (G - 1)) / (SSW / (n - G)) ~ F(G-1, n-G)`.

The sums of squares are quadratic forms `Zᵀ P_B Z` and `Zᵀ P_W Z` of the standardized vector in
the symmetric idempotents built from group averaging and grand-mean centering; their ranks are
`G - 1` and `n - G`. Independence is `indepFun_sumSqBetween_sumSqWithin`, and the ratio law is
`map_div_chiSquare_eq_snedecorF`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal NNReal

namespace ProbabilityTheory

@[expose] public section

open MeasureTheory Matrix Finset

private theorem coord_std {m0 : ℝ} {v : NNReal} (hv : v ≠ 0) :
    Measure.map (fun x : ℝ => (x - m0) / Real.sqrt (v : ℝ)) (gaussianReal m0 v)
      = gaussianReal 0 1 := by
  have hne : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have hvpos : 0 < (v : ℝ) := lt_of_le_of_ne (NNReal.coe_nonneg v) (Ne.symm hne)
  have hfun : (fun x : ℝ => (x - m0) / Real.sqrt (v : ℝ))
      = (fun y : ℝ => y / Real.sqrt (v : ℝ)) ∘ (fun x : ℝ => x - m0) := rfl
  rw [hfun, ← Measure.map_map (by fun_prop) (by fun_prop)]
  rw [gaussianReal_map_sub_const]
  rw [gaussianReal_map_div_const]
  have hsv : (Real.sqrt (v : ℝ)) ^ 2 = (v : ℝ) := Real.sq_sqrt (NNReal.coe_nonneg v)
  have hmk : NNReal.mk ((Real.sqrt (v : ℝ)) ^ 2) (sq_nonneg _) = v := by
    ext
    simp only [NNReal.coe_mk]
    exact hsv
  simp only [sub_self, zero_div]
  rw [hmk]
  rw [div_self hv]

private theorem pi_std {ι : Type*} [Fintype ι] {m0 : ℝ} {v : NNReal} (hv : v ≠ 0) :
    Measure.map (fun x : ι → ℝ => fun i => (x i - m0) / Real.sqrt (v : ℝ))
      (Measure.pi fun _ : ι => gaussianReal m0 v)
      = Measure.pi fun _ : ι => gaussianReal 0 1 := by
  have h := Measure.pi_map_pi (μ := fun _ : ι => gaussianReal m0 v)
    (f := fun _ : ι => fun y : ℝ => (y - m0) / Real.sqrt (v : ℝ))
    (fun i => by fun_prop)
  calc Measure.map (fun x : ι → ℝ => fun i => (x i - m0) / Real.sqrt (v : ℝ))
        (Measure.pi fun _ : ι => gaussianReal m0 v)
      = Measure.pi fun i => Measure.map
          ((fun _ : ι => fun y : ℝ => (y - m0) / Real.sqrt (v : ℝ)) i)
          (gaussianReal m0 v) := h
    _ = Measure.pi fun _ : ι => gaussianReal 0 1 := by
        simp only [coord_std hv]

private theorem hasLaw_std {ι : Type*} [Fintype ι] {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ι → ℝ} {m0 : ℝ} {v : NNReal}
    (hv : v ≠ 0) (hX : HasLaw X (Measure.pi fun _ : ι => gaussianReal m0 v) μ) :
    HasLaw (fun ω => fun i => (X ω i - m0) / Real.sqrt (v : ℝ))
      (Measure.pi fun _ : ι => gaussianReal 0 1) μ := by
  have hf : Measurable (fun x : ι → ℝ => fun i => (x i - m0) / Real.sqrt (v : ℝ)) := by
    fun_prop
  refine ⟨hf.comp_aemeasurable hX.aemeasurable, ?_⟩
  have hcomp : (fun ω => (fun x : ι → ℝ => fun i => (x i - m0) / Real.sqrt (v : ℝ)) (X ω))
      = (fun x : ι → ℝ => fun i => (x i - m0) / Real.sqrt (v : ℝ)) ∘ X := rfl
  have hmap : μ.map (fun ω => (fun x : ι → ℝ => fun i => (x i - m0) / Real.sqrt (v : ℝ)) (X ω))
      = (Measure.pi fun _ : ι => gaussianReal m0 v).map
        (fun x : ι → ℝ => fun i => (x i - m0) / Real.sqrt (v : ℝ)) := by
    rw [hcomp, ← hX.map_eq, AEMeasurable.map_map_of_aemeasurable hf.aemeasurable hX.aemeasurable]
  calc μ.map (fun ω => fun i => (X ω i - m0) / Real.sqrt (v : ℝ))
      = (Measure.pi fun _ : ι => gaussianReal m0 v).map
        (fun x : ι → ℝ => fun i => (x i - m0) / Real.sqrt (v : ℝ)) := hmap
    _ = Measure.pi fun _ : ι => gaussianReal 0 1 := pi_std hv

private theorem groupMean_affine {ι G : Type*} [Fintype ι] [DecidableEq G]
    (grp : ι → G) (hne : ∀ g, ∃ i, grp i = g)
    (z : ι → ℝ) (m0 s : ℝ) (g : G) :
    groupMean grp (fun i => m0 + s * z i) g = m0 + s * groupMean grp z g := by
  classical
  unfold groupMean
  obtain ⟨i0, hi0⟩ := hne g
  have hcard : (#{i | grp i = g} : ℕ) ≠ 0 := by
    apply Finset.card_ne_zero.mpr
    exact ⟨i0, by simp [hi0]⟩
  have hcardR : ((#{i | grp i = g} : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hcard
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  field_simp

private theorem grandMean_affine {ι : Type*} [Fintype ι]
    (z : ι → ℝ) (m0 s : ℝ) (hn : 0 < Fintype.card ι) :
    (∑ i, (m0 + s * z i)) / Fintype.card ι = m0 + s * ((∑ i, z i) / Fintype.card ι) := by
  have hnR : ((Fintype.card ι : ℕ) : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Finset.mul_sum]
  field_simp

private noncomputable def cellMat {ι G : Type*} [Fintype ι] [DecidableEq G] (grp : ι → G) :
    Matrix ι ι ℝ :=
  fun i j => if grp j = grp i then ((#{k | grp k = grp i} : ℕ) : ℝ)⁻¹ else 0

private noncomputable def grandMat {ι : Type*} [Fintype ι] : Matrix ι ι ℝ :=
  fun _ _ => ((Fintype.card ι : ℕ) : ℝ)⁻¹

private theorem cellMat_mulVec {ι G : Type*} [Fintype ι] [DecidableEq G]
    (grp : ι → G) (x : ι → ℝ) (i : ι) :
    (cellMat grp *ᵥ x) i = groupMean grp x (grp i) := by
  simp only [Matrix.mulVec, dotProduct, cellMat, ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  rw [← Finset.mul_sum]
  unfold groupMean
  rw [div_eq_inv_mul]
private theorem grandMat_mulVec {ι : Type*} [Fintype ι] (x : ι → ℝ) (i : ι) :
    (grandMat *ᵥ x) i = (∑ j, x j) / Fintype.card ι := by
  simp only [Matrix.mulVec, dotProduct, grandMat]
  rw [← Finset.mul_sum]
  rw [div_eq_inv_mul]

private theorem cellMat_hermitian {ι G : Type*} [Fintype ι] [DecidableEq G]
    (grp : ι → G) : (cellMat grp).IsHermitian := by
  classical
  ext i j
  simp only [Matrix.conjTranspose_apply, cellMat]
  by_cases h : grp j = grp i
  · simp [h]
  · have h' : grp i ≠ grp j := Ne.symm h
    simp [h, h']

private theorem grandMat_hermitian {ι : Type*} [Fintype ι] :
    (grandMat (ι := ι)).IsHermitian := by
  classical
  ext i j
  simp [Matrix.conjTranspose_apply, grandMat]

private theorem grandMat_idem {ι : Type*} [Fintype ι]
    (hn : 0 < Fintype.card ι) : grandMat (ι := ι) * grandMat = grandMat := by
  classical
  ext i j
  simp only [Matrix.mul_apply, grandMat]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hnR : ((Fintype.card ι : ℕ) : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  field_simp
private theorem cellMat_idem {ι G : Type*} [Fintype ι] [DecidableEq G]
    (grp : ι → G) (hne : ∀ g, ∃ i, grp i = g) :
    cellMat grp * cellMat grp = cellMat grp := by
  classical
  ext i j
  simp only [Matrix.mul_apply, cellMat]
  by_cases h : grp j = grp i
  · obtain ⟨i0, hi0⟩ := hne (grp i)
    have hm : (#{k | grp k = grp i} : ℕ) ≠ 0 := by
      apply Finset.card_ne_zero.mpr
      exact ⟨i0, by simp [hi0]⟩
    have hmR : ((#{k | grp k = grp i} : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hm
    simp only [h, ↓reduceIte]
    have hterm : ∀ k : ι,
        (if grp k = grp i then ((#{a | grp a = grp i} : ℕ) : ℝ)⁻¹ else 0) *
        (if grp i = grp k then ((#{a | grp a = grp k} : ℕ) : ℝ)⁻¹ else 0)
        = if grp k = grp i then
            ((#{a | grp a = grp i} : ℕ) : ℝ)⁻¹ * ((#{a | grp a = grp i} : ℕ) : ℝ)⁻¹
          else 0 := by
      intro k
      by_cases hk : grp k = grp i
      · simp [hk]
      · have hk' : ¬ (grp i = grp k) := fun e => hk e.symm
        simp [hk, hk']
    simp_rw [hterm]
    rw [← Finset.sum_filter]
    rw [Finset.sum_const]
    have hcard_eq :
        (Finset.filter (fun k => grp k = grp i) Finset.univ).card = #{k | grp k = grp i} := rfl
    rw [hcard_eq, nsmul_eq_mul]
    rw [← mul_assoc, mul_inv_cancel₀ hmR, one_mul]
  · simp only [h, ↓reduceIte]
    rw [Finset.sum_eq_zero]
    intro k _
    by_cases hk : grp k = grp i
    · simp [hk, h]
    · simp [hk]
private theorem cellMat_row_sum {ι G : Type*} [Fintype ι] [DecidableEq G]
    (grp : ι → G) (hne : ∀ g, ∃ i, grp i = g) (i : ι) :
    ∑ k, cellMat grp i k = 1 := by
  simp only [cellMat]
  rw [← Finset.sum_filter, Finset.sum_const]
  obtain ⟨i0, hi0⟩ := hne (grp i)
  have hm : (#{k | grp k = grp i} : ℕ) ≠ 0 := by
    apply Finset.card_ne_zero.mpr
    exact ⟨i0, by simp [hi0]⟩
  have hmR : ((#{k | grp k = grp i} : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hm
  have hcard_eq :
      (Finset.filter (fun k => grp k = grp i) Finset.univ).card = #{k | grp k = grp i} := rfl
  rw [hcard_eq, nsmul_eq_mul, mul_inv_cancel₀ hmR]

private theorem cellMat_col_sum {ι G : Type*} [Fintype ι] [DecidableEq G]
    (grp : ι → G) (hne : ∀ g, ∃ i, grp i = g) (j : ι) :
    ∑ k, cellMat grp k j = 1 := by
  have hterm : ∀ k : ι, cellMat grp k j
      = if grp k = grp j then ((#{a | grp a = grp j} : ℕ) : ℝ)⁻¹ else 0 := by
    intro k
    simp only [cellMat]
    by_cases hk : grp j = grp k
    · simp [hk]
    · have hkk : ¬ (grp k = grp j) := fun e => hk e.symm
      simp [hk, hkk]
  simp_rw [hterm]
  rw [← Finset.sum_filter, Finset.sum_const]
  obtain ⟨i0, hi0⟩ := hne (grp j)
  have hm : (#{k | grp k = grp j} : ℕ) ≠ 0 := by
    apply Finset.card_ne_zero.mpr
    exact ⟨i0, by simp [hi0]⟩
  have hmR : ((#{k | grp k = grp j} : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hm
  have hcard_eq :
      (Finset.filter (fun k => grp k = grp j) Finset.univ).card = #{k | grp k = grp j} := rfl
  rw [hcard_eq, nsmul_eq_mul, mul_inv_cancel₀ hmR]

private theorem cellMat_mul_grandMat {ι G : Type*} [Fintype ι] [DecidableEq G]
    (grp : ι → G) (hne : ∀ g, ∃ i, grp i = g) :
    cellMat grp * grandMat = grandMat := by
  classical
  ext i j
  simp only [Matrix.mul_apply, grandMat]
  rw [← Finset.sum_mul, cellMat_row_sum grp hne i, one_mul]

private theorem grandMat_mul_cellMat {ι G : Type*} [Fintype ι] [DecidableEq G]
    (grp : ι → G) (hne : ∀ g, ∃ i, grp i = g) :
    grandMat * cellMat grp = grandMat := by
  classical
  ext i j
  simp only [Matrix.mul_apply, grandMat]
  rw [← Finset.mul_sum, cellMat_col_sum grp hne j, mul_one]
private noncomputable def btwMat {ι G : Type*} [Fintype ι] [DecidableEq G] (grp : ι → G) :
    Matrix ι ι ℝ :=
  cellMat grp - grandMat

private noncomputable def wthMat {ι G : Type*} [Fintype ι] [DecidableEq G] [DecidableEq ι]
    (grp : ι → G) : Matrix ι ι ℝ :=
  1 - cellMat grp

private theorem btwMat_hermitian {ι G : Type*} [Fintype ι] [DecidableEq G]
    (grp : ι → G) : (btwMat grp).IsHermitian := by
  classical
  unfold btwMat
  exact (cellMat_hermitian grp).sub (grandMat_hermitian)

private theorem wthMat_hermitian {ι G : Type*} [Fintype ι] [DecidableEq G] [DecidableEq ι]
    (grp : ι → G) : (wthMat grp).IsHermitian := by
  unfold wthMat
  exact Matrix.isHermitian_one.sub (cellMat_hermitian grp)

private theorem btwMat_idem {ι G : Type*} [Fintype ι] [DecidableEq G]
    (grp : ι → G) (hne : ∀ g, ∃ i, grp i = g) (hn : 0 < Fintype.card ι) :
    btwMat grp * btwMat grp = btwMat grp := by
  classical
  simp only [btwMat]
  rw [sub_mul, mul_sub, mul_sub, cellMat_idem grp hne, cellMat_mul_grandMat grp hne,
    grandMat_mul_cellMat grp hne, grandMat_idem hn]
  rw [sub_self, sub_zero]

private theorem wthMat_idem {ι G : Type*} [Fintype ι] [DecidableEq G] [DecidableEq ι]
    (grp : ι → G) (hne : ∀ g, ∃ i, grp i = g) :
    wthMat grp * wthMat grp = wthMat grp := by
  simp only [wthMat]
  rw [sub_mul, mul_sub, mul_sub, one_mul, one_mul, mul_one, cellMat_idem grp hne]
  rw [sub_self, sub_zero]

private theorem dotProduct_mulVec_eq {ι : Type*} [Fintype ι]
    {M : Matrix ι ι ℝ} (hM : M.IsHermitian) (hMM : M * M = M) (x : ι → ℝ) :
    x ⬝ᵥ M *ᵥ x = (M *ᵥ x) ⬝ᵥ (M *ᵥ x) := by
  classical
  have hT : Mᵀ = M := by simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hM.eq
  calc x ⬝ᵥ M *ᵥ x = x ⬝ᵥ (M * M) *ᵥ x := by rw [hMM]
    _ = x ⬝ᵥ M *ᵥ (M *ᵥ x) := by rw [Matrix.mulVec_mulVec]
    _ = (x ᵥ* M) ⬝ᵥ (M *ᵥ x) := Matrix.dotProduct_mulVec _ _ _
    _ = (M *ᵥ x) ⬝ᵥ (M *ᵥ x) := by rw [← Matrix.mulVec_transpose, hT]

private theorem btwMat_mulVec {ι G : Type*} [Fintype ι] [DecidableEq G]
    (grp : ι → G) (x : ι → ℝ) (i : ι) :
    (btwMat grp *ᵥ x) i = groupMean grp x (grp i) - (∑ j, x j) / Fintype.card ι := by
  classical
  simp only [btwMat, Matrix.sub_mulVec, Pi.sub_apply, cellMat_mulVec, grandMat_mulVec]

private theorem wthMat_mulVec {ι G : Type*} [Fintype ι] [DecidableEq G] [DecidableEq ι]
    (grp : ι → G) (x : ι → ℝ) (i : ι) :
    (wthMat grp *ᵥ x) i = x i - groupMean grp x (grp i) := by
  simp only [wthMat, Matrix.sub_mulVec, Pi.sub_apply, Matrix.one_mulVec, cellMat_mulVec]

private theorem eigenvalues_zero_or_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (hAA : A * A = A) (j : ι) :
    hA.eigenvalues j = 0 ∨ hA.eigenvalues j = 1 := by
  set v := (hA.eigenvectorBasis j).ofLp with hv
  set lam := hA.eigenvalues j with hlam
  have hAv : A *ᵥ v = lam • v := hA.mulVec_eigenvectorBasis j
  have hbasis0 : hA.eigenvectorBasis j ≠ 0 := hA.eigenvectorBasis.orthonormal.ne_zero j
  have hv0 : v ≠ 0 := fun e => hbasis0 (WithLp.ofLp_injective 2 e)
  have h1 : (A * A) *ᵥ v = A *ᵥ v := by rw [hAA]
  rw [← Matrix.mulVec_mulVec, hAv, Matrix.mulVec_smul, hAv] at h1
  obtain ⟨i, hi⟩ : ∃ i, v i ≠ 0 := by
    obtain ⟨i, hii⟩ := Function.ne_iff.mp hv0
    exact ⟨i, by simpa using hii⟩
  have hcoord : lam * (lam * v i) = lam * v i := by
    have hci := congrArg (fun w : ι → ℝ => w i) h1
    simpa [Pi.smul_apply, smul_eq_mul] using hci
  have hring : lam * (lam * v i) = lam ^ 2 * v i := by ring
  rw [hring] at hcoord
  have hlam2 : lam ^ 2 = lam := mul_right_cancel₀ hi hcoord
  have hfac : lam * (lam - 1) = 0 := by linear_combination hlam2
  rcases mul_eq_zero.mp hfac with h0 | h1'
  · exact Or.inl h0
  · exact Or.inr (sub_eq_zero.mp h1')
private theorem rank_eq_trace_of_idem {ι : Type*} [Fintype ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (hAA : A * A = A) :
    (A.rank : ℝ) = A.trace := by
  classical
  have h01 : ∀ i, hA.eigenvalues i = 0 ∨ hA.eigenvalues i = 1 :=
    fun j => eigenvalues_zero_or_one hA hAA j
  rw [hA.rank_eq_card_non_zero_eigs, hA.trace_eq_sum_eigenvalues]
  simp only [RCLike.ofReal_real_eq_id, id_eq]
  have hterm : ∀ i : ι, (if hA.eigenvalues i ≠ 0 then (1 : ℝ) else 0) = hA.eigenvalues i := by
    intro i
    rcases h01 i with h0 | h1
    · simp [h0]
    · simp [h1]
  calc ((Fintype.card {i // hA.eigenvalues i ≠ 0} : ℕ) : ℝ)
      = ∑ i, (if hA.eigenvalues i ≠ 0 then (1 : ℝ) else 0) := by
        rw [Fintype.card_subtype, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ = ∑ i, hA.eigenvalues i := Finset.sum_congr rfl fun i _ => hterm i

private theorem trace_cellMat {ι G : Type*} [Fintype ι] [Fintype G] [DecidableEq G]
    (grp : ι → G) (hne : ∀ g, ∃ i, grp i = g) : (cellMat grp).trace = (Fintype.card G : ℝ) := by
  classical
  simp only [Matrix.trace, Matrix.diag, cellMat, ↓reduceIte]
  rw [← Finset.sum_fiberwise Finset.univ grp (fun i => ((#{k | grp k = grp i} : ℕ) : ℝ)⁻¹)]
  have hinner : ∀ g : G, (∑ i with grp i = g, ((#{k | grp k = grp i} : ℕ) : ℝ)⁻¹) = 1 := by
    intro g
    obtain ⟨i0, hi0⟩ := hne g
    have hm : (#{k | grp k = g} : ℕ) ≠ 0 := by
      apply Finset.card_ne_zero.mpr
      exact ⟨i0, by simp [hi0]⟩
    have hmR : ((#{k | grp k = g} : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hm
    have hrewrite : (∑ i with grp i = g, ((#{k | grp k = grp i} : ℕ) : ℝ)⁻¹)
        = ∑ i with grp i = g, ((#{k | grp k = g} : ℕ) : ℝ)⁻¹ := by
      refine Finset.sum_congr rfl fun i hi => ?_
      have hgi : grp i = g := by simpa using hi
      rw [hgi]
    rw [hrewrite, Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.filter (fun i => grp i = g) Finset.univ).card = #{k | grp k = g} := rfl
    rw [hcard, mul_inv_cancel₀ hmR]
  simp_rw [hinner]
  simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

private theorem trace_grandMat {ι : Type*} [Fintype ι]
    (hn : 0 < Fintype.card ι) : (grandMat (ι := ι)).trace = 1 := by
  classical
  simp only [Matrix.trace, Matrix.diag, grandMat]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hnR : ((Fintype.card ι : ℕ) : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  exact mul_inv_cancel₀ hnR

private theorem trace_btwMat {ι G : Type*} [Fintype ι] [Fintype G] [DecidableEq G]
    (grp : ι → G) (hne : ∀ g, ∃ i, grp i = g) (hn : 0 < Fintype.card ι) :
    (btwMat grp).trace = (Fintype.card G : ℝ) - 1 := by
  classical
  simp only [btwMat, Matrix.trace_sub, trace_cellMat grp hne, trace_grandMat hn]

private theorem trace_wthMat {ι G : Type*} [Fintype ι] [Fintype G] [DecidableEq G] [DecidableEq ι]
    (grp : ι → G) (hne : ∀ g, ∃ i, grp i = g) :
    (wthMat grp).trace = (Fintype.card ι : ℝ) - (Fintype.card G : ℝ) := by
  simp only [wthMat, Matrix.trace_sub, Matrix.trace_one, trace_cellMat grp hne]

private theorem rank_btwMat {ι G : Type*} [Fintype ι] [Fintype G] [DecidableEq G]
    (grp : ι → G) (hne : ∀ g, ∃ i, grp i = g) (hn : 0 < Fintype.card ι)
    (hG : 2 ≤ Fintype.card G) : (btwMat grp).rank = Fintype.card G - 1 := by
  classical
  have hrt := rank_eq_trace_of_idem (btwMat_hermitian grp) (btwMat_idem grp hne hn)
  rw [trace_btwMat grp hne hn] at hrt
  have h1 : 1 ≤ Fintype.card G := by omega
  have hcast : ((Fintype.card G - 1 : ℕ) : ℝ) = (Fintype.card G : ℝ) - 1 := by
    rw [Nat.cast_sub h1, Nat.cast_one]
  rw [← hcast] at hrt
  exact Nat.cast_injective hrt

private theorem rank_wthMat {ι G : Type*} [Fintype ι] [Fintype G] [DecidableEq G] [DecidableEq ι]
    (grp : ι → G) (hne : ∀ g, ∃ i, grp i = g)
    (hι : Fintype.card G < Fintype.card ι) :
    (wthMat grp).rank = Fintype.card ι - Fintype.card G := by
  have hrt := rank_eq_trace_of_idem (wthMat_hermitian grp) (wthMat_idem grp hne)
  rw [trace_wthMat grp hne] at hrt
  have hle : Fintype.card G ≤ Fintype.card ι := le_of_lt hι
  have hcast : ((Fintype.card ι - Fintype.card G : ℕ) : ℝ)
      = (Fintype.card ι : ℝ) - (Fintype.card G : ℝ) := Nat.cast_sub hle
  rw [← hcast] at hrt
  exact Nat.cast_injective hrt

private theorem meas_quad {ι : Type*} [Fintype ι] (M : Matrix ι ι ℝ) :
    Measurable (fun x : ι → ℝ => x ⬝ᵥ M *ᵥ x) := by
  classical
  fun_prop

end

end ProbabilityTheory

namespace ProbabilityTheory

@[expose] public section


open MeasureTheory

/-- Between-group sum of squares `SSB = ∑ᵢ (x̄_{grp i} - x̄)²`. -/
noncomputable def sumSqBetween {ι G : Type*} [Fintype ι] [DecidableEq G] (grp : ι → G)
    (x : ι → ℝ) : ℝ :=
  ∑ i, (groupMean grp x (grp i) - (∑ j, x j) / Fintype.card ι) ^ 2

/-- Within-group sum of squares `SSW = ∑ᵢ (xᵢ - x̄_{grp i})²`. -/
noncomputable def sumSqWithin {ι G : Type*} [Fintype ι] [DecidableEq G] (grp : ι → G)
    (x : ι → ℝ) : ℝ :=
  ∑ i, (x i - groupMean grp x (grp i)) ^ 2

open Matrix Finset in private theorem sumSqBetween_affine {ι G : Type*} [Fintype ι] [DecidableEq G]
    (grp : ι → G) (hne : ∀ g, ∃ i, grp i = g) (hn : 0 < Fintype.card ι)
    (z : ι → ℝ) (m0 s v : ℝ) (hs2 : s ^ 2 = v) (hv0 : v ≠ 0) :
    sumSqBetween grp (fun i => m0 + s * z i) / v = sumSqBetween grp z := by
  unfold sumSqBetween
  have hterm : ∀ i : ι, (groupMean grp (fun j => m0 + s * z j) (grp i)
      - (∑ j, (m0 + s * z j)) / Fintype.card ι) ^ 2
      = s ^ 2 * (groupMean grp z (grp i) - (∑ j, z j) / Fintype.card ι) ^ 2 := by
    intro i
    rw [groupMean_affine grp hne z m0 s (grp i), grandMean_affine z m0 s hn]
    ring
  simp_rw [hterm, ← Finset.mul_sum, hs2]
  exact mul_div_cancel_left₀ _ hv0

open Matrix Finset in private theorem sumSqWithin_affine {ι G : Type*} [Fintype ι] [DecidableEq G]
    (grp : ι → G) (hne : ∀ g, ∃ i, grp i = g)
    (z : ι → ℝ) (m0 s v : ℝ) (hs2 : s ^ 2 = v) (hv0 : v ≠ 0) :
    sumSqWithin grp (fun i => m0 + s * z i) / v = sumSqWithin grp z := by
  unfold sumSqWithin
  have hterm : ∀ i : ι, ((m0 + s * z i) - groupMean grp (fun j => m0 + s * z j) (grp i)) ^ 2
      = s ^ 2 * (z i - groupMean grp z (grp i)) ^ 2 := by
    intro i
    rw [groupMean_affine grp hne z m0 s (grp i)]
    ring
  simp_rw [hterm, ← Finset.mul_sum, hs2]
  exact mul_div_cancel_left₀ _ hv0

open Matrix Finset in
private theorem quad_btw {ι G : Type*} [Fintype ι] [DecidableEq G]
    (grp : ι → G) (hne : ∀ g, ∃ i, grp i = g) (hn : 0 < Fintype.card ι) (x : ι → ℝ) :
    x ⬝ᵥ btwMat grp *ᵥ x = sumSqBetween grp x := by
  classical
  rw [dotProduct_mulVec_eq (btwMat_hermitian grp) (btwMat_idem grp hne hn) x]
  unfold sumSqBetween
  simp only [dotProduct, btwMat_mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_two]

open Matrix Finset in
private theorem quad_wth {ι G : Type*} [Fintype ι] [DecidableEq G] [DecidableEq ι]
    (grp : ι → G) (hne : ∀ g, ∃ i, grp i = g) (x : ι → ℝ) :
    x ⬝ᵥ wthMat grp *ᵥ x = sumSqWithin grp x := by
  rw [dotProduct_mulVec_eq (wthMat_hermitian grp) (wthMat_idem grp hne) x]
  unfold sumSqWithin
  simp only [dotProduct, wthMat_mulVec]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [pow_two]

open Matrix Finset in
private theorem meas_ssb {ι G : Type*} [Fintype ι] [DecidableEq G] (grp : ι → G) :
    Measurable (fun x : ι → ℝ => sumSqBetween grp x) := by
  unfold sumSqBetween groupMean
  fun_prop

open Matrix Finset in
private theorem meas_ssw {ι G : Type*} [Fintype ι] [DecidableEq G] (grp : ι → G) :
    Measurable (fun x : ι → ℝ => sumSqWithin grp x) := by
  unfold sumSqWithin groupMean
  fun_prop

/-- **Between-group chi-square law**: under `H₀` (all group means equal) with i.i.d. `N(μ, v)`
observations, `v ≠ 0`, and all groups nonempty, `SSB / v ~ χ²_{G-1}`. -/
theorem hasLaw_sumSqBetween_div {ι G : Type*} [Fintype ι] [Fintype G] [DecidableEq G]
    (grp : ι → G) (hne : ∀ g, ∃ i, grp i = g) (hG : 2 ≤ Fintype.card G)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ι → ℝ} {m0 : ℝ} {v : NNReal}
    (hv : v ≠ 0) (hX : HasLaw X (Measure.pi fun _ : ι => gaussianReal m0 v) μ) :
    HasLaw (fun ω => sumSqBetween grp (X ω) / (v : ℝ))
      (chiSquareMeasure (Fintype.card G - 1)) μ := by
  classical
  have hsurj : Function.Surjective grp := fun g => hne g
  have hle : Fintype.card G ≤ Fintype.card ι := Fintype.card_le_of_surjective grp hsurj
  have hn : 0 < Fintype.card ι := by omega
  have hneR : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have hs0 : Real.sqrt (v : ℝ) ≠ 0 := by
    rw [Real.sqrt_ne_zero']
    exact lt_of_le_of_ne (NNReal.coe_nonneg v) (Ne.symm hneR)
  have hs2 : (Real.sqrt (v : ℝ)) ^ 2 = (v : ℝ) := Real.sq_sqrt (NNReal.coe_nonneg v)
  set Z : Ω → ι → ℝ := fun ω i => (X ω i - m0) / Real.sqrt (v : ℝ) with hZdef
  have hZ : HasLaw Z (Measure.pi fun _ : ι => gaussianReal 0 1) μ := hasLaw_std hv hX
  have hXeq : ∀ ω, X ω = fun i => m0 + Real.sqrt (v : ℝ) * Z ω i := by
    intro ω
    funext i
    simp only [hZdef]
    field_simp
    ring
  have hscale : ∀ ω, sumSqBetween grp (X ω) / (v : ℝ) = sumSqBetween grp (Z ω) := by
    intro ω
    rw [hXeq ω]
    exact sumSqBetween_affine grp hne hn (Z ω) m0 (Real.sqrt (v : ℝ)) (v : ℝ) hs2 hneR
  have hquad : ∀ ω, sumSqBetween grp (X ω) / (v : ℝ)
      = dotProduct (Z ω) (Matrix.mulVec (btwMat grp) (Z ω)) := by
    intro ω
    calc sumSqBetween grp (X ω) / (v : ℝ)
        = sumSqBetween grp (Z ω) := hscale ω
      _ = dotProduct (Z ω) (Matrix.mulVec (btwMat grp) (Z ω)) := (quad_btw grp hne hn (Z ω)).symm
  have hfun : (fun ω => sumSqBetween grp (X ω) / (v : ℝ))
      = (fun ω => dotProduct (Z ω) (Matrix.mulVec (btwMat grp) (Z ω))) := funext hquad
  rw [hfun]
  have hrank : (btwMat grp).rank = Fintype.card G - 1 := rank_btwMat grp hne hn hG
  have hrankpos : 0 < (btwMat grp).rank := by rw [hrank]; omega
  have hpi : (Measure.pi fun _ : ι => gaussianReal 0 1).map
        (fun x : ι → ℝ => dotProduct x (Matrix.mulVec (btwMat grp) x))
      = chiSquareMeasure (btwMat grp).rank :=
    pi_gaussianReal_map_dotProduct_mulVec (btwMat_hermitian grp) (btwMat_idem grp hne hn) hrankpos
  have hmeas : Measurable (fun x : ι → ℝ => dotProduct x (Matrix.mulVec (btwMat grp) x)) :=
    meas_quad (btwMat grp)
  have hHasQuad : HasLaw (fun ω => dotProduct (Z ω) (Matrix.mulVec (btwMat grp) (Z ω)))
      (chiSquareMeasure (btwMat grp).rank) μ := by
    refine ⟨hmeas.comp_aemeasurable hZ.aemeasurable, ?_⟩
    have hcomp : (fun ω => dotProduct (Z ω) (Matrix.mulVec (btwMat grp) (Z ω)))
        = (fun x : ι → ℝ => dotProduct x (Matrix.mulVec (btwMat grp) x)) ∘ Z := rfl
    rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable hmeas.aemeasurable hZ.aemeasurable,
      hZ.map_eq, hpi]
  rw [← hrank]
  exact hHasQuad

/-- **Within-group chi-square law**: under the same hypotheses with `n > G`,
`SSW / v ~ χ²_{n-G}`. -/
theorem hasLaw_sumSqWithin_div {ι G : Type*} [Fintype ι] [Fintype G] [DecidableEq G]
    (grp : ι → G) (hne : ∀ g, ∃ i, grp i = g) (hι : Fintype.card G < Fintype.card ι)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ι → ℝ} {m0 : ℝ} {v : NNReal}
    (hv : v ≠ 0) (hX : HasLaw X (Measure.pi fun _ : ι => gaussianReal m0 v) μ) :
    HasLaw (fun ω => sumSqWithin grp (X ω) / (v : ℝ))
      (chiSquareMeasure (Fintype.card ι - Fintype.card G)) μ := by
  classical
  have hneR : (v : ℝ) ≠ 0 := NNReal.coe_ne_zero.mpr hv
  have hs0 : Real.sqrt (v : ℝ) ≠ 0 := by
    rw [Real.sqrt_ne_zero']
    exact lt_of_le_of_ne (NNReal.coe_nonneg v) (Ne.symm hneR)
  have hs2 : (Real.sqrt (v : ℝ)) ^ 2 = (v : ℝ) := Real.sq_sqrt (NNReal.coe_nonneg v)
  set Z : Ω → ι → ℝ := fun ω i => (X ω i - m0) / Real.sqrt (v : ℝ) with hZdef
  have hZ : HasLaw Z (Measure.pi fun _ : ι => gaussianReal 0 1) μ := hasLaw_std hv hX
  have hXeq : ∀ ω, X ω = fun i => m0 + Real.sqrt (v : ℝ) * Z ω i := by
    intro ω
    funext i
    simp only [hZdef]
    field_simp
    ring
  have hscale : ∀ ω, sumSqWithin grp (X ω) / (v : ℝ) = sumSqWithin grp (Z ω) := by
    intro ω
    rw [hXeq ω]
    exact sumSqWithin_affine grp hne (Z ω) m0 (Real.sqrt (v : ℝ)) (v : ℝ) hs2 hneR
  have hquad : ∀ ω, sumSqWithin grp (X ω) / (v : ℝ)
      = dotProduct (Z ω) (Matrix.mulVec (wthMat grp) (Z ω)) := by
    intro ω
    calc sumSqWithin grp (X ω) / (v : ℝ)
        = sumSqWithin grp (Z ω) := hscale ω
      _ = dotProduct (Z ω) (Matrix.mulVec (wthMat grp) (Z ω)) := (quad_wth grp hne (Z ω)).symm
  have hfun : (fun ω => sumSqWithin grp (X ω) / (v : ℝ))
      = (fun ω => dotProduct (Z ω) (Matrix.mulVec (wthMat grp) (Z ω))) := funext hquad
  rw [hfun]
  have hrank : (wthMat grp).rank = Fintype.card ι - Fintype.card G := rank_wthMat grp hne hι
  have hrankpos : 0 < (wthMat grp).rank := by rw [hrank]; omega
  have hpi : (Measure.pi fun _ : ι => gaussianReal 0 1).map
        (fun x : ι → ℝ => dotProduct x (Matrix.mulVec (wthMat grp) x))
      = chiSquareMeasure (wthMat grp).rank :=
    pi_gaussianReal_map_dotProduct_mulVec (wthMat_hermitian grp) (wthMat_idem grp hne) hrankpos
  have hmeas : Measurable (fun x : ι → ℝ => dotProduct x (Matrix.mulVec (wthMat grp) x)) :=
    meas_quad (wthMat grp)
  have hHasQuad : HasLaw (fun ω => dotProduct (Z ω) (Matrix.mulVec (wthMat grp) (Z ω)))
      (chiSquareMeasure (wthMat grp).rank) μ := by
    refine ⟨hmeas.comp_aemeasurable hZ.aemeasurable, ?_⟩
    have hcomp : (fun ω => dotProduct (Z ω) (Matrix.mulVec (wthMat grp) (Z ω)))
        = (fun x : ι → ℝ => dotProduct x (Matrix.mulVec (wthMat grp) x)) ∘ Z := rfl
    rw [hcomp, ← AEMeasurable.map_map_of_aemeasurable hmeas.aemeasurable hZ.aemeasurable,
      hZ.map_eq, hpi]
  rw [← hrank]
  exact hHasQuad

/-- **One-way ANOVA `F` test**: under `H₀` with `G ≥ 2` groups and `n > G`,
`(SSB / (G - 1)) / (SSW / (n - G)) ~ F(G - 1, n - G)`. -/
theorem hasLaw_oneWay_ANOVA_F {ι G : Type*} [Fintype ι] [Fintype G] [DecidableEq G]
    (grp : ι → G) (hne : ∀ g, ∃ i, grp i = g) (hG : 2 ≤ Fintype.card G)
    (hι : Fintype.card G < Fintype.card ι)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ι → ℝ} {m0 : ℝ} {v : NNReal}
    (hv : v ≠ 0) (hX : HasLaw X (Measure.pi fun _ : ι => gaussianReal m0 v) μ) :
    HasLaw (fun ω => (sumSqBetween grp (X ω) / (v : ℝ) / ((Fintype.card G - 1 : ℕ) : ℝ)) /
        (sumSqWithin grp (X ω) / (v : ℝ) / ((Fintype.card ι - Fintype.card G : ℕ) : ℝ)))
      (snedecorFMeasure (Fintype.card G - 1) (Fintype.card ι - Fintype.card G)) μ := by
  classical
  have hV1 : HasLaw (fun ω => sumSqBetween grp (X ω) / (v : ℝ))
      (chiSquareMeasure (Fintype.card G - 1)) μ :=
    hasLaw_sumSqBetween_div grp hne hG hv hX
  have hV2 : HasLaw (fun ω => sumSqWithin grp (X ω) / (v : ℝ))
      (chiSquareMeasure (Fintype.card ι - Fintype.card G)) μ :=
    hasLaw_sumSqWithin_div grp hne hι hv hX
  have := hX.isProbabilityMeasure
  have hIndepPi := indepFun_sumSqBetween_sumSqWithin (G := G) grp m0 v
  have hf : Measurable (fun x : ι → ℝ => sumSqBetween grp x) := meas_ssb grp
  have hg : Measurable (fun x : ι → ℝ => sumSqWithin grp x) := meas_ssw grp
  have hAZ : AEMeasurable (fun ω => sumSqBetween grp (X ω)) μ :=
    hf.comp_aemeasurable hX.aemeasurable
  have hBZ : AEMeasurable (fun ω => sumSqWithin grp (X ω)) μ :=
    hg.comp_aemeasurable hX.aemeasurable
  have hIndepX : IndepFun (fun ω => sumSqBetween grp (X ω))
      (fun ω => sumSqWithin grp (X ω)) μ := by
    rw [indepFun_iff_map_prod_eq_prod_map_map hAZ hBZ]
    have hpair : μ.map (fun ω => (sumSqBetween grp (X ω), sumSqWithin grp (X ω)))
        = (Measure.pi fun _ : ι => gaussianReal m0 v).map
          (fun x => (sumSqBetween grp x, sumSqWithin grp x)) := by
      have hcomp : (fun ω => (sumSqBetween grp (X ω), sumSqWithin grp (X ω)))
          = (fun x : ι → ℝ => (sumSqBetween grp x, sumSqWithin grp x)) ∘ X := rfl
      rw [hcomp, ← hX.map_eq,
        AEMeasurable.map_map_of_aemeasurable (hf.prodMk hg).aemeasurable hX.aemeasurable]
    have hfX : μ.map (fun ω => sumSqBetween grp (X ω))
        = (Measure.pi fun _ : ι => gaussianReal m0 v).map (fun x => sumSqBetween grp x) := by
      have hcomp : (fun ω => sumSqBetween grp (X ω))
          = (fun x : ι → ℝ => sumSqBetween grp x) ∘ X := rfl
      rw [hcomp, ← hX.map_eq, AEMeasurable.map_map_of_aemeasurable hf.aemeasurable hX.aemeasurable]
    have hgX : μ.map (fun ω => sumSqWithin grp (X ω))
        = (Measure.pi fun _ : ι => gaussianReal m0 v).map (fun x => sumSqWithin grp x) := by
      have hcomp : (fun ω => sumSqWithin grp (X ω))
          = (fun x : ι → ℝ => sumSqWithin grp x) ∘ X := rfl
      rw [hcomp, ← hX.map_eq, AEMeasurable.map_map_of_aemeasurable hg.aemeasurable hX.aemeasurable]
    rw [hpair, hfX, hgX]
    exact hIndepPi.map_prod_eq_prod_map_map hf.aemeasurable hg.aemeasurable
  have hV : IndepFun (fun ω => sumSqBetween grp (X ω) / (v : ℝ))
      (fun ω => sumSqWithin grp (X ω) / (v : ℝ)) μ :=
    hIndepX.comp (φ := fun y : ℝ => y / (v : ℝ)) (ψ := fun y : ℝ => y / (v : ℝ))
      (by fun_prop) (by fun_prop)
  have hd1 : 0 < Fintype.card G - 1 := by omega
  have hd2 : 0 < Fintype.card ι - Fintype.card G := by omega
  have hFmap := map_div_chiSquare_eq_snedecorF hd1 hd2 hV1 hV2 hV
  have hF : Measurable (fun x : ι → ℝ =>
      (sumSqBetween grp x / (v : ℝ) / ((Fintype.card G - 1 : ℕ) : ℝ)) /
      (sumSqWithin grp x / (v : ℝ) / ((Fintype.card ι - Fintype.card G : ℕ) : ℝ))) := by
    unfold sumSqBetween sumSqWithin groupMean
    fun_prop
  refine ⟨hF.comp_aemeasurable hX.aemeasurable, hFmap⟩

end

end ProbabilityTheory
