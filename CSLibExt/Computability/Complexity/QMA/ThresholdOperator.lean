/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QMA.BlockEigenbasis
public import MathlibExt.Probability.Distributions.PoissonBinomial
public import Mathlib.LinearAlgebra.Matrix.DotProduct
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.Analysis.Complex.Order


/-!
# Threshold operator: spectral identities

The acceptance-operator-free spectral half of QMA threshold amplification over the merged block eigenbasis: threshold operator, Parseval weights, the convex-combination identity, and the product-witness identity. Exponential tail bounds are downstream.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder
namespace Cslib.Complexity.Classes.QMA

set_option autoImplicit false

/-- Number of accepting blocks in an outcome string. -/
noncomputable def acceptCount {k : ℕ} (b : Fin k → Bool) : ℝ := ∑ i, if b i then (1 : ℝ) else 0

/-- Heterogeneous Bernoulli upper-tail weight as a finite sum over outcome
strings; identified with the Poisson-binomial tail in
`tailWeight_eq_poissonBinomialTail` below. -/
noncomputable def tailWeight {k : ℕ} (μ : Fin k → ℝ) (T : ℝ) : ℝ := ∑ b ∈ Finset.univ.filter (fun b : Fin k → Bool => T ≤ acceptCount b), ∏ i, if b i then μ i else 1 - μ i

/-- T_k = Σ_{|S| ≥ T} ⊗_{i∈S} Q ⊗_{i∉S} (1 - Q) in Atlas block form (merged thresholdBlockOp is the single-subset operator) -/
noncomputable def thresholdOp (k : ℕ) {m : ℕ} (Q : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) (T : ℝ) : Matrix (Fin (2 ^ (k * m))) (Fin (2 ^ (k * m))) ℂ := ∑ b ∈ Finset.univ.filter (fun b : Fin k → Bool => T ≤ acceptCount b), thresholdBlockOp Q b

/-- The Euclidean squared norm of a lifted vector is the Atlas squared norm. -/
private theorem norm_toLp_sq {n : ℕ} (Ψ : Fin (2 ^ n) → ℂ) :
    ‖WithLp.toLp 2 Ψ‖ ^ 2 = sqNorm Ψ := by
  have hcast : star Ψ ⬝ᵥ Ψ = ((‖WithLp.toLp 2 Ψ‖ ^ 2 : ℝ) : ℂ) := by
    have h := EuclideanSpace.inner_eq_star_dotProduct
      (WithLp.toLp 2 Ψ) (WithLp.toLp 2 Ψ)
    rw [inner_self_eq_norm_sq_to_K, dotProduct_comm,
      ← RCLike.ofReal_pow] at h
    exact h.symm
  have hsq := sqNorm_eq_re_star_dotProduct Ψ
  rw [hcast, Complex.ofReal_re] at hsq
  exact hsq.symm

/-- A block operator of Hermitian blocks is Hermitian. -/
private theorem isHermitian_blockOp {k m : ℕ}
    {A : Fin k → Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ}
    (hA : ∀ i, (A i).IsHermitian) : (blockOp A).IsHermitian := by
  have hentry : ∀ (i : Fin k) (s t : Fin (2 ^ (k * m))),
      star (A i (blockDigit k m i t) (blockDigit k m i s))
        = A i (blockDigit k m i s) (blockDigit k m i t) := by
    intro i s t
    have hAi' : ((A i)ᴴ) = A i := hA i
    have hsym : A i (blockDigit k m i s) (blockDigit k m i t)
        = star (A i (blockDigit k m i t) (blockDigit k m i s)) := by
      conv_lhs => rw [← hAi']
      rw [Matrix.conjTranspose_apply]
    exact hsym.symm
  show (blockOp A)ᴴ = blockOp A
  ext s t
  rw [Matrix.conjTranspose_apply]
  simp only [blockOp, star_prod]
  exact Finset.prod_congr rfl (fun i _ => hentry i s t)

/-- A sum of Hermitian matrices is Hermitian. -/
private theorem isHermitian_finset_sum {ι : Type*} {n : Type*}
    (f : ι → Matrix n n ℂ) (s : Finset ι) :
    (∀ b ∈ s, (f b).IsHermitian) → (∑ b ∈ s, f b).IsHermitian := by
  classical
  induction s using Finset.induction with
  | empty =>
    intro _
    simp only [Finset.sum_empty]
    show (0 : Matrix n n ℂ)ᴴ = 0
    ext i j
    rw [Matrix.conjTranspose_apply]
    simp
  | insert a s has ih =>
    intro h
    rw [Finset.sum_insert has]
    exact ((h a (Finset.mem_insert_self a s)).add
      (ih (fun b hb => h b (Finset.mem_insert_of_mem hb))))

/-- For a Hermitian matrix, the sesquilinear form is conjugate-symmetric. -/
private theorem star_dotProduct_mulVec_adjoint {n : Type*} [Fintype n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (x y : n → ℂ) :
    star x ⬝ᵥ (A *ᵥ y) = starRingEnd ℂ (star y ⬝ᵥ (A *ᵥ x)) := by
  have hentry : ∀ i j, A i j = star (A j i) := by
    intro i j
    have hA' : Aᴴ = A := hA
    conv_lhs => rw [← hA']
    rw [Matrix.conjTranspose_apply]
  simp only [Matrix.mulVec, dotProduct, Pi.star_apply, map_sum, map_mul,
    Finset.mul_sum, Finset.sum_mul]
  simp only [starRingEnd_apply, star_star]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [hentry i j]
  ring

/-- The expectation of a Hermitian matrix in any vector is real. -/
private theorem star_dotProduct_mulVec_self_eq_re {n : Type*} [Fintype n]
    {A : Matrix n n ℂ} (hA : A.IsHermitian) (x : n → ℂ) :
    star x ⬝ᵥ (A *ᵥ x) = (((star x ⬝ᵥ (A *ᵥ x)).re : ℝ) : ℂ) := by
  have hconj : starRingEnd ℂ (star x ⬝ᵥ (A *ᵥ x)) = star x ⬝ᵥ (A *ᵥ x) :=
    (star_dotProduct_mulVec_adjoint hA x x).symm
  rw [starRingEnd_apply] at hconj
  have him : (star x ⬝ᵥ (A *ᵥ x)).im = 0 := Complex.conj_eq_iff_im.mp hconj
  have hre := Complex.re_add_im (star x ⬝ᵥ (A *ᵥ x))
  rw [him] at hre
  simpa using hre.symm

/-- If `Q` is Hermitian, the threshold operator is Hermitian for every threshold `T`. -/
theorem thresholdOp_isHermitian {k m : ℕ} {Q : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ} (hQ : Q.IsHermitian) (T : ℝ) : (thresholdOp k Q T).IsHermitian := by
  have hblock : ∀ b ∈ Finset.univ.filter (fun b : Fin k → Bool => T ≤ acceptCount b),
      (thresholdBlockOp Q b).IsHermitian := by
    intro b _
    show (blockOp (fun i => if b i then Q else 1 - Q)).IsHermitian
    apply isHermitian_blockOp
    intro i
    by_cases hb : b i
    · simp [hb]
      exact hQ
    · simp [hb]
      exact Matrix.isHermitian_one.sub hQ
  show (∑ b ∈ Finset.univ.filter (fun b : Fin k → Bool => T ≤ acceptCount b),
    thresholdBlockOp Q b).IsHermitian
  exact isHermitian_finset_sum _ _ hblock

/-- diagonal action of T_k on the product eigenbasis (sum of merged thresholdBlockOp_mulVec_productEigenvector) -/
theorem thresholdOp_mulVec_productEigenvector {k m : ℕ} {Q : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ} (hQ : Q.IsHermitian) (T : ℝ) (j : Fin k → Fin (2 ^ m)) : thresholdOp k Q T *ᵥ productEigenvector hQ j = ((tailWeight (fun i => hQ.eigenvalues (j i)) T : ℝ) : ℂ) • productEigenvector hQ j := by
  have hsum : thresholdOp k Q T *ᵥ productEigenvector hQ j
      = ∑ b ∈ Finset.univ.filter (fun b : Fin k → Bool => T ≤ acceptCount b),
        ((∏ i, if b i then ((hQ.eigenvalues (j i) : ℝ) : ℂ)
          else 1 - ((hQ.eigenvalues (j i) : ℝ) : ℂ)) • productEigenvector hQ j) := by
    unfold thresholdOp
    rw [Matrix.sum_mulVec]
    apply Finset.sum_congr rfl
    intro b _
    exact thresholdBlockOp_mulVec_productEigenvector hQ b j
  rw [hsum, ← Finset.sum_smul]
  congr 1
  unfold tailWeight
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hb : b i
  · simp only [ite_eq_left hb]
  · simp only [ite_eq_right hb, Complex.ofReal_sub, Complex.ofReal_one]

/-- Parseval: the weights `‖⟪v_j, Ψ⟫‖²` over the product eigenbasis sum to the squared norm
of `Ψ`. -/
theorem sum_norm_sq_inner_productEigenbasis {k m : ℕ} {Q : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ} (hQ : Q.IsHermitian) (Ψ : Fin (2 ^ (k * m)) → ℂ) : ∑ j : Fin k → Fin (2 ^ m), ‖inner ℂ (productEigenbasis hQ k j) (WithLp.toLp 2 Ψ)‖ ^ 2 = sqNorm Ψ := by
  rw [(productEigenbasis hQ k).sum_sq_norm_inner_right (WithLp.toLp 2 Ψ)]
  exact norm_toLp_sq Ψ

/-- For Hermitian `Q` and every `k`-block vector `Ψ`, entangled or not, the quadratic form of the
threshold operator is `∑ j, ‖⟪v_j, Ψ⟫‖² * tailWeight (λ_j) T` over the product eigenvectors `v_j`
with eigenvalue tuples `λ_j`; the combination is convex when `Ψ` is a unit vector. -/
theorem star_dotProduct_thresholdOp_mulVec {k m : ℕ} {Q : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ} (hQ : Q.IsHermitian) (T : ℝ) (Ψ : Fin (2 ^ (k * m)) → ℂ) : star Ψ ⬝ᵥ (thresholdOp k Q T *ᵥ Ψ) = ∑ j : Fin k → Fin (2 ^ m), ((‖inner ℂ (productEigenbasis hQ k j) (WithLp.toLp 2 Ψ)‖ ^ 2 * tailWeight (fun i => hQ.eigenvalues (j i)) T : ℝ) : ℂ) := by
  have hT : (thresholdOp k Q T).IsHermitian := thresholdOp_isHermitian hQ T
  have hLHS : star Ψ ⬝ᵥ (thresholdOp k Q T *ᵥ Ψ)
      = inner ℂ (WithLp.toLp 2 Ψ) (WithLp.toLp 2 (thresholdOp k Q T *ᵥ Ψ)) := by
    rw [EuclideanSpace.inner_toLp_toLp, dotProduct_comm]
  rw [hLHS, ← (productEigenbasis hQ k).sum_inner_mul_inner]
  apply Finset.sum_congr rfl
  intro j _
  have hpe : ⇑(productEigenbasis hQ k j) = productEigenvector hQ j :=
    productEigenbasis_apply hQ j
  have hdiag := thresholdOp_mulVec_productEigenvector hQ T j
  have hF1 : inner ℂ (WithLp.toLp 2 Ψ) (productEigenbasis hQ k j)
      = star Ψ ⬝ᵥ productEigenvector hQ j := by
    have h := EuclideanSpace.inner_eq_star_dotProduct (WithLp.toLp 2 Ψ)
      (productEigenbasis hQ k j)
    have h' : inner ℂ (WithLp.toLp 2 Ψ) (productEigenbasis hQ k j)
        = (⇑(productEigenbasis hQ k j)) ⬝ᵥ star Ψ := h
    rw [h', hpe, dotProduct_comm]
  have hconj : starRingEnd ℂ (((tailWeight (fun i => hQ.eigenvalues (j i)) T : ℝ) : ℂ))
      = ((tailWeight (fun i => hQ.eigenvalues (j i)) T : ℝ) : ℂ) := by
    rw [starRingEnd_apply]
    exact RCLike.conj_ofReal _
  have hmul : (star Ψ ⬝ᵥ productEigenvector hQ j)
        * starRingEnd ℂ (star Ψ ⬝ᵥ productEigenvector hQ j)
      = ((‖star Ψ ⬝ᵥ productEigenvector hQ j‖ ^ 2 : ℝ) : ℂ) := by
    rw [starRingEnd_apply]
    have h := RCLike.mul_conj (star Ψ ⬝ᵥ productEigenvector hQ j)
    simpa [Complex.ofReal_pow] using h
  have hF2 : inner ℂ (productEigenbasis hQ k j)
        (WithLp.toLp 2 (thresholdOp k Q T *ᵥ Ψ))
      = ((tailWeight (fun i => hQ.eigenvalues (j i)) T : ℝ) : ℂ)
        * starRingEnd ℂ (star Ψ ⬝ᵥ productEigenvector hQ j) := by
    have h := EuclideanSpace.inner_eq_star_dotProduct (productEigenbasis hQ k j)
      (WithLp.toLp 2 (thresholdOp k Q T *ᵥ Ψ))
    have h' : inner ℂ (productEigenbasis hQ k j)
          (WithLp.toLp 2 (thresholdOp k Q T *ᵥ Ψ))
        = (thresholdOp k Q T *ᵥ Ψ) ⬝ᵥ star ⇑(productEigenbasis hQ k j) := h
    have hadj := star_dotProduct_mulVec_adjoint hT (productEigenvector hQ j) Ψ
    rw [h', hpe, dotProduct_comm, hadj, hdiag]
    simp only [dotProduct_smul, smul_eq_mul, map_mul, hconj]
  have hnorm : ‖inner ℂ (productEigenbasis hQ k j) (WithLp.toLp 2 Ψ)‖
      = ‖star Ψ ⬝ᵥ productEigenvector hQ j‖ := by
    have h1 : inner ℂ (productEigenbasis hQ k j) (WithLp.toLp 2 Ψ)
        = starRingEnd ℂ (star Ψ ⬝ᵥ productEigenvector hQ j) := by
      rw [← hF1, starRingEnd_apply]
      exact (inner_conj_symm _ _).symm
    rw [h1, starRingEnd_apply]
    exact RCLike.norm_conj _
  rw [hF1, hF2, hnorm, Complex.ofReal_mul, ← hmul]
  ring

/-- If `Q` and `1 - Q` are positive semidefinite, every eigenvalue of `Q` lies in `[0, 1]`. -/
theorem eigenvalues_mem_Icc_of_posSemidef {m : ℕ} {Q : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ} (hQ0 : Q.PosSemidef) (hQ1 : (1 - Q).PosSemidef) (j : Fin (2 ^ m)) : hQ0.isHermitian.eigenvalues j ∈ Set.Icc (0 : ℝ) 1 := by
  rw [Set.mem_Icc]
  refine ⟨hQ0.eigenvalues_nonneg j, ?_⟩
  set v : Fin (2 ^ m) → ℂ := ⇑(hQ0.isHermitian.eigenvectorBasis j) with hv
  have hnn := hQ1.re_dotProduct_nonneg v
  have hnorm1 : inner ℂ (hQ0.isHermitian.eigenvectorBasis j)
      (hQ0.isHermitian.eigenvectorBasis j) = 1 := by
    have h := orthonormal_iff_ite.mp hQ0.isHermitian.eigenvectorBasis.orthonormal j j
    rwa [ite_eq_left rfl] at h
  have hvv : star v ⬝ᵥ v = 1 := by
    have h := EuclideanSpace.inner_eq_star_dotProduct (hQ0.isHermitian.eigenvectorBasis j)
      (hQ0.isHermitian.eigenvectorBasis j)
    rw [hnorm1, dotProduct_comm] at h
    exact h.symm
  have heig : hQ0.isHermitian.eigenvalues j = (star v ⬝ᵥ (Q *ᵥ v)).re := by
    have hmul := hQ0.isHermitian.mulVec_eigenvectorBasis j
    have hdot : star v ⬝ᵥ (Q *ᵥ v) = ((hQ0.isHermitian.eigenvalues j : ℝ) : ℂ) := by
      have hQv : Q *ᵥ v = ((hQ0.isHermitian.eigenvalues j : ℝ) : ℂ) • v := hmul
      rw [hQv]
      simp only [dotProduct_smul, smul_eq_mul, hvv, mul_one]
    rw [hdot, Complex.ofReal_re]
  have hsub : star v ⬝ᵥ ((1 - Q) *ᵥ v) = 1 - star v ⬝ᵥ (Q *ᵥ v) := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hvv]
  rw [hsub] at hnn
  have hnn' : 0 ≤ 1 - (star v ⬝ᵥ (Q *ᵥ v)).re := by
    simpa using hnn
  rw [← heig] at hnn'
  linarith

/-- If every `μ i` lies in `[0, 1]`, the tail weight lies in `[0, 1]` for every threshold. -/
theorem tailWeight_mem_Icc {k : ℕ} {μ : Fin k → ℝ} (hμ : ∀ i, μ i ∈ Set.Icc (0 : ℝ) 1) (T : ℝ) : tailWeight μ T ∈ Set.Icc (0 : ℝ) 1 := by
  have hfactor : ∀ (b : Fin k → Bool) (i : Fin k),
      0 ≤ (if b i then μ i else 1 - μ i) := by
    intro b i
    by_cases hb : b i
    · simp only [ite_eq_left hb]
      exact (hμ i).1
    · simp only [ite_eq_right hb]
      have h2 := (hμ i).2
      linarith
  rw [Set.mem_Icc]
  constructor
  · show 0 ≤ ∑ b ∈ Finset.univ.filter (fun b : Fin k → Bool => T ≤ acceptCount b),
        ∏ i, (if b i then μ i else 1 - μ i)
    apply Finset.sum_nonneg
    intro b _
    apply Finset.prod_nonneg
    intro i _
    exact hfactor b i
  · have hsub : tailWeight μ T
        ≤ ∑ b : Fin k → Bool, ∏ i, (if b i then μ i else 1 - μ i) := by
      show (∑ b ∈ Finset.univ.filter (fun b : Fin k → Bool => T ≤ acceptCount b),
          ∏ i, (if b i then μ i else 1 - μ i)) ≤ _
      refine Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) ?_
      intro b _ _
      apply Finset.prod_nonneg
      intro i _
      exact hfactor b i
    have hfull : (∑ b : Fin k → Bool, ∏ i, (if b i then μ i else 1 - μ i)) = 1 := by
      have h := Fintype.prod_sum (fun i (c : Bool) => if c then μ i else 1 - μ i)
      have hper : ∀ i : Fin k, (∑ c : Bool, (if c then μ i else 1 - μ i)) = 1 := by
        intro i
        rw [Fintype.sum_bool]
        first
          | show μ i + (1 - μ i) = 1; ring
      show (∑ x : Fin k → Bool, ∏ i, (fun i (c : Bool) => if c then μ i else 1 - μ i) i (x i)) = 1
      rw [← h]
      simp only [hper, Finset.prod_const_one]
    rw [hfull] at hsub
    exact hsub

/-- The outcome-string upper-tail weight is the Poisson-binomial tail at
the ceiling threshold. -/
theorem tailWeight_eq_poissonBinomialTail {k : ℕ} (μ : Fin k → ℝ) (T : ℝ) :
    tailWeight μ T = ProbabilityTheory.poissonBinomialTail μ ⌈T⌉₊ := by
  classical
  have hcount : ∀ b : Fin k → Bool,
      acceptCount b = ((Finset.univ.filter (fun i => b i)).card : ℝ) := by
    intro b
    exact Finset.sum_boole (fun i : Fin k => b i) Finset.univ (R := ℝ)
  have hpred : ∀ b : Fin k → Bool,
      (T ≤ acceptCount b) ↔ (⌈T⌉₊ ≤ (Finset.univ.filter (fun i => b i)).card) := by
    intro b
    rw [hcount b]
    exact Nat.ceil_le.symm
  have hprod : ∀ b : Fin k → Bool,
      (∏ i, if b i then μ i else 1 - μ i)
        = (∏ i ∈ Finset.univ.filter (fun i => b i), μ i)
          * ∏ i ∈ Finset.univ \ Finset.univ.filter (fun i => b i), (1 - μ i) := by
    intro b
    have hset : Finset.univ.filter (fun i : Fin k => ¬ (b i : Prop))
        = Finset.univ \ Finset.univ.filter (fun i => b i) := by
      ext i
      simp
    rw [Finset.prod_ite]
    congr 1
    rw [hset]
  have hleft : ∀ b : Fin k → Bool,
      (fun i => decide (i ∈ Finset.univ.filter (fun j => b j))) = b := by
    intro b
    funext i
    by_cases hb : b i <;> simp [hb]
  have hright : ∀ A : Finset (Fin k),
      Finset.univ.filter (fun i => decide (i ∈ A)) = A := by
    intro A
    ext i
    simp
  have hregroup : tailWeight μ T
      = ∑ A ∈ Finset.univ.powerset.filter (fun A => ⌈T⌉₊ ≤ A.card),
        (∏ i ∈ A, μ i) * ∏ i ∈ Finset.univ \ A, (1 - μ i) := by
    unfold tailWeight
    apply Finset.sum_nbij (fun b => Finset.univ.filter (fun j => b j))
    · intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_powerset] at hb ⊢
      constructor
      · exact Finset.filter_subset _ _
      · exact (hpred b).mp hb
    · intro x₁ _ x₂ _ heq
      simp only at heq
      have e1 := hleft x₁
      have e2 := hleft x₂
      rw [← e1, ← e2, heq]
    · intro A hA
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at hA
      refine ⟨fun i => decide (i ∈ A), ?_, ?_⟩
      · simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
        apply (hpred _).mpr
        have hr := hright A
        have hcard : (Finset.univ.filter (fun j => decide (j ∈ A))).card = A.card := by
          rw [hr]
        rw [hcard]
        exact hA.2
      · exact hright A
    · intro b _
      exact hprod b
  have hexpand : ProbabilityTheory.poissonBinomialTail μ ⌈T⌉₊
      = ∑ A ∈ Finset.univ.powerset.filter (fun A => ⌈T⌉₊ ≤ A.card),
        (∏ i ∈ A, μ i) * ∏ i ∈ Finset.univ \ A, (1 - μ i) := by
    unfold ProbabilityTheory.poissonBinomialTail ProbabilityTheory.poissonBinomialPMF
    have hset : (Finset.Icc ⌈T⌉₊ k).biUnion
        (fun j => (Finset.univ : Finset (Fin k)).powersetCard j)
        = Finset.univ.powerset.filter (fun A => ⌈T⌉₊ ≤ A.card) := by
      ext A
      simp only [Finset.mem_biUnion, Finset.mem_powersetCard, Finset.mem_Icc,
        Finset.mem_filter, Finset.mem_powerset]
      constructor
      · rintro ⟨j, ⟨hcj, _⟩, hsub, hcard⟩
        refine ⟨hsub, ?_⟩
        rw [hcard]
        exact hcj
      · rintro ⟨hsub, hcc⟩
        refine ⟨A.card, ⟨hcc, ?_⟩, hsub, rfl⟩
        have h1 : A.card ≤ (Finset.univ : Finset (Fin k)).card :=
          Finset.card_le_card hsub
        rwa [Finset.card_univ, Fintype.card_fin] at h1
    have hdisj : ((↑(Finset.Icc ⌈T⌉₊ k) : Set ℕ)).PairwiseDisjoint
        (fun j => (Finset.univ : Finset (Fin k)).powersetCard j) := by
      intro x _ y _ hne
      exact Finset.disjoint_powersetCard_of_ne hne _ _
    have hbi := Finset.sum_biUnion (s := Finset.Icc ⌈T⌉₊ k)
      (t := fun j => (Finset.univ : Finset (Fin k)).powersetCard j)
      (f := fun A => (∏ i ∈ A, μ i) * ∏ i ∈ Finset.univ \ A, (1 - μ i)) hdisj
    rw [hset] at hbi
    exact hbi.symm
  rw [hregroup, hexpand]

/-- For Hermitian `Q`, a unit vector `Ψ` and a bound `B` on `tailWeight (λ_j) T` for every
eigenvalue tuple `λ_j`, the real part of the quadratic form of the threshold operator is at
most `B`. -/
theorem re_star_dotProduct_thresholdOp_mulVec_le {k m : ℕ} {Q : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ} (hQ : Q.IsHermitian) (T B : ℝ) (Ψ : Fin (2 ^ (k * m)) → ℂ) (hΨ : sqNorm Ψ = 1) (hB : ∀ j : Fin k → Fin (2 ^ m), tailWeight (fun i => hQ.eigenvalues (j i)) T ≤ B) : (star Ψ ⬝ᵥ (thresholdOp k Q T *ᵥ Ψ)).re ≤ B := by
  have hmain := star_dotProduct_thresholdOp_mulVec hQ T Ψ
  have hre : (star Ψ ⬝ᵥ (thresholdOp k Q T *ᵥ Ψ)).re
      = ∑ j : Fin k → Fin (2 ^ m), ‖inner ℂ (productEigenbasis hQ k j) (WithLp.toLp 2 Ψ)‖ ^ 2
        * tailWeight (fun i => hQ.eigenvalues (j i)) T := by
    rw [hmain, Complex.re_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [Complex.ofReal_re]
  rw [hre]
  calc (∑ j : Fin k → Fin (2 ^ m), ‖inner ℂ (productEigenbasis hQ k j) (WithLp.toLp 2 Ψ)‖ ^ 2
          * tailWeight (fun i => hQ.eigenvalues (j i)) T)
        ≤ (∑ j : Fin k → Fin (2 ^ m), ‖inner ℂ (productEigenbasis hQ k j) (WithLp.toLp 2 Ψ)‖ ^ 2 * B) :=
          Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hB j) (sq_nonneg _))
      _ = B := by rw [← Finset.sum_mul, sum_norm_sq_inner_productEigenbasis, hΨ, one_mul]

/-- For Hermitian `Q` and a unit vector `ψ`, the quadratic form of the threshold operator at the
product vector `ψ ⊗ ⋯ ⊗ ψ` is `tailWeight (p, …, p) T` with `p = Re ⟪ψ, Q ψ⟫`. -/
theorem star_dotProduct_thresholdOp_mulVec_blockProd_const {k m : ℕ} {Q : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ} (hQ : Q.IsHermitian) (T : ℝ) (ψ : Fin (2 ^ m) → ℂ) (hψ : sqNorm ψ = 1) : star (blockProd (fun _ : Fin k => ψ)) ⬝ᵥ (thresholdOp k Q T *ᵥ blockProd (fun _ : Fin k => ψ)) = ((tailWeight (fun _ : Fin k => (star ψ ⬝ᵥ (Q *ᵥ ψ)).re) T : ℝ) : ℂ) := by
  have he : star ψ ⬝ᵥ (Q *ᵥ ψ) = (((star ψ ⬝ᵥ (Q *ᵥ ψ)).re : ℝ) : ℂ) :=
    star_dotProduct_mulVec_self_eq_re hQ ψ
  have hψ1 : star ψ ⬝ᵥ ψ = 1 := by
    have hcast : star ψ ⬝ᵥ ψ = ((‖WithLp.toLp 2 ψ‖ ^ 2 : ℝ) : ℂ) := by
      have h := EuclideanSpace.inner_eq_star_dotProduct
        (WithLp.toLp 2 ψ) (WithLp.toLp 2 ψ)
      rw [inner_self_eq_norm_sq_to_K, dotProduct_comm,
        ← RCLike.ofReal_pow] at h
      exact h.symm
    rw [hcast, norm_toLp_sq, hψ, Complex.ofReal_one]
  have hsum : star (blockProd (fun _ : Fin k => ψ)) ⬝ᵥ
        (thresholdOp k Q T *ᵥ blockProd (fun _ : Fin k => ψ))
      = ∑ b ∈ Finset.univ.filter (fun b : Fin k → Bool => T ≤ acceptCount b),
        ∏ i, (if b i then star ψ ⬝ᵥ (Q *ᵥ ψ) else 1 - star ψ ⬝ᵥ (Q *ᵥ ψ)) := by
    unfold thresholdOp
    rw [Matrix.sum_mulVec, dotProduct_sum]
    apply Finset.sum_congr rfl
    intro b _
    have hb2 : star (blockProd (fun _ : Fin k => ψ)) ⬝ᵥ
          (blockOp (fun i => if b i then Q else 1 - Q) *ᵥ blockProd (fun _ : Fin k => ψ))
        = ∏ i, star ψ ⬝ᵥ ((if b i then Q else 1 - Q) *ᵥ ψ) :=
      blockExpectation_blockProd (fun i => if b i then Q else 1 - Q) (fun _ : Fin k => ψ)
    show star (blockProd (fun _ : Fin k => ψ)) ⬝ᵥ
        (blockOp (fun i => if b i then Q else 1 - Q) *ᵥ blockProd (fun _ : Fin k => ψ)) = _
    rw [hb2]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hbi : b i
    · simp [hbi]
    · simp [hbi]
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub, hψ1]
  rw [hsum]
  unfold tailWeight
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hbi : b i
  · simp only [ite_eq_left hbi]
    show star ψ ⬝ᵥ (Q *ᵥ ψ) = (((star ψ ⬝ᵥ (Q *ᵥ ψ)).re : ℝ) : ℂ)
    exact he
  · simp only [ite_eq_right hbi, Complex.ofReal_sub, Complex.ofReal_one]
    conv_lhs => rw [he]

end Cslib.Complexity.Classes.QMA
