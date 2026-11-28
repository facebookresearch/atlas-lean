/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Complexity.QMA.ThresholdOperator
public import MathlibExt.Probability.BernoulliProductTail

/-!
# Threshold amplification of an acceptance operator

Exponential bounds for the threshold operator `thresholdOp k Q T` of an operator `0 ≤ Q ≤ 1`: the
sum, over outcome strings with at least `T` accepting blocks, of block products of `Q` and
`1 - Q`. Soundness holds for every unit `k`-block vector, entangled or not; completeness holds for
the product witness `ψ ⊗ ⋯ ⊗ ψ`. At threshold `k (c + s) / 2` with `2 p ≤ k (c - s) ^ 2` both
errors are at most `2⁻ᵖ`, and one block returns `Q`. The tails are Hoeffding's inequality for
independent Bernoulli coordinates with heterogeneous means.

This file is about operators only: it states nothing about circuits, acceptance probabilities of a
verifier, or complexity classes.

Sources: R. de Wolf, Quantum Computing: Lecture Notes, arXiv:1907.09415, Chapter 14.1 (error
reduction for QMA); W. Hoeffding, Probability inequalities for sums of bounded random variables,
Journal of the American Statistical Association 58 (1963), 13-30.
-/

@[expose] public section

open scoped BigOperators Matrix ComplexOrder
namespace Cslib.Complexity.Classes.QMA

set_option autoImplicit false

private theorem tailWeight_eq_measureReal {k : ℕ} {μ : Fin k → ℝ}
    (hμ : ∀ i, μ i ∈ Set.Icc (0 : ℝ) 1) (T : ℝ) :
    tailWeight μ T = (MathlibExt.Probability.Combinatorics.RandomSubset.randomSubsetLaw
      (fun i => (⟨μ i, hμ i⟩ : unitInterval))).real
      {ω | T ≤ ∑ i, MathlibExt.Probability.BernoulliProductTail.coordVar i ω} := by
  rw [MathlibExt.Probability.BernoulliProductTail.measureReal_sum_ge_eq_sum]
  rfl

/-- **Upper tail.** If every `μ i` lies in `[0, 1]` and is at most `s`, and `k * s ≤ T`, the tail
weight is at most `exp (-2 (T - k s) ^ 2 / k)`. At `k = 0` the bound is `exp 0 = 1`. -/
theorem tailWeight_le_exp {k : ℕ} {μ : Fin k → ℝ} (hμ : ∀ i, μ i ∈ Set.Icc (0 : ℝ) 1)
    {s T : ℝ} (hs : ∀ i, μ i ≤ s) (hT : (k : ℝ) * s ≤ T) :
    tailWeight μ T ≤ Real.exp (-2 * (T - (k : ℝ) * s) ^ 2 / (k : ℝ)) := by
  rw [tailWeight_eq_measureReal hμ T]
  exact MathlibExt.Probability.BernoulliProductTail.measureReal_sum_ge_le_exp _ _ _ hs hT

/-- **Lower tail.** If every `μ i` lies in `[0, 1]` and is at least `c`, and `T ≤ k * c`, the
tail weight is at least `1 - exp (-2 (k c - T) ^ 2 / k)`. -/
theorem one_sub_exp_le_tailWeight {k : ℕ} {μ : Fin k → ℝ} (hμ : ∀ i, μ i ∈ Set.Icc (0 : ℝ) 1)
    {c T : ℝ} (hc : ∀ i, c ≤ μ i) (hT : T ≤ (k : ℝ) * c) :
    1 - Real.exp (-2 * ((k : ℝ) * c - T) ^ 2 / (k : ℝ)) ≤ tailWeight μ T := by
  rw [tailWeight_eq_measureReal hμ T]
  have hmeas : MeasurableSet {ω : Fin k → Bool | T ≤ ∑ i,
      MathlibExt.Probability.BernoulliProductTail.coordVar i ω} :=
    (Set.toFinite _).measurableSet
  have hcompl := MeasureTheory.probReal_compl_eq_one_sub (μ :=
    MathlibExt.Probability.Combinatorics.RandomSubset.randomSubsetLaw
      (fun i => (⟨μ i, hμ i⟩ : unitInterval))) hmeas
  have hsub : {ω : Fin k → Bool | T ≤ ∑ i,
      MathlibExt.Probability.BernoulliProductTail.coordVar i ω}ᶜ ⊆
      {ω : Fin k → Bool | ∑ i,
        MathlibExt.Probability.BernoulliProductTail.coordVar i ω ≤ T} := by
    intro ω hω
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hω ⊢
    exact le_of_lt hω
  have hmono := MeasureTheory.measureReal_mono (μ :=
    MathlibExt.Probability.Combinatorics.RandomSubset.randomSubsetLaw
      (fun i => (⟨μ i, hμ i⟩ : unitInterval))) hsub
  have hle := MathlibExt.Probability.BernoulliProductTail.measureReal_sum_le_le_exp
    (fun i => (⟨μ i, hμ i⟩ : unitInterval)) _ _ hc hT
  linarith

private theorem quad_mem_Icc {m : ℕ} {Q : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ}
    (hQ0 : Q.PosSemidef) (hQ1 : (1 - Q).PosSemidef)
    (ψ : Fin (2 ^ m) → ℂ) (hψ : sqNorm ψ = 1) :
    (star ψ ⬝ᵥ (Q *ᵥ ψ)).re ∈ Set.Icc (0 : ℝ) 1 := by
  have h0 : 0 ≤ (star ψ ⬝ᵥ (Q *ᵥ ψ)).re := by
    have h := hQ0.re_dotProduct_nonneg ψ
    rwa [RCLike.re_to_complex] at h
  have h1 : (star ψ ⬝ᵥ (Q *ᵥ ψ)).re ≤ 1 := by
    have h := hQ1.re_dotProduct_nonneg ψ
    rw [RCLike.re_to_complex, Matrix.sub_mulVec, Matrix.one_mulVec,
      dotProduct_sub, Complex.sub_re, ← sqNorm_eq_re_star_dotProduct,
      hψ] at h
    linarith
  exact ⟨h0, h1⟩

private theorem eigenvalues_le_of_quad_le {m : ℕ}
    {Q : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ} (hQ0 : Q.PosSemidef)
    {s : ℝ}
    (hs : ∀ ψ : Fin (2 ^ m) → ℂ,
      sqNorm ψ = 1 → (star ψ ⬝ᵥ (Q *ᵥ ψ)).re ≤ s)
    (j : Fin (2 ^ m)) : hQ0.isHermitian.eigenvalues j ≤ s := by
  have h1 : star ⇑(hQ0.isHermitian.eigenvectorBasis j) ⬝ᵥ
      ⇑(hQ0.isHermitian.eigenvectorBasis j) = 1 := by
    have h : inner ℂ (⇑hQ0.isHermitian.eigenvectorBasis j)
        (⇑hQ0.isHermitian.eigenvectorBasis j) = 1 := by
      simp only [inner_self_eq_norm_sq_to_K,
        OrthonormalBasis.norm_eq_one, Complex.coe_algebraMap,
        Complex.ofReal_one, one_pow]
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm] at h
    exact h
  have hnorm : sqNorm ⇑(hQ0.isHermitian.eigenvectorBasis j) = 1 := by
    rw [sqNorm_eq_re_star_dotProduct, h1]
    rfl
  have hs_e := hs ⇑(hQ0.isHermitian.eigenvectorBasis j) hnorm
  rw [hQ0.isHermitian.mulVec_eigenvectorBasis j, dotProduct_smul, h1] at hs_e
  simpa using hs_e

/-- **Soundness against entangled witnesses.** If `0 ≤ Q ≤ 1` and every unit vector `ψ` has
`Re ⟪ψ, Q ψ⟫ ≤ s`, then for `k * s ≤ T` every unit `k`-block vector `Ψ`, entangled or not, has
`Re ⟪Ψ, thresholdOp k Q T Ψ⟫ ≤ exp (-2 (T - k s) ^ 2 / k)`. -/
theorem re_star_dotProduct_thresholdOp_mulVec_le_exp {k m : ℕ}
    {Q : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ} (hQ0 : Q.PosSemidef) (hQ1 : (1 - Q).PosSemidef)
    {s T : ℝ} (hs : ∀ ψ : Fin (2 ^ m) → ℂ, sqNorm ψ = 1 → (star ψ ⬝ᵥ (Q *ᵥ ψ)).re ≤ s)
    (hT : (k : ℝ) * s ≤ T) (Ψ : Fin (2 ^ (k * m)) → ℂ) (hΨ : sqNorm Ψ = 1) :
    (star Ψ ⬝ᵥ (thresholdOp k Q T *ᵥ Ψ)).re ≤ Real.exp (-2 * (T - (k : ℝ) * s) ^ 2 / (k : ℝ)) := by
  refine re_star_dotProduct_thresholdOp_mulVec_le hQ0.isHermitian T _ Ψ hΨ ?_
  intro j
  refine tailWeight_le_exp ?_ ?_ hT
  · intro i
    exact eigenvalues_mem_Icc_of_posSemidef hQ0 hQ1 (j i)
  · intro i
    exact eigenvalues_le_of_quad_le hQ0 hs (j i)

/-- **Completeness for the product witness.** If `0 ≤ Q ≤ 1` and the unit vector `ψ` has
`c ≤ Re ⟪ψ, Q ψ⟫`, then for `T ≤ k * c` the product vector `ψ ⊗ ⋯ ⊗ ψ` has threshold expectation
at least `1 - exp (-2 (k c - T) ^ 2 / k)`. -/
theorem one_sub_exp_le_re_star_dotProduct_thresholdOp_mulVec_blockProd {k m : ℕ}
    {Q : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ} (hQ0 : Q.PosSemidef) (hQ1 : (1 - Q).PosSemidef)
    {c T : ℝ} (ψ : Fin (2 ^ m) → ℂ) (hψ : sqNorm ψ = 1) (hc : c ≤ (star ψ ⬝ᵥ (Q *ᵥ ψ)).re)
    (hT : T ≤ (k : ℝ) * c) :
    1 - Real.exp (-2 * ((k : ℝ) * c - T) ^ 2 / (k : ℝ)) ≤
      (star (blockProd (fun _ : Fin k => ψ)) ⬝ᵥ
        (thresholdOp k Q T *ᵥ blockProd (fun _ : Fin k => ψ))).re := by
  rw [star_dotProduct_thresholdOp_mulVec_blockProd_const hQ0.isHermitian T ψ hψ,
    Complex.ofReal_re]
  refine one_sub_exp_le_tailWeight ?_ ?_ hT
  · intro i
    exact quad_mem_Icc hQ0 hQ1 ψ hψ
  · intro i
    exact hc

/-- From `2 p ≤ k d ^ 2`, the Hoeffding bound `exp (-2 × (k × d / 2) ^ 2 / k)` is at most `2⁻ᵖ`. -/
private theorem amplify_exp_le_inv_two_pow {k p : ℕ} {d : ℝ}
    (hk : 2 * (p : ℝ) ≤ (k : ℝ) * d ^ 2) :
    Real.exp (-2 * ((k : ℝ) * d / 2) ^ 2 / (k : ℝ)) ≤ ((2 : ℝ) ^ p)⁻¹ := by
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp only [Nat.cast_zero, zero_mul] at hk
    have hp0 : p = 0 := by
      have h1 : (p : ℝ) ≤ 0 := by linarith
      have h2 : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
      exact Nat.cast_eq_zero.mp (le_antisymm h1 h2)
    subst hp0
    simp
  · have hkR : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hkpos
    have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkR
    have hexp : -2 * ((k : ℝ) * d / 2) ^ 2 / (k : ℝ) = -((k : ℝ) * d ^ 2 / 2) := by
      field_simp
    rw [hexp, Real.exp_neg]
    have hpos : (0 : ℝ) < (2 : ℝ) ^ p := by positivity
    have h2e : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    have hpow : (2 : ℝ) ^ p ≤ (Real.exp 1) ^ p := pow_le_pow_left₀ (by norm_num) h2e p
    have hexpn : (Real.exp 1) ^ p = Real.exp ((p : ℝ) * 1) := (Real.exp_nat_mul 1 p).symm
    have hle : (p : ℝ) * 1 ≤ (k : ℝ) * d ^ 2 / 2 := by linarith [hk]
    have hexple : Real.exp ((p : ℝ) * 1) ≤ Real.exp ((k : ℝ) * d ^ 2 / 2) :=
      Real.exp_le_exp.mpr hle
    have hfinal : (2 : ℝ) ^ p ≤ Real.exp ((k : ℝ) * d ^ 2 / 2) := by
      calc (2 : ℝ) ^ p ≤ (Real.exp 1) ^ p := hpow
        _ = Real.exp ((p : ℝ) * 1) := hexpn
        _ ≤ Real.exp ((k : ℝ) * d ^ 2 / 2) := hexple
    exact inv_anti₀ hpos hfinal

/-- Number of repetitions `2 p q ^ 2`: enough for error `2⁻ᵖ` when the gap `c - s` is at least
`1 / q` (`two_mul_le_amplifyCount_mul_sq`). -/
def amplifyCount (p q : ℕ) : ℕ := 2 * p * q ^ 2

/-- If `1 ≤ q (c - s)`, then `k = amplifyCount p q` satisfies `2 p ≤ k (c - s) ^ 2`. -/
theorem two_mul_le_amplifyCount_mul_sq {p q : ℕ} {c s : ℝ} (hgap : 1 ≤ (q : ℝ) * (c - s)) :
    2 * (p : ℝ) ≤ (amplifyCount p q : ℝ) * (c - s) ^ 2 := by
  have hgap2 : (1 : ℝ) ≤ ((q : ℝ) * (c - s)) ^ 2 := by
    nlinarith [hgap, sq_nonneg ((q : ℝ) * (c - s) - 1)]
  have hpn : (0 : ℝ) ≤ (p : ℝ) := Nat.cast_nonneg p
  unfold amplifyCount
  push_cast
  nlinarith [hgap2, hpn]

/-- **Amplified soundness.** For `s ≤ c` and `2 p ≤ k (c - s) ^ 2`, if every unit vector has
`Re ⟪ψ, Q ψ⟫ ≤ s` under `0 ≤ Q ≤ 1`, then at threshold `k (c + s) / 2` every unit `k`-block vector,
entangled or not, has threshold expectation at most `2⁻ᵖ`. -/
theorem thresholdOp_amplify_sound {k m p : ℕ} {Q : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ}
    (hQ0 : Q.PosSemidef) (hQ1 : (1 - Q).PosSemidef) {c s : ℝ} (hsc : s ≤ c)
    (hk : 2 * (p : ℝ) ≤ (k : ℝ) * (c - s) ^ 2)
    (hs : ∀ ψ : Fin (2 ^ m) → ℂ, sqNorm ψ = 1 → (star ψ ⬝ᵥ (Q *ᵥ ψ)).re ≤ s)
    (Ψ : Fin (2 ^ (k * m)) → ℂ) (hΨ : sqNorm Ψ = 1) :
    (star Ψ ⬝ᵥ (thresholdOp k Q ((k : ℝ) * (c + s) / 2) *ᵥ Ψ)).re ≤ ((2 : ℝ) ^ p)⁻¹ := by
  have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hT : (k : ℝ) * s ≤ (k : ℝ) * (c + s) / 2 := by
    have h1 : (0 : ℝ) ≤ (k : ℝ) * (c - s) := mul_nonneg hkn (sub_nonneg.mpr hsc)
    linarith
  have hTS : ((k : ℝ) * (c + s) / 2) - (k : ℝ) * s = (k : ℝ) * (c - s) / 2 := by ring
  have hexp_le :
      Real.exp (-2 * (((k : ℝ) * (c + s) / 2) - (k : ℝ) * s) ^ 2 / (k : ℝ)) ≤
        ((2 : ℝ) ^ p)⁻¹ := by
    rw [hTS]
    exact amplify_exp_le_inv_two_pow hk
  have hbound := re_star_dotProduct_thresholdOp_mulVec_le_exp hQ0 hQ1 hs hT Ψ hΨ
  exact hbound.trans hexp_le

/-- **Amplified completeness.** For `s ≤ c` and `2 p ≤ k (c - s) ^ 2`, if the unit vector `ψ` has
`c ≤ Re ⟪ψ, Q ψ⟫` under `0 ≤ Q ≤ 1`, then at threshold `k (c + s) / 2` its `k`-fold product has
threshold expectation at least `1 - 2⁻ᵖ`. -/
theorem thresholdOp_amplify_complete {k m p : ℕ} {Q : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ}
    (hQ0 : Q.PosSemidef) (hQ1 : (1 - Q).PosSemidef) {c s : ℝ} (hsc : s ≤ c)
    (hk : 2 * (p : ℝ) ≤ (k : ℝ) * (c - s) ^ 2)
    (ψ : Fin (2 ^ m) → ℂ) (hψ : sqNorm ψ = 1) (hc : c ≤ (star ψ ⬝ᵥ (Q *ᵥ ψ)).re) :
    1 - ((2 : ℝ) ^ p)⁻¹ ≤
      (star (blockProd (fun _ : Fin k => ψ)) ⬝ᵥ
        (thresholdOp k Q ((k : ℝ) * (c + s) / 2) *ᵥ blockProd (fun _ : Fin k => ψ))).re := by
  have hkn : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hT : (k : ℝ) * (c + s) / 2 ≤ (k : ℝ) * c := by
    have h1 : (0 : ℝ) ≤ (k : ℝ) * (c - s) := mul_nonneg hkn (sub_nonneg.mpr hsc)
    linarith
  have hTS : (k : ℝ) * c - (k : ℝ) * (c + s) / 2 = (k : ℝ) * (c - s) / 2 := by ring
  have hexp_le :
      Real.exp (-2 * ((k : ℝ) * c - (k : ℝ) * (c + s) / 2) ^ 2 / (k : ℝ)) ≤
        ((2 : ℝ) ^ p)⁻¹ := by
    rw [hTS]
    exact amplify_exp_le_inv_two_pow hk
  have hbound :=
    one_sub_exp_le_re_star_dotProduct_thresholdOp_mulVec_blockProd hQ0 hQ1 ψ hψ hc hT
  have hmono : 1 - ((2 : ℝ) ^ p)⁻¹ ≤
      1 - Real.exp (-2 * ((k : ℝ) * c - (k : ℝ) * (c + s) / 2) ^ 2 / (k : ℝ)) := by
    linarith [hexp_le]
  exact hmono.trans hbound

private theorem filter_one_eq_singleton {T : ℝ} (hT0 : 0 < T) (hT1 : T ≤ 1) :
    Finset.univ.filter (fun b : Fin 1 → Bool => T ≤ acceptCount b) = {fun _ => true} := by
  ext b
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · intro h
    cases hb : b 0
    · have hacc : acceptCount b = 0 := by simp [acceptCount, hb]
      linarith
    · funext i
      have hi : i = 0 := Subsingleton.elim i 0
      rw [hi]
      simpa using hb
  · intro h
    rw [h]
    have h1 : acceptCount (fun _ : Fin 1 => true) = 1 := by
      simp [acceptCount]
    linarith

/-- **One block returns the operator.** For a threshold `T` in `(0, 1]`, the threshold operator
on one block is `Q`, read through the index identification `2 ^ m = 2 ^ (1 * m)`. -/
theorem thresholdOp_one_submatrix {m : ℕ} (Q : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ) {T : ℝ}
    (hT0 : 0 < T) (hT1 : T ≤ 1) :
    (thresholdOp 1 Q T).submatrix
        (Fin.cast (by rw [Nat.one_mul]) : Fin (2 ^ m) → Fin (2 ^ (1 * m)))
        (Fin.cast (by rw [Nat.one_mul]) : Fin (2 ^ m) → Fin (2 ^ (1 * m))) = Q := by
  have hd : ∀ u : Fin (2 ^ m),
      blockDigit 1 m 0 ((Fin.cast (by rw [Nat.one_mul]) : Fin (2 ^ m) → Fin (2 ^ (1 * m))) u)
        = u := by
    intro u
    ext
    simp [blockDigit, Nat.mod_eq_of_lt u.isLt]
  unfold thresholdOp
  rw [filter_one_eq_singleton hT0 hT1, Finset.sum_singleton]
  ext u v
  simp only [Matrix.submatrix_apply, thresholdBlockOp, blockOp, Fin.prod_univ_one, ite_true, hd]

end Cslib.Complexity.Classes.QMA
