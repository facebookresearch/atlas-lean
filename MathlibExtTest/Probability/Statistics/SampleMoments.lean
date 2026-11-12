/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.SampleMoments
public import Mathlib.MeasureTheory.Measure.Dirac.Basic
public import Mathlib.MeasureTheory.Measure.Prod
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.Independence.InfinitePi

@[expose] public section

open MeasureTheory ProbabilityTheory MathlibExt.Probability
open scoped BigOperators ENNReal

namespace MathlibExtTest.Probability.Statistics.SampleMoments

open MathlibExt.Probability

/-- A fair coin on `Bool`. -/
noncomputable def fairCoin : Measure Bool :=
  (2 : ENNReal)⁻¹ • (Measure.dirac true + Measure.dirac false)

instance : IsProbabilityMeasure fairCoin := by
  constructor
  simp [fairCoin, ← two_mul, ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top]

/-- The sign `±1` of a coin toss. -/
noncomputable def coinSign (b : Bool) : ℝ := if b then 1 else -1

/-- Two fair signs on `Bool × Bool`: coordinate `0` reads the first coin, coordinate `1` the
second. -/
noncomputable def twoSigns (i : Fin 2) (ω : Bool × Bool) : ℝ :=
  if i = 0 then coinSign ω.1 else coinSign ω.2

/-- Constant observations: the sample variance is identically `0`. -/
example (c : ℝ) (n : ℕ) (hn : 2 ≤ n) :
    FiniteProbability.sampleVarUnbiased (fun _ : Fin n => c) = 0 := by
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  rw [FiniteProbability.sampleVarUnbiased_eq_sum_div, FiniteProbability.sampleMean_eq_sum_div]
  simp [Finset.sum_const, hnR]

private theorem iIndepFun_twoSigns : iIndepFun twoSigns (fairCoin.prod fairCoin) := by
  have key : ∀ S : Finset (Fin 2), S = ∅ ∨ S = {0} ∨ S = {1} ∨ S = Finset.univ := by decide
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets _
  have h0 : twoSigns 0 ⁻¹' sets 0 = (coinSign ⁻¹' sets 0) ×ˢ Set.univ := by
    ext ω; simp [twoSigns]
  have h1 : twoSigns 1 ⁻¹' sets 1 = Set.univ ×ˢ (coinSign ⁻¹' sets 1) := by
    ext ω; simp [twoSigns]
  rcases key S with rfl | rfl | rfl | rfl
  · simp
  · simp
  · simp
  · have : (⋂ i ∈ (Finset.univ : Finset (Fin 2)), twoSigns i ⁻¹' sets i)
        = (coinSign ⁻¹' sets 0) ×ˢ (coinSign ⁻¹' sets 1) := by
      ext ω; simp [Fin.forall_fin_two, twoSigns]
    rw [this, Fin.prod_univ_two, h0, h1]
    simp only [Measure.prod_prod, measure_univ, mul_one, one_mul]

/-- The two coordinate signs are independent under the product of two fair coins. -/
example : iIndepFun twoSigns (fairCoin.prod fairCoin) := by
  exact iIndepFun_twoSigns

private theorem integral_fairCoin (f : Bool → ℝ) :
    ∫ b, f b ∂fairCoin = (f true + f false) / 2 := by
  rw [fairCoin, integral_smul_measure, integral_add_measure (integrable_dirac (by simp))
    (integrable_dirac (by simp)), integral_dirac, integral_dirac, ENNReal.toReal_inv,
    ENNReal.toReal_ofNat, smul_eq_mul]
  ring

private theorem variance_coinSign : variance coinSign fairCoin = 1 := by
  rw [variance_eq_integral (measurable_of_finite _).aemeasurable]
  simp only [integral_fairCoin, coinSign]
  norm_num

private theorem identDistrib_fst : IdentDistrib Prod.fst id (fairCoin.prod fairCoin) fairCoin :=
  ⟨measurable_fst.aemeasurable, aemeasurable_id, by
    rw [Measure.map_fst_prod, measure_univ, one_smul, Measure.map_id]⟩

private theorem identDistrib_snd : IdentDistrib Prod.snd id (fairCoin.prod fairCoin) fairCoin :=
  ⟨measurable_snd.aemeasurable, aemeasurable_id, by
    rw [Measure.map_snd_prod, measure_univ, one_smul, Measure.map_id]⟩

private theorem identDistrib_twoSigns (i : Fin 2) :
    IdentDistrib (twoSigns i) (twoSigns 0) (fairCoin.prod fairCoin) (fairCoin.prod fairCoin) := by
  have hm : Measurable coinSign := measurable_of_finite _
  fin_cases i
  · exact IdentDistrib.refl (measurable_of_finite _).aemeasurable
  · have h1 : twoSigns 1 = coinSign ∘ Prod.snd := by funext ω; simp [twoSigns]
    have h0 : twoSigns 0 = coinSign ∘ Prod.fst := by funext ω; simp [twoSigns]
    show IdentDistrib (twoSigns 1) (twoSigns 0) _ _
    rw [h1, h0]
    exact (identDistrib_snd.comp hm).trans (identDistrib_fst.comp hm).symm

private theorem variance_twoSigns0 : variance (twoSigns 0) (fairCoin.prod fairCoin) = 1 := by
  have h0 : twoSigns 0 = coinSign ∘ Prod.fst := by funext ω; simp [twoSigns]
  rw [h0, ← variance_coinSign]
  exact (identDistrib_fst.comp (measurable_of_finite coinSign)).variance_eq

/-- The common variance of a fair sign is `1`. -/
example : variance (twoSigns 0) (fairCoin.prod fairCoin) = 1 := by
  exact variance_twoSigns0

/-- **Use of the finite theorem.** `n = 2`, two independent fair signs: applying
`integral_sampleVariance_of_iid_fin` (with `i0 = 0`) gives `E s² = Var X₀ = 1`. The proof must
invoke `integral_sampleVariance_of_iid_fin`; a direct computation of the integral does not
count. -/
example :
    ∫ ω, FiniteProbability.sampleVarUnbiased (fun i => twoSigns i ω)
      ∂(fairCoin.prod fairCoin) = 1 := by
  have h := (integral_sampleVariance_of_iid_fin le_rfl twoSigns 0 iIndepFun_twoSigns
    identDistrib_twoSigns MemLp.of_discrete).2
  rw [variance_twoSigns0] at h
  exact h

/-- Negative check: independence cannot be dropped. Duplicating one fair sign `Y` (`Xᵢ = Y` for
`i : Fin 2`, identically distributed but dependent) gives `Var Y = 1` while the sample variance
is identically `0`, so its mean `0` is not `Var Y`. -/
example :
    variance coinSign fairCoin = 1 ∧
      ∫ ω, FiniteProbability.sampleVarUnbiased (fun _ : Fin 2 => coinSign ω) ∂fairCoin = 0 := by
  refine ⟨variance_coinSign, ?_⟩
  simp [FiniteProbability.sampleVarUnbiased_eq_sum_div, FiniteProbability.sampleMean_eq_sum_div]

/-- The i.i.d. fair-sign sequence: coordinate signs under the product of fair coins on
`ℕ → Bool`. -/
noncomputable def fairSigns (i : ℕ) (ω : ℕ → Bool) : ℝ := coinSign (ω i)

/-- `n = 2`, i.i.d. fair signs: `integral_sampleVariance_of_iid` gives `E s² = Var X₀ = 1`. -/
example :
    ∫ ω, FiniteProbability.sampleVarUnbiased (fun i : Fin 2 => fairSigns i ω)
      ∂(Measure.infinitePi fun _ : ℕ => fairCoin) = 1 := by
  set μ := Measure.infinitePi fun _ : ℕ => fairCoin
  have hsign : Measurable coinSign := measurable_of_countable _
  have hind : iIndepFun fairSigns μ :=
    iIndepFun_infinitePi (P := fun _ : ℕ => fairCoin) (X := fun _ => coinSign) fun _ => hsign
  have hid : ∀ i, IdentDistrib (fairSigns i) (fairSigns 0) μ μ := fun i =>
    (show IdentDistrib (fun ω : ℕ → Bool => ω i) (fun ω => ω 0) μ μ from
      ⟨(measurable_pi_apply i).aemeasurable, (measurable_pi_apply 0).aemeasurable, by
        rw [Measure.infinitePi_map_eval, Measure.infinitePi_map_eval]⟩).comp hsign
  have hL2 : MemLp (fairSigns 0) 2 μ :=
    MemLp.of_bound (hsign.comp (measurable_pi_apply 0)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by
        unfold fairSigns coinSign; split_ifs <;> simp)
  have hvar : variance (fairSigns 0) μ = 1 := by
    change variance (fun ω : ℕ → Bool => coinSign (ω 0)) μ = 1
    rw [(measurePreserving_eval_infinitePi _ 0).variance_fun_comp hsign.aemeasurable,
      variance_eq_integral hsign.aemeasurable, fairCoin, integral_smul_measure,
      integral_add_measure .of_finite .of_finite, integral_dirac, integral_dirac,
      integral_smul_measure, integral_add_measure .of_finite .of_finite, integral_dirac,
      integral_dirac]
    norm_num [coinSign]
  have h := (integral_sampleVariance_of_iid fairSigns hind hid hL2 2 le_rfl).2
  rw [hvar] at h
  exact h

end MathlibExtTest.Probability.Statistics.SampleMoments
