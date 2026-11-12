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
open MathlibExt.Probability.Statistics.EstimationRisk
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

/-- Helper: `coinSign` is measurable (domain `Bool` is countable). -/
private theorem measurable_coinSign : Measurable coinSign :=
  measurable_of_countable _

/-- Helper: values of `coinSign`. -/
private theorem coinSign_true : coinSign true = 1 := rfl

private theorem coinSign_false : coinSign false = -1 := rfl

private theorem coinSign_eq (b : Bool) : coinSign b = 1 ∨ coinSign b = -1 := by
  cases b
  · exact Or.inr coinSign_false
  · exact Or.inl coinSign_true

/-- Helper: closed form of the unbiased sample variance for `n = 2`. -/
private theorem sampleVarUnbiased_fin_two (x : Fin 2 → ℝ) :
    FiniteProbability.sampleVarUnbiased x = (x 0 - x 1) ^ 2 / 2 := by
  simp only [FiniteProbability.sampleVarUnbiased_eq_sum_div,
    FiniteProbability.sampleMean_eq_sum_div, Fin.sum_univ_two, Fintype.card_fin]
  ring

/-- The fair-sign fixture: independence, identical distribution, square-integrability, and
unit variance, on the infinite product of fair coins. -/
private theorem fairSigns_setup :
    iIndepFun fairSigns (Measure.infinitePi fun _ : ℕ => fairCoin) ∧
      (∀ i, IdentDistrib (fairSigns i) (fairSigns 0)
        (Measure.infinitePi fun _ : ℕ => fairCoin)
        (Measure.infinitePi fun _ : ℕ => fairCoin)) ∧
      MemLp (fairSigns 0) 2 (Measure.infinitePi fun _ : ℕ => fairCoin) ∧
      variance (fairSigns 0) (Measure.infinitePi fun _ : ℕ => fairCoin) = 1 := by
  have hmeas : Measurable coinSign := measurable_coinSign
  have hIndep : iIndepFun fairSigns (Measure.infinitePi fun _ : ℕ => fairCoin) :=
    iIndepFun_infinitePi (X := fun _ => coinSign) (fun _ => hmeas)
  have hLaw : ∀ i, HasLaw (fairSigns i) (fairCoin.map coinSign)
      (Measure.infinitePi fun _ : ℕ => fairCoin) := fun i =>
    { aemeasurable := (hmeas.comp (measurable_pi_apply i)).aemeasurable
      map_eq := by
        have hcomp : fairSigns i = coinSign ∘ (fun ω : ℕ → Bool => ω i) := by
          funext ω; rfl
        rw [hcomp, ← Measure.map_map hmeas (measurable_pi_apply i),
          Measure.infinitePi_map_eval] }
  have hIdent : ∀ i, IdentDistrib (fairSigns i) (fairSigns 0)
      (Measure.infinitePi fun _ : ℕ => fairCoin)
      (Measure.infinitePi fun _ : ℕ => fairCoin) :=
    fun i => (hLaw i).identDistrib (hLaw 0)
  have hMemLp : MemLp (fairSigns 0) 2 (Measure.infinitePi fun _ : ℕ => fairCoin) :=
    MemLp.of_bound (hmeas.comp (measurable_pi_apply 0)).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun ω => by
        simp only [fairSigns]
        obtain h | h := coinSign_eq (ω 0) <;> simp only [h, Real.norm_eq_abs] <;> norm_num)
  have hVar : variance (fairSigns 0) (Measure.infinitePi fun _ : ℕ => fairCoin) = 1 := by
    have hIdD : IdentDistrib (fairSigns 0) coinSign
        (Measure.infinitePi fun _ : ℕ => fairCoin) fairCoin :=
      (hLaw 0).identDistrib (hasLaw_map hmeas.aemeasurable)
    rw [hIdD.variance_eq]
    exact variance_coinSign
  exact ⟨hIndep, hIdent, hMemLp, hVar⟩

/-- Use: `n = 2` unbiasedness gives `E s² = 1` for a unit-variance family. Obtains the
fair-sign fixture from `fairSigns_setup`, then invokes the unbiasedness theorem through
`IsUnbiased.expect_eq` (beta-reduce the `Unit` application before rewriting with the
variance value); a direct integral computation does not count. -/
example :
    IsUnbiased
      (fun ω => FiniteProbability.sampleVarUnbiased (fun i : Fin 2 => fairSigns i ω))
      (fun _ : Unit => ⟨Measure.infinitePi fun _ : ℕ => fairCoin, inferInstance⟩)
      (fun _ => variance (fairSigns 0) (Measure.infinitePi fun _ : ℕ => fairCoin)) ∧
    ∫ ω, FiniteProbability.sampleVarUnbiased (fun i : Fin 2 => fairSigns i ω)
      ∂(Measure.infinitePi fun _ : ℕ => fairCoin) = 1 := by
  obtain ⟨hIndep, hIdent, hMemLp, hVar⟩ := fairSigns_setup
  have hunb := isUnbiased_sampleVariance_of_iid fairSigns hIndep hIdent hMemLp (n := 2) le_rfl
  refine ⟨hunb, ?_⟩
  have hE : ∫ ω, FiniteProbability.sampleVarUnbiased (fun i : Fin 2 => fairSigns i ω)
      ∂(Measure.infinitePi fun _ : ℕ => fairCoin)
      = variance (fairSigns 0) (Measure.infinitePi fun _ : ℕ => fairCoin) :=
    hunb.expect_eq ()
  exact hE.trans hVar

/-- Use: the family MSE of the fair-sign `s²` is its variance `1`. Obtains the variance
value from `fairSigns_setup`, then invokes the MSE corollary; the fourth-moment hypotheses
`hMem`/`h2` are bound explicitly since they are not implied by `hMemLp`. -/
example
    (hMem : ∀ _ : Unit, MemLp
      (fun ω => FiniteProbability.sampleVarUnbiased (fun i : Fin 2 => fairSigns i ω)) 2
      (Measure.infinitePi fun _ : ℕ => fairCoin))
    (h2 : ∀ _ : Unit, Integrable
      (fun x => (FiniteProbability.sampleVarUnbiased (fun i : Fin 2 => fairSigns i x)
        - variance (fairSigns 0) (Measure.infinitePi fun _ : ℕ => fairCoin)) ^ 2)
      (Measure.infinitePi fun _ : ℕ => fairCoin)) :
    MathlibExt.Probability.Statistics.EstimationRisk.familyMeanSquaredError
      (fun ω => FiniteProbability.sampleVarUnbiased (fun i : Fin 2 => fairSigns i ω))
      (fun _ : Unit => (⟨Measure.infinitePi fun _ : ℕ => fairCoin, inferInstance⟩ :
        ProbabilityMeasure (ℕ → Bool)))
      (fun _ => variance (fairSigns 0) (Measure.infinitePi fun _ : ℕ => fairCoin)) h2
      = fun _ => 1 := by
  obtain ⟨hIndep, hIdent, hMemLp, hVar⟩ := fairSigns_setup
  have hmeasH : Measurable (fun p : Bool × Bool =>
      (coinSign p.1 - coinSign p.2) ^ 2 / 2) :=
    (((measurable_coinSign.comp measurable_fst).sub
      (measurable_coinSign.comp measurable_snd)).pow_const 2).div_const 2
  have hmeasπ : Measurable (fun ω : ℕ → Bool => (ω 0, ω 1)) :=
    (measurable_pi_apply 0).prodMk (measurable_pi_apply 1)
  have hWeq : (fun ω : ℕ → Bool => FiniteProbability.sampleVarUnbiased
        (fun i : Fin 2 => fairSigns i ω))
        = (fun p : Bool × Bool => (coinSign p.1 - coinSign p.2) ^ 2 / 2)
          ∘ (fun ω : ℕ → Bool => (ω 0, ω 1)) := by
    funext ω
    simp only [sampleVarUnbiased_fin_two, fairSigns, Fin.val_zero, Fin.val_one,
      Function.comp_apply]
  have hIdD : IdentDistrib
      (fun ω : ℕ → Bool => FiniteProbability.sampleVarUnbiased
        (fun i : Fin 2 => fairSigns i ω))
      (fun p : Bool × Bool => (coinSign p.1 - coinSign p.2) ^ 2 / 2)
      (Measure.infinitePi fun _ : ℕ => fairCoin)
      (fairCoin.prod fairCoin) :=
    { aemeasurable_fst := by rw [hWeq]; exact (hmeasH.comp hmeasπ).aemeasurable
      aemeasurable_snd := hmeasH.aemeasurable
      map_eq := by
        rw [hWeq, ← Measure.map_map hmeasH hmeasπ,
          Measure.infinitePi_map_eval_prod (show (0 : ℕ) ≠ 1 by norm_num)] }
  have hMemH : MemLp (fun p : Bool × Bool =>
      (coinSign p.1 - coinSign p.2) ^ 2 / 2) 2 (fairCoin.prod fairCoin) :=
    MemLp.of_bound hmeasH.aestronglyMeasurable 2 (Filter.Eventually.of_forall fun p => by
      obtain h0 | h0 := coinSign_eq p.1 <;> obtain h1 | h1 := coinSign_eq p.2 <;>
        simp only [h0, h1, Real.norm_eq_abs] <;> norm_num)
  have hHint : ∫ p, (coinSign p.1 - coinSign p.2) ^ 2 / 2
      ∂(fairCoin.prod fairCoin) = 1 := by
    have hinner : ∀ b₀ : Bool, (∫ b₁, (coinSign (b₀, b₁).1 - coinSign (b₀, b₁).2) ^ 2 / 2
        ∂fairCoin) = 1 := by
      intro b₀
      rw [integral_fairCoin]
      show ((coinSign b₀ - coinSign true) ^ 2 / 2 +
        ((coinSign b₀ - coinSign false) ^ 2 / 2)) / 2 = 1
      cases b₀ <;> rw [coinSign_true, coinSign_false] <;> norm_num
    rw [integral_prod _ (hMemH.integrable one_le_two)]
    simp only [hinner, integral_const, measureReal_def, IsProbabilityMeasure.measure_univ,
      ENNReal.toReal_one, one_smul]
  have hHsq : ∫ p, ((coinSign p.1 - coinSign p.2) ^ 2 / 2) ^ 2
      ∂(fairCoin.prod fairCoin) = 2 := by
    have hinner2 : ∀ b₀ : Bool, (∫ b₁,
        (((coinSign (b₀, b₁).1 - coinSign (b₀, b₁).2) ^ 2 / 2)) ^ 2
        ∂fairCoin) = 2 := by
      intro b₀
      rw [integral_fairCoin]
      show (((coinSign b₀ - coinSign true) ^ 2 / 2) ^ 2 +
        (((coinSign b₀ - coinSign false) ^ 2 / 2) ^ 2)) / 2 = 2
      cases b₀ <;> rw [coinSign_true, coinSign_false] <;> norm_num
    rw [integral_prod _ hMemH.integrable_sq]
    simp only [hinner2, integral_const, measureReal_def, IsProbabilityMeasure.measure_univ,
      ENNReal.toReal_one, one_smul]
  have hHvar : variance (fun p : Bool × Bool =>
      (coinSign p.1 - coinSign p.2) ^ 2 / 2) (fairCoin.prod fairCoin) = 1 := by
    have h := variance_eq_sub hMemH
    simp only [Pi.pow_apply] at h
    rw [hHint, hHsq] at h
    norm_num at h
    exact h
  have hWvar : variance (fun ω : ℕ → Bool => FiniteProbability.sampleVarUnbiased
      (fun i : Fin 2 => fairSigns i ω))
      (Measure.infinitePi fun _ : ℕ => fairCoin) = 1 := by
    rw [hIdD.variance_eq]
    exact hHvar
  have hcor := familyMeanSquaredError_sampleVariance_of_iid fairSigns hIndep hIdent hMemLp
    le_rfl hMem h2
  rw [hcor, hWvar]

/-- Boundary: constant observations have zero sample variance. -/
example (c : ℝ) :
    ∫ _ : Bool, FiniteProbability.sampleVarUnbiased (fun _ : Fin 2 => c) ∂fairCoin = 0 := by
  have h0 : FiniteProbability.sampleVarUnbiased (fun _ : Fin 2 => c) = 0 := by
    simp only [sampleVarUnbiased_fin_two]
    norm_num
  rw [h0]
  simp

/-- Negative: a dependent duplicate keeps variance `σ²`, not `σ² / n`. Duplicating one fair
sign (`Xᵢ = Y` for `i : Fin 2`) gives `Var Y = 1` while the sample variance is identically
`0`. -/
example :
    variance coinSign fairCoin = 1 ∧
      ∫ ω, FiniteProbability.sampleVarUnbiased (fun _ : Fin 2 => coinSign ω) ∂fairCoin
        = 0 := by
  refine ⟨variance_coinSign, ?_⟩
  have h0 : ∀ ω : Bool,
      FiniteProbability.sampleVarUnbiased (fun _ : Fin 2 => coinSign ω) = 0 := fun ω => by
    simp only [sampleVarUnbiased_fin_two]
    norm_num
  simp only [h0]
  simp

/-- Positive: `n = 1` recovers the single observation. Invokes the independence-free
unbiasedness theorem through `IsUnbiased.expect_eq` (beta-reduce the `Unit` application). -/
example (X : ℕ → Bool → ℝ)
    (hIdent : ∀ i, IdentDistrib (X i) (X 0) fairCoin fairCoin)
    (hMemLp : MemLp (X 0) 2 fairCoin) :
    ∫ ω, FiniteProbability.sampleMean (fun i : Fin 1 => X i ω) ∂fairCoin
      = ∫ ω, X 0 ω ∂fairCoin := by
  have h := isUnbiased_sampleMean_family X hIdent hMemLp 1 one_pos
  exact MathlibExt.Probability.Statistics.EstimationRisk.IsUnbiased.expect_eq h ()

/-- Boundary: constant observations have zero mean shift. -/
example (c : ℝ) :
    ∫ _ : Bool, (∑ _i ∈ Finset.range 2, c) / ((2 : ℕ) : ℝ) ∂fairCoin = c := by
  have hconst : (∑ _i ∈ Finset.range 2, c) / ((2 : ℕ) : ℝ) = c := by
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    norm_num
  simp only [hconst, integral_const, measureReal_def,
    IsProbabilityMeasure.measure_univ, ENNReal.toReal_one, one_smul]

/-- Family-MSE use: the fair-sign `n = 2` mean has MSE `1 / 2 = variance / n`, nonzero.
Obtains the fixture from `fairSigns_setup`, then invokes the iid family-MSE theorem (the
`∃ h2` witness is the internally constructed evidence); the only supplied extra is the
statement shape itself. -/
example :
    let μ := Measure.infinitePi fun _ : ℕ => fairCoin;
    ∃ h2, MathlibExt.Probability.Statistics.EstimationRisk.familyMeanSquaredError
      (fun ω => FiniteProbability.sampleMean (fun i : Fin 2 => fairSigns i ω))
      (fun _ : Unit => (⟨μ, inferInstance⟩ : ProbabilityMeasure (ℕ → Bool)))
      (fun _ => ∫ ω, fairSigns 0 ω ∂μ) h2
      = fun _ => 1 / 2 := by
  obtain ⟨hIndep, hIdent, hMemLp, hvar⟩ := fairSigns_setup
  obtain ⟨h2, hMSE⟩ :=
    familyMeanSquaredError_sampleMean_of_iid fairSigns hIndep hIdent hMemLp 2 (by norm_num)
  exact ⟨h2, hMSE.trans (by rw [hvar]; funext u; norm_num)⟩

/-- Heavy-tail boundary: the mean identity needs only L¹, while the MSE half needs L².
With mere integrability and a common mean (no `MemLp`, no identical distribution, so a
heavy tail with a common mean, or square-integrable observations with different
distributions, are covered), the `n`-sample canonical mean is still unbiased, hence its
expectation is `mu`. Invokes the generalized unbiasedness theorem. -/
example {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ℕ → Ω → ℝ)
    (hInt : ∀ i, Integrable (X i) μ) {mu : ℝ} (hMean : ∀ i, ∫ ω, X i ω ∂μ = mu)
    (n : ℕ) (hn : 0 < n) :
    ∫ ω, FiniteProbability.sampleMean (fun i : Fin n => X i ω) ∂μ = mu := by
  have h := isUnbiased_sampleMean_of_common_mean X hInt hMean n hn
  exact MathlibExt.Probability.Statistics.EstimationRisk.IsUnbiased.expect_eq h ()

/-- Negative: a dependent duplicate keeps variance `σ²`, not `σ² / n` — and the target's
iid-based proof does not apply (no `iIndepFun` is available or assumed). With `X i = coinSign`
for all `i`, the `n = 2` mean is `coinSign` itself with variance `1 ≠ 1 / 2`. -/
example (hvar : variance coinSign fairCoin = 1) :
    variance (fun ω => (∑ _i ∈ Finset.range 2, coinSign ω) / ((2 : ℕ) : ℝ)) fairCoin
      = 1 := by
  have hfun : (fun ω => (∑ _i ∈ Finset.range 2, coinSign ω) / ((2 : ℕ) : ℝ))
      = coinSign := by
    funext ω
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    norm_num
  rw [hfun, hvar]

end MathlibExtTest.Probability.Statistics.SampleMoments
