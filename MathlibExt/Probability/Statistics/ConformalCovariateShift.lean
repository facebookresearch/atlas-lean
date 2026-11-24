/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.WeightedConformal
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd
public import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
public import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Kernel.Composition.WithDensity
import Mathlib.Algebra.BigOperators.Fin

/-!
# Weighted split conformal coverage under covariate shift

`le_measure_score_le_weightedQuantile` gives marginal coverage for an independent test
observation drawn with a different covariate law. The proof averages the covered weight over
the possible test coordinates under the i.i.d. training law.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset
open MathlibExt.Probability.Statistics.WeightedConformal
open scoped ENNReal

namespace MathlibExt.Probability.ConformalCovariateShiftWanted

section

variable {ι Z : Type*} [Fintype ι]

/-- Total weight at scores strictly below coordinate `i`. -/
private noncomputable def lowerMass (v w : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, if v j < v i then w j else 0

/-- Take a least-scoring rejected coordinate. All scores strictly below it are covered,
and their weight alone reaches the required fraction of the total. -/
private lemma le_sum_covered (v w : ι → ℝ) (hw : ∀ i, 0 ≤ w i) {β : ℝ} (hβ : β ≤ 1) :
    β * ∑ j, w j ≤ ∑ i, if lowerMass v w i < β * ∑ j, w j then w i else 0 := by
  classical
  let bad := univ.filter fun i => β * ∑ j, w j ≤ lowerMass v w i
  rcases bad.eq_empty_or_nonempty with h | h
  · have hall (i : ι) : lowerMass v w i < β * ∑ j, w j := by
      have : i ∉ bad := by simp [h]
      simpa [bad] using this
    simpa [hall] using mul_le_mul_of_nonneg_right hβ (sum_nonneg fun i _ => hw i)
  · obtain ⟨i, hi, hmin⟩ := exists_min_image bad v h
    refine ((mem_filter.mp hi).2).trans (sum_le_sum fun j _ => ?_)
    by_cases hji : v j < v i
    · have hj : j ∉ bad := fun hj => hji.not_ge (hmin j hj)
      have hgood : lowerMass v w j < β * ∑ k, w k := by simpa [bad] using hj
      simp [hji, hgood]
    · simp only [ite_eq_right hji]
      split <;> simp [hw]

/-- The event that the strictly lower scores carry less than a fraction `β` of all weight. -/
private def covered (s w : Z → ℝ) (β : ℝ) (i : ι) : Set (ι → Z) :=
  {z | lowerMass (s ∘ z) (w ∘ z) i < β * ∑ j, w (z j)}

private lemma mem_covered_perm (s w : Z → ℝ) (β : ℝ) (e : Equiv.Perm ι) (i : ι) (z : ι → Z) :
    z ∘ e ∈ covered s w β i ↔ z ∈ covered s w β (e i) := by
  change (∑ j, if s (z (e j)) < s (z (e i)) then w (z (e j)) else 0) <
    β * ∑ j, w (z (e j)) ↔ _
  rw [Equiv.sum_comp e (fun j => if s (z j) < s (z (e i)) then w (z j) else 0),
    Equiv.sum_comp e (fun j => w (z j))]
  rfl

variable [MeasurableSpace Z]

private lemma measurableSet_covered {s w : Z → ℝ} (hs : Measurable s) (hw : Measurable w)
    (β : ℝ) (i : ι) : MeasurableSet (covered s w β i) := by
  unfold covered lowerMass
  apply measurableSet_lt
  · exact Finset.measurable_fun_sum _ fun j _ =>
      Measurable.ite (measurableSet_lt (hs.comp (measurable_pi_apply j))
        (hs.comp (measurable_pi_apply i))) (hw.comp (measurable_pi_apply j)) measurable_const
  · fun_prop

/-- Under the i.i.d. base law every coordinate contributes the same expected covered weight. -/
private lemma le_setLIntegral_covered (μ : Measure Z) [IsProbabilityMeasure μ]
    {s w : Z → ℝ} (hs : Measurable s) (hw : Measurable w) (hw0 : ∀ x, 0 ≤ w x)
    (hw1 : ∫⁻ x, ENNReal.ofReal (w x) ∂μ = 1) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (t : ι) :
    ENNReal.ofReal β ≤ ∫⁻ z in covered s w β t, ENNReal.ofReal (w (z t))
      ∂Measure.pi (fun _ : ι => μ) := by
  classical
  let P := Measure.pi (fun _ : ι => μ)
  let W (i : ι) (z : ι → Z) := ENNReal.ofReal (w (z i))
  let C (i : ι) := covered s w β i
  have hW (i : ι) : Measurable (W i) := (hw.comp (measurable_pi_apply i)).ennreal_ofReal
  have hC (i : ι) : MeasurableSet (C i) := measurableSet_covered hs hw β i
  have hmean (i : ι) : ∫⁻ z, W i z ∂P = 1 :=
    ((measurePreserving_eval (fun _ : ι => μ) i).lintegral_comp hw.ennreal_ofReal).trans hw1
  have hsymm (i : ι) : ∫⁻ z, (C i).indicator (W i) z ∂P =
      ∫⁻ z, (C t).indicator (W t) z ∂P := by
    let e := Equiv.swap t i
    let perm := MeasurableEquiv.piCongrLeft (fun _ : ι => Z) e
    have hperm (z : ι → Z) : perm z = z ∘ e := by
      funext j
      simpa [perm, e] using MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => Z) e z (e j)
    rw [← (measurePreserving_piCongrLeft (fun _ : ι => μ) e).lintegral_comp_emb
      perm.measurableEmbedding ((C t).indicator (W t))]
    apply lintegral_congr
    intro z
    change (C i).indicator (W i) z = (C t).indicator (W t) (perm z)
    simp only [hperm, Set.indicator_apply, C, mem_covered_perm, W, Function.comp_apply,
      e, Equiv.swap_apply_left]
  have hpoint (z : ι → Z) : ENNReal.ofReal β * ∑ j, W j z ≤
      ∑ i, (C i).indicator (W i) z := by
    have h := ENNReal.ofReal_le_ofReal (le_sum_covered (s ∘ z) (w ∘ z) (fun j => hw0 (z j)) hβ1)
    change ENNReal.ofReal (β * ∑ j, w (z j)) ≤
      ENNReal.ofReal (∑ i, if z ∈ C i then w (z i) else 0) at h
    rw [ENNReal.ofReal_mul hβ0, ENNReal.ofReal_sum_of_nonneg (fun j _ => hw0 (z j)),
      ENNReal.ofReal_sum_of_nonneg (fun i _ => ite_nonneg (hw0 (z i)) le_rfl)] at h
    refine h.trans_eq (sum_congr rfl fun i _ => ?_)
    by_cases hi : z ∈ C i <;> simp [hi, W]
  have havg := lintegral_mono (μ := P) hpoint
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_finsetSum _ (fun i _ => hW i),
    lintegral_finsetSum _ (fun i _ => (hW i).indicator (hC i))] at havg
  simp only [hmean, hsymm, sum_const, card_univ, nsmul_eq_mul, mul_one] at havg
  have : Nonempty ι := ⟨t⟩
  rw [mul_comm] at havg
  exact (lintegral_indicator (μ := P) (hC t) (W t)) ▸
    (ENNReal.mul_le_mul_iff_right (by exact_mod_cast Fintype.card_ne_zero)
      (ENNReal.natCast_ne_top _)).mp havg

end

/-- **Weighted split conformal coverage under covariate shift.** Let `P_X`, `P̃_X` be probability
measures on the covariate space with `P̃_X ≪ P_X`, let `κ` be a Markov kernel giving the
conditional law of the response, and let `w` be the Radon-Nikodym derivative `dP̃_X / dP_X`.
Let the data `D = ((X₁, Y₁), …, (Xₙ, Yₙ); (X_{n+1}, Y_{n+1}))` have law
`(P_X ⊗ κ)^{⊗ n} ⊗ (P̃_X ⊗ κ)`, and let `s` be a measurable score function. For `0 < α < 1`, the
test score `s(X_{n+1}, Y_{n+1})` is at most the level-`(1 - α)` quantile of
`∑ᵢ pᵢ δ_{s(Xᵢ, Yᵢ)} + p_{n+1} δ_{+∞}`, with `pᵢ = w(Xᵢ) / (∑ⱼ w(Xⱼ) + w(X_{n+1}))`, with
probability at least `1 - α`.

Source: R. J. Tibshirani, R. F. Barber, E. J. Candès and A. Ramdas, *Conformal prediction under
covariate shift*, NeurIPS 2019, arXiv:1904.06019, Corollary 1, for a score function that does not
depend on the data bag, `S((x, y), Z) = s(x, y)`; this is the weighted split conformal case of
their Section 2.2, which uses `s(x, y) = |y - μ₀(x)|` for a regression function `μ₀` fitted on
independent data (the statement is conditional on that fit). The event is `Y_{n+1} ∈ Ĉₙ(X_{n+1})`
for the band `Ĉₙ(x) = {y : s(x, y) ≤ Quantile(1 - α; ∑ᵢ pᵢ(x) δ_{Vᵢ} + p_{n+1}(x) δ_∞)}`. -/
theorem le_measure_score_le_weightedQuantile {𝒳 : Type*} [MeasurableSpace 𝒳]
    (PX PtX : Measure 𝒳) [IsProbabilityMeasure PX] [IsProbabilityMeasure PtX] (hac : PtX ≪ PX)
    (κ : Kernel 𝒳 ℝ) [IsMarkovKernel κ] {s : 𝒳 × ℝ → ℝ} (hs : Measurable s) {α : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1) (n : ℕ) :
    ENNReal.ofReal (1 - α) ≤
      ((Measure.pi fun _ : Fin n => PX ⊗ₘ κ).prod (PtX ⊗ₘ κ))
        {D | (s D.2 : WithTop ℝ) ≤ weightedQuantile (1 - α) (fun i => s (D.1 i))
          (fun i => (PtX.rnDeriv PX (D.1 i).1).toReal /
            (∑ j, (PtX.rnDeriv PX (D.1 j).1).toReal + (PtX.rnDeriv PX D.2.1).toReal))} := by
  classical
  let μ := PX ⊗ₘ κ
  let r (x : 𝒳) := (PtX.rnDeriv PX x).toReal
  let w (z : 𝒳 × ℝ) := r z.1
  have hr : Measurable r := (Measure.measurable_rnDeriv PtX PX).ennreal_toReal
  have hw : Measurable w := hr.comp measurable_fst
  have hw0 (z) : 0 ≤ w z := ENNReal.toReal_nonneg
  have hX : PX.withDensity (fun x => ENNReal.ofReal (r x)) = PtX := by
    refine (withDensity_congr_ae ?_).trans (PtX.withDensity_rnDeriv_eq PX hac)
    filter_upwards [PtX.rnDeriv_lt_top PX] with x hx using ENNReal.ofReal_toReal hx.ne
  have hshift : μ.withDensity (fun z => ENNReal.ofReal (w z)) = PtX ⊗ₘ κ := by
    exact (Measure.withDensity_compProd (κ := κ) hr.ennreal_ofReal).symm.trans
      (congrArg (fun ν => ν ⊗ₘ κ) hX)
  have hw1 : ∫⁻ z, ENNReal.ofReal (w z) ∂μ = 1 := by
    simpa [withDensity_apply] using congrArg (fun ν : Measure (𝒳 × ℝ) => ν Set.univ) hshift
  let t := Fin.last n
  let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => 𝒳 × ℝ) t).trans
    MeasurableEquiv.prodComm
  have he : MeasurePreserving e (Measure.pi fun _ => μ) ((Measure.pi fun _ : Fin n => μ).prod μ) :=
    Measure.measurePreserving_swap.comp (measurePreserving_piFinSuccAbove (fun _ => μ) t)
  have he₁ (z : Fin (n + 1) → 𝒳 × ℝ) (i : Fin n) : (e z).1 i = z i.castSucc := by
    change z ((Fin.last n).succAbove i) = _
    rw [Fin.succAbove_last]
  have he₂ (z : Fin (n + 1) → 𝒳 × ℝ) : (e z).2 = z t := rfl
  change ENNReal.ofReal (1 - α) ≤ ((Measure.pi fun _ : Fin n => μ).prod (PtX ⊗ₘ κ))
    {D | (s D.2 : WithTop ℝ) ≤ weightedQuantile (1 - α) (fun i => s (D.1 i))
      (fun i => w (D.1 i) / (∑ j, w (D.1 j) + w D.2))}
  rw [← hshift, prod_withDensity_right hw.ennreal_ofReal, withDensity_apply',
    ← he.setLIntegral_comp_preimage_emb e.measurableEmbedding]
  refine (le_setLIntegral_covered μ hs hw hw0 hw1 (sub_nonneg.mpr hα1.le)
    (sub_le_self _ hα0.le) t).trans (lintegral_mono_set ?_)
  intro z hz
  change (s (e z).2 : WithTop ℝ) ≤ _
  simp only [he₁, he₂]
  rw [coe_le_weightedQuantile_iff (sub_pos.mpr hα1) _
    (fun i => div_nonneg (hw0 _) (add_nonneg (sum_nonneg fun _ _ => hw0 _) (hw0 _)))]
  change lowerMass (s ∘ z) (w ∘ z) t < (1 - α) * ∑ j, w (z j) at hz
  simp only [lowerMass, Fin.sum_univ_castSucc, Function.comp_apply, t, lt_self_iff_false,
    ite_false, add_zero] at hz
  rw [← sum_div, sum_filter]
  apply (div_lt_iff₀ ?_).2 hz
  have hlow : 0 ≤ ∑ i : Fin n, if s (z i.castSucc) < s (z t) then w (z i.castSucc) else 0 :=
    sum_nonneg fun i _ => ite_nonneg (hw0 _) le_rfl
  exact pos_of_mul_pos_right (hlow.trans_lt hz) (sub_nonneg.mpr hα1.le)

end MathlibExt.Probability.ConformalCovariateShiftWanted
