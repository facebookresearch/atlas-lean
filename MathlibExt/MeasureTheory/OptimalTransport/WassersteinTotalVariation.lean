/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.MeasureTheory.OptimalTransport.Wasserstein
public import MathlibExt.Probability.TotalVariationDistance
public import Mathlib.MeasureTheory.Measure.Decomposition.Hahn
public import Mathlib.MeasureTheory.Measure.Sub

/-!
# Control of the Wasserstein distance by total variation

On a space of finite diameter `D`, `W_1(μ, ν) ≤ D · sup_B |μ(B) - ν(B)|`. The proof uses the
transference plan of Villani's proof of Theorem 6.15: keep the common part `μ ∧ ν` in place and
spread the excess `(μ - ν)₊` uniformly over the deficit `(μ - ν)₋`
(C. Villani, *Optimal Transport: Old and New*, Springer 2009, Theorem 6.15 and Particular
Case 6.16).

Villani's `‖μ - ν‖_TV` is the total variation norm (his Conventions), so
`‖μ - ν‖_TV = 2 sup_B |μ(B) - ν(B)|`, and equation (6.11) reads `‖μ - ν‖_TV = 2 inf P[X ≠ Y]`; while
`MathlibExt.Probability.TotalVariationDistance.totalVariationDist` is `sup_B |μ(B) - ν(B)|`; the
bound here, `W_1 ≤ D · sup_B |μ(B) - ν(B)| = (D / 2) ‖μ - ν‖_TV`, therefore implies Particular
Case 6.16, `W_1 ≤ D ‖μ - ν‖_TV`.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal

open MathlibExt.MeasureTheory.OptimalTransport.KantorovichWanted (IsCoupling)
open MathlibExt.Probability.TotalVariationDistance (totalVariationDist)

namespace MathlibExt.MeasureTheory.OptimalTransport.Wasserstein

/-- A single measurable set bounds the total variation distance from below. -/
private lemma toReal_sub_le_totalVariationDist {Ω : Type*} [MeasurableSpace Ω]
    (μ ν : Measure Ω) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {s : Set Ω}
    (hs : MeasurableSet s) :
    (μ s).toReal - (ν s).toReal ≤ totalVariationDist μ ν := by
  have hbdd : BddAbove (Set.range fun s : {s : Set Ω // MeasurableSet s} =>
      |(μ s.1).toReal - (ν s.1).toReal|) := by
    refine ⟨2, ?_⟩
    rintro _ ⟨t, rfl⟩
    have h1 : (μ t.1).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (measure_ne_top μ univ) (measure_mono (subset_univ t.1))
    have h2 : (ν t.1).toReal ≤ 1 := by
      simpa using ENNReal.toReal_mono (measure_ne_top ν univ) (measure_mono (subset_univ t.1))
    have h3 : 0 ≤ (μ t.1).toReal := ENNReal.toReal_nonneg
    have h4 : 0 ≤ (ν t.1).toReal := ENNReal.toReal_nonneg
    rw [abs_le]; constructor <;> linarith
  exact (le_abs_self _).trans
    (le_ciSup hbdd (⟨s, hs⟩ : {s : Set Ω // MeasurableSet s}))

/-- **Wasserstein distance controlled by total variation.** On a pseudo-extended metric space of
diameter at most `D` (second countable, with a σ-algebra containing the open sets), for all
probability measures `μ, ν`,
`W_1(μ, ν) ≤ D · sup_B |μ(B) - ν(B)|`, the supremum over measurable sets `B`
(C. Villani, *Optimal Transport: Old and New*, Springer 2009, Particular Case 6.16, proved with
the transference plan of the proof of Theorem 6.15; Villani's `‖μ - ν‖_TV`, the total variation
norm, is twice the supremum used here, so this is the sharper form). -/
theorem wasserstein_one_le_mul_totalVariationDist {X : Type*} [PseudoEMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X] [SecondCountableTopology X] {D : ℝ≥0}
    (hD : ∀ x y : X, edist x y ≤ D) (μ ν : ProbabilityMeasure X) :
    wasserstein 1 μ ν ≤
      D * ENNReal.ofReal (totalVariationDist (μ : Measure X) (ν : Measure X)) := by
  set μ' : Measure X := (μ : Measure X)
  set ν' : Measure X := (ν : Measure X)
  obtain ⟨S, hS⟩ := exists_isHahnDecomposition ν' μ'
  have hSm : MeasurableSet S := hS.measurableSet
  -- Common part, excess and deficit.
  set m : Measure X := ν'.restrict S + μ'.restrict Sᶜ
  set α : Measure X := μ'.restrict S - ν'.restrict S
  set β : Measure X := ν'.restrict Sᶜ - μ'.restrict Sᶜ
  have hμ : α + m = μ' := by
    simp only [α, m]
    rw [← add_assoc, Measure.sub_add_cancel_of_le hS.le_on, Measure.restrict_add_restrict_compl hSm]
  have hν : β + m = ν' := by
    simp only [β, m]
    rw [add_comm (ν'.restrict S), ← add_assoc, Measure.sub_add_cancel_of_le hS.ge_on_compl,
      add_comm, Measure.restrict_add_restrict_compl hSm]
  set a : ℝ≥0∞ := α univ
  have hm_fin : m univ ≠ ∞ := by
    have : m univ ≤ μ' univ := by rw [← hμ]; simp
    exact ne_top_of_le_ne_top (measure_ne_top μ' univ) this
  have hab : β univ = a := by
    have h1 : α univ + m univ = 1 := by
      rw [← Measure.add_apply, hμ]; exact measure_univ
    have h2 : β univ + m univ = 1 := by
      rw [← Measure.add_apply, hν]; exact measure_univ
    exact (ENNReal.add_left_inj hm_fin).1 (h2.trans h1.symm)
  have ha_fin : a ≠ ∞ := by
    have : a ≤ μ' univ := by rw [← hμ]; simp [a]
    exact ne_top_of_le_ne_top (measure_ne_top μ' univ) this
  -- The transference plan.
  have hdiag : Measurable (fun x : X => (x, x)) := by fun_prop
  set π : Measure (X × X) := m.map (fun x => (x, x)) + a⁻¹ • α.prod β
  have hscale : (a⁻¹ * a) • α = α := by
    by_cases ha : a = 0
    · have : α = 0 := Measure.measure_univ_eq_zero.1 ha
      rw [this]; simp
    · rw [ENNReal.inv_mul_cancel ha ha_fin, one_smul]
  have hscale' : (a⁻¹ * a) • β = β := by
    by_cases ha : a = 0
    · have : β = 0 := Measure.measure_univ_eq_zero.1 (hab.trans ha)
      rw [this]; simp
    · rw [ENNReal.inv_mul_cancel ha ha_fin, one_smul]
  have h1 : π.map Prod.fst = μ' := by
    simp only [π]
    rw [Measure.map_add _ _ measurable_fst, Measure.map_smul,
      Measure.map_map measurable_fst hdiag, Measure.map_fst_prod, hab, smul_smul, hscale]
    rotate_left
    · exact measurable_fst.aemeasurable
    rw [show (Prod.fst ∘ fun x : X => (x, x)) = id from rfl, Measure.map_id, add_comm, ← hμ]
  have h2 : π.map Prod.snd = ν' := by
    simp only [π]
    rw [Measure.map_add _ _ measurable_snd, Measure.map_smul,
      Measure.map_map measurable_snd hdiag, Measure.map_snd_prod, smul_smul, hscale']
    rotate_left
    · exact measurable_snd.aemeasurable
    rw [show (Prod.snd ∘ fun x : X => (x, x)) = id from rfl, Measure.map_id, add_comm, ← hν]
  have hπP : IsProbabilityMeasure π := by
    constructor
    have := congrArg (fun ρ : Measure X => ρ univ) h1
    simp only [Measure.map_apply measurable_fst MeasurableSet.univ, preimage_univ] at this
    rw [this]; exact measure_univ
  let πP : ProbabilityMeasure (X × X) := ⟨π, hπP⟩
  have hc : IsCoupling μ ν πP := ⟨h1.symm, h2.symm⟩
  -- Its cost.
  have hd : Measurable (fun z : X × X => edist z.1 z.2) := measurable_edist
  have hcost : ∫⁻ z, edist z.1 z.2 ∂π ≤ D * a := by
    simp only [π]
    rw [lintegral_add_measure, lintegral_map hd hdiag, lintegral_smul_measure]
    simp only [edist_self, lintegral_zero, zero_add]
    calc a⁻¹ * ∫⁻ z, edist z.1 z.2 ∂(α.prod β)
        ≤ a⁻¹ * ∫⁻ _, (D : ℝ≥0∞) ∂(α.prod β) := by
          gcongr with z; exact hD z.1 z.2
      _ = D * a := by
          rw [lintegral_const, ← Set.univ_prod_univ, Measure.prod_prod, hab]
          by_cases ha : a = 0
          · simp [ha]
          · rw [mul_comm (D : ℝ≥0∞), ← mul_assoc, ← mul_assoc, ENNReal.inv_mul_cancel ha ha_fin,
              one_mul, mul_comm]
  have hW : wasserstein 1 μ ν ≤ D * a := by
    calc wasserstein 1 μ ν
        ≤ (∫⁻ z, edist z.1 z.2 ^ (1 : ℝ) ∂π) ^ (1 / (1 : ℝ)) :=
          wasserstein_le_of_isCoupling zero_le_one hc
      _ = ∫⁻ z, edist z.1 z.2 ∂π := by simp
      _ ≤ D * a := hcost
  refine hW.trans ?_
  gcongr
  -- `a = μ(S) - ν(S) ≤ sup_B |μ(B) - ν(B)|`.
  have ha_eq : a = μ' S - ν' S := by
    simp only [a, α]
    rw [Measure.sub_apply MeasurableSet.univ hS.le_on, Measure.restrict_apply_univ,
      Measure.restrict_apply_univ]
  rw [ha_eq, ← ENNReal.ofReal_toReal (ne_top_of_le_ne_top (measure_ne_top μ' S) tsub_le_self)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hle : ν' S ≤ μ' S := by
    have := hS.le_on univ
    simpa using this
  rw [ENNReal.toReal_sub_of_le hle (measure_ne_top μ' S)]
  exact toReal_sub_le_totalVariationDist μ' ν' hSm

end MathlibExt.MeasureTheory.OptimalTransport.Wasserstein
