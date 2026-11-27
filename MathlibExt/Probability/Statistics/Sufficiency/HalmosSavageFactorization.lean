/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.Sufficiency.Basic
import MathlibExt.Probability.Statistics.Sufficiency.CountableFactorization
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Halmos–Savage factorization, necessity

A countable subfamily whose density supports cover those of the entire family almost everywhere
provides a finite dominating measure `Q` by taking a positively weighted sum. For each parameter,
apply the countable factorization theorem to that subfamily with the parameter adjoined. Summing
the subfamily's factorizations expresses `Q` with the same common factor; dividing out its
statistic-dependent density gives the desired factorization relative to `Q`.
-/

namespace MathlibExt.Probability.Statistics.Sufficiency

open MeasureTheory
open scoped ENNReal

/-- A countable selection of density supports suffices to dominate the whole family. -/
private lemma exists_countable_dominating_sum {Ω Θ : Type*} {m₀ : MeasurableSpace Ω}
    (μ : Measure[m₀] Ω) [SigmaFinite μ] (P : Θ → Measure[m₀] Ω)
    [∀ θ, IsProbabilityMeasure (P θ)] (hdom : ∀ θ, P θ ≪ μ) :
    ∃ (D : Set (Set Ω)) (_ : Countable D) (e : D → Θ) (w : D → ℝ≥0∞),
      IsFiniteMeasure (Measure.sum fun i => w i • P (e i)) ∧
      ∀ θ, P θ ≪ Measure.sum fun i => w i • P (e i) := by
  classical
  let A (θ : Θ) : Set Ω := {x | (P θ).rnDeriv μ x ≠ 0}
  obtain ⟨D, hD, hDc, hcover⟩ := μ.exists_ae_subset_biUnion_countable
    (C := Set.range A) (by
      rintro _ ⟨θ, rfl⟩
      exact (measurableSet_eq_fun (Measure.measurable_rnDeriv _ _) measurable_const).compl)
  let : Encodable D := hDc.toEncodable
  have he : ∀ i : D, ∃ θ, A θ = i.1 := fun i => hD i.2
  choose e he using he
  let w (i : D) : ℝ≥0∞ := (2⁻¹ : ℝ≥0∞) ^ Encodable.encode i
  have hw (i : D) : w i ≠ 0 := pow_ne_zero _ (by simp)
  refine ⟨D, hDc.to_subtype, e, w, ?_, ?_⟩
  · constructor
    rw [Measure.sum_apply _ MeasurableSet.univ]
    simp only [_root_.smul_apply, smul_eq_mul, measure_univ, mul_one]
    exact ENNReal.tsum_geometric_two_encode_le_two.trans_lt (by simp)
  · intro θ
    apply Measure.AbsolutelyContinuous.mk
    intro s _ hs
    have hz (i : D) : P (e i) s = 0 := by
      have hac : P (e i) ≪ Measure.sum fun j => w j • P (e j) :=
        Measure.absolutelyContinuous_sum_right i
          (Measure.AbsolutelyContinuous.rfl.smul_right (hw i))
      exact hac hs
    have hz' (i : D) : μ (i.1 ∩ s) = 0 := by
      rw [← he i]
      have hzero := hz i
      rw [← Measure.withDensity_rnDeriv_eq _ _ (hdom (e i))] at hzero
      exact (withDensity_apply_eq_zero (Measure.measurable_rnDeriv _ _)).mp hzero
    have hnull : μ (⋃₀ D ∩ s) = 0 := by
      rw [Set.sUnion_eq_iUnion, Set.iUnion_inter]
      exact measure_iUnion_null hz'
    rw [← Measure.withDensity_rnDeriv_eq _ _ (hdom θ),
      withDensity_apply_eq_zero (Measure.measurable_rnDeriv _ _)]
    exact measure_mono_null_ae ((hcover (A θ) ⟨θ, rfl⟩).inter
      (ae_of_all μ (fun _ h => h) : s ≤ᵐ[μ] s)) hnull

/-- Change the reference density from `1` to `d`, taking the quotient only where cancellation
is valid. Absolute continuity handles the zero set of `d`, and finiteness its infinite set. -/
private lemma withDensity_div_of_absolutelyContinuous {Ω : Type*} {m₀ : MeasurableSpace Ω}
    (ν : Measure[m₀] Ω) {f d : Ω → ℝ≥0∞} (hf : Measurable f) (hd : Measurable d)
    [IsFiniteMeasure (ν.withDensity d)] (hac : ν.withDensity f ≪ ν.withDensity d) :
    (ν.withDensity d).withDensity (fun x => f x / d x) = ν.withDensity f := by
  have hquot : Measurable (fun x => f x / d x) := hf.div hd
  rw [← withDensity_mul ν hd hquot]
  apply withDensity_congr_ae
  have hdtop : ∀ᵐ x ∂ν, d x < ∞ :=
    ae_lt_top hd (isFiniteMeasure_withDensity_iff.mp inferInstance)
  have hdne : ∀ᵐ x ∂(ν.withDensity d), d x ≠ 0 :=
    (ae_withDensity_iff hd).2 (ae_of_all _ fun _ h => h)
  have hfd := (ae_withDensity_iff hf).1 (hac.ae_le hdne)
  filter_upwards [hdtop, hfd] with x hxt hx
  change d x * (f x / d x) = f x
  by_cases hfx : f x = 0
  · simp [hfx]
  · exact ENNReal.mul_div_cancel (hx hfx) hxt.ne

@[expose] public section

/-- **Halmos–Savage factorization, necessity.** If the family of probability measures `P` is
dominated by a σ-finite measure `μ` and the statistic `T` is sufficient for `P`, then the
densities factor as `dP_θ/dμ = g_θ(T) · h` with measurable `g_θ` and `h`, `h` free of `θ`.

Source: P. R. Halmos and L. J. Savage, *Application of the Radon–Nikodym theorem to the theory
of sufficient statistics*, Ann. Math. Statist. 20 (1949), 225–241. -/
theorem exists_factorization_of_isSufficient_comap {Ω Θ τ : Type*}
    [MeasurableSpace τ] {m₀ : MeasurableSpace Ω} {T : Ω → τ} (hT : Measurable T)
    (μ : Measure[m₀] Ω) [SigmaFinite μ] (P : Θ → Measure[m₀] Ω)
    [∀ θ, IsProbabilityMeasure (P θ)] (hdom : ∀ θ, P θ ≪ μ)
    (hP : IsSufficient (MeasurableSpace.comap T ‹MeasurableSpace τ›) P) :
    ∃ (g : Θ → τ → ℝ≥0∞) (h : Ω → ℝ≥0∞), (∀ θ, Measurable (g θ)) ∧ Measurable h ∧
      ∀ θ, P θ = μ.withDensity (fun ω => g θ (T ω) * h ω) := by
  classical
  rcases isEmpty_or_nonempty Θ with hΘ | hΘ
  · exact ⟨fun _ _ => 0, fun _ => 0, isEmptyElim, measurable_const, isEmptyElim⟩
  obtain ⟨D, hD, e, w, hQfin, hQdom⟩ := exists_countable_dominating_sum μ P hdom
  let Q : Measure[m₀] Ω := Measure.sum fun i => w i • P (e i)
  have hQμ : Q ≪ μ := Measure.absolutelyContinuous_sum_left fun i =>
    Measure.smul_absolutelyContinuous.trans (hdom (e i))
  have hfactor (θ : Θ) : ∃ g : τ → ℝ≥0∞, Measurable g ∧
      P θ = Q.withDensity (fun ω => g (T ω)) := by
    let a : Option D → Θ := fun i => i.elim θ e
    have (i : Option D) : IsProbabilityMeasure (P (a i)) := inferInstance
    have hPa : IsSufficient (MeasurableSpace.comap T ‹MeasurableSpace τ›) (P ∘ a) := by
      refine ⟨hP.1, fun i => hP.2.1 (a i), fun s hs => ?_⟩
      obtain ⟨η, hη, hηP⟩ := hP.2.2 s hs
      exact ⟨η, hη, fun i => hηP (a i)⟩
    obtain ⟨b, k, hb, hk, hfac⟩ := exists_factorization_of_isSufficient_comap_countable
      hT μ (fun i => P (a i)) (fun i => hdom (a i)) hPa
    let ν := μ.withDensity k
    have hbT (i : Option D) : Measurable (fun ω => b i (T ω)) := (hb i).comp hT
    have hν (i : Option D) : P (a i) = ν.withDensity (fun ω => b i (T ω)) := by
      change P (a i) = (μ.withDensity k).withDensity (fun ω => b i (T ω))
      rw [hfac i, ← withDensity_mul μ hk (hbT i)]
      congr 1
      funext ω
      exact mul_comm _ _
    let d (t : τ) : ℝ≥0∞ := ∑' i : D, w i * b (some i) t
    have hd : Measurable d := Measurable.tsum fun i => measurable_const.mul (hb (some i))
    have hdT : Measurable (fun ω => d (T ω)) := hd.comp hT
    have hQ : Q = ν.withDensity (fun ω => d (T ω)) := by
      let F (i : D) (ω : Ω) : ℝ≥0∞ := w i * b (some i) (T ω)
      have hF (i : D) : Measurable (F i) := measurable_const.mul (hbT (some i))
      have heq : (fun ω => d (T ω)) = ∑' i, F i := by
        ext ω
        exact (Pi.tsum_apply (f := F) (Pi.summable.2 fun _ => CompleteLattice.summable)).symm
      rw [heq, withDensity_tsum hF]
      change Measure.sum _ = Measure.sum _
      congr 1
      funext i
      change w i • P (a (some i)) = ν.withDensity (w i • (fun ω => b (some i) (T ω)))
      rw [withDensity_smul (w i) (hbT (some i)), hν (some i)]
    have : IsFiniteMeasure (ν.withDensity (fun ω => d (T ω))) := hQ ▸ hQfin
    refine ⟨fun t => b none t / d t, (hb none).div hd, ?_⟩
    have hac : ν.withDensity (fun ω => b none (T ω)) ≪
        ν.withDensity (fun ω => d (T ω)) := by
      rw [← hν none, ← hQ]
      exact hQdom θ
    calc
      P θ = ν.withDensity (fun ω => b none (T ω)) := hν none
      _ = (ν.withDensity fun ω => d (T ω)).withDensity (fun ω => b none (T ω) / d (T ω)) :=
        (withDensity_div_of_absolutelyContinuous ν (hbT none) hdT hac).symm
      _ = Q.withDensity (fun ω => b none (T ω) / d (T ω)) := by rw [hQ]
  choose g hg hfac using hfactor
  have hh := Measure.measurable_rnDeriv Q μ
  refine ⟨g, Q.rnDeriv μ, hg, hh, fun θ => ?_⟩
  have hgT : Measurable (fun ω => g θ (T ω)) := (hg θ).comp hT
  calc
    P θ = Q.withDensity (fun ω => g θ (T ω)) := hfac θ
    _ = (μ.withDensity (Q.rnDeriv μ)).withDensity (fun ω => g θ (T ω)) :=
      congrArg (fun ν => ν.withDensity (fun ω => g θ (T ω)))
        (Measure.withDensity_rnDeriv_eq Q μ hQμ).symm
    _ = μ.withDensity (Q.rnDeriv μ * fun ω => g θ (T ω)) := (withDensity_mul μ hh hgT).symm
    _ = μ.withDensity (fun ω => g θ (T ω) * Q.rnDeriv μ ω) := by
      congr 1
      funext ω
      exact mul_comm _ _

end

end MathlibExt.Probability.Statistics.Sufficiency
