/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































































import Mathlib
import Code.Ising.GibbsSimplex
import Code.Ising.GibbsExtreme
import Code.Ising.GibbsChoquet
import Code.Ising.GibbsSimplexInfinite
import Code.Foundations.StochasticDomination
import Code.Foundations.Ergodicity

open MeasureTheory ProbabilityTheory MeasurableSpace Set Filter Topology
open scoped BigOperators ENNReal StatMech

set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace StatMech

namespace Ising

open StatMech.Lattice

variable {d : ℕ}









variable {E : Type*}









theorem gec_convexSummand_eq_on_clopen {μ ν₁ ν₂ : Measure (ConfigSpace E)} {a b : ℝ≥0∞}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hat : a ≠ ⊤) (hbt : b ≠ ⊤)
    (hconv : μ = a • ν₁ + b • ν₂)
    (h1 : ν₁ ≼c μ) (h2 : ν₂ ≼c μ) :
    μ ≼c ν₁ := by
  intro A hAcl hAu
  
  set p := μ.real A with hp
  set p₁ := ν₁.real A with hp1
  set p₂ := ν₂.real A with hp2
  set α := a.toReal with hα
  set β := b.toReal with hβ
  
  have hμA : μ A = a * ν₁ A + b * ν₂ A := by
    rw [hconv]; simp [Measure.add_apply, Measure.smul_apply]
  have hreal : p = α * p₁ + β * p₂ := by
    rw [hp, hp1, hp2, hα, hβ]
    unfold Measure.real
    rw [hμA, ENNReal.toReal_add (ENNReal.mul_ne_top hat (measure_ne_top ν₁ A))
      (ENNReal.mul_ne_top hbt (measure_ne_top ν₂ A)), ENNReal.toReal_mul, ENNReal.toReal_mul]
  have hαβ : α + β = 1 := by
    rw [hα, hβ, ← ENNReal.toReal_add hat hbt, hab, ENNReal.toReal_one]
  have hαpos : 0 < α := by rw [hα]; exact ENNReal.toReal_pos ha.ne' hat
  have hβpos : 0 < β := by rw [hβ]; exact ENNReal.toReal_pos hb.ne' hbt
  
  have hd1 : p₁ ≤ p := h1 A hAcl hAu
  have hd2 : p₂ ≤ p := h2 A hAcl hAu
  
  
  have hzero : α * (p - p₁) + β * (p - p₂) = 0 := by
    have : α * (p - p₁) + β * (p - p₂) = (α + β) * p - (α * p₁ + β * p₂) := by ring
    rw [this, hαβ, ← hreal]; ring
  have ht1 : 0 ≤ α * (p - p₁) := mul_nonneg hαpos.le (by linarith)
  have ht2 : 0 ≤ β * (p - p₂) := mul_nonneg hβpos.le (by linarith)
  have h1eq : α * (p - p₁) = 0 := by linarith
  have hp1eq : p = p₁ := by
    have := (mul_eq_zero.mp h1eq).resolve_left hαpos.ne'
    linarith
  
  exact le_of_eq hp1eq










theorem gec_max_extreme [Countable E] {μ ν₁ ν₂ : Measure (ConfigSpace E)} {a b : ℝ≥0∞}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hat : a ≠ ⊤) (hbt : b ≠ ⊤)
    (hconv : μ = a • ν₁ + b • ν₂)
    (h1 : ν₁ ≼c μ) (h2 : ν₂ ≼c μ) :
    ν₁ = μ ∧ ν₂ = μ := by
  have hμ1 : μ ≼c ν₁ := gec_convexSummand_eq_on_clopen ha hb hab hat hbt hconv h1 h2
  have hμ2 : μ ≼c ν₂ := by
    refine gec_convexSummand_eq_on_clopen hb ha (by rw [add_comm]; exact hab) hbt hat ?_ h2 h1
    rw [hconv, add_comm]
  exact ⟨gsi_clopen_antisymm h1 hμ1, gsi_clopen_antisymm h2 hμ2⟩






theorem gec_min_extreme [Countable E] {μ ν₁ ν₂ : Measure (ConfigSpace E)} {a b : ℝ≥0∞}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hat : a ≠ ⊤) (hbt : b ≠ ⊤)
    (hconv : μ = a • ν₁ + b • ν₂)
    (h1 : μ ≼c ν₁) (h2 : μ ≼c ν₂) :
    ν₁ = μ ∧ ν₂ = μ := by
  
  have key : ∀ (w₁ w₂ : Measure (ConfigSpace E)) (s t : ℝ≥0∞),
      IsProbabilityMeasure w₁ → IsProbabilityMeasure w₂ → 0 < s → 0 < t → s + t = 1 →
      s ≠ ⊤ → t ≠ ⊤ → μ = s • w₁ + t • w₂ → μ ≼c w₁ → μ ≼c w₂ → w₁ ≼c μ := by
    intro w₁ w₂ s t hw1 hw2 hs ht hst hsT htT hcv hm1 hm2 A hAcl hAu
    have hμA : μ A = s * w₁ A + t * w₂ A := by
      rw [hcv]; simp [Measure.add_apply, Measure.smul_apply]
    have hreal : μ.real A = s.toReal * w₁.real A + t.toReal * w₂.real A := by
      unfold Measure.real
      rw [hμA, ENNReal.toReal_add (ENNReal.mul_ne_top hsT (measure_ne_top w₁ A))
        (ENNReal.mul_ne_top htT (measure_ne_top w₂ A)), ENNReal.toReal_mul, ENNReal.toReal_mul]
    have hst' : s.toReal + t.toReal = 1 := by
      rw [← ENNReal.toReal_add hsT htT, hst, ENNReal.toReal_one]
    have hspos : 0 < s.toReal := ENNReal.toReal_pos hs.ne' hsT
    have htpos : 0 < t.toReal := ENNReal.toReal_pos ht.ne' htT
    have hd1 : μ.real A ≤ w₁.real A := hm1 A hAcl hAu
    have hd2 : μ.real A ≤ w₂.real A := hm2 A hAcl hAu
    have hzero : s.toReal * (w₁.real A - μ.real A) + t.toReal * (w₂.real A - μ.real A) = 0 := by
      have : s.toReal * (w₁.real A - μ.real A) + t.toReal * (w₂.real A - μ.real A)
          = (s.toReal * w₁.real A + t.toReal * w₂.real A) - (s.toReal + t.toReal) * μ.real A := by
        ring
      rw [this, hst', ← hreal]; ring
    have ht1 : 0 ≤ s.toReal * (w₁.real A - μ.real A) := mul_nonneg hspos.le (by linarith)
    have ht2 : 0 ≤ t.toReal * (w₂.real A - μ.real A) := mul_nonneg htpos.le (by linarith)
    have h1eq : s.toReal * (w₁.real A - μ.real A) = 0 := by linarith
    have hp1eq : w₁.real A = μ.real A := by
      have := (mul_eq_zero.mp h1eq).resolve_left hspos.ne'
      linarith
    exact le_of_eq hp1eq
  have hν1 : ν₁ ≼c μ := key ν₁ ν₂ a b ‹_› ‹_› ha hb hab hat hbt hconv h1 h2
  have hν2 : ν₂ ≼c μ :=
    key ν₂ ν₁ b a ‹_› ‹_› hb ha (by rw [add_comm]; exact hab) hbt hat
      (by rw [hconv, add_comm]) h2 h1
  exact ⟨gsi_clopen_antisymm hν1 h1, gsi_clopen_antisymm hν2 h2⟩



















theorem gec_plusState_extreme (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    {ν₁ ν₂ : Measure (ConfigSpace (Site d))} [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h₁ : IsDLRState d β h ν₁) (h₂ : IsDLRState d β h ν₂)
    {a b : ℝ≥0∞} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hat : a ≠ ⊤) (hbt : b ≠ ⊤)
    (hconv : (plusState d β h : Measure (ConfigSpace (Site d))) = a • ν₁ + b • ν₂) :
    ν₁ = (plusState d β h : Measure (ConfigSpace (Site d)))
      ∧ ν₂ = (plusState d β h : Measure (ConfigSpace (Site d))) := by
  have hd1 : ν₁ ≼c (plusState d β h : Measure (ConfigSpace (Site d))) :=
    (gsi_infinite_volume_sandwich β h hβ hh ν₁ h₁).2
  have hd2 : ν₂ ≼c (plusState d β h : Measure (ConfigSpace (Site d))) :=
    (gsi_infinite_volume_sandwich β h hβ hh ν₂ h₂).2
  exact gec_max_extreme ha hb hab hat hbt hconv hd1 hd2














theorem gec_minusState_extreme (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    {ν₁ ν₂ : Measure (ConfigSpace (Site d))} [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h₁ : IsDLRState d β h ν₁) (h₂ : IsDLRState d β h ν₂)
    {a b : ℝ≥0∞} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hat : a ≠ ⊤) (hbt : b ≠ ⊤)
    (hconv : (minusState d β h : Measure (ConfigSpace (Site d))) = a • ν₁ + b • ν₂) :
    ν₁ = (minusState d β h : Measure (ConfigSpace (Site d)))
      ∧ ν₂ = (minusState d β h : Measure (ConfigSpace (Site d))) := by
  have hd1 : (minusState d β h : Measure (ConfigSpace (Site d))) ≼c ν₁ :=
    (gsi_infinite_volume_sandwich β h hβ hh ν₁ h₁).1
  have hd2 : (minusState d β h : Measure (ConfigSpace (Site d))) ≼c ν₂ :=
    (gsi_infinite_volume_sandwich β h hβ hh ν₂ h₂).1
  exact gec_min_extreme ha hb hab hat hbt hconv hd1 hd2









theorem gec_plusState_no_proper_split (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    {ν₁ ν₂ : Measure (ConfigSpace (Site d))} [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h₁ : IsDLRState d β h ν₁) (h₂ : IsDLRState d β h ν₂)
    {a b : ℝ≥0∞} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hat : a ≠ ⊤) (hbt : b ≠ ⊤)
    (hconv : (plusState d β h : Measure (ConfigSpace (Site d))) = a • ν₁ + b • ν₂) :
    ν₁ = ν₂ := by
  obtain ⟨e1, e2⟩ := gec_plusState_extreme β h hβ hh h₁ h₂ ha hb hab hat hbt hconv
  rw [e1, e2]



theorem gec_minusState_no_proper_split (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    {ν₁ ν₂ : Measure (ConfigSpace (Site d))} [IsProbabilityMeasure ν₁] [IsProbabilityMeasure ν₂]
    (h₁ : IsDLRState d β h ν₁) (h₂ : IsDLRState d β h ν₂)
    {a b : ℝ≥0∞} (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1) (hat : a ≠ ⊤) (hbt : b ≠ ⊤)
    (hconv : (minusState d β h : Measure (ConfigSpace (Site d))) = a • ν₁ + b • ν₂) :
    ν₁ = ν₂ := by
  obtain ⟨e1, e2⟩ := gec_minusState_extreme β h hβ hh h₁ h₂ ha hb hab hat hbt hconv
  rw [e1, e2]


















open StatMech.ConfigSpace

variable {G : Type*} [Group G] [MulAction G E]





theorem gec_cond_isTranslationInvariant {μ : Measure (ConfigSpace E)}
    (hμ : IsTranslationInvariant (G := G) μ)
    {s : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hinv : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) :
    IsTranslationInvariant (G := G) (μ[|s]) := by
  intro g
  have hrestr : MeasurePreserving (shift g : ConfigSpace E → ConfigSpace E)
      (μ.restrict s) (μ.restrict s) := by
    have h := (hμ g).restrict_preimage hs
    rwa [hinv g] at h
  refine ⟨measurable_shift g, ?_⟩
  rw [ProbabilityTheory.cond, Measure.map_smul, hrestr.map_eq]




theorem gec_invariant_decomp {μ : Measure (ConfigSpace E)} [IsFiniteMeasure μ]
    {s : Set (ConfigSpace E)} (hs : MeasurableSet s)
    (hs0 : μ s ≠ 0) (hsc0 : μ sᶜ ≠ 0) :
    μ = (μ s) • (μ[|s]) + (μ sᶜ) • (μ[|sᶜ]) := by
  have h1 : (μ s) • (μ[|s]) = μ.restrict s := by
    rw [ProbabilityTheory.cond, smul_smul, ENNReal.mul_inv_cancel hs0 (measure_ne_top μ s), one_smul]
  have h2 : (μ sᶜ) • (μ[|sᶜ]) = μ.restrict sᶜ := by
    rw [ProbabilityTheory.cond, smul_smul, ENNReal.mul_inv_cancel hsc0 (measure_ne_top μ sᶜ),
      one_smul]
  rw [h1, h2, Measure.restrict_add_restrict_compl hs]













theorem gec_ergodic_of_noProperSplit {μ : Measure (ConfigSpace E)} [IsProbabilityMeasure μ]
    (hti : IsTranslationInvariant (G := G) μ)
    (P : Measure (ConfigSpace E) → Prop)
    (hsplit : ∀ (ν₁ ν₂ : Measure (ConfigSpace E)) (a b : ℝ≥0∞),
      IsProbabilityMeasure ν₁ → IsProbabilityMeasure ν₂ → P ν₁ → P ν₂ →
        0 < a → 0 < b → a + b = 1 → a ≠ ⊤ → b ≠ ⊤ → μ = a • ν₁ + b • ν₂ → ν₁ = ν₂)
    (hclosure : ∀ {s : Set (ConfigSpace E)}, MeasurableSet s →
      (∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' s = s) →
        μ s ≠ 0 → μ sᶜ ≠ 0 → P (μ[|s]) ∧ P (μ[|sᶜ])) :
    IsErgodic (G := G) μ := by
  refine ⟨hti, ?_⟩
  intro s hs hinv
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hs0, hs1⟩ := hcon
  rw [measure_univ] at hs1
  have hab : μ s + μ sᶜ = 1 := by
    rw [← measure_univ (μ := μ)]; exact measure_add_measure_compl hs
  have hsc0 : μ sᶜ ≠ 0 := fun h => hs1 (by rw [h, add_zero] at hab; exact hab)
  have hinvc : ∀ g : G, (shift g : ConfigSpace E → ConfigSpace E) ⁻¹' sᶜ = sᶜ := fun g => by
    rw [Set.preimage_compl, hinv g]
  haveI hp1 : IsProbabilityMeasure (μ[|s]) := cond_isProbabilityMeasure hs0
  haveI hp2 : IsProbabilityMeasure (μ[|sᶜ]) := cond_isProbabilityMeasure hsc0
  obtain ⟨hP1, hP2⟩ := hclosure hs hinv hs0 hsc0
  have hapos : 0 < μ s := pos_iff_ne_zero.mpr hs0
  have hbpos : 0 < μ sᶜ := pos_iff_ne_zero.mpr hsc0
  have hdecomp : μ = (μ s) • (μ[|s]) + (μ sᶜ) • (μ[|sᶜ]) := gec_invariant_decomp hs hs0 hsc0
  have heq : (μ[|s]) = (μ[|sᶜ]) :=
    hsplit (μ[|s]) (μ[|sᶜ]) (μ s) (μ sᶜ) hp1 hp2 hP1 hP2 hapos hbpos hab
      (measure_ne_top μ s) (measure_ne_top μ sᶜ) hdecomp
  have hval1 : (μ[|s]) s = 1 := cond_apply_self hs0 (measure_ne_top μ s)
  have hval2 : (μ[|sᶜ]) s = 0 := by
    rw [cond_apply hs.compl, Set.inter_comm, Set.inter_compl_self, measure_empty, mul_zero]
  rw [heq, hval2] at hval1
  exact one_ne_zero hval1.symm


























theorem gec_plusState_isErgodic_of_closure (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))))
    (hclosure : ∀ {s : Set (ConfigSpace (Site d))}, MeasurableSet s →
      (∀ g : Multiplicative (Site d),
        (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' s = s) →
      (plusState d β h : Measure (ConfigSpace (Site d))) s ≠ 0 →
      (plusState d β h : Measure (ConfigSpace (Site d))) sᶜ ≠ 0 →
        IsDLRState d β h ((plusState d β h : Measure (ConfigSpace (Site d)))[|s])
          ∧ IsDLRState d β h ((plusState d β h : Measure (ConfigSpace (Site d)))[|sᶜ])) :
    IsErgodic (G := Multiplicative (Site d))
      (plusState d β h : Measure (ConfigSpace (Site d))) := by
  refine gec_ergodic_of_noProperSplit hti
    (fun ν => ∃ _ : IsFiniteMeasure ν, IsDLRState d β h ν) ?_ ?_
  · intro ν₁ ν₂ a b hpν1 hpν2 hD1 hD2 ha hb hab hat hbt hconv
    obtain ⟨_, hD1'⟩ := hD1; obtain ⟨_, hD2'⟩ := hD2
    exact gec_plusState_no_proper_split β h hβ hh hD1' hD2' ha hb hab hat hbt hconv
  · intro s hs hinv hs0 hsc0
    haveI := cond_isProbabilityMeasure hs0
    haveI := cond_isProbabilityMeasure hsc0
    obtain ⟨hc1, hc2⟩ := hclosure hs hinv hs0 hsc0
    exact ⟨⟨inferInstance, hc1⟩, ⟨inferInstance, hc2⟩⟩



theorem gec_minusState_isErgodic_of_closure (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h)
    (hti : IsTranslationInvariant (G := Multiplicative (Site d))
      (minusState d β h : Measure (ConfigSpace (Site d))))
    (hclosure : ∀ {s : Set (ConfigSpace (Site d))}, MeasurableSet s →
      (∀ g : Multiplicative (Site d),
        (shift g : ConfigSpace (Site d) → ConfigSpace (Site d)) ⁻¹' s = s) →
      (minusState d β h : Measure (ConfigSpace (Site d))) s ≠ 0 →
      (minusState d β h : Measure (ConfigSpace (Site d))) sᶜ ≠ 0 →
        IsDLRState d β h ((minusState d β h : Measure (ConfigSpace (Site d)))[|s])
          ∧ IsDLRState d β h ((minusState d β h : Measure (ConfigSpace (Site d)))[|sᶜ])) :
    IsErgodic (G := Multiplicative (Site d))
      (minusState d β h : Measure (ConfigSpace (Site d))) := by
  refine gec_ergodic_of_noProperSplit hti
    (fun ν => ∃ _ : IsFiniteMeasure ν, IsDLRState d β h ν) ?_ ?_
  · intro ν₁ ν₂ a b hpν1 hpν2 hD1 hD2 ha hb hab hat hbt hconv
    obtain ⟨_, hD1'⟩ := hD1; obtain ⟨_, hD2'⟩ := hD2
    exact gec_minusState_no_proper_split β h hβ hh hD1' hD2' ha hb hab hat hbt hconv
  · intro s hs hinv hs0 hsc0
    haveI := cond_isProbabilityMeasure hs0
    haveI := cond_isProbabilityMeasure hsc0
    obtain ⟨hc1, hc2⟩ := hclosure hs hinv hs0 hsc0
    exact ⟨⟨inferInstance, hc1⟩, ⟨inferInstance, hc2⟩⟩

end Ising

end StatMech
