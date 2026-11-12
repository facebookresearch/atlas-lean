/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Measure.MeasuredSets
import Mathlib.Order.CompletePartialOrder
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Independence.ZeroOne
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring

@[expose] public section

section

open MeasureTheory
open scoped ENNReal

namespace MathlibExt.Probability.HewittSavageWanted

/-!
# Hewitt–Savage zero–one law

The iid symmetric zero–one law on Polish spaces.
-/

/-- Any measurable set in an iid countable product can be approximated by a finite cylinder. -/
private theorem exists_cylinder_approx {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (E : Set (ℕ → S)) (hE : MeasurableSet E) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ F ∈ measurableCylinders (fun _ : ℕ => S),
      Measure.infinitePi (fun _ : ℕ => μ) (symmDiff F E) < ε := by
  have hcov : ∃ D : Set (Set (ℕ → S)), D.Countable ∧
      D ⊆ measurableCylinders (fun _ : ℕ => S) ∧
      Measure.infinitePi (fun _ : ℕ => μ) (⋃₀ D)ᶜ = 0 := by
    refine ⟨{Set.univ}, Set.countable_singleton _, ?_, ?_⟩
    · intro t ht
      simp only [Set.mem_singleton_iff] at ht
      rw [ht]
      exact univ_mem_measurableCylinders _
    · rw [Set.sUnion_singleton, Set.compl_univ, measure_empty]
  have hgen : (inferInstance : MeasurableSpace (ℕ → S)) =
      MeasurableSpace.generateFrom (measurableCylinders (fun _ : ℕ => S)) :=
    generateFrom_measurableCylinders.symm
  exact exists_measure_symmDiff_lt_of_generateFrom_isSetRing
    isSetRing_measurableCylinders hcov hgen hE hε

/-- Precomposing with a permutation of `ℕ` is measurable. -/
private theorem measurable_comp_perm {S : Type*} [MeasurableSpace S] (σ : Equiv.Perm ℕ) :
    Measurable (fun ω : ℕ → S => ω ∘ ⇑σ) :=
  Measurable.of_eval fun i => measurable_pi_apply (⇑σ i)

/-- An iid product measure is invariant under permuting coordinates. -/
private theorem map_comp_perm {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] (σ : Equiv.Perm ℕ) :
    (Measure.infinitePi (fun _ : ℕ => μ)).map (fun ω : ℕ → S => ω ∘ ⇑σ) =
      Measure.infinitePi (fun _ : ℕ => μ) := by
  have heq : (fun ω : ℕ → S => ω ∘ ⇑σ) = (fun ω : ℕ → S => fun i => ω (⇑σ i)) := rfl
  rw [heq]
  exact Measure.map_infinitePi_infinitePi_of_inj
    (P := fun _ : ℕ => μ) (Equiv.injective σ)

/-- Coordinate projections are independent under an iid product. -/
private theorem iIndep_comap_eval {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ] :
    ProbabilityTheory.iIndep
      (fun n : ℕ => MeasurableSpace.comap (fun ω : ℕ → S => ω n) inferInstance)
      (Measure.infinitePi (fun _ : ℕ => μ)) := by
  have h2 := (ProbabilityTheory.iIndepFun_infinitePi (P := fun _ : ℕ => μ)
    (X := fun (_ : ℕ) => (id : S → S)) (by fun_prop)).iIndep
  simpa using h2

/-- A cylinder over `J` is measurable with respect to the coordinates in `J`. -/
private theorem measurableSet_cylinderEvents_cylinder {S : Type*} [MeasurableSpace S]
    (J : Finset ℕ) (Tset : Set (∀ _ : ↥J, S)) (hTset : MeasurableSet Tset) :
    MeasurableSet[cylinderEvents (↑J : Set ℕ)] (cylinder (α := fun _ : ℕ => S) J Tset) := by
  have hrestr : Measurable[cylinderEvents (↑J : Set ℕ)]
      (fun ω : ℕ → S => fun i : ↥J => ω ↑i) := by
    rw [@measurable_pi_iff]
    intro i
    exact measurable_cylinderEvent_apply (Finset.mem_coe.mpr i.2)
  have heq : cylinder (α := fun _ : ℕ => S) J Tset =
      (fun ω : ℕ → S => fun i : ↥J => ω ↑i) ⁻¹' Tset := rfl
  rw [heq]
  exact hrestr hTset

/-- The preimage of a cylinder over `J` under a coordinate permutation is measurable
with respect to the coordinates in the permuted index set. -/
private theorem measurableSet_cylinderEvents_preimage {S : Type*} [MeasurableSpace S]
    (J : Finset ℕ) (Tset : Set (∀ _ : ↥J, S)) (hTset : MeasurableSet Tset)
    (σ : Equiv.Perm ℕ) :
    MeasurableSet[cylinderEvents (⇑σ '' ↑J : Set ℕ)]
      ((fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' (cylinder (α := fun _ : ℕ => S) J Tset)) := by
  have hmap : Measurable[cylinderEvents (⇑σ '' ↑J : Set ℕ)]
      (fun ω : ℕ → S => fun i : ↥J => ω (⇑σ ↑i)) := by
    rw [@measurable_pi_iff]
    intro i
    have hmem : ⇑σ ↑i ∈ ⇑σ '' (↑J : Set ℕ) := ⟨↑i, Finset.mem_coe.mpr i.2, rfl⟩
    exact measurable_cylinderEvent_apply hmem
  have heq : (fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' (cylinder (α := fun _ : ℕ => S) J Tset) =
      (fun ω : ℕ → S => fun i : ↥J => ω (⇑σ ↑i)) ⁻¹' Tset :=
    (Set.preimage_comp).symm
  rw [heq]
  exact hmap hTset

/-- **Hewitt–Savage zero–one law.** Let $\mu$ be a probability measure on a measurable space $S$,
and let $E \subseteq S^{\mathbb{N}}$ be a set that is measurable for the product σ-algebra and
invariant under every finitely supported permutation $\sigma$ of $\mathbb{N}$, that is,
$\{\omega : \omega \circ \sigma \in E\} = E$ whenever $\sigma$ moves only finitely many points.
Then $E$ has measure $0$ or $1$ under the product measure $\mu^{\otimes \mathbb{N}}$.

No topological assumption on $S$ is needed. -/
theorem hewitt_savage_zero_one_general
    {S : Type*} [MeasurableSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (E : Set (ℕ → S)) (hE : MeasurableSet E)
    (hSym : ∀ (σ : Equiv.Perm ℕ), Set.Finite {n : ℕ | σ n ≠ n} →
      (fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' E = E) :
    Measure.infinitePi (fun _ : ℕ => μ) E = 0 ∨
      Measure.infinitePi (fun _ : ℕ => μ) E = 1 := by
  have hne : Measure.infinitePi (fun _ : ℕ => μ) E ≠ ∞ := measure_ne_top _ _
  suffices hsq : Measure.infinitePi (fun _ : ℕ => μ) E =
      Measure.infinitePi (fun _ : ℕ => μ) E * Measure.infinitePi (fun _ : ℕ => μ) E by
    have hle : Measure.infinitePi (fun _ : ℕ => μ) E ≤ 1 := prob_le_one
    have hrr : (Measure.infinitePi (fun _ : ℕ => μ) E).toReal =
        (Measure.infinitePi (fun _ : ℕ => μ) E).toReal *
          (Measure.infinitePi (fun _ : ℕ => μ) E).toReal := by
      have h2 := congrArg ENNReal.toReal hsq
      rwa [ENNReal.toReal_mul] at h2
    have hr1 : (Measure.infinitePi (fun _ : ℕ => μ) E).toReal ≤ 1 :=
      calc (Measure.infinitePi (fun _ : ℕ => μ) E).toReal ≤ (1 : ℝ≥0∞).toReal :=
            (ENNReal.toReal_le_toReal hne ENNReal.one_ne_top).mpr hle
        _ = 1 := ENNReal.toReal_one
    have h01 : (Measure.infinitePi (fun _ : ℕ => μ) E).toReal = 0 ∨
        (Measure.infinitePi (fun _ : ℕ => μ) E).toReal = 1 := by
      have hfactor : (Measure.infinitePi (fun _ : ℕ => μ) E).toReal *
          (1 - (Measure.infinitePi (fun _ : ℕ => μ) E).toReal) = 0 := by
        have h : (Measure.infinitePi (fun _ : ℕ => μ) E).toReal *
            (1 - (Measure.infinitePi (fun _ : ℕ => μ) E).toReal) =
            (Measure.infinitePi (fun _ : ℕ => μ) E).toReal -
              (Measure.infinitePi (fun _ : ℕ => μ) E).toReal *
                (Measure.infinitePi (fun _ : ℕ => μ) E).toReal := by ring
        rw [← hrr, sub_self] at h
        exact h
      rcases mul_eq_zero.mp hfactor with h | h
      · exact Or.inl h
      · exact Or.inr (by linarith)
    rcases h01 with h0 | h1
    · refine Or.inl ?_
      have hPE : Measure.infinitePi (fun _ : ℕ => μ) E =
          ENNReal.ofReal (Measure.infinitePi (fun _ : ℕ => μ) E).toReal :=
        (ENNReal.ofReal_toReal hne).symm
      rw [hPE, h0, ENNReal.ofReal_zero]
    · refine Or.inr ?_
      have hPE : Measure.infinitePi (fun _ : ℕ => μ) E =
          ENNReal.ofReal (Measure.infinitePi (fun _ : ℕ => μ) E).toReal :=
        (ENNReal.ofReal_toReal hne).symm
      rw [hPE, h1, ENNReal.ofReal_one]
  have key : ∀ δ : ℝ, 0 < δ →
      |(Measure.infinitePi (fun _ : ℕ => μ) E).toReal -
        (Measure.infinitePi (fun _ : ℕ => μ) E).toReal *
          (Measure.infinitePi (fun _ : ℕ => μ) E).toReal| ≤ 4 * δ := by
    intro δ hδ
    obtain ⟨F, hFmem, hFapprox⟩ :=
      exists_cylinder_approx μ E hE (ENNReal.ofReal_pos.mpr hδ)
    have hFreal : ((Measure.infinitePi (fun _ : ℕ => μ) (symmDiff F E))).toReal < δ := by
      have hfin : Measure.infinitePi (fun _ : ℕ => μ) (symmDiff F E) ≠ ∞ :=
        measure_ne_top _ _
      have h2 : (Measure.infinitePi (fun _ : ℕ => μ) (symmDiff F E)).toReal <
          (ENNReal.ofReal δ).toReal :=
        (ENNReal.toReal_lt_toReal hfin ENNReal.ofReal_ne_top).mpr hFapprox
      rwa [ENNReal.toReal_ofReal hδ.le] at h2
    rw [mem_measurableCylinders] at hFmem
    obtain ⟨J, Tset, hTset, hFeq⟩ := hFmem
    obtain ⟨N, hN⟩ := Finset.exists_nat_subset_range J
    have hJmem : ∀ j : ℕ, j ∈ J → j < N := fun j hj => Finset.mem_range.mp (hN hj)
    have hinv : Function.Involutive
        (fun i : ℕ => if i < N then i + N else if i < 2 * N then i - N else i) := by
      intro i
      dsimp only
      split_ifs <;> omega
    set σ : Equiv.Perm ℕ := Equiv.ofBijective _ hinv.bijective with hσdef
    have hσ : ∀ n : ℕ, ⇑σ n =
        (if n < N then n + N else if n < 2 * N then n - N else n) := fun n => rfl
    have hσfin : Set.Finite {n : ℕ | ⇑σ n ≠ n} := by
      apply Set.Finite.subset (Finset.finite_toSet (Finset.range (2 * N)))
      intro n hn
      have hn' : ⇑σ n ≠ n := hn
      rw [Finset.mem_coe, Finset.mem_range]
      by_contra hlt
      push Not at hlt
      exact hn' (by
        rw [hσ n, ite_eq_right (show ¬ n < N by omega), ite_eq_right (show ¬ n < 2 * N by omega)])
    have hTE : (fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' E = E := hSym σ hσfin
    have hσimg : ⇑σ '' (↑J : Set ℕ) ⊆ (↑J : Set ℕ)ᶜ := by
      intro x hx
      obtain ⟨m, hmJ, rfl⟩ := hx
      rw [Set.mem_compl_iff]
      intro hmem
      have hmN : m < N := hJmem m (Finset.mem_coe.mp hmJ)
      have hlt : ⇑σ m < N := hJmem _ (Finset.mem_coe.mp hmem)
      rw [hσ m, ite_eq_left hmN] at hlt
      omega
    have hcoord := iIndep_comap_eval μ
    have hle : ∀ n : ℕ, MeasurableSpace.comap (fun ω : ℕ → S => ω n) inferInstance ≤
        (inferInstance : MeasurableSpace (ℕ → S)) :=
      fun n => (measurable_pi_apply n).comap_le
    have hbi := ProbabilityTheory.indep_biSup_compl hle hcoord (↑J : Set ℕ)
    have hB : (⨆ n ∈ (↑J : Set ℕ)ᶜ,
          MeasurableSpace.comap (fun ω : ℕ → S => ω n) inferInstance) =
        cylinderEvents ((↑J : Set ℕ)ᶜ) := rfl
    rw [hB] at hbi
    have hIndep : ProbabilityTheory.Indep (cylinderEvents (↑J : Set ℕ))
        (cylinderEvents (⇑σ '' ↑J : Set ℕ)) (Measure.infinitePi (fun _ : ℕ => μ)) :=
      ProbabilityTheory.indep_of_indep_of_le_right hbi (cylinderEvents_mono hσimg)
    have hFev : MeasurableSet[cylinderEvents (↑J : Set ℕ)] F := by
      rw [hFeq]
      exact measurableSet_cylinderEvents_cylinder J Tset hTset
    have hF'ev : MeasurableSet[cylinderEvents (⇑σ '' ↑J : Set ℕ)]
        ((fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' F) := by
      rw [hFeq]
      exact measurableSet_cylinderEvents_preimage J Tset hTset σ
    have hindep := hIndep.indepSet_of_measurableSet hFev hF'ev
    have hmul : Measure.infinitePi (fun _ : ℕ => μ)
          (F ∩ (fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' F) =
        Measure.infinitePi (fun _ : ℕ => μ) F *
          Measure.infinitePi (fun _ : ℕ => μ)
            ((fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' F) :=
      ProbabilityTheory.IndepSet.measure_inter_eq_mul hindep
    have hTmeas : Measurable (fun ω : ℕ → S => ω ∘ ⇑σ) := measurable_comp_perm σ
    have hmap : (Measure.infinitePi (fun _ : ℕ => μ)).map (fun ω : ℕ → S => ω ∘ ⇑σ) =
        Measure.infinitePi (fun _ : ℕ => μ) := map_comp_perm μ σ
    have hFmeas : MeasurableSet F := by
      rw [hFeq]
      exact MeasurableSet.cylinder J hTset
    have hF'meas : MeasurableSet ((fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' F) :=
      hTmeas hFmeas
    have hPF' : Measure.infinitePi (fun _ : ℕ => μ)
          ((fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' F) =
        Measure.infinitePi (fun _ : ℕ => μ) F := by
      rw [← Measure.map_apply hTmeas hFmeas, hmap]
    have hpre : (fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' (symmDiff F E) =
        symmDiff ((fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' F) E := by
      rw [Set.preimage_symmDiff, hTE]
    have hEF' : Measure.infinitePi (fun _ : ℕ => μ)
          (symmDiff E ((fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' F)) =
        Measure.infinitePi (fun _ : ℕ => μ) (symmDiff F E) := by
      calc Measure.infinitePi (fun _ : ℕ => μ)
              (symmDiff E ((fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' F))
          = Measure.infinitePi (fun _ : ℕ => μ)
              (symmDiff ((fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' F) E) := by
            rw [symmDiff_comm]
        _ = Measure.infinitePi (fun _ : ℕ => μ)
              ((fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' (symmDiff F E)) := by
            rw [hpre]
        _ = Measure.infinitePi (fun _ : ℕ => μ) (symmDiff F E) := by
            rw [← Measure.map_apply hTmeas (hFmeas.symmDiff hE), hmap]
    have hq' : ((Measure.infinitePi (fun _ : ℕ => μ))
          ((fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' F)).toReal =
        ((Measure.infinitePi (fun _ : ℕ => μ)) F).toReal := by
      rw [hPF']
    have hmulr : ((Measure.infinitePi (fun _ : ℕ => μ))
          (F ∩ (fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' F)).toReal =
        ((Measure.infinitePi (fun _ : ℕ => μ)) F).toReal *
          ((Measure.infinitePi (fun _ : ℕ => μ))
            ((fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' F)).toReal := by
      rw [hmul, ENNReal.toReal_mul]
    have e1 : |(Measure.infinitePi (fun _ : ℕ => μ) E).toReal -
        ((Measure.infinitePi (fun _ : ℕ => μ)) F).toReal| < δ := by
      have h := abs_measureReal_sub_le_measureReal_symmDiff
        (μ := Measure.infinitePi (fun _ : ℕ => μ))
        hE.nullMeasurableSet hFmeas.nullMeasurableSet
      simp only [Measure.real] at h
      have hcomm : ((Measure.infinitePi (fun _ : ℕ => μ))
            (symmDiff E F)).toReal =
          ((Measure.infinitePi (fun _ : ℕ => μ)) (symmDiff F E)).toReal := by
        rw [symmDiff_comm]
      linarith
    have e2 : |(Measure.infinitePi (fun _ : ℕ => μ) E).toReal -
        ((Measure.infinitePi (fun _ : ℕ => μ))
          ((fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' F)).toReal| < δ := by
      have h := abs_measureReal_sub_le_measureReal_symmDiff
        (μ := Measure.infinitePi (fun _ : ℕ => μ))
        hE.nullMeasurableSet hF'meas.nullMeasurableSet
      simp only [Measure.real] at h
      have hcongr : ((Measure.infinitePi (fun _ : ℕ => μ))
            (symmDiff E ((fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' F))).toReal =
          ((Measure.infinitePi (fun _ : ℕ => μ)) (symmDiff F E)).toReal := by
        rw [hEF']
      linarith
    have hcapmeas : MeasurableSet (F ∩
        (fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' F) :=
      hFmeas.inter hF'meas
    have hsub2 : symmDiff E (F ∩
          (fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' F) ⊆
        symmDiff E F ∪
          symmDiff E ((fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' F) := by
      intro x hx
      rw [Set.mem_symmDiff, Set.mem_inter_iff] at hx
      rw [Set.mem_union, Set.mem_symmDiff, Set.mem_symmDiff]
      tauto
    have hub : ((Measure.infinitePi (fun _ : ℕ => μ))
          (symmDiff E (F ∩
            (fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' F))).toReal < 2 * δ := by
      have hmono : ((Measure.infinitePi (fun _ : ℕ => μ))
            (symmDiff E (F ∩
              (fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' F))).toReal ≤
          ((Measure.infinitePi (fun _ : ℕ => μ))
            (symmDiff E F ∪
              symmDiff E ((fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' F))).toReal := by
        have h := measureReal_mono (μ := Measure.infinitePi (fun _ : ℕ => μ)) hsub2
        simpa only [Measure.real] using h
      have hunion : ((Measure.infinitePi (fun _ : ℕ => μ))
            (symmDiff E F ∪
              symmDiff E ((fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' F))).toReal ≤
          ((Measure.infinitePi (fun _ : ℕ => μ)) (symmDiff E F)).toReal +
            ((Measure.infinitePi (fun _ : ℕ => μ))
              (symmDiff E ((fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' F))).toReal := by
        have h := measureReal_union_le (μ := Measure.infinitePi (fun _ : ℕ => μ))
          (symmDiff E F)
          (symmDiff E ((fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' F))
        simpa only [Measure.real] using h
      have hEF'real : ((Measure.infinitePi (fun _ : ℕ => μ))
            (symmDiff E ((fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' F))).toReal =
          ((Measure.infinitePi (fun _ : ℕ => μ)) (symmDiff F E)).toReal := by
        rw [hEF']
      have hcomm : ((Measure.infinitePi (fun _ : ℕ => μ))
            (symmDiff E F)).toReal =
          ((Measure.infinitePi (fun _ : ℕ => μ)) (symmDiff F E)).toReal := by
        rw [symmDiff_comm]
      linarith
    have hstep1 : |(Measure.infinitePi (fun _ : ℕ => μ) E).toReal -
        ((Measure.infinitePi (fun _ : ℕ => μ)) F).toReal *
          ((Measure.infinitePi (fun _ : ℕ => μ))
            ((fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' F)).toReal| < 2 * δ := by
      have h := abs_measureReal_sub_le_measureReal_symmDiff
        (μ := Measure.infinitePi (fun _ : ℕ => μ))
        hE.nullMeasurableSet hcapmeas.nullMeasurableSet
      simp only [Measure.real] at h
      rw [hmulr] at h
      have hub' := hub
      linarith
    have hstep1' : |(Measure.infinitePi (fun _ : ℕ => μ) E).toReal -
        ((Measure.infinitePi (fun _ : ℕ => μ)) F).toReal *
          ((Measure.infinitePi (fun _ : ℕ => μ)) F).toReal| < 2 * δ := by
      rw [hq'] at hstep1
      exact hstep1
    have hple : ∀ s : Set (ℕ → S), ((Measure.infinitePi (fun _ : ℕ => μ)) s).toReal ≤ 1 := by
      intro s
      calc ((Measure.infinitePi (fun _ : ℕ => μ)) s).toReal ≤ (1 : ℝ≥0∞).toReal :=
            (ENNReal.toReal_le_toReal (measure_ne_top _ _) ENNReal.one_ne_top).mpr prob_le_one
        _ = 1 := ENNReal.toReal_one
    have hqq : |((Measure.infinitePi (fun _ : ℕ => μ)) F).toReal *
          ((Measure.infinitePi (fun _ : ℕ => μ)) F).toReal -
        (Measure.infinitePi (fun _ : ℕ => μ) E).toReal *
          (Measure.infinitePi (fun _ : ℕ => μ) E).toReal| ≤ δ * 2 := by
      have hfactor : ((Measure.infinitePi (fun _ : ℕ => μ)) F).toReal *
              ((Measure.infinitePi (fun _ : ℕ => μ)) F).toReal -
            (Measure.infinitePi (fun _ : ℕ => μ) E).toReal *
              (Measure.infinitePi (fun _ : ℕ => μ) E).toReal =
          (((Measure.infinitePi (fun _ : ℕ => μ)) F).toReal -
            (Measure.infinitePi (fun _ : ℕ => μ) E).toReal) *
          (((Measure.infinitePi (fun _ : ℕ => μ)) F).toReal +
            (Measure.infinitePi (fun _ : ℕ => μ) E).toReal) := by ring
      rw [hfactor, abs_mul]
      have h1 : |((Measure.infinitePi (fun _ : ℕ => μ)) F).toReal -
          (Measure.infinitePi (fun _ : ℕ => μ) E).toReal| ≤ δ := by
        rw [abs_sub_comm]
        exact e1.le
      have h2 : |((Measure.infinitePi (fun _ : ℕ => μ)) F).toReal +
          (Measure.infinitePi (fun _ : ℕ => μ) E).toReal| ≤ 2 := by
        rw [abs_of_nonneg (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)]
        linarith [hple E, hple F]
      exact mul_le_mul h1 h2 (abs_nonneg _) hδ.le
    have hfin : |(Measure.infinitePi (fun _ : ℕ => μ) E).toReal -
        (Measure.infinitePi (fun _ : ℕ => μ) E).toReal *
          (Measure.infinitePi (fun _ : ℕ => μ) E).toReal| < 2 * δ + δ * 2 := by
      have heq : (Measure.infinitePi (fun _ : ℕ => μ) E).toReal -
            (Measure.infinitePi (fun _ : ℕ => μ) E).toReal *
              (Measure.infinitePi (fun _ : ℕ => μ) E).toReal =
          ((Measure.infinitePi (fun _ : ℕ => μ) E).toReal -
            ((Measure.infinitePi (fun _ : ℕ => μ)) F).toReal *
              ((Measure.infinitePi (fun _ : ℕ => μ)) F).toReal) +
          (((Measure.infinitePi (fun _ : ℕ => μ)) F).toReal *
              ((Measure.infinitePi (fun _ : ℕ => μ)) F).toReal -
            (Measure.infinitePi (fun _ : ℕ => μ) E).toReal *
              (Measure.infinitePi (fun _ : ℕ => μ) E).toReal) := by ring
      rw [heq]
      exact lt_of_le_of_lt (abs_add_le _ _) (add_lt_add_of_lt_of_le hstep1' hqq)
    linarith
  have hreal_sq : (Measure.infinitePi (fun _ : ℕ => μ) E).toReal =
      (Measure.infinitePi (fun _ : ℕ => μ) E).toReal *
        (Measure.infinitePi (fun _ : ℕ => μ) E).toReal := by
    have h0 : |(Measure.infinitePi (fun _ : ℕ => μ) E).toReal -
        (Measure.infinitePi (fun _ : ℕ => μ) E).toReal *
          (Measure.infinitePi (fun _ : ℕ => μ) E).toReal| ≤ 0 := by
      apply le_of_forall_pos_le_add
      intro ε hε
      have h := key (ε / 4) (by linarith)
      linarith
    rw [abs_nonpos_iff] at h0
    linarith
  have hsq : Measure.infinitePi (fun _ : ℕ => μ) E =
      Measure.infinitePi (fun _ : ℕ => μ) E * Measure.infinitePi (fun _ : ℕ => μ) E := by
    have h2 := congrArg ENNReal.ofReal hreal_sq
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hne] at h2
    exact h2
  exact hsq

/--
**Hewitt–Savage zero–one law on a Polish space.** Let $S$ be a Polish space with its Borel
σ-algebra, let $\mu$ be a probability measure on $S$, and let $E \subseteq S^{\mathbb{N}}$ be a set
that is measurable for the product σ-algebra and invariant under every finitely supported
permutation $\sigma$ of $\mathbb{N}$, that is, $\{\omega : \omega \circ \sigma \in E\} = E$
whenever $\sigma$ moves only finitely many points. Then $E$ has measure $0$ or $1$ under the
product measure $\mu^{\otimes \mathbb{N}}$.

The Polish and Borel assumptions are not used in the proof: the same conclusion holds for a
probability measure on any measurable space.

Proves `Wanted` entry `hewitt_savage_zero_one`.

Source: E. Hewitt and L. J. Savage, Symmetric measures on Cartesian products,
Trans. Amer. Math. Soc. 80 (1955) 470–501; textbook in Kallenberg, Probabilistic Symmetries and
Invariance Principles; general holds for product of identical Borel probabilities.
-/
@[nolint unusedArguments]
theorem hewitt_savage_zero_one
    {S : Type*} [TopologicalSpace S] [PolishSpace S] [MeasurableSpace S] [BorelSpace S]
    (μ : Measure S) [IsProbabilityMeasure μ]
    (E : Set (ℕ → S)) (hE : MeasurableSet E)
    (hSym : ∀ (σ : Equiv.Perm ℕ), Set.Finite {n : ℕ | σ n ≠ n} →
      (fun ω : ℕ → S => ω ∘ ⇑σ) ⁻¹' E = E) :
    Measure.infinitePi (fun _ : ℕ => μ) E = 0 ∨
      Measure.infinitePi (fun _ : ℕ => μ) E = 1 := by
  exact hewitt_savage_zero_one_general μ E hE hSym

end MathlibExt.Probability.HewittSavageWanted
